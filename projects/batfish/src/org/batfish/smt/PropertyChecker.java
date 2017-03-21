package org.batfish.smt;


import com.microsoft.z3.*;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.*;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.smt.answers.SmtManyAnswerElement;
import org.batfish.smt.answers.SmtOneAnswerElement;
import org.batfish.smt.utils.PathRegexes;
import org.batfish.smt.utils.PatternUtils;

import java.util.*;
import java.util.regex.Pattern;

/**
 * <p>A collection of functions to checks if various properties
 * hold in the network. The general flow is to create a new encoder
 * object for the network, instrument additional properties on top of
 * the model, and then assert the negation of the property of interest.</p>
 *
 * @author Ryan Beckett
 */
public class PropertyChecker {

    /*
     * Compute the forwarding behavior for the network. This adds no additional
     * constraints on top of the base network encoding. Forwarding will be
     * determined only for a particular network environment, failure scenario,
     * and data plane packet.
     */
    public static AnswerElement computeForwarding(IBatfish batfish, HeaderSpace h) {
        Encoder encoder = new Encoder(h, batfish);
        encoder.computeEncoding();
        if (encoder.getMainSlice().getLogicalGraph().getEnvironmentVars().size() > 0) {
            System.out.println("Warning: forwarding computed for only a single concrete " +
                    "environment");
        }
        VerificationResult result = encoder.verify();
        SmtOneAnswerElement answer = new SmtOneAnswerElement();
        answer.setResult(result);

        // EncoderSlice slice = encoder.getMainSlice();
        // result.debug(slice, null);

        return answer;
    }

    /*
     * Compute if a collection of source routers can reach a collection of destination
     * ports. This is broken up into multiple queries, one for each destination port.
     */
    public static AnswerElement computeReachability(IBatfish batfish, HeaderSpace h, String
            ingressNodeRegexStr, String notIngressNodeRegexStr, String finalNodeRegexStr, String
            notFinalNodeRegexStr, String finalIfaceRegexStr, String notFinalIfaceRegexStr) {

        PathRegexes p = new PathRegexes(finalNodeRegexStr, notFinalNodeRegexStr,
                finalIfaceRegexStr, notFinalIfaceRegexStr, ingressNodeRegexStr,
                notIngressNodeRegexStr);

        Graph graph = new Graph(batfish);
        List<GraphEdge> destinationPorts = PatternUtils.findMatchingEdges(graph, p);
        List<String> sourceRouters = PatternUtils.findMatchingNodes(graph, p);
        Map<String, VerificationResult> result = new HashMap<>();

        for (GraphEdge ge : destinationPorts) {
            // Add the interface destination
            boolean addedDestination = false;
            if (h.getDstIps().isEmpty()) {
                addedDestination = true;
                Prefix destination = ge.getStart().getPrefix();
                IpWildcard dst = new IpWildcard(destination);
                h.getDstIps().add(dst);
            }

            Encoder enc = new Encoder(h, graph);
            enc.computeEncoding();

            EncoderSlice slice = enc.getMainSlice();

            PropertyAdder pa = new PropertyAdder(slice);
            Map<String, BoolExpr> reachableVars = pa.instrumentReachability(ge);

            Context ctx = enc.getCtx();

            BoolExpr allReach = ctx.mkBool(false);
            for (String router : sourceRouters) {
                BoolExpr reach = reachableVars.get(router);
                allReach = ctx.mkOr(allReach, ctx.mkNot(reach));
            }
            enc.add(allReach);

            VerificationResult res = enc.verify();
            result.put(ge.getRouter() + "," + ge.getStart().getName(), res);

            // Remove the interface
            if (addedDestination) {
                h.getDstIps().clear();
            }
        }

        SmtManyAnswerElement answer = new SmtManyAnswerElement();
        answer.setResult(result);
        return answer;
    }

    /*
     * Compute if there can ever be a black hole for routers that are
     * not at the edge of the network. This is almost certainly a bug.
     */
    public static AnswerElement computeBlackHole(IBatfish batfish) {
        Graph graph = new Graph(batfish);

        HeaderSpace h = new HeaderSpace();

        Encoder enc = new Encoder(h, graph);
        enc.computeEncoding();

        Context ctx = enc.getCtx();

        EncoderSlice slice = enc.getMainSlice();

        // Collect routers that have no host/environment edge
        List<String> toCheck = new ArrayList<>();
        graph.getEdgeMap().forEach((router, edges) -> {
            boolean check = true;
            for (GraphEdge edge : edges) {
                if (edge.getEnd() == null) {
                    check = false;
                    break;
                }
            }
            if (check) {
                toCheck.add(router);
            }
        });

        // Ensure the router never receives traffic and then drops the traffic
        BoolExpr someBlackHole = ctx.mkBool(false);

        for (String router : toCheck) {
            Map<GraphEdge, BoolExpr> edges = slice.getSymbolicDecisions().getDataForwarding().get
                    (router);
            BoolExpr doesNotFwd = ctx.mkBool(true);
            for (Map.Entry<GraphEdge, BoolExpr> entry : edges.entrySet()) {
                BoolExpr dataFwd = entry.getValue();
                doesNotFwd = ctx.mkAnd(doesNotFwd, ctx.mkNot(dataFwd));
            }

            BoolExpr isFwdTo = ctx.mkBool(false);
            Set<String> neighbors = graph.getNeighbors().get(router);
            for (String n : neighbors) {
                for (Map.Entry<GraphEdge, BoolExpr> entry : slice.getSymbolicDecisions()
                                                               .getDataForwarding().get(n)
                                                               .entrySet()) {
                    GraphEdge ge = entry.getKey();
                    BoolExpr fwd = entry.getValue();
                    if (router.equals(ge.getPeer())) {
                        isFwdTo = ctx.mkOr(isFwdTo, fwd);
                    }
                }
            }

            someBlackHole = ctx.mkOr(someBlackHole, ctx.mkAnd(isFwdTo, doesNotFwd));
        }

        enc.add(someBlackHole);

        VerificationResult result = enc.verify();

        SmtOneAnswerElement answer = new SmtOneAnswerElement();
        answer.setResult(result);
        return answer;
    }

    /*
     * Compute whether the path length will always be bounded by a constant k
     * for a collection of source routers to any of a number of destination ports.
     */
    public static AnswerElement computeBoundedLength(IBatfish batfish, HeaderSpace h, String
            ingressNodeRegexStr, String notIngressNodeRegexStr, String finalNodeRegexStr, String
            notFinalNodeRegexStr, String finalIfaceRegexStr, String notFinalIfaceRegexStr, int k) {

        PathRegexes p = new PathRegexes(finalNodeRegexStr, notFinalNodeRegexStr,
                finalIfaceRegexStr, notFinalIfaceRegexStr, ingressNodeRegexStr,
                notIngressNodeRegexStr);

        Graph graph = new Graph(batfish);
        List<GraphEdge> destinationPorts = PatternUtils.findMatchingEdges(graph, p);
        List<String> sourceRouters = PatternUtils.findMatchingNodes(graph, p);
        Map<String, VerificationResult> result = new HashMap<>();

        for (GraphEdge ge : destinationPorts) {
            // Add the interface destination
            boolean addedDestination = false;
            if (h.getDstIps().isEmpty()) {
                addedDestination = true;
                Prefix destination = ge.getStart().getPrefix();
                IpWildcard dst = new IpWildcard(destination);
                h.getDstIps().add(dst);
            }

            Encoder enc = new Encoder(h, graph);
            enc.computeEncoding();

            EncoderSlice slice = enc.getMainSlice();

            PropertyAdder pa = new PropertyAdder(slice);
            Map<String, ArithExpr> lenVars = pa.instrumentPathLength(ge);

            Context ctx = enc.getCtx();

            // All routers bounded by a particular length
            BoolExpr allBounded = ctx.mkBool(false);
            for (String router : sourceRouters) {
                ArithExpr len = lenVars.get(router);
                ArithExpr bound = ctx.mkInt(k);
                allBounded = ctx.mkOr(allBounded, ctx.mkGt(len, bound));
            }
            enc.add(allBounded);

            VerificationResult res = enc.verify();
            result.put(ge.getRouter() + "," + ge.getStart().getName(), res);

            // Remove the interface destination
            if (addedDestination) {
                h.getDstIps().clear();
            }
        }

        SmtManyAnswerElement answer = new SmtManyAnswerElement();
        answer.setResult(result);
        return answer;
    }

    /*
     * Computes whether a collection of source routers will always have
     * equal path length to destination port(s).
     */
    public static AnswerElement computeEqualLength(IBatfish batfish, HeaderSpace h, String
            ingressNodeRegexStr, String notIngressNodeRegexStr, String finalNodeRegexStr, String
            notFinalNodeRegexStr, String finalIfaceRegexStr, String notFinalIfaceRegexStr) {

        PathRegexes p = new PathRegexes(finalNodeRegexStr, notFinalNodeRegexStr,
                finalIfaceRegexStr, notFinalIfaceRegexStr, ingressNodeRegexStr,
                notIngressNodeRegexStr);

        Graph graph = new Graph(batfish);
        List<GraphEdge> destinationPorts = PatternUtils.findMatchingEdges(graph, p);
        List<String> sourceRouters = PatternUtils.findMatchingNodes(graph, p);
        Map<String, VerificationResult> result = new HashMap<>();

        for (GraphEdge ge : destinationPorts) {
            // Add the interface destination
            boolean addedDestination = false;
            if (h.getDstIps().isEmpty()) {
                addedDestination = true;
                Prefix destination = ge.getStart().getPrefix();
                IpWildcard dst = new IpWildcard(destination);
                h.getDstIps().add(dst);
            }

            Encoder enc = new Encoder(h, graph);
            enc.computeEncoding();

            EncoderSlice slice = enc.getMainSlice();

            PropertyAdder pa = new PropertyAdder(slice);
            Map<String, ArithExpr> lenVars = pa.instrumentPathLength(ge);

            Context ctx = enc.getCtx();

            // All routers have the same length through transitivity
            List<Expr> lens = new ArrayList<>();
            for (String router : sourceRouters) {
                lens.add(lenVars.get(router));
            }
            BoolExpr allEqual = PropertyAdder.allEqual(ctx, lens);

            enc.add(ctx.mkNot(allEqual));

            VerificationResult res = enc.verify();
            result.put(ge.getRouter() + "," + ge.getStart().getName(), res);

            if (addedDestination) {
                h.getDstIps().clear();
            }
        }

        SmtManyAnswerElement answer = new SmtManyAnswerElement();
        answer.setResult(result);
        return answer;
    }


    // TODO: this is broken due to peer regex
    /*
     * Computes whether load balancing for each source node in a collection is
     * within some threshold k of the each other.
     */
    public static AnswerElement computeLoadBalance(IBatfish batfish, HeaderSpace h, String
            ingressNodeRegexStr, String notIngressNodeRegexStr, String finalNodeRegexStr, String
            notFinalNodeRegexStr, String finalIfaceRegexStr, String notFinalIfaceRegexStr, int k) {

        PathRegexes p = new PathRegexes(finalNodeRegexStr, notFinalNodeRegexStr,
                finalIfaceRegexStr, notFinalIfaceRegexStr, ingressNodeRegexStr,
                notIngressNodeRegexStr);

        Graph graph = new Graph(batfish);
        List<GraphEdge> destinationPorts = PatternUtils.findMatchingEdges(graph, p);
        List<String> sourceRouters = PatternUtils.findMatchingNodes(graph, p);
        Map<String, List<String>> peerRouters = new HashMap<>();
        Map<String, VerificationResult> result = new HashMap<>();

        List<String> pRouters = PatternUtils.findMatchingNodes(graph, p);

        // TODO: refactor this out separately
        for (String router : sourceRouters) {
            List<String> list = new ArrayList<>();
            peerRouters.put(router, list);
            Set<String> neighbors = graph.getNeighbors().get(router);
            for (String peer : pRouters) {
                if (neighbors.contains(peer)) {
                    list.add(peer);
                }
            }
        }

        for (GraphEdge ge : destinationPorts) {
            // Add the interface destination
            boolean addedDestination = false;
            if (h.getDstIps().isEmpty()) {
                addedDestination = true;
                Prefix destination = ge.getStart().getPrefix();
                IpWildcard dst = new IpWildcard(destination);
                h.getDstIps().add(dst);
            }

            Encoder enc = new Encoder(h, graph);
            enc.computeEncoding();

            EncoderSlice slice = enc.getMainSlice();

            PropertyAdder pa = new PropertyAdder(slice);
            Map<String, ArithExpr> loadVars = pa.instrumentLoad(ge);

            Context ctx = enc.getCtx();

            // TODO: add threshold
            // All routers bounded by a particular length
            List<Expr> peerLoads = new ArrayList<>();
            peerRouters.forEach((router, allPeers) -> {
                // ArithExpr load = loadVars.get(router);
                for (String peer : allPeers) {
                    peerLoads.add(loadVars.get(peer));
                }
            });
            BoolExpr evenLoads = PropertyAdder.allEqual(ctx, peerLoads);
            enc.add(ctx.mkNot(evenLoads));

            VerificationResult res = enc.verify();
            result.put(ge.getRouter() + "," + ge.getStart().getName(), res);

            if (addedDestination) {
                h.getDstIps().clear();
            }
        }

        SmtManyAnswerElement answer = new SmtManyAnswerElement();
        answer.setResult(result);
        return answer;
    }

    /*
     * Computes whether or not two routers are equivalent.
     * To be equivalent, each router must have identical intefaces.
     *
     * We then relate the environments on each interface for each router
     * so that they are required to be equal.
     *
     * We finally check that their forwarding decisions and exported messages
     * will be equal given their equal inputs.
     */
    public static AnswerElement computeLocalConsistency(IBatfish batfish, Pattern n) {
        Graph graph = new Graph(batfish);
        List<String> routers = PatternUtils.findMatchingNodes(graph, n, Pattern.compile(""));

        Map<String, VerificationResult> result = new HashMap<>();

        HeaderSpace h = new HeaderSpace();

        int len = routers.size();
        if (len <= 1) {
            SmtManyAnswerElement answer = new SmtManyAnswerElement();
            answer.setResult(new HashMap<>());
            return answer;
        }

        for (int i = 0; i < len - 1; i++) {
            String r1 = routers.get(i);
            String r2 = routers.get(i + 1);

            // TODO: reorder to encode after checking if we can compare them

            // Create transfer function for router 1
            Set<String> toModel1 = new TreeSet<>();
            toModel1.add(r1);
            Graph g1 = new Graph(batfish, toModel1);
            Encoder e1 = new Encoder(h, g1);
            e1.computeEncoding();

            Context ctx = e1.getCtx();

            // Create transfer function for router 2
            // Reuse the context and solver
            Set<String> toModel2 = new TreeSet<>();
            toModel2.add(r2);
            Graph g2 = new Graph(batfish, toModel2);
            Encoder e2 = new Encoder(e1, g2);
            e2.computeEncoding();

            EncoderSlice slice1 = e1.getMainSlice();
            EncoderSlice slice2 = e2.getMainSlice();

            // Ensure that the two routers have the same interfaces for comparison
            Pattern p = Pattern.compile(".*");
            Pattern neg = Pattern.compile("");
            List<GraphEdge> edges1 = PatternUtils.findMatchingEdges(g1, p, neg, p, neg);
            List<GraphEdge> edges2 = PatternUtils.findMatchingEdges(g2, p, neg, p, neg);
            Set<String> ifaces1 = interfaces(edges1);
            Set<String> ifaces2 = interfaces(edges2);

            if (!(ifaces1.containsAll(ifaces2) && ifaces2.containsAll(ifaces1))) {
                String msg = String.format("Routers %s and %s have different interfaces", r1, r2);
                System.out.println(msg);
                SmtManyAnswerElement answer = new SmtManyAnswerElement();
                answer.setResult(new TreeMap<>());
                return answer;
            }

            // TODO: check running same protocols?

            // Map<String, Map<Protocol, Map<String, EnumMap<EdgeType, LogicalEdge>>>>
            //        lgeMap1 = logicalEdgeMap(e1);
            Map<String, Map<Protocol, Map<String, EnumMap<EdgeType, LogicalEdge>>>>
                    lgeMap2 = logicalEdgeMap(slice2);

            BoolExpr equalEnvs = ctx.mkBool(true);
            BoolExpr equalOutputs = ctx.mkBool(true);
            BoolExpr equalIncomingAcls = ctx.mkBool(true);

            Configuration conf1 = g1.getConfigurations().get(r1);
            Configuration conf2 = g2.getConfigurations().get(r2);

            // Set environments equal
            for (Protocol proto1 : slice1.getProtocols().get(r1)) {
                for (ArrayList<LogicalEdge> es : slice1.getLogicalGraph().getLogicalEdges().get(r1)
                                                   .get(proto1)) {
                    for (LogicalEdge lge1 : es) {

                        String ifaceName = lge1.getEdge().getStart().getName();

                        LogicalEdge lge2 = lgeMap2.get(r2).get(proto1).get(ifaceName).get
                                (lge1.getEdgeType());

                        if (lge1.getEdgeType() == EdgeType.IMPORT) {

                            SymbolicRecord vars1 = slice1.getLogicalGraph().getEnvironmentVars().get
                                    (lge1);
                            SymbolicRecord vars2 = slice2.getLogicalGraph().getEnvironmentVars().get
                                    (lge2);

                            BoolExpr aclIn1 = slice1.getIncomingAcls().get(lge1.getEdge());
                            BoolExpr aclIn2 = slice2.getIncomingAcls().get(lge2.getEdge());

                            if (aclIn1 == null) {
                                aclIn1 = ctx.mkBool(true);
                            }
                            if (aclIn2 == null) {
                                aclIn2 = ctx.mkBool(true);
                            }

                            equalIncomingAcls = ctx.mkAnd(equalIncomingAcls, ctx.mkEq(aclIn1,
                                    aclIn2));

                            boolean hasEnv1 = (vars1 != null);
                            boolean hasEnv2 = (vars2 != null);

                            if (hasEnv1 && hasEnv2) {
                                BoolExpr samePermitted = ctx.mkEq(vars1.getPermitted(),
                                        vars2.getPermitted());

                                // Set communities equal
                                BoolExpr equalComms = e1.True();
                                for (Map.Entry<CommunityVar, BoolExpr> entry :
                                        vars1.getCommunities().entrySet()) {
                                    CommunityVar cvar = entry.getKey();
                                    BoolExpr ce1 = entry.getValue();
                                    BoolExpr ce2 = vars2.getCommunities().get(cvar);
                                    if (ce2 == null) {
                                        System.out.println("Community: " + cvar.getValue());
                                        throw new BatfishException("mismatched communities");
                                    }
                                    equalComms = e1.And(equalComms, e1.Eq(ce1, ce2));
                                }

                                BoolExpr equalVars = slice1.equal(conf1, proto1, vars1, vars2, lge1);
                                equalEnvs = ctx.mkAnd(equalEnvs, samePermitted, equalVars,
                                        equalComms);

                            } else if (hasEnv1 || hasEnv2) {
                                System.out.println("Edge1: " + lge1);
                                System.out.println("Edge2: " + lge2);
                                throw new BatfishException("one had environment");
                            }

                        } else {

                            SymbolicRecord out1 = lge1.getSymbolicRecord();
                            SymbolicRecord out2 = lge2.getSymbolicRecord();

                            equalOutputs = ctx.mkAnd(equalOutputs, slice1.equal(conf1, proto1, out1,
                                    out2, lge1));
                        }
                    }
                }
            }

            // TODO: check both have same environment variables (e.g., screw up configuring peer
            // connection)

            BoolExpr validDest;
            validDest = ignoredDestinations(ctx, slice1, r1, conf1);
            validDest = ctx.mkAnd(validDest, ignoredDestinations(ctx, slice2, r2, conf2));

            Map<String, GraphEdge> geMap2 = interfaceMap(edges2);
            BoolExpr sameForwarding = ctx.mkBool(true);
            for (GraphEdge ge1 : edges1) {
                GraphEdge ge2 = geMap2.get(ge1.getStart().getName());
                BoolExpr dataFwd1 = slice1.getSymbolicDecisions().getDataForwarding().get(r1, ge1);
                BoolExpr dataFwd2 = slice2.getSymbolicDecisions().getDataForwarding().get(r2, ge2);
                sameForwarding = ctx.mkAnd(sameForwarding, ctx.mkEq(dataFwd1, dataFwd2));
            }

            // Ensure packets are the same
            SymbolicPacket p1 = slice1.getSymbolicPacket();
            SymbolicPacket p2 = slice2.getSymbolicPacket();
            BoolExpr equalPackets = p1.mkEqual(p2);

            BoolExpr assumptions = ctx.mkAnd(equalEnvs, equalPackets, validDest);
            BoolExpr required = ctx.mkAnd(equalOutputs, equalIncomingAcls);

            e2.add(assumptions);
            e2.add(ctx.mkNot(required));

            VerificationResult res = e2.verify();

            // res.debug(e2.getMainSlice(), null);

            String name = r1 + "<-->" + r2;
            result.put(name, res);
        }

        SmtManyAnswerElement answer = new SmtManyAnswerElement();
        answer.setResult(result);
        return answer;
    }

    /*
     * Get the interfaces for a l
     */
    private static Set<String> interfaces(List<GraphEdge> edges) {
        Set<String> ifaces = new TreeSet<>();
        for (GraphEdge edge : edges) {
            ifaces.add(edge.getStart().getName());
        }
        return ifaces;
    }

    /*
     * Build the inverse map for each logical edge
     */
    private static Map<String, Map<Protocol, Map<String, EnumMap<EdgeType,
            LogicalEdge>>>> logicalEdgeMap(EncoderSlice enc) {

        Map<String, Map<Protocol, Map<String, EnumMap<EdgeType, LogicalEdge>>>> acc =
                new HashMap<>();
        enc.getLogicalGraph().getLogicalEdges().forEach((router, map) -> {
            Map<Protocol, Map<String, EnumMap<EdgeType, LogicalEdge>>> mapAcc = new
                    HashMap<>();
            acc.put(router, mapAcc);
            map.forEach((proto, edges) -> {
                Map<String, EnumMap<EdgeType, LogicalEdge>> edgesMap = new HashMap<>();
                mapAcc.put(proto, edgesMap);
                for (ArrayList<LogicalEdge> xs : edges) {
                    for (LogicalEdge lge : xs) {
                        // Should have import since only connected to environment
                        String ifaceName = lge.getEdge().getStart().getName();
                        EnumMap<EdgeType, LogicalEdge> typeMap = edgesMap.get(ifaceName);
                        if (typeMap == null) {
                            EnumMap<EdgeType, LogicalEdge> m = new EnumMap<>(EdgeType.class);
                            m.put(lge.getEdgeType(), lge);
                            edgesMap.put(ifaceName, m);
                        } else {
                            typeMap.put(lge.getEdgeType(), lge);
                        }

                    }
                }

            });
        });
        return acc;
    }

    /*
     * Creates a boolean variable representing destinations we don't want
     * to consider due to local differences.
     */
    private static BoolExpr ignoredDestinations(Context ctx, EncoderSlice e1, String r1, Configuration
            conf1) {
        BoolExpr validDest = ctx.mkBool(true);
        for (Protocol proto1 : e1.getProtocols().get(r1)) {
            List<Prefix> prefixes = e1.getOriginatedNetworks(conf1, proto1);
            BoolExpr dest = e1.relevantOrigination(prefixes);
            validDest = ctx.mkAnd(validDest, ctx.mkNot(dest));
        }
        return validDest;
    }

    /*
     * Create a map from interface name to graph edge.
     */
    private static Map<String, GraphEdge> interfaceMap(List<GraphEdge> edges) {
        Map<String, GraphEdge> ifaceMap = new HashMap<>();
        for (GraphEdge edge : edges) {
            ifaceMap.put(edge.getStart().getName(), edge);
        }
        return ifaceMap;
    }

    /*
     * Computes multipath consistency, which ensures traffic that travels
     * multiple paths will be treated equivalently by each path
     * (i.e., dropped or accepted by each).
     */
    public static AnswerElement computeMultipathConsistency(IBatfish batfish, HeaderSpace h,
            String finalNodeRegexStr, String notFinalNodeRegexStr, String finalIfaceRegexStr,
            String notFinalIfaceRegexStr) {

        PathRegexes p = new PathRegexes(finalNodeRegexStr, notFinalNodeRegexStr,
                finalIfaceRegexStr, notFinalIfaceRegexStr, null, null);

        Graph graph = new Graph(batfish);
        List<GraphEdge> destinationPorts = PatternUtils.findMatchingEdges(graph, p);
        Map<String, VerificationResult> result = new HashMap<>();

        for (GraphEdge ge : destinationPorts) {
            // Add the interface destination
            boolean addedDestination = false;
            if (h.getDstIps().isEmpty()) {
                addedDestination = true;
                Prefix destination = ge.getStart().getPrefix();
                IpWildcard dst = new IpWildcard(destination);
                h.getDstIps().add(dst);
            }

            Encoder enc = new Encoder(h, graph);
            enc.computeEncoding();

            EncoderSlice slice = enc.getMainSlice();

            PropertyAdder pa = new PropertyAdder(slice);
            Map<String, BoolExpr> reachableVars = pa.instrumentReachability(ge);

            BoolExpr acc = enc.False();
            for (Map.Entry<String, Configuration> entry : graph.getConfigurations().entrySet()) {
                String router = entry.getKey();
                BoolExpr reach = reachableVars.get(router);

                BoolExpr all = enc.True();
                for (GraphEdge edge : graph.getEdgeMap().get(router)) {
                    BoolExpr dataFwd = slice.getForwardsAcross().get(router, edge);
                    BoolExpr ctrFwd = slice.getSymbolicDecisions().getControlForwarding().get
                            (router, edge);
                    BoolExpr peerReach = enc.True();
                    if (edge.getPeer() != null) {
                        peerReach = reachableVars.get(edge.getPeer());
                    }
                    BoolExpr imp = enc.Implies(ctrFwd, enc.And(dataFwd, peerReach));

                    all = enc.And(all, imp);
                }

                acc = enc.Or(acc, enc.Not(enc.Implies(reach, all)));
            }

            enc.add( acc );

            VerificationResult res = enc.verify();
            result.put(ge.getRouter() + "," + ge.getStart().getName(), res);

            if (addedDestination) {
                h.getDstIps().clear();
            }
        }

        SmtManyAnswerElement answer = new SmtManyAnswerElement();
        answer.setResult(result);
        return answer;
    }

    /*
     * Checks for routing loops in the network. For efficiency reasons,
     * we only check for loops with routers that use static routes since
     * these can override the usual loop-prevention mechanisms.
     */
    public static AnswerElement computeRoutingLoop(IBatfish batfish) {
        Graph graph = new Graph(batfish);

        // Collect all relevant destinations
        List<Prefix> prefixes = new ArrayList<>();
        graph.getStaticRoutes().forEach((router, ifaceMap) -> {
            ifaceMap.forEach((ifaceName, srs) -> {
                for (StaticRoute sr : srs) {
                    prefixes.add(sr.getNetwork());
                }
            });
        });

        HeaderSpace h = new HeaderSpace();

        SortedSet<IpWildcard> pfxs = new TreeSet<>();
        for (Prefix prefix : prefixes) {
            pfxs.add(new IpWildcard(prefix));
        }
        h.setDstIps(pfxs);

        // Collect all routers that use static routes as a
        // potential node along a loop
        List<String> routers = new ArrayList<>();
        graph.getConfigurations().forEach((router, conf) -> {
            if (conf.getDefaultVrf().getStaticRoutes().size() > 0) {
                routers.add(router);
            }
        });

        Encoder enc = new Encoder(h, graph);
        enc.computeEncoding();
        Context ctx = enc.getCtx();

        EncoderSlice slice = enc.getMainSlice();

        PropertyAdder pa = new PropertyAdder(slice);

        BoolExpr someLoop = ctx.mkBool(false);
        for (String router : routers) {
            BoolExpr hasLoop = pa.instrumentLoop(router);
            someLoop = ctx.mkOr(someLoop, hasLoop);
        }
        enc.add(someLoop);

        VerificationResult result = enc.verify();

        SmtOneAnswerElement answer = new SmtOneAnswerElement();
        answer.setResult(result);
        return answer;
    }

}
