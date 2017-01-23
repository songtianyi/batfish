package org.batfish.smt.answers;


import com.fasterxml.jackson.core.JsonProcessingException;
import com.microsoft.z3.*;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.RoutingProtocol;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.smt.*;
import org.batfish.smt.utils.PatternUtils;

import java.util.*;
import java.util.regex.Pattern;

public class SmtLocalConsistencyAnswerElement implements AnswerElement {

    private Map<String, VerificationResult> _result;

    public SmtLocalConsistencyAnswerElement(IBatfish batfish, Pattern n) {
        Graph graph = new Graph(batfish);
        List<String> routers = PatternUtils.findMatchingNodes(graph, n);
        _result = new HashMap<>();

        Prefix destination = new Prefix("0.0.0.0/0");

        int len = routers.size();
        if (len <= 1) {
            return;
        }

        for (int i = 0; i < len-1; i++) {
            String r1 = routers.get(i);
            String r2 = routers.get(i+1);

            // TODO: reorder to encode after checking if we can compare them

            // Create transfer function for router 1
            Set<String> toModel1 = new TreeSet<>();
            toModel1.add(r1);
            Graph g1 = new Graph(batfish, toModel1);
            Encoder e1 = new Encoder(Collections.singletonList(destination), g1);
            e1.computeEncoding();

            Context ctx = e1.getCtx();
            Solver solver = e1.getSolver();

            // Create transfer function for router 2
            // Reuse the context and solver
            Set<String> toModel2 = new TreeSet<>();
            toModel2.add(r2);
            Graph g2 = new Graph(batfish, toModel2);
            Encoder e2 = new Encoder(e1, g2);
            e2.computeEncoding();

            // Ensure that the two routers have the same interfaces for comparison
            Pattern p = Pattern.compile(".*");
            List<GraphEdge> edges1 = PatternUtils.findMatchingEdge(g1, p, p);
            List<GraphEdge> edges2 = PatternUtils.findMatchingEdge(g2, p, p);
            Set<String> ifaces1 = interfaces(edges1);
            Set<String> ifaces2 = interfaces(edges2);

            if (!(ifaces1.containsAll(ifaces2) && ifaces2.containsAll(ifaces1))) {
                String msg = String.format("Routers %s and %s have different interfaces", r1, r2);
                System.out.println(msg);
                return;
            }

            // TODO: check running same protocols?

            Map<String, EnumMap<RoutingProtocol, Map<String, EnumMap<EdgeType, LogicalGraphEdge>>>> lgeMap1 = logicalEdgeMap(e1);
            Map<String, EnumMap<RoutingProtocol, Map<String, EnumMap<EdgeType, LogicalGraphEdge>>>> lgeMap2 = logicalEdgeMap(e2);

            BoolExpr equalEnvs = ctx.mkBool(true);
            BoolExpr equalOutputs = ctx.mkBool(true);

            Configuration conf1 = g1.getConfigurations().get(r1);
            Configuration conf2 = g2.getConfigurations().get(r2);

            // Set environments equal
            for (RoutingProtocol proto1 : e1.getProtocols().get(r1)) {
                for (ArrayList<LogicalGraphEdge> es : e1.getEdgeVariableMap().get(r1).get(proto1)) {
                    for (LogicalGraphEdge lge1 : es) {

                        String ifaceName = lge1.getEdge().getStart().getName();
                        LogicalGraphEdge lge2 = lgeMap2.get(r2).get(proto1).get(ifaceName).get(lge1.getEdgeType());

                        if (lge1.getEdgeType() == EdgeType.IMPORT) {

                            EdgeVars vars1 = e1.getEnvironmentVars().get(lge1);
                            EdgeVars vars2 = e2.getEnvironmentVars().get(lge2);

                            boolean hasEnv1 = (vars1 != null);
                            boolean hasEnv2 = (vars2 != null);

                            if (hasEnv1 && hasEnv2) {
                                BoolExpr samePermitted = ctx.mkEq(vars1.getPermitted(), vars2.getPermitted());
                                equalEnvs = ctx.mkAnd(equalEnvs, samePermitted, e1.equal(conf1, proto1, vars1, vars2, lge1));
                            } else if (hasEnv1 || hasEnv2) {
                                System.out.println("Edge1: " + lge1);
                                System.out.println("Edge2: " + lge2);
                                throw new BatfishException("one had environment");
                            }

                        } else {

                            EdgeVars out1 = lge1.getEdgeVars();
                            EdgeVars out2 = lge2.getEdgeVars();

                            equalOutputs = ctx.mkAnd(equalOutputs, e1.equal(conf1, proto1, out1, out2, lge1));
                        }
                    }
                }
            }

            // TODO: check both have same environment variables (e.g., screw up configuring peer connection)

            BoolExpr validDest;
            validDest = ignoredDestinations(ctx, e1, r1, conf1);
            validDest = ctx.mkAnd(validDest, ignoredDestinations(ctx, e2, r2, conf2));

            Map<String, GraphEdge> geMap2 = interfaceMap(edges2);
            BoolExpr sameForwarding = ctx.mkBool(true);
            for (GraphEdge ge1 : edges1) {
                GraphEdge ge2 = geMap2.get(ge1.getStart().getName());
                BoolExpr dataFwd1 = e1.getDataForwarding().get(r1).get(ge1);
                BoolExpr dataFwd2 = e2.getDataForwarding().get(r2).get(ge2);
                sameForwarding = ctx.mkAnd(sameForwarding, ctx.mkEq(dataFwd1, dataFwd2));
            }

            BoolExpr assumptions = ctx.mkAnd(equalEnvs, validDest);
            BoolExpr required = ctx.mkAnd(sameForwarding, equalOutputs);

            solver.add( assumptions );
            solver.add( ctx.mkNot(required) );

            String name = r1 + "<-->" + r2;
            VerificationResult result = e2.verify();
            _result.put(name, result);
        }
    }

    private Map<String, EnumMap<RoutingProtocol, Map<String, EnumMap<EdgeType, LogicalGraphEdge>>>> logicalEdgeMap(Encoder enc) {
        Map<String, EnumMap<RoutingProtocol, Map<String, EnumMap<EdgeType, LogicalGraphEdge>>>> acc = new HashMap<>();
        enc.getEdgeVariableMap().forEach((router, map) -> {
            EnumMap<RoutingProtocol, Map<String, EnumMap<EdgeType, LogicalGraphEdge>>> mapAcc = new EnumMap<>(RoutingProtocol.class);
            acc.put(router, mapAcc);
            map.forEach((proto, edges) -> {
                Map<String, EnumMap<EdgeType, LogicalGraphEdge>> edgesMap = new HashMap<>();
                mapAcc.put(proto, edgesMap);
                for (ArrayList<LogicalGraphEdge> xs : edges) {
                    for (LogicalGraphEdge lge : xs) {
                        // Should have import since only connected to environment
                        String ifaceName = lge.getEdge().getStart().getName();
                        EnumMap<EdgeType, LogicalGraphEdge> typeMap = edgesMap.get(ifaceName);
                        if (typeMap == null) {
                            EnumMap<EdgeType, LogicalGraphEdge> m = new EnumMap<>(EdgeType.class);
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

    private Map<String, GraphEdge> interfaceMap(List<GraphEdge> edges) {
        Map<String, GraphEdge> ifaceMap = new HashMap<>();
        for (GraphEdge edge : edges) {
            ifaceMap.put(edge.getStart().getName(), edge);
        }
        return ifaceMap;
    }

    private Set<String> interfaces(List<GraphEdge> edges) {
        Set<String> ifaces = new TreeSet<>();
        for (GraphEdge edge : edges) {
            ifaces.add(edge.getStart().getName());
        }
        return ifaces;
    }

    private BoolExpr ignoredDestinations(Context ctx, Encoder e1, String r1, Configuration conf1) {
        // Don't consider directly connected routes
        BoolExpr validDest = ctx.mkBool(true);
        for (RoutingProtocol proto1 : e1.getProtocols().get(r1)) {
            if (proto1 == RoutingProtocol.CONNECTED) {
                List<Prefix> prefixes = e1.getOriginatedNetworks(conf1, proto1);
                BoolExpr dest = e1.relevantOrigination(prefixes);
                validDest = ctx.mkAnd(validDest, ctx.mkNot(dest));
            }
        }
        return validDest;
    }

    public Map<String, VerificationResult> getResult() {
        return _result;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        return "LOCAL CONSISTENCY PRETTY PRINT";
    }
}