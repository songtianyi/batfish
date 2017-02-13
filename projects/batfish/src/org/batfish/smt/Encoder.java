package org.batfish.smt;

import com.microsoft.z3.*;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.*;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.*;
import org.batfish.datamodel.routing_policy.statement.*;

import java.util.*;
import java.util.regex.Matcher;

// Features:
// ---------
//   - Avoid loops in BGP when non-standard (or non-common) local-pref internally
//   - iBGP by comparing local-pref internally
//     * Requires reachability, and no ACLs for loopbacks
//   - maximum path length by protocol
//   - RIP, EIGRP routing protocols
//
// Environment stuff:
// ------------------
//   - Ensure Local preference/MED transitive depending on local/remote/send community AS?
//
// Small items:
// ------------
//   - What to do with overflow?
//   - Ensure distance is transfered over with redistribution
//   - Compute multipath correctly (how do we handle some multipath)


/**
 * An object that is responsible for creating a symbolic representation
 * of both the network control and data planes.
 */
public class Encoder {

    static final boolean ENABLE_DEBUGGING = false;

    static final int BITS = 0;

    static final int DEFAULT_CISCO_VLAN_OSPF_COST = 1;

    static final String BGP_NETWORK_FILTER_LIST_NAME = "BGP_NETWORK_NETWORKS_FILTER";

    static final String BGP_COMMON_FILTER_LIST_NAME = "BGP_COMMON_EXPORT_POLICY";

    // static final String BGP_AGGREGATE_FILTER_LIST_NAME = "BGP_AGGREGATE_NETWORKS_FILTER";
    // Globally unique identifier for distinguishing multiple instances of variables
    private static int encodingId = 0;

    private List<Prefix> _destinations;

    private Optimizations _optimizations;

    private LogicalGraph _logicalGraph;

    private SymbolicDecisions _symbolicDecisions;

    private SymbolicFailures _symbolicFailures;

    private SymbolicPacket _symbolicPacket;

    private Map<Interface, BoolExpr> _inboundAcls;

    private Map<Interface, BoolExpr> _outboundAcls;

    private Set<CommunityVar> _allCommunities;

    private Map<CommunityVar, List<CommunityVar>> _communityDependencies;

    private List<Expr> _allVariables;

    private List<SymbolicRecord> _allSymbolicRecords;

    private Context _ctx;

    private Solver _solver;

    private UnsatCore _unsatCore;


    public Encoder(IBatfish batfish, List<Prefix> destinations) {
        this(destinations, new Graph(batfish));
    }

    public Encoder(List<Prefix> destinations, Graph graph) {
        this(destinations, graph, null, null, null);
    }

    private Encoder(
            List<Prefix> destinations, Graph graph, Context ctx, Solver solver, List<Expr> vars) {
        HashMap<String, String> cfg = new HashMap<>();

        // allows for unsat core when debugging
        if (ENABLE_DEBUGGING) {
            cfg.put("proof", "true");
            cfg.put("auto-config", "false");
        }

        _ctx = (ctx == null ? new Context(cfg) : ctx);

        if (solver == null) {
            if (ENABLE_DEBUGGING) {
                _solver = _ctx.mkSolver();
            } else {
                Tactic t1 = _ctx.mkTactic("simplify");
                Tactic t2 = _ctx.mkTactic("solve-eqs");
                Tactic t3 = _ctx.mkTactic("smt");
                Tactic t = _ctx.then(t1, t2, t3);
                _solver = _ctx.mkSolver(t);
            }
        } else {
            _solver = solver;
            encodingId = encodingId + 1;
        }

        _destinations = destinations;
        _optimizations = new Optimizations(this);
        _logicalGraph = new LogicalGraph(graph);
        _symbolicDecisions = new SymbolicDecisions();
        _symbolicFailures = new SymbolicFailures();
        _symbolicPacket = new SymbolicPacket(_ctx, encodingId);
        _allSymbolicRecords = new ArrayList<>();

        if (vars == null) {
            _allVariables = new ArrayList<>();
        } else {
            _allVariables = vars;
        }

        _allVariables.add(_symbolicPacket.getDstIp());
        _allVariables.add(_symbolicPacket.getSrcIp());
        _allVariables.add(_symbolicPacket.getDstPort());
        _allVariables.add(_symbolicPacket.getSrcPort());
        _allVariables.add(_symbolicPacket.getIcmpCode());
        _allVariables.add(_symbolicPacket.getIcmpType());
        _allVariables.add(_symbolicPacket.getTcpAck());
        _allVariables.add(_symbolicPacket.getTcpCwr());
        _allVariables.add(_symbolicPacket.getTcpEce());
        _allVariables.add(_symbolicPacket.getTcpFin());
        _allVariables.add(_symbolicPacket.getTcpPsh());
        _allVariables.add(_symbolicPacket.getTcpRst());
        _allVariables.add(_symbolicPacket.getTcpSyn());
        _allVariables.add(_symbolicPacket.getTcpUrg());
        _allVariables.add(_symbolicPacket.getIpProtocol());

        _inboundAcls = new HashMap<>();
        _outboundAcls = new HashMap<>();

        initCommunities();

        _unsatCore = new UnsatCore(ENABLE_DEBUGGING);
    }

    public void initCommunities() {
        _allCommunities = findAllCommunities();

        // TODO: only add other communities if there is another value that can be matched.
        // Add an other variable for each regex community
        List<CommunityVar> others = new ArrayList<>();
        for (CommunityVar c : _allCommunities) {
            if (c.getType() == CommunityVar.Type.REGEX) {
                CommunityVar x = new CommunityVar(CommunityVar.Type.OTHER, c.getValue(), c.asLong
                        ());
                others.add(x);
            }
        }
        for (CommunityVar c : others) {
            _allCommunities.add(c);
        }

        // Map community regex matches to Java regex
        Map<CommunityVar, java.util.regex.Pattern> regexes = new HashMap<>();
        for (CommunityVar c : _allCommunities) {
            if (c.getType() == CommunityVar.Type.REGEX) {
                java.util.regex.Pattern p = java.util.regex.Pattern.compile(c.getValue());
                regexes.put(c, p);
            }
        }

        _communityDependencies = new HashMap<>();
        for (CommunityVar c1 : _allCommunities) {
            // map exact match to corresponding regexes
            if (c1.getType() == CommunityVar.Type.REGEX) {

                List<CommunityVar> list = new ArrayList<>();
                _communityDependencies.put(c1, list);
                java.util.regex.Pattern p = regexes.get(c1);

                for (CommunityVar c2 : _allCommunities) {
                    if (c2.getType() == CommunityVar.Type.EXACT) {
                        Matcher m = p.matcher(c2.getValue());
                        if (m.find()) {
                            list.add(c2);
                        }
                    }
                    if (c2.getType() == CommunityVar.Type.OTHER) {
                        if (c1.getValue().equals(c2.getValue())) {
                            list.add(c2);
                        }
                    }
                }
            }
        }
    }

    public Set<CommunityVar> findAllCommunities() {
        Set<CommunityVar> comms = new HashSet<>();
        getGraph().getConfigurations().forEach((router, conf) -> {
            conf.getRoutingPolicies().forEach((name, pol) -> {
                AstVisitor v = new AstVisitor();
                v.visit(conf, pol.getStatements(), stmt -> {
                    if (stmt instanceof SetCommunity) {
                        SetCommunity sc = (SetCommunity) stmt;
                        comms.addAll(findAllCommunities(conf, sc.getExpr()));
                    }
                    if (stmt instanceof AddCommunity) {
                        AddCommunity ac = (AddCommunity) stmt;
                        comms.addAll(findAllCommunities(conf, ac.getExpr()));
                    }
                    if (stmt instanceof DeleteCommunity) {
                        DeleteCommunity dc = (DeleteCommunity) stmt;
                        comms.addAll(findAllCommunities(conf, dc.getExpr()));
                    }
                    if (stmt instanceof RetainCommunity) {
                        RetainCommunity rc = (RetainCommunity) stmt;
                        comms.addAll(findAllCommunities(conf, rc.getExpr()));
                    }
                }, expr -> {
                    if (expr instanceof MatchCommunitySet) {
                        MatchCommunitySet m = (MatchCommunitySet) expr;
                        CommunitySetExpr ce = m.getExpr();
                        comms.addAll(findAllCommunities(conf, ce));
                    }
                });
            });
        });
        return comms;
    }

    public Graph getGraph() {
        return _logicalGraph.getGraph();
    }

    public Set<CommunityVar> findAllCommunities(Configuration conf, CommunitySetExpr ce) {
        Set<CommunityVar> comms = new HashSet<>();
        if (ce instanceof InlineCommunitySet) {
            InlineCommunitySet c = (InlineCommunitySet) ce;
            for (CommunitySetElem cse : c.getCommunities()) {
                if (cse.getPrefix() instanceof LiteralCommunitySetElemHalf && cse.getSuffix()
                        instanceof LiteralCommunitySetElemHalf) {
                    LiteralCommunitySetElemHalf x = (LiteralCommunitySetElemHalf) cse.getPrefix();
                    LiteralCommunitySetElemHalf y = (LiteralCommunitySetElemHalf) cse.getSuffix();
                    int prefixInt = x.getValue();
                    int suffixInt = y.getValue();
                    String val = prefixInt + ":" + suffixInt;
                    Long l = (((long) prefixInt) << 16) | (suffixInt);
                    CommunityVar var = new CommunityVar(CommunityVar.Type.EXACT, val, l);
                    comms.add(var);
                } else {
                    throw new BatfishException("TODO: community non literal: " + cse);
                }
            }
        }
        if (ce instanceof NamedCommunitySet) {
            NamedCommunitySet c = (NamedCommunitySet) ce;
            String cname = c.getName();
            CommunityList cl = conf.getCommunityLists().get(cname);
            if (cl != null) {
                for (CommunityListLine line : cl.getLines()) {
                    CommunityVar var = new CommunityVar(CommunityVar.Type.REGEX, line.getRegex(),
                            null);
                    comms.add(var);
                }
            }
        }
        return comms;
    }

    public Encoder(Encoder e, Graph graph) {
        this(e.getDestinations(), graph, e.getCtx(), e.getSolver(), e.getAllVariables());
    }

    public List<Prefix> getDestinations() {
        return _destinations;
    }

    public Context getCtx() {
        return _ctx;
    }

    public Solver getSolver() {
        return _solver;
    }

    public List<Expr> getAllVariables() {
        return _allVariables;
    }

    public LogicalGraph getLogicalGraph() {
        return _logicalGraph;
    }

    public SymbolicDecisions getSymbolicDecisions() {
        return _symbolicDecisions;
    }

    public SymbolicPacket getSymbolicPacket() {
        return _symbolicPacket;
    }

    public Map<Interface, BoolExpr> getIncomingAcls() {
        return _inboundAcls;
    }

    public Map<Interface, BoolExpr> getOutgoingAcls() {
        return _outboundAcls;
    }

    public Set<CommunityVar> getAllCommunities() {
        return _allCommunities;
    }

    public Map<CommunityVar, List<CommunityVar>> getCommunityDependencies() {
        return _communityDependencies;
    }

    public UnsatCore getUnsatCore() {
        return _unsatCore;
    }

    public void add(BoolExpr e) {
        _unsatCore.track(_solver, _ctx, e);
    }

    public BoolExpr False() {
        return _ctx.mkBool(false);
    }

    public BoolExpr Bool(boolean val) {
        return _ctx.mkBool(val);
    }

    public BoolExpr Not(BoolExpr e) {
        return _ctx.mkNot(e);
    }

    public BoolExpr Or(BoolExpr... vals) {
        return _ctx.mkOr(vals);
    }

    public BoolExpr Implies(BoolExpr e1, BoolExpr e2) {
        return _ctx.mkImplies(e1, e2);
    }

    public BoolExpr Gt(ArithExpr e1, ArithExpr e2) {
        return _ctx.mkGt(e1, e2);
    }

    public ArithExpr Sum(ArithExpr e1, ArithExpr e2) {
        return _ctx.mkAdd(e1, e2);
    }

    public ArithExpr Sub(ArithExpr e1, ArithExpr e2) {
        return _ctx.mkSub(e1, e2);
    }

    public BoolExpr If(BoolExpr cond, BoolExpr case1, BoolExpr case2) {
        return (BoolExpr) _ctx.mkITE(cond, case1, case2);
    }

    public boolean overlaps(Prefix p1, Prefix p2) {
        long l1 = p1.getNetworkPrefix().getAddress().asLong();
        long l2 = p2.getNetworkPrefix().getAddress().asLong();
        long u1 = p1.getNetworkPrefix().getEndAddress().asLong();
        long u2 = p2.getNetworkPrefix().getEndAddress().asLong();
        return (l1 >= l2 && l1 <= u2) || (u1 <= u2 && u1 >= l2) || (u2 >= l1 && u2 <= u1) || (l2
                >= l1 && l2 <= u1);
    }

    private void addChoiceVariables() {
        getGraph().getEdgeMap().forEach((router, edges) -> {
            Configuration conf = getGraph().getConfigurations().get(router);

            Map<RoutingProtocol, Map<LogicalEdge, BoolExpr>> map = new HashMap<>();
            _symbolicDecisions.getChoiceVariables().put(router, map);

            for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {

                Map<LogicalEdge, BoolExpr> edgeMap = new HashMap<>();
                map.put(proto, edgeMap);

                for (LogicalEdge e : collectAllImportLogicalEdges(router, conf, proto)) {
                    String chName = e.getSymbolicRecord().getName() + "_choice";
                    BoolExpr choiceVar = _ctx.mkBoolConst(chName);
                    _allVariables.add(choiceVar);
                    edgeMap.put(e, choiceVar);
                }
            }
        });
    }

    private void buildEdgeMap() {
        getGraph().getEdgeMap().forEach((router, edges) -> {
            for (RoutingProtocol p : getGraph().getProtocols().get(router)) {
                _logicalGraph.getLogicalEdges().put(router, p, new ArrayList<>());
            }
        });
    }

    private void addForwardingVariables() {
        getGraph().getEdgeMap().forEach((router, edges) -> {
            for (GraphEdge edge : edges) {
                String iface = edge.getStart().getName();

                String cName = "control-forwarding_" + router + "_" + iface;
                BoolExpr cForward = _ctx.mkBoolConst(cName);
                _allVariables.add(cForward);
                _symbolicDecisions.getControlForwarding().put(router, edge, cForward);

                String dName = "data-forwarding_" + router + "_" + iface;
                BoolExpr dForward = _ctx.mkBoolConst(dName);
                _allVariables.add(dForward);
                _symbolicDecisions.getDataForwarding().put(router, edge, dForward);
            }
        });
    }

    private void addBestVariables() {

        getGraph().getEdgeMap().forEach((router, edges) -> {

            List<RoutingProtocol> allProtos = getGraph().getProtocols().get(router);

            // Overall best
            for (int len = 0; len <= BITS; len++) {
                String name = String.format("%s_%s_%s_%s", router, "OVERALL", "none", "BEST");
                String historyName = name + "_history";

                SymbolicEnum<RoutingProtocol> h = new SymbolicEnum<>(this, allProtos, historyName);

                SymbolicRecord evBest = new SymbolicRecord(this, name, router, RoutingProtocol
                        .AGGREGATE, _optimizations, _ctx, h);
                _allSymbolicRecords.add(evBest);
                _symbolicDecisions.getBestNeighbor().put(router, evBest);
            }

            // Best per protocol
            if (!_optimizations.getSliceHasSingleProtocol().contains(router)) {
                for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {
                    String name = String.format("%s_%s_%s_%s", router, proto.protocolName(),
                            "none", "BEST");
                    String historyName = name + "_history";

                    SymbolicEnum<RoutingProtocol> h = new SymbolicEnum<>(this, allProtos, historyName);

                    for (int len = 0; len <= BITS; len++) {
                        SymbolicRecord evBest = new SymbolicRecord(this, name, router, proto,
                                _optimizations, _ctx, h);
                        _allSymbolicRecords.add(evBest);
                        _symbolicDecisions.getBestNeighborPerProtocol().put(router, proto, evBest);
                    }
                }
            }
        });
    }

    private void addSymbolicRecords() {
        Map<String, EnumMap<RoutingProtocol, Map<GraphEdge, ArrayList<LogicalEdge>>>>
                importInverseMap = new HashMap<>();
        Map<String, EnumMap<RoutingProtocol, Map<GraphEdge, ArrayList<LogicalEdge>>>>
                exportInverseMap = new HashMap<>();
        Map<String, EnumMap<RoutingProtocol, SymbolicRecord>> singleExportMap = new HashMap<>();

        // add edge EXPORT and IMPORT state variables
        getGraph().getEdgeMap().forEach((router, edges) -> {

            EnumMap<RoutingProtocol, SymbolicRecord> singleProtoMap;
            singleProtoMap = new EnumMap<>(RoutingProtocol.class);
            EnumMap<RoutingProtocol, Map<GraphEdge, ArrayList<LogicalEdge>>> importEnumMap;
            importEnumMap = new EnumMap<>(RoutingProtocol.class);
            EnumMap<RoutingProtocol, Map<GraphEdge, ArrayList<LogicalEdge>>> exportEnumMap;
            exportEnumMap = new EnumMap<>(RoutingProtocol.class);

            singleExportMap.put(router, singleProtoMap);
            importInverseMap.put(router, importEnumMap);
            exportInverseMap.put(router, exportEnumMap);

            for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {

                boolean useSingleExport = _optimizations.getSliceCanKeepSingleExportVar().get
                        (router).get(proto);

                Map<GraphEdge, ArrayList<LogicalEdge>> importGraphEdgeMap = new HashMap<>();
                Map<GraphEdge, ArrayList<LogicalEdge>> exportGraphEdgeMap = new HashMap<>();

                importEnumMap.put(proto, importGraphEdgeMap);
                exportEnumMap.put(proto, exportGraphEdgeMap);

                for (GraphEdge e : edges) {

                    Interface iface = e.getStart();
                    Configuration conf = getGraph().getConfigurations().get(router);

                    if (getGraph().isInterfaceUsed(conf, proto, iface)) {

                        ArrayList<LogicalEdge> importEdgeList = new ArrayList<>();
                        ArrayList<LogicalEdge> exportEdgeList = new ArrayList<>();
                        importGraphEdgeMap.put(e, importEdgeList);
                        exportGraphEdgeMap.put(e, exportEdgeList);

                        for (int len = 0; len <= BITS; len++) {

                            String ifaceName = e.getStart().getName();

                            // If we use a single set of export variables, then make sure
                            // to reuse the existing variables instead of creating new ones
                            if (useSingleExport) {
                                SymbolicRecord singleVars = singleExportMap.get(router).get(proto);
                                SymbolicRecord ev1;
                                if (singleVars == null) {
                                    String name = String.format("%s_%s_%s_%s", router, proto
                                            .protocolName(), "", "SINGLE-EXPORT");
                                    ev1 = new SymbolicRecord(this, name, router, proto,
                                            _optimizations, _ctx, null);
                                    singleProtoMap.put(proto, ev1);
                                    _allSymbolicRecords.add(ev1);
                                } else {
                                    ev1 = singleVars;
                                }
                                LogicalEdge eExport = new LogicalEdge(e, EdgeType.EXPORT, len, ev1);
                                exportEdgeList.add(eExport);

                            } else {
                                // String name = proto.protocolName();
                                String name = String.format("%s_%s_%s_%s", router, proto
                                        .protocolName(), ifaceName, "EXPORT");

                                SymbolicRecord ev1 = new SymbolicRecord(this, name, router,
                                        proto, _optimizations, _ctx, null);
                                LogicalEdge eExport = new LogicalEdge(e, EdgeType.EXPORT, len, ev1);
                                exportEdgeList.add(eExport);
                                _allSymbolicRecords.add(ev1);
                            }

                            boolean notNeeded = _optimizations.getSliceCanCombineImportExportVars
                                    ().get(router).get(proto).contains(e);

                            if (notNeeded) {
                                String name = String.format("%s_%s_%s_%s", router, proto
                                        .protocolName(), ifaceName, "IMPORT");
                                SymbolicRecord ev2 = new SymbolicRecord(name);
                                LogicalEdge eImport = new LogicalEdge(e, EdgeType.IMPORT, len, ev2);
                                importEdgeList.add(eImport);
                            } else {

                                String name = String.format("%s_%s_%s_%s", router, proto
                                        .protocolName(), ifaceName, "IMPORT");
                                SymbolicRecord ev2 = new SymbolicRecord(this, name, router,
                                        proto, _optimizations, _ctx, null);
                                LogicalEdge eImport = new LogicalEdge(e, EdgeType.IMPORT, len, ev2);
                                importEdgeList.add(eImport);
                                _allSymbolicRecords.add(ev2);
                            }
                        }

                        List<ArrayList<LogicalEdge>> es = _logicalGraph.getLogicalEdges().get
                                (router, proto);
                        ArrayList<LogicalEdge> allEdges = new ArrayList<>();
                        allEdges.addAll(importEdgeList);
                        allEdges.addAll(exportEdgeList);
                        es.add(allEdges);
                    }
                }

            }
        });

        // Build a map to find the opposite of a given edge
        _logicalGraph.getLogicalEdges().forEach((router, edgeLists) -> {
            for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {

                for (ArrayList<LogicalEdge> edgeList : edgeLists.get(proto)) {

                    for (int i = 0; i < edgeList.size(); i++) {

                        LogicalEdge e = edgeList.get(i);

                        GraphEdge edge = e.getEdge();
                        Map<GraphEdge, ArrayList<LogicalEdge>> m;

                        if (edge.getPeer() != null) {

                            if (e.getEdgeType() == EdgeType.IMPORT) {
                                m = exportInverseMap.get(edge.getPeer()).get(proto);

                            } else {
                                m = importInverseMap.get(edge.getPeer()).get(proto);
                            }

                            if (m != null) {
                                GraphEdge otherEdge = getGraph().getOtherEnd().get(edge);
                                LogicalEdge other = m.get(otherEdge).get(i / 2);
                                _logicalGraph.getOtherEnd().put(e, other);
                            }

                        }

                    }
                }
            }
        });
    }

    private void computeOptimizations() {
        _optimizations.computeOptimizations();
    }

    private void addEnvironmentVariables() {
        getGraph().getConfigurations().forEach((router, conf) -> {
            for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {
                if (proto == RoutingProtocol.BGP) {
                    _logicalGraph.getLogicalEdges().get(router, proto).forEach(eList -> {
                        eList.forEach(e -> {
                            if (e.getEdgeType() == EdgeType.IMPORT) {
                                BgpNeighbor n = getGraph().getBgpNeighbors().get(e.getEdge());
                                if (n != null && e.getEdge().getEnd() == null) {
                                    String address;
                                    if (n.getAddress() == null) {
                                        address = "null";
                                    } else {
                                        address = n.getAddress().toString();
                                    }

                                    String ifaceName = "ENV-" + address;
                                    String name = String.format("%s_%s_%s_%s", router, proto
                                            .protocolName(), ifaceName, "EXPORT");
                                    SymbolicRecord vars = new SymbolicRecord(this, name, router,
                                            proto, _optimizations, _ctx, null);

                                    _allSymbolicRecords.add(vars);
                                    _logicalGraph.getEnvironmentVars().put(e, vars);
                                }
                            }
                        });
                    });
                }
            }
        });
    }

    private void addFailedLinkVariables() {
        getGraph().getEdgeMap().forEach((router, edges) -> {
            for (GraphEdge ge : edges) {
                if (ge.getPeer() == null) {
                    Interface i = ge.getStart();
                    String name = "failed-edge_" + ge.getRouter() + "_" + i.getName();
                    ArithExpr var = _ctx.mkIntConst(name);
                    _symbolicFailures.getFailedEdgeLinks().put(ge, var);
                }
            }
        });
        getGraph().getNeighbors().forEach((router, peers) -> {
            for (String peer : peers) {
                // sort names for unique
                String pair = (router.compareTo(peer) < 0 ? router + "_" + peer : peer + "_" +
                        router);
                String name = "failed-internal_" + pair;
                ArithExpr var = _ctx.mkIntConst(name);
                _symbolicFailures.getFailedInternalLinks().put(router, peer, var);
            }
        });
    }

    private void addVariables() {
        buildEdgeMap();
        addForwardingVariables();
        addBestVariables();
        addSymbolicRecords();
        addChoiceVariables();
        addEnvironmentVariables();
        addFailedLinkVariables();
    }

    private void addBoundConstraints() {

        ArithExpr upperBound4 = Int((long) Math.pow(2, 4));
        ArithExpr upperBound8 = Int((long) Math.pow(2, 8));
        ArithExpr upperBound16 = Int((long) Math.pow(2, 16));
        ArithExpr upperBound32 = Int((long) Math.pow(2, 32));
        ArithExpr zero = Int(0);

        // Valid 32 bit integers
        add(Ge(_symbolicPacket.getDstIp(), zero));
        add(Ge(_symbolicPacket.getSrcIp(), zero));
        add(Lt(_symbolicPacket.getDstIp(), upperBound32));
        add(Lt(_symbolicPacket.getSrcIp(), upperBound32));

        // Valid 16 bit integer
        add(Ge(_symbolicPacket.getDstPort(), zero));
        add(Ge(_symbolicPacket.getSrcPort(), zero));
        add(Lt(_symbolicPacket.getDstPort(), upperBound16));
        add(Lt(_symbolicPacket.getSrcPort(), upperBound16));

        // Valid 8 bit integer
        add(Ge(_symbolicPacket.getIcmpType(), zero));
        add(Ge(_symbolicPacket.getIpProtocol(), zero));
        add(Lt(_symbolicPacket.getIcmpType(), upperBound8));
        add(Lt(_symbolicPacket.getIpProtocol(), upperBound8));

        // Valid 4 bit integer
        add(Ge(_symbolicPacket.getIcmpCode(), zero));
        add(Lt(_symbolicPacket.getIcmpCode(), upperBound4));

        for (SymbolicRecord e : _allSymbolicRecords) {
            if (e.getAdminDist() != null) {
                add(Ge(e.getAdminDist(), zero));
                //_solver.add(_ctx.mkLe(e.getAdminDist(), _ctx.mkInt(200)));
            }
            if (e.getMed() != null) {
                add(Ge(e.getMed(), zero));
                //_solver.add(_ctx.mkLe(e.getMed(), _ctx.mkInt(100)));
            }
            if (e.getLocalPref() != null) {
                add(Ge(e.getLocalPref(), zero));
                //_solver.add(_ctx.mkLe(e.getLocalPref(), _ctx.mkInt(100)));
            }
            if (e.getMetric() != null) {
                add(Ge(e.getMetric(), zero));
                //_solver.add(_ctx.mkLe(e.getMetric(), _ctx.mkInt(200)));
            }
            if (e.getPrefixLength() != null) {
                add(Ge(e.getPrefixLength(), zero));
                add(Le(e.getPrefixLength(), Int(32)));
            }
        }
    }

    // TODO: optimize this function
    private void addCommunityConstraints() {
        for (SymbolicRecord r : _allSymbolicRecords) {
            r.getCommunities().forEach((cvar, e) -> {
                if (cvar.getType() == CommunityVar.Type.REGEX) {
                    BoolExpr acc = False();
                    List<CommunityVar> deps = _communityDependencies.get(cvar);
                    for (CommunityVar dep : deps) {
                        BoolExpr depExpr = r.getCommunities().get(dep);
                        acc = Or(acc, depExpr);
                    }
                    // System.out.println("Community constraint:\n" + acc.simplify());
                    add(acc);
                }
            });
        }
    }

    private void addFailedConstraints(int k) {
        List<ArithExpr> vars = new ArrayList<>();
        _symbolicFailures.getFailedInternalLinks().forEach((router, peer, var) -> {
            vars.add(var);
        });
        _symbolicFailures.getFailedEdgeLinks().forEach((ge, var) -> {
            vars.add(var);
        });

        ArithExpr sum = Int(0);
        for (ArithExpr var : vars) {
            sum = Sum(sum, var);
            add(Ge(var, Int(0)));
            add(Le(var, Int(1)));
        }
        if (k == 0) {
            for (ArithExpr var : vars) {
                add(Eq(var, Int(0)));
            }
        } else {
            add(Le(sum, Int(k)));
        }
    }

    public BoolExpr isRelevantFor(SymbolicRecord vars, PrefixRange range) {
        Prefix p = range.getPrefix();
        SubRange r = range.getLengthRange();
        long pfx = p.getNetworkAddress().asLong();
        int len = p.getPrefixLength();
        int lower = r.getStart();
        int upper = r.getEnd();

        // well formed prefix
        assert (p.getPrefixLength() < lower && lower <= upper);

        BoolExpr lowerBitsMatch = firstBitsEqual(_symbolicPacket.getDstIp(), pfx, len);
        if (lower == upper) {
            BoolExpr equalLen = Eq(vars.getPrefixLength(), Int(lower));
            return And(equalLen, lowerBitsMatch);
        } else {
            BoolExpr lengthLowerBound = Ge(vars.getPrefixLength(), Int(lower));
            BoolExpr lengthUpperBound = Le(vars.getPrefixLength(), Int(upper));
            return And(lengthLowerBound, lengthUpperBound, lowerBitsMatch);
        }
    }

    private BoolExpr firstBitsEqual(ArithExpr x, long y, int n) {
        assert (n >= 0 && n <= 32);
        if (n == 0) {
            return True();
        }
        long bound = (long) Math.pow(2, 32 - n);
        ArithExpr upperBound = Int(y + bound);
        return And(Ge(x, Int(y)), Lt(x, upperBound));
    }

    public BoolExpr Eq(Expr e1, Expr e2) {
        return _ctx.mkEq(e1, e2);
    }

    public ArithExpr Int(long l) {
        return _ctx.mkInt(l);
    }

    public BoolExpr And(BoolExpr... vals) {
        return _ctx.mkAnd(vals);
    }

    public BoolExpr Ge(ArithExpr e1, ArithExpr e2) {
        return _ctx.mkGe(e1, e2);
    }

    public BoolExpr Le(ArithExpr e1, ArithExpr e2) {
        return _ctx.mkLe(e1, e2);
    }

    public BoolExpr True() {
        return _ctx.mkBool(true);
    }

    public BoolExpr Lt(ArithExpr e1, ArithExpr e2) {
        return _ctx.mkLt(e1, e2);
    }


    /**
     * TODO:
     * This was copied from BdpDataPlanePlugin.java
     * to make things easier for now.
     */
    private void initOspfInterfaceCosts(Configuration conf) {
        if (conf.getDefaultVrf().getOspfProcess() != null) {
            conf.getInterfaces().forEach((interfaceName, i) -> {
                if (i.getActive()) {
                    Integer ospfCost = i.getOspfCost();
                    if (ospfCost == null) {
                        if (interfaceName.startsWith("Vlan")) {
                            // TODO: fix for non-cisco
                            ospfCost = DEFAULT_CISCO_VLAN_OSPF_COST;
                        } else {
                            if (i.getBandwidth() != null) {
                                ospfCost = Math.max((int) (conf.getDefaultVrf().getOspfProcess()
                                                               .getReferenceBandwidth() / i
                                        .getBandwidth()), 1);
                            } else {
                                throw new BatfishException("Expected non-null interface " +
                                        "bandwidth" + " for \"" + conf.getHostname() + "\":\"" +
                                        interfaceName + "\"");
                            }
                        }
                    }
                    i.setOspfCost(ospfCost);
                }
            });
        }
    }


    public Set<RoutingProtocol> findRedistributedProtocols(Configuration conf, RoutingPolicy pol,
            RoutingProtocol p) {
        Set<RoutingProtocol> protos = new HashSet<>();
        AstVisitor v = new AstVisitor();
        v.visit(conf, pol.getStatements(), stmt -> {}, expr -> {
            if (expr instanceof MatchProtocol) {
                MatchProtocol mp = (MatchProtocol) expr;
                RoutingProtocol other = mp.getProtocol();
                if (other != p) {
                    switch (other) {
                        case BGP:
                            protos.add(other);
                            break;
                        case OSPF:
                            protos.add(other);
                            break;
                        case STATIC:
                            protos.add(other);
                            break;
                        case CONNECTED:
                            protos.add(other);
                            break;
                        case IBGP:
                            break;
                        default:
                            throw new BatfishException("Unrecognized protocol: " + other
                                    .protocolName());
                    }
                }
            }
        });
        return protos;
    }

    private void initRedistributionProtocols() {
        getGraph().getConfigurations().forEach((router, conf) -> {

            for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {

                Set<RoutingProtocol> redistributed = new HashSet<>();
                redistributed.add(proto);

                _logicalGraph.getRedistributedProtocols().put(router, proto, redistributed);

                RoutingPolicy pol = getGraph().findCommonRoutingPolicy(router, proto);
                if (pol != null) {
                    Set<RoutingProtocol> ps = findRedistributedProtocols(conf, pol, proto);
                    for (RoutingProtocol p : ps) {
                        // Make sure there is actually a routing process for the other protocol
                        // For example, it might get sliced away if not relevant
                        boolean isProto = getGraph().getProtocols().get(router).contains(p);
                        if (isProto) {
                            redistributed.add(p);
                        }
                    }
                }

            }
        });
    }


    private BoolExpr isRelevantFor(Prefix p, ArithExpr ae) {
        long pfx = p.getNetworkAddress().asLong();
        return firstBitsEqual(ae, pfx, p.getPrefixLength());
    }

    public List<Prefix> getOriginatedNetworks(Configuration conf, RoutingProtocol proto) {
        List<Prefix> acc = new ArrayList<>();

        if (proto == RoutingProtocol.OSPF) {
            conf.getDefaultVrf().getOspfProcess().getAreas().forEach((areaID, area) -> {
                // if (areaID == 0) {
                for (Interface iface : area.getInterfaces()) {
                    if (iface.getActive() && iface.getOspfEnabled()) {
                        acc.add(iface.getPrefix());
                    }
                }
                // } else {
                //     throw new BatfishException("Error: only support area 0 at the moment");
                // }
            });
            return acc;
        }

        if (proto == RoutingProtocol.BGP) {
            conf.getRouteFilterLists().forEach((name, list) -> {
                for (RouteFilterLine line : list.getLines()) {
                    if (name.contains(BGP_NETWORK_FILTER_LIST_NAME)) {
                        acc.add(line.getPrefix());
                    }
                }
            });
            return acc;
        }

        if (proto == RoutingProtocol.CONNECTED) {
            conf.getInterfaces().forEach((name, iface) -> {
                Prefix p = iface.getPrefix();
                if (p != null) {
                    acc.add(p);
                }
            });
            return acc;
        }

        if (proto == RoutingProtocol.STATIC) {
            for (StaticRoute sr : conf.getDefaultVrf().getStaticRoutes()) {
                if (sr.getNetwork() != null) {
                    acc.add(sr.getNetwork());
                }
            }
            return acc;
        }

        throw new BatfishException("ERROR: getOriginatedNetworks: " + proto.protocolName());
    }

    public BoolExpr safeEq(Expr x, Expr value) {
        if (x == null) {
            return True();
        }
        return Eq(x, value);
    }

    public BoolExpr safeEqAdd(ArithExpr x, ArithExpr value, Integer cost) {
        if (x == null) {
            return True();
        }
        if (cost == null) {
            return Eq(x, value);
        }
        return Eq(x, Sum(value, Int(cost)));
    }

    public int defaultId() {
        return 0;
    }

    public int defaultMetric(RoutingProtocol proto) {
        if (proto == RoutingProtocol.CONNECTED) {
            return 0;
        }
        if (proto == RoutingProtocol.STATIC) {
            return 0;
        }
        return 0;
    }

    public int defaultMed(RoutingProtocol proto) {
        if (proto == RoutingProtocol.BGP) {
            return 100;
        }
        return 0;
    }

    public int defaultLocalPref() {
        return 0;
    }

    public int defaultLength() {
        return 0;
    }

    // TODO: depends on configuration
    public boolean isMultipath(Configuration conf, RoutingProtocol proto) {
        if (proto == RoutingProtocol.CONNECTED) {
            return true;
        } else if (proto == RoutingProtocol.STATIC) {
            return true;
        } else if (proto == RoutingProtocol.OSPF) {
            return true;
        } else {
            return true;
        }
    }

    private SymbolicRecord correctVars(LogicalEdge e) {
        SymbolicRecord vars = e.getSymbolicRecord();
        if (!vars.getIsUsed()) {
            return _logicalGraph.getOtherEnd().get(e).getSymbolicRecord();
        }
        return vars;
    }

    private BoolExpr equalHelper(ArithExpr best, ArithExpr vars, ArithExpr defaultVal) {
        BoolExpr tru = True();
        if (vars == null) {
            if (best != null) {
                return Eq(best, defaultVal);
            } else {
                return tru;
            }
        } else {
            return Eq(best, vars);
        }
    }

    public BoolExpr equalHistories(RoutingProtocol proto, SymbolicRecord best, SymbolicRecord vars) {
        BoolExpr history;
        if (best.getProtocolHistory() == null || vars.getProtocolHistory() == null) {
            history = True();
        } else {
            history = best.getProtocolHistory().mkEqual(vars.getProtocolHistory());
        }
        return history;
    }

    public BoolExpr equal(
            Configuration conf, RoutingProtocol proto, SymbolicRecord best, SymbolicRecord vars,
            LogicalEdge e) {

        ArithExpr defaultLocal = Int(defaultLocalPref());
        ArithExpr defaultAdmin = Int(defaultAdminDistance(conf, proto));
        ArithExpr defaultMet = Int(defaultMetric(proto));
        ArithExpr defaultMed = Int(defaultMed(proto));
        ArithExpr defaultLen = Int(defaultLength());

        BoolExpr equalLen;
        BoolExpr equalAd;
        BoolExpr equalLp;
        BoolExpr equalMet;
        BoolExpr equalMed;
        BoolExpr equalId;

        equalLen = equalHelper(best.getPrefixLength(), vars.getPrefixLength(), defaultLen);
        equalAd = equalHelper(best.getAdminDist(), vars.getAdminDist(), defaultAdmin);
        equalLp = equalHelper(best.getLocalPref(), vars.getLocalPref(), defaultLocal);
        equalMet = equalHelper(best.getMetric(), vars.getMetric(), defaultMet);
        equalMed = equalHelper(best.getMed(), vars.getMed(), defaultMed);

        if (vars.getRouterId() == null) {
            if (best.getRouterId() == null || e == null) {
                equalId = True();
            } else {
                Long peerId = _logicalGraph.findRouterId(e, proto);
                if (isMultipath(conf, proto) || peerId == null) {
                    equalId = True();
                } else {
                    equalId = Eq(best.getRouterId(), Int(peerId));
                }
            }
        } else {
            equalId = Eq(best.getRouterId(), vars.getRouterId());
        }

        BoolExpr history = equalHistories(proto, best, vars);

        return And(equalLen, equalAd, equalLp, equalMet, equalMed, equalId, history);
    }

    private BoolExpr geBetterHelper(
            ArithExpr best, ArithExpr vars, ArithExpr defaultVal, boolean less, boolean bestCond) {
        BoolExpr fal = False();
        if (vars == null) {
            if (best != null && bestCond) {
                if (less) {
                    return Lt(best, defaultVal);
                } else {
                    return Gt(best, defaultVal);
                }
            } else {
                return fal;
            }
        } else {
            if (less) {
                return Lt(best, vars);
            } else {
                return Gt(best, vars);
            }
        }
    }

    private BoolExpr geEqualHelper(
            ArithExpr best, ArithExpr vars, ArithExpr defaultVal, boolean bestCond) {
        BoolExpr tru = True();
        if (vars == null) {
            if (best != null && bestCond) {
                return Eq(best, defaultVal);
            } else {
                return tru;
            }
        } else {
            return Eq(best, vars);
        }
    }

    private BoolExpr greaterOrEqual(
            Configuration conf, RoutingProtocol proto, SymbolicRecord best, SymbolicRecord vars,
            LogicalEdge e) {

        ArithExpr defaultLocal = Int(defaultLocalPref());
        ArithExpr defaultAdmin = Int(defaultAdminDistance(conf, proto));
        ArithExpr defaultMet = Int(defaultMetric(proto));
        ArithExpr defaultMed = Int(defaultMed(proto));
        ArithExpr defaultLen = Int(defaultLength());

        BoolExpr betterLen = geBetterHelper(best.getPrefixLength(), vars.getPrefixLength(),
                defaultLen, false, true);
        BoolExpr equalLen = geEqualHelper(best.getPrefixLength(), vars.getPrefixLength(),
                defaultLen, true);

        boolean keepAd = _optimizations.getKeepAdminDist();
        BoolExpr betterAd = geBetterHelper(best.getAdminDist(), vars.getAdminDist(),
                defaultAdmin, true, keepAd);
        BoolExpr equalAd = geEqualHelper(best.getAdminDist(), vars.getAdminDist(), defaultAdmin,
                keepAd);

        boolean keepLp = _optimizations.getKeepLocalPref();
        BoolExpr betterLp = geBetterHelper(best.getLocalPref(), vars.getLocalPref(),
                defaultLocal, false, keepLp);
        BoolExpr equalLp = geEqualHelper(best.getLocalPref(), vars.getLocalPref(), defaultLocal,
                keepLp);

        BoolExpr betterMet = geBetterHelper(best.getMetric(), vars.getMetric(), defaultMet, true,
                true);
        BoolExpr equalMet = geEqualHelper(best.getMetric(), vars.getMetric(), defaultMet, true);

        BoolExpr betterMed = geBetterHelper(best.getMed(), vars.getMed(), defaultMed, true, true);
        BoolExpr equalMed = geEqualHelper(best.getMed(), vars.getMed(), defaultMed, true);

        BoolExpr tiebreak;
        if (vars.getRouterId() == null) {
            if (best.getRouterId() == null) {
                tiebreak = True();
            } else {
                Long peerId = _logicalGraph.findRouterId(e, proto);
                if (isMultipath(conf, proto) || peerId == null) {
                    tiebreak = True();
                } else {
                    tiebreak = Le(best.getRouterId(), Int(peerId));
                }
            }
        } else {
            tiebreak = Le(best.getRouterId(), vars.getRouterId());
        }

        BoolExpr b = And(equalMed, tiebreak);
        BoolExpr b0 = Or(betterMed, b);
        BoolExpr b1 = And(equalMet, b0);
        BoolExpr b2 = Or(betterMet, b1);
        BoolExpr b3 = And(equalLp, b2);
        BoolExpr b4 = Or(betterLp, b3);
        BoolExpr b5 = And(equalAd, b4);
        BoolExpr b6 = Or(betterAd, b5);
        BoolExpr b7 = And(equalLen, b6);
        return Or(betterLen, b7);
    }

    private void addBestOverallConstraints() {
        getGraph().getConfigurations().forEach((router, conf) -> {

            // These constraints will be added at the protocol-level when a single protocol
            if (!_optimizations.getSliceHasSingleProtocol().contains(router)) {

                boolean someProto = false;

                BoolExpr acc = null;
                BoolExpr somePermitted = null;
                SymbolicRecord best = _symbolicDecisions.getBestNeighbor().get(router);

                for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {
                    someProto = true;

                    SymbolicRecord bestVars = _symbolicDecisions.getBestVars(_optimizations,
                            router, proto);

                    if (somePermitted == null) {
                        somePermitted = bestVars.getPermitted();
                    } else {
                        somePermitted = Or(somePermitted, bestVars.getPermitted());
                    }

                    BoolExpr val = And(bestVars.getPermitted(), equal(conf, proto, best,
                            bestVars, null));
                    if (acc == null) {
                        acc = val;
                    } else {
                        acc = Or(acc, val);
                    }
                    add(Implies(bestVars.getPermitted(), greaterOrEqual(conf, proto, best,
                            bestVars, null)));
                }

                if (someProto) {
                    if (acc != null) {
                        add(Eq(somePermitted, best.getPermitted()));
                        add(Implies(somePermitted, acc));
                    }
                } else {
                    add(Not(best.getPermitted()));
                }
            }
        });
    }

    private Set<LogicalEdge> collectAllImportLogicalEdges(String router, Configuration conf,
            RoutingProtocol proto) {
        Set<LogicalEdge> eList = new HashSet<>();
        for (ArrayList<LogicalEdge> es : _logicalGraph.getLogicalEdges().get(router, proto)) {
            for (LogicalEdge le : es) {
                if (_logicalGraph.isEdgeUsed(conf, proto, le) && le.getEdgeType() == EdgeType
                        .IMPORT) {
                    eList.add(le);
                }
            }
        }
        return eList;
    }

    private void addBestPerProtocolConstraints() {
        getGraph().getConfigurations().forEach((router, conf) -> {

            for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {

                // TODO: must do this for each of 32 lens
                SymbolicRecord bestVars = _symbolicDecisions.getBestVars(_optimizations, router,
                        proto);
                BoolExpr acc = null;
                BoolExpr somePermitted = null;

                for (LogicalEdge e : collectAllImportLogicalEdges(router, conf, proto)) {

                    SymbolicRecord vars = correctVars(e);

                    if (somePermitted == null) {
                        somePermitted = vars.getPermitted();
                    } else {
                        somePermitted = Or(somePermitted, vars.getPermitted());
                    }

                    BoolExpr v = And(vars.getPermitted(), equal(conf, proto, bestVars, vars, e));
                    if (acc == null) {
                        acc = v;
                    } else {
                        acc = Or(acc, v);
                    }
                    add(Implies(vars.getPermitted(), greaterOrEqual(conf, proto, bestVars, vars,
                            e)));

                }

                if (acc != null) {
                    add(Eq(somePermitted, bestVars.getPermitted()));
                    // best is one of the allowed ones
                    add(Implies(somePermitted, acc));
                }
            }

        });
    }

    private void addChoicePerProtocolConstraints() {
        getGraph().getConfigurations().forEach((router, conf) -> {
            for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {
                SymbolicRecord bestVars = _symbolicDecisions.getBestVars(_optimizations, router,
                        proto);
                for (LogicalEdge e : collectAllImportLogicalEdges(router, conf, proto)) {
                    SymbolicRecord vars = correctVars(e);
                    BoolExpr choice = _symbolicDecisions.getChoiceVariables().get(router, proto, e);
                    BoolExpr isBest = equal(conf, proto, bestVars, vars, e);
                    add(Eq(choice, And(vars.getPermitted(), isBest)));
                }
            }
        });
    }

    private void addControlForwardingConstraints() {
        getGraph().getConfigurations().forEach((router, conf) -> {

            boolean someEdge = false;

            SymbolicRecord best = _symbolicDecisions.getBestNeighbor().get(router);
            Map<GraphEdge, BoolExpr> cfExprs = new HashMap<>();

            for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {

                for (LogicalEdge e : collectAllImportLogicalEdges(router, conf, proto)) {

                    someEdge = true;

                    SymbolicRecord vars = correctVars(e);
                    BoolExpr choice = _symbolicDecisions.getChoiceVariables().get(router, proto, e);
                    BoolExpr isBest = And(choice, equal(conf, proto, best, vars, e));

                    GraphEdge ge = e.getEdge();
                    BoolExpr cForward = _symbolicDecisions.getControlForwarding().get(router, ge);
                    add(Implies(isBest, cForward));

                    // record the negation as well
                    BoolExpr existing = cfExprs.get(ge);
                    if (existing == null) {
                        cfExprs.put(ge, isBest);
                    } else {
                        cfExprs.put(ge, Or(existing, isBest));
                    }

                }
            }

            // Handle the case that the router has no protocol running
            if (!someEdge) {
                for (GraphEdge ge : getGraph().getEdgeMap().get(router)) {
                    BoolExpr cForward = _symbolicDecisions.getControlForwarding().get(router, ge);
                    add(Not(cForward));
                }
            } else {
                _logicalGraph.getLogicalEdges().get(router).forEach((proto, eList) -> {
                    eList.forEach(edges -> {
                        edges.forEach(le -> {
                            GraphEdge ge = le.getEdge();
                            BoolExpr expr = cfExprs.get(ge);
                            BoolExpr cForward = _symbolicDecisions.getControlForwarding().get
                                    (router, ge);
                            if (expr != null) {
                                add(Implies(Not(expr), Not(cForward)));
                            } else {
                                add(Not(cForward));
                            }
                        });
                    });
                });
            }
        });

    }

    private BoolExpr computeWildcardMatch(Set<IpWildcard> wcs, ArithExpr field) {
        BoolExpr acc = False();
        for (IpWildcard wc : wcs) {
            if (!wc.isPrefix()) {
                throw new BatfishException("ERROR: computeDstWildcards, non sequential mask " +
                        "detected");
            }
            acc = Or(acc, isRelevantFor(wc.toPrefix(), field));
        }
        return (BoolExpr) acc.simplify();
    }

    private BoolExpr computeValidRange(Set<SubRange> ranges, ArithExpr field) {
        BoolExpr acc = False();
        for (SubRange range : ranges) {
            int start = range.getStart();
            int end = range.getEnd();
            if (start == end) {
                BoolExpr val = Eq(field, Int(start));
                acc = Or(acc, val);
            } else {
                BoolExpr val1 = Ge(field, Int(start));
                BoolExpr val2 = Le(field, Int(end));
                acc = Or(acc, And(val1, val2));
            }
        }
        return (BoolExpr) acc.simplify();
    }

    private BoolExpr computeTcpFlags(TcpFlags flags) {
        BoolExpr acc = True();
        if (flags.getUseAck()) {
            acc = And(acc, Eq(_symbolicPacket.getTcpAck(), Bool(flags.getAck())));
        }
        if (flags.getUseCwr()) {
            acc = And(acc, Eq(_symbolicPacket.getTcpCwr(), Bool(flags.getCwr())));
        }
        if (flags.getUseEce()) {
            acc = And(acc, Eq(_symbolicPacket.getTcpEce(), Bool(flags.getEce())));
        }
        if (flags.getUseFin()) {
            acc = And(acc, Eq(_symbolicPacket.getTcpFin(), Bool(flags.getFin())));
        }
        if (flags.getUsePsh()) {
            acc = And(acc, Eq(_symbolicPacket.getTcpPsh(), Bool(flags.getPsh())));
        }
        if (flags.getUseRst()) {
            acc = And(acc, Eq(_symbolicPacket.getTcpRst(), Bool(flags.getRst())));
        }
        if (flags.getUseSyn()) {
            acc = And(acc, Eq(_symbolicPacket.getTcpSyn(), Bool(flags.getSyn())));
        }
        if (flags.getUseUrg()) {
            acc = And(acc, Eq(_symbolicPacket.getTcpUrg(), Bool(flags.getUrg())));
        }
        return (BoolExpr) acc.simplify();
    }

    private BoolExpr computeTcpFlags(List<TcpFlags> flags) {
        BoolExpr acc = False();
        for (TcpFlags fs : flags) {
            acc = Or(acc, computeTcpFlags(fs));
        }
        return (BoolExpr) acc.simplify();
    }

    private BoolExpr computeIpProtocols(Set<IpProtocol> ipProtos) {
        BoolExpr acc = False();
        for (IpProtocol proto : ipProtos) {
            ArithExpr protoNum = Int(proto.number());
            acc = Or(acc, Eq(protoNum, _symbolicPacket.getIpProtocol()));
        }
        return (BoolExpr) acc.simplify();
    }

    private BoolExpr computeACL(IpAccessList acl) {
        // Check if there is an ACL first
        if (acl == null) {
            return True();
        }

        BoolExpr acc = False();

        List<IpAccessListLine> lines = new ArrayList<>(acl.getLines());
        Collections.reverse(lines);

        for (IpAccessListLine l : lines) {
            BoolExpr local = null;

            if (l.getDstIps() != null) {
                local = computeWildcardMatch(l.getDstIps(), _symbolicPacket.getDstIp());
            }

            if (l.getSrcIps() != null) {
                BoolExpr val = computeWildcardMatch(l.getSrcIps(), _symbolicPacket.getSrcIp());
                local = (local == null ? val : And(local, val));
            }

            if (l.getDscps() != null && !l.getDscps().isEmpty()) {
                throw new BatfishException("detected dscps");
            }

            if (l.getDstPorts() != null && !l.getDstPorts().isEmpty()) {
                BoolExpr val = computeValidRange(l.getDstPorts(), _symbolicPacket.getDstPort());
                local = (local == null ? val : And(local, val));
            }

            if (l.getSrcPorts() != null && !l.getSrcPorts().isEmpty()) {
                BoolExpr val = computeValidRange(l.getSrcPorts(), _symbolicPacket.getSrcPort());
                local = (local == null ? val : And(local, val));
            }

            if (l.getEcns() != null && !l.getEcns().isEmpty()) {
                throw new BatfishException("detected ecns");
            }

            if (l.getTcpFlags() != null && !l.getTcpFlags().isEmpty()) {
                BoolExpr val = computeTcpFlags(l.getTcpFlags());
                local = (local == null ? val : And(local, val));
            }

            if (l.getFragmentOffsets() != null && !l.getFragmentOffsets().isEmpty()) {
                throw new BatfishException("detected fragment offsets");
            }

            if (l.getIcmpCodes() != null && !l.getIcmpCodes().isEmpty()) {
                BoolExpr val = computeValidRange(l.getIcmpCodes(), _symbolicPacket.getIcmpCode());
                local = (local == null ? val : And(local, val));
            }

            if (l.getIcmpTypes() != null && !l.getIcmpTypes().isEmpty()) {
                BoolExpr val = computeValidRange(l.getIcmpTypes(), _symbolicPacket.getIcmpType());
                local = (local == null ? val : And(local, val));
            }

            if (l.getStates() != null && !l.getStates().isEmpty()) {
                throw new BatfishException("detected states");
            }

            if (l.getIpProtocols() != null && !l.getIpProtocols().isEmpty()) {
                BoolExpr val = computeIpProtocols(l.getIpProtocols());
                local = (local == null ? val : And(local, val));
            }

            if (l.getNotDscps() != null && !l.getNotDscps().isEmpty()) {
                throw new BatfishException("detected NOT dscps");
            }

            if (l.getNotDstIps() != null && !l.getNotDstIps().isEmpty()) {
                throw new BatfishException("detected NOT dst ip");
            }

            if (l.getNotSrcIps() != null && !l.getNotSrcIps().isEmpty()) {
                throw new BatfishException("detected NOT src ip");
            }

            if (l.getNotDstPorts() != null && !l.getNotDstPorts().isEmpty()) {
                throw new BatfishException("detected NOT dst port");
            }

            if (l.getNotSrcPorts() != null && !l.getNotSrcPorts().isEmpty()) {
                throw new BatfishException("detected NOT src port");
            }

            if (l.getNotEcns() != null && !l.getNotEcns().isEmpty()) {
                throw new BatfishException("detected NOT ecns");
            }

            if (l.getNotIcmpCodes() != null && !l.getNotIcmpCodes().isEmpty()) {
                throw new BatfishException("detected NOT icmp codes");
            }

            if (l.getNotIcmpTypes() != null && !l.getNotIcmpTypes().isEmpty()) {
                throw new BatfishException("detected NOT icmp types");
            }

            if (l.getNotFragmentOffsets() != null && !l.getNotFragmentOffsets().isEmpty()) {
                throw new BatfishException("detected NOT fragment offset");
            }

            if (l.getNotIpProtocols() != null && !l.getNotIpProtocols().isEmpty()) {
                throw new BatfishException("detected NOT ip protocols");
            }

            if (local != null) {
                BoolExpr ret;
                if (l.getAction() == LineAction.ACCEPT) {
                    ret = True();
                } else {
                    ret = False();
                }

                if (l.getNegate()) {
                    local = Not(local);
                }

                acc = If(local, ret, acc);
            }
        }

        return acc;
    }

    private void addAclFunctions() {
        getGraph().getEdgeMap().forEach((router, edges) -> {
            for (GraphEdge ge : edges) {
                Interface i = ge.getStart();

                IpAccessList outbound = i.getOutgoingFilter();
                if (outbound != null) {
                    String outName = router + "_" + i.getName() + "_OUTBOUND_" + outbound.getName();
                    BoolExpr outAcl = _ctx.mkBoolConst(outName);
                    BoolExpr outAclFunc = computeACL(outbound);
                    add(Eq(outAcl, outAclFunc));
                    _outboundAcls.put(i, outAcl);
                }

                IpAccessList inbound = i.getIncomingFilter();
                if (inbound != null) {
                    String inName = router + "_" + i.getName() + "_INBOUND_" + inbound.getName();
                    BoolExpr inAcl = _ctx.mkBoolConst(inName);
                    BoolExpr inAclFunc = computeACL(inbound);
                    add(Eq(inAcl, inAclFunc));
                    _inboundAcls.put(i, inAcl);
                }
            }
        });
    }

    private void addDataForwardingConstraints() {
        getGraph().getEdgeMap().forEach((router, edges) -> {
            for (GraphEdge ge : edges) {
                BoolExpr acl = _inboundAcls.get(ge.getStart());
                if (acl == null) {
                    acl = True();
                }
                BoolExpr cForward = _symbolicDecisions.getControlForwarding().get(router, ge);
                BoolExpr dForward = _symbolicDecisions.getDataForwarding().get(router, ge);
                BoolExpr notBlocked = And(cForward, acl);
                add(Eq(notBlocked, dForward));
            }
        });
    }

    public BoolExpr relevantOrigination(List<Prefix> prefixes) {
        BoolExpr acc = False();
        for (Prefix p : prefixes) {
            acc = Or(acc, isRelevantFor(p, _symbolicPacket.getDstIp()));
        }
        return acc;
    }

    private Integer addedCost(RoutingProtocol proto, Interface iface) {
        switch (proto) {
            case OSPF:
                return iface.getOspfCost();
            case ISIS:
                return iface.getIsisCost();
        }
        return 1;
    }

    public int defaultAdminDistance(Configuration conf, RoutingProtocol proto) {
        return proto.getDefaultAdministrativeCost(conf.getConfigurationFormat());
    }

    private void addImportConstraint(
            LogicalEdge e, SymbolicRecord varsOther, Configuration conf, RoutingProtocol proto,
            Interface iface, String router, List<Prefix> originations) {

        SymbolicRecord vars = e.getSymbolicRecord();

        ArithExpr failed = _symbolicFailures.getFailedVariable(e.getEdge());
        BoolExpr notFailed = Eq(failed, Int(0));

        if (vars.getIsUsed()) {

            if (proto == RoutingProtocol.CONNECTED) {
                Prefix p = iface.getPrefix();
                BoolExpr relevant = And(Bool(iface.getActive()), isRelevantFor(p, _symbolicPacket
                        .getDstIp()), notFailed);
                BoolExpr per = vars.getPermitted();
                BoolExpr len = safeEq(vars.getPrefixLength(), Int(p.getPrefixLength()));
                BoolExpr ad = safeEq(vars.getAdminDist(), Int(1));
                BoolExpr lp = safeEq(vars.getLocalPref(), Int(0));
                BoolExpr met = safeEq(vars.getMetric(), Int(0));
                BoolExpr values = And(per, len, ad, lp, met);
                add(If(relevant, values, Not(vars.getPermitted())));
            }

            if (proto == RoutingProtocol.STATIC) {
                List<StaticRoute> srs = getGraph().getStaticRoutes().get(router).get(iface
                        .getName()); // should exist
                assert (srs != null);
                BoolExpr acc = Not(vars.getPermitted());
                for (StaticRoute sr : srs) {
                    Prefix p = sr.getNetwork();
                    BoolExpr relevant = And(Bool(iface.getActive()), isRelevantFor(p,
                            _symbolicPacket.getDstIp()), notFailed);
                    BoolExpr per = vars.getPermitted();
                    BoolExpr len = safeEq(vars.getPrefixLength(), Int(p.getPrefixLength()));
                    BoolExpr ad = safeEq(vars.getAdminDist(), Int(sr.getAdministrativeCost()));
                    BoolExpr lp = safeEq(vars.getLocalPref(), Int(0));
                    BoolExpr met = safeEq(vars.getMetric(), Int(0));
                    BoolExpr values = And(per, len, ad, lp, met);
                    acc = If(relevant, values, acc);
                }
                add(acc);
            }

            if (proto == RoutingProtocol.OSPF || proto == RoutingProtocol.BGP) {
                BoolExpr val = Not(vars.getPermitted());
                if (varsOther != null) {
                    // Get the import policy for a given network, can return null if none,
                    // in which case we just will copy over the old variables.

                    BoolExpr isRoot = relevantOrigination(originations);
                    BoolExpr usable = And(Not(isRoot), Bool(iface.getActive()), varsOther
                            .getPermitted(), notFailed);
                    BoolExpr importFunction;
                    RoutingPolicy pol = getGraph().findImportRoutingPolicy(router, proto, e);
                    if (pol != null) {

                        TransferFunction f = new TransferFunction(this, conf, varsOther, vars,
                                proto, proto, pol.getStatements(), null);
                        importFunction = f.compute();
                        // System.out.println("IMPORT FUNCTION: " + router + " " + varsOther
                        // .getName());
                        // System.out.println(importFunction.simplify());
                    } else {
                        // just copy the export policy in ospf/bgp
                        BoolExpr per = Eq(vars.getPermitted(), varsOther.getPermitted());
                        BoolExpr lp = safeEq(vars.getLocalPref(), varsOther.getLocalPref());
                        BoolExpr ad = safeEq(vars.getAdminDist(), varsOther.getAdminDist());
                        BoolExpr met = safeEq(vars.getMetric(), varsOther.getMetric());
                        BoolExpr med = safeEq(vars.getMed(), varsOther.getMed());
                        BoolExpr len = safeEq(vars.getPrefixLength(), varsOther.getPrefixLength());
                        importFunction = And(per, lp, ad, met, med, len);
                    }

                    add(If(usable, importFunction, val));
                } else {
                    add(val);
                }

            }
        }
    }

    private boolean addExportConstraint(
            LogicalEdge e, SymbolicRecord varsOther, Configuration conf, RoutingProtocol proto,
            Interface iface, String router, boolean usedExport, List<Prefix> originations) {

        SymbolicRecord vars = e.getSymbolicRecord();

        ArithExpr failed = _symbolicFailures.getFailedVariable(e.getEdge());
        BoolExpr notFailed = Eq(failed, Int(0));

        // only add constraints once when using a single copy of export variables
        if (!_optimizations.getSliceCanKeepSingleExportVar().get(router).get(proto) ||
                !usedExport) {

            if (proto == RoutingProtocol.CONNECTED) {
                BoolExpr val = Not(vars.getPermitted());
                add(val);
            }

            if (proto == RoutingProtocol.STATIC) {
                BoolExpr val = Not(vars.getPermitted());
                add(val);
            }

            if (proto == RoutingProtocol.OSPF || proto == RoutingProtocol.BGP) {
                // originated routes
                Integer cost = addedCost(proto, iface);
                BoolExpr val = Not(vars.getPermitted());

                BoolExpr usable = And(Bool(iface.getActive()), varsOther.getPermitted(), notFailed);

                BoolExpr acc;
                RoutingPolicy pol = getGraph().findExportRoutingPolicy(router, proto, e);
                if (pol != null) {

                    // We have to wrap this with the right thing for some reason
                    List<Statement> statements;
                    if (proto == RoutingProtocol.OSPF) {
                        If i = new If();
                        Statements.StaticStatement s =
                                new Statements.StaticStatement(Statements.ExitAccept);
                        i.setTrueStatements(Collections.singletonList(s));
                        i.setFalseStatements(pol.getStatements());
                        BooleanExpr expr = new MatchProtocol(RoutingProtocol.OSPF);
                        i.setGuard(expr);
                        statements = Collections.singletonList(i);
                    } else {
                        statements = pol.getStatements();
                    }

                    // System.out.println("Got export function for: " + router);
                    TransferFunction f = new TransferFunction(
                            this, conf, varsOther, vars, proto, proto, statements, cost);
                    acc = f.compute();

                    // System.out.println("EXPORT FUNCTION: " + router + " " + varsOther.getName());
                    // System.out.println(acc);
                    // System.out.println("SIMPLIFIED: " + router + " " + varsOther.getName());
                    // System.out.println(acc.simplify());

                } else {
                    BoolExpr per = vars.getPermitted();
                    BoolExpr len = safeEq(vars.getPrefixLength(), varsOther.getPrefixLength());
                    BoolExpr ad = safeEq(vars.getAdminDist(), varsOther.getAdminDist());
                    BoolExpr med = safeEq(vars.getMed(), varsOther.getMed());
                    BoolExpr lp = safeEq(vars.getLocalPref(), varsOther.getLocalPref());
                    BoolExpr met = safeEqAdd(vars.getMetric(), varsOther.getMetric(), cost);
                    acc = And(per, len, ad, med, lp, met);

                    // TODO: need a cleaner way to deal with this
                    if (proto == RoutingProtocol.OSPF) {
                        BoolExpr isOspf = varsOther.getProtocolHistory().checkIfValue(proto);
                        acc = If(isOspf, acc, val);
                    }

                }

                acc = If(usable, acc, val);

                for (Prefix p : originations) {
                    BoolExpr relevant = And(Bool(iface.getActive()), isRelevantFor(p,
                            _symbolicPacket.getDstIp()));
                    int adminDistance = defaultAdminDistance(conf, proto);
                    int prefixLength = p.getPrefixLength();
                    BoolExpr per = vars.getPermitted();
                    BoolExpr lp = safeEq(vars.getLocalPref(), Int(0));
                    BoolExpr ad = safeEq(vars.getAdminDist(), Int(adminDistance));
                    BoolExpr met = safeEq(vars.getMetric(), Int(cost));
                    BoolExpr med = safeEq(vars.getMed(), Int(100));
                    BoolExpr len = safeEq(vars.getPrefixLength(), Int(prefixLength));
                    BoolExpr values = And(per, lp, ad, met, med, len);
                    acc = If(relevant, values, acc);
                }

                add(acc);
            }
            return true;
        }
        return false;
    }

    private void addTransferFunction() {
        getGraph().getConfigurations().forEach((router, conf) -> {
            for (RoutingProtocol proto : getGraph().getProtocols().get(router)) {
                Boolean usedExport = false;
                List<Prefix> originations = getOriginatedNetworks(conf, proto);
                for (ArrayList<LogicalEdge> eList : _logicalGraph.getLogicalEdges().get(router,
                        proto)) {
                    for (LogicalEdge e : eList) {
                        GraphEdge ge = e.getEdge();
                        Interface iface = ge.getStart();
                        if (getGraph().isInterfaceUsed(conf, proto, iface)) {
                            SymbolicRecord varsOther;
                            switch (e.getEdgeType()) {
                                case IMPORT:
                                    varsOther = _logicalGraph.findOtherVars(e);
                                    addImportConstraint(e, varsOther, conf, proto, iface, router,
                                            originations);
                                    break;

                                case EXPORT:
                                    // varsOther = _symbolicDecisions.getBestVars(_optimizations, router, proto);
                                    varsOther = _symbolicDecisions.getBestNeighbor().get(router);
                                    usedExport = addExportConstraint(e, varsOther, conf, proto,
                                            iface, router, usedExport, originations);
                                    break;
                            }
                        }
                    }
                }
            }
        });
    }

    private void addHistoryConstraints() {
        _symbolicDecisions.getBestNeighborPerProtocol().forEach((router, proto, vars) -> {
            assert(vars.getProtocolHistory() != null);
            add(vars.getProtocolHistory().checkIfValue(proto));
        });

        _symbolicDecisions.getBestNeighbor().forEach((router, vars) -> {
            if (_optimizations.getSliceHasSingleProtocol().contains(router)) {
                RoutingProtocol proto = getGraph().getProtocols().get(router).get(0);
                add(vars.getProtocolHistory().checkIfValue(proto));
            }
        });
    }

    private void addUnusedDefaultValueConstraints() {
        for (SymbolicRecord vars : _allSymbolicRecords) {

            BoolExpr notPermitted = Not(vars.getPermitted());
            ArithExpr zero = Int(0);

            if (vars.getAdminDist() != null) {
                add(Implies(notPermitted, Eq(vars.getAdminDist(), zero)));
            }
            if (vars.getMed() != null) {
                add(Implies(notPermitted, Eq(vars.getMed(), zero)));
            }
            if (vars.getLocalPref() != null) {
                add(Implies(notPermitted, Eq(vars.getLocalPref(), zero)));
            }
            if (vars.getPrefixLength() != null) {
                add(Implies(notPermitted, Eq(vars.getPrefixLength(), zero)));
            }
            if (vars.getMetric() != null) {
                add(Implies(notPermitted, Eq(vars.getMetric(), zero)));
            }
            if (vars.getProtocolHistory() != null) {
                add(Implies(notPermitted, vars.getProtocolHistory().isDefaultValue() ));
            }
            vars.getCommunities().forEach((cvar, e) -> {
                add(Implies(notPermitted, Not(e)));
            });
        }
    }

    private void addDestinationConstraint() {
        BoolExpr validDestRange = False();
        for (Prefix p : _destinations) {
            long lower = p.getAddress().asLong();
            long upper = p.getEndAddress().asLong();
            BoolExpr constraint;
            if (lower == upper) {
                constraint = Eq(_symbolicPacket.getDstIp(), Int(lower));
            } else {
                BoolExpr x = Ge(_symbolicPacket.getDstIp(), Int(lower));
                BoolExpr y = Le(_symbolicPacket.getDstIp(), Int(upper));
                constraint = And(x, y);
            }
            validDestRange = Or(validDestRange, constraint);
        }

        add(validDestRange);
    }

    private void initConfigurations() {
        getGraph().getConfigurations().forEach((router, conf) -> {
            initOspfInterfaceCosts(conf);
        });
    }

    public VerificationResult verify() {
        int numVariables = _allVariables.size();
        int numConstraints = _solver.getAssertions().length;
        int numNodes = getGraph().getConfigurations().size();
        int numEdges = 0;
        for (Map.Entry<String, Set<String>> e : getGraph().getNeighbors().entrySet()) {
            numEdges += e.getValue().size();
        }
        long start = System.currentTimeMillis();
        Status status = _solver.check();
        long time = System.currentTimeMillis() - start;

        VerificationStats stats = new VerificationStats(numNodes, numEdges, numVariables,
                numConstraints, time);

        if (status == Status.UNSATISFIABLE) {
            return new VerificationResult(true, null, null, null, null, null);
        } else if (status == Status.UNKNOWN) {
            throw new BatfishException("ERROR: satisfiability unknown");
        } else {
            Model m = _solver.getModel();
            SortedMap<Expr, String> valuation = new TreeMap<>();
            SortedMap<String, String> model = new TreeMap<>();

            // Full model
            for (Expr e : _allVariables) {
                String name = e.toString();
                Expr val = m.evaluate(e, false);
                if (!val.equals(e)) {
                    String s = val.toString();
                    model.put(name, s);
                    valuation.put(e, s);
                }
            }

            // Packet model
            String dstIp = valuation.get(_symbolicPacket.getDstIp());
            String srcIp = valuation.get(_symbolicPacket.getSrcIp());
            String dstPt = valuation.get(_symbolicPacket.getDstPort());
            String srcPt = valuation.get(_symbolicPacket.getSrcPort());
            String icmpCode = valuation.get(_symbolicPacket.getIcmpCode());
            String icmpType = valuation.get(_symbolicPacket.getIcmpType());
            String ipProtocol = valuation.get(_symbolicPacket.getIpProtocol());
            String tcpAck = valuation.get(_symbolicPacket.getTcpAck());
            String tcpCwr = valuation.get(_symbolicPacket.getTcpCwr());
            String tcpEce = valuation.get(_symbolicPacket.getTcpEce());
            String tcpFin = valuation.get(_symbolicPacket.getTcpFin());
            String tcpPsh = valuation.get(_symbolicPacket.getTcpPsh());
            String tcpRst = valuation.get(_symbolicPacket.getTcpRst());
            String tcpSyn = valuation.get(_symbolicPacket.getTcpSyn());
            String tcpUrg = valuation.get(_symbolicPacket.getTcpUrg());

            SortedMap<String, String> packetModel = new TreeMap<>();

            Ip dip = new Ip(Long.parseLong(dstIp));
            Ip sip = new Ip(Long.parseLong(srcIp));

            packetModel.put("dstIp", dip.toString());

            if (sip.asLong() != 0) {
                packetModel.put("srcIp", sip.toString());
            }
            if (dstPt != null && !dstPt.equals("0")) {
                packetModel.put("dstPort", dstPt);
            }
            if (srcPt != null && !srcPt.equals("0")) {
                packetModel.put("srcPort", srcPt);
            }
            if (icmpCode != null && !icmpCode.equals("0")) {
                packetModel.put("icmpCode", icmpCode); // TODO: convert to be readable
            }
            if (icmpType != null && !icmpType.equals("0")) {
                packetModel.put("icmpType", icmpType); // TODO: convert to be readable
            }
            if (ipProtocol != null && !ipProtocol.equals("0")) {
                packetModel.put("ipProtocol", ipProtocol); // TODO: convert this to be readable
            }
            if (tcpAck != null && tcpAck.equals("true")) {
                packetModel.put("tcpAck", "set");
            }
            if (tcpCwr != null && tcpCwr.equals("true")) {
                packetModel.put("tcpCwr", "set");
            }
            if (tcpEce != null && tcpEce.equals("true")) {
                packetModel.put("tcpEce", "set");
            }
            if (tcpFin != null && tcpFin.equals("true")) {
                packetModel.put("tcpFin", "set");
            }
            if (tcpPsh != null && tcpPsh.equals("true")) {
                packetModel.put("tcpPsh", "set");
            }
            if (tcpRst != null && tcpRst.equals("true")) {
                packetModel.put("tcpRst", "set");
            }
            if (tcpSyn != null && tcpSyn.equals("true")) {
                packetModel.put("tcpSyn", "set");
            }
            if (tcpUrg != null && tcpUrg.equals("true")) {
                packetModel.put("tcpUrg", "set");
            }

            // Environment model
            SortedMap<String, SortedMap<String, String>> envModel = new TreeMap<>();
            _logicalGraph.getEnvironmentVars().forEach((lge, r) -> {

                if (valuation.get(r.getPermitted()).equals("true")) {
                    SortedMap<String, String> recordMap = new TreeMap<>();
                    GraphEdge ge = lge.getEdge();
                    String nodeIface = ge.getRouter() + "," + ge.getStart().getName() + " (BGP)";
                    envModel.put(nodeIface, recordMap);
                    if (r.getPrefixLength() != null) {
                        String x = valuation.get(r.getPrefixLength());
                        if (x != null) {
                            int len = Integer.parseInt(x);
                            Prefix p1 = new Prefix(dip, len);
                            Prefix p2 = p1.getNetworkPrefix();
                            recordMap.put("prefix", p2.toString());
                        }
                    }
                    if (r.getAdminDist() != null) {
                        String x = valuation.get(r.getAdminDist());
                        if (x != null) {
                            recordMap.put("admin distance", x);
                        }
                    }
                    if (r.getLocalPref() != null) {
                        String x = valuation.get(r.getLocalPref());
                        if (x != null) {
                            recordMap.put("local preference", x);
                        }
                    }
                    if (r.getMetric() != null) {
                        String x = valuation.get(r.getMetric());
                        if (x != null) {
                            recordMap.put("protocol metric", x);
                        }
                    }
                    if (r.getMed() != null) {
                        String x = valuation.get(r.getMed());
                        if (x != null) {
                            recordMap.put("multi-exit disc.", valuation.get(r.getMed()));
                        }
                    }

                    r.getCommunities().forEach((cvar, e) -> {
                        String c = valuation.get(e);
                        // TODO: what about OTHER type?
                        if (c.equals("true") && cvar.getType() == CommunityVar.Type.EXACT) {
                            recordMap.put("community (" + cvar.getValue() + ")", "set");
                        }
                    });
                }
            });

            // Forwarding Model
            SortedSet<String> fwdModel = new TreeSet<>();
            _symbolicDecisions.getDataForwarding().forEach((router, edge, e) -> {
                String s = valuation.get(e);
                if (s != null && s.equals("true")) {
                    fwdModel.add(edge.toString());
                }
            });

            SortedSet<String> failures = new TreeSet<>();
            _symbolicFailures.getFailedInternalLinks().forEach((x, y, e) -> {
                String s = valuation.get(e);
                if (s != null && s.equals("true")) {
                    failures.add("link(" + x + "," + y + ")");
                }
            });
            _symbolicFailures.getFailedEdgeLinks().forEach((ge, e) -> {
                String s = valuation.get(e);
                if (s != null && s.equals("true")) {
                    failures.add("link(" + ge.getRouter() + "," + ge.getStart().getName() + ")");
                }
            });

            return new VerificationResult(false, model, packetModel, envModel, fwdModel, failures);
        }
    }

    public void computeEncoding() {
        if (ENABLE_DEBUGGING) {
            System.out.println(getGraph().toString());
        }
        initConfigurations();
        computeOptimizations();
        initRedistributionProtocols();
        addVariables();
        addBoundConstraints();
        addCommunityConstraints();
        addFailedConstraints(0);
        addTransferFunction();
        addHistoryConstraints();
        addBestPerProtocolConstraints();
        addChoicePerProtocolConstraints();
        addBestOverallConstraints();
        addControlForwardingConstraints();
        addAclFunctions();
        addDataForwardingConstraints();
        addUnusedDefaultValueConstraints();
        addDestinationConstraint();
    }
}