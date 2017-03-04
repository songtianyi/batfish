package org.batfish.smt;

import com.microsoft.z3.*;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.*;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.*;
import org.batfish.datamodel.routing_policy.statement.*;
import org.batfish.smt.utils.Table2;

import java.util.*;
import java.util.regex.Matcher;

/*
 * - Basic iBGP support
 *      * Optimize for failures=0 case
 *      * Optimize for consistent preferences case
 *
 * - Add check for block-to-external for internal prefix space
 * - Add check for block-to-internal for internal prefix space
 * - Ensure that loopbacks/next-hops are reachable
 * - Check for BGP route deflection
 */


/**
 * An object that is responsible for creating a symbolic representation
 * of both the network control and data planes.
 */
public class EncoderSlice {

    static final int BITS = 0;

    static final String BGP_NETWORK_FILTER_LIST_NAME = "BGP_NETWORK_NETWORKS_FILTER";

    static final String BGP_COMMON_FILTER_LIST_NAME = "BGP_COMMON_EXPORT_POLICY";

    private Encoder _encoder;

    private String _sliceName;

    private HeaderSpace _headerSpace;

    private Optimizations _optimizations;

    private LogicalGraph _logicalGraph;

    private SymbolicDecisions _symbolicDecisions;

    private SymbolicPacket _symbolicPacket;

    private Map<Interface, BoolExpr> _inboundAcls;

    private Map<Interface, BoolExpr> _outboundAcls;

    private Table2<String, GraphEdge, BoolExpr> _forwardsAcross;

    private Set<CommunityVar> _allCommunities;

    private Map<CommunityVar, List<CommunityVar>> _communityDependencies;

    public EncoderSlice(Encoder enc, HeaderSpace h, IBatfish batfish, String sliceName) {
        this(enc, h, new Graph(batfish), sliceName);
    }

    public EncoderSlice(Encoder enc, HeaderSpace h, Graph graph, String sliceName) {
        _encoder = enc;
        _sliceName = sliceName;
        _headerSpace = h;
        _optimizations = new Optimizations(this);
        _logicalGraph = new LogicalGraph(graph);
        _symbolicDecisions = new SymbolicDecisions();
        _symbolicPacket = new SymbolicPacket(enc.getCtx(), enc.getId(), _sliceName);

        enc.getAllVariables().add(_symbolicPacket.getDstIp());
        enc.getAllVariables().add(_symbolicPacket.getSrcIp());
        enc.getAllVariables().add(_symbolicPacket.getDstPort());
        enc.getAllVariables().add(_symbolicPacket.getSrcPort());
        enc.getAllVariables().add(_symbolicPacket.getIcmpCode());
        enc.getAllVariables().add(_symbolicPacket.getIcmpType());
        enc.getAllVariables().add(_symbolicPacket.getTcpAck());
        enc.getAllVariables().add(_symbolicPacket.getTcpCwr());
        enc.getAllVariables().add(_symbolicPacket.getTcpEce());
        enc.getAllVariables().add(_symbolicPacket.getTcpFin());
        enc.getAllVariables().add(_symbolicPacket.getTcpPsh());
        enc.getAllVariables().add(_symbolicPacket.getTcpRst());
        enc.getAllVariables().add(_symbolicPacket.getTcpSyn());
        enc.getAllVariables().add(_symbolicPacket.getTcpUrg());
        enc.getAllVariables().add(_symbolicPacket.getIpProtocol());

        _inboundAcls = new HashMap<>();
        _outboundAcls = new HashMap<>();
        _forwardsAcross = new Table2<>();

        initCommunities();
        initOptimizations();
        initRedistributionProtocols();
        initVariables();
        initAclFunctions();
        initForwardingAcross();
    }

    private void initCommunities() {
        _allCommunities = findAllCommunities();

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

    Graph getGraph() {
        return _logicalGraph.getGraph();
    }

    Map<String, List<RoutingProtocol>> getProtocols() {
        return _optimizations.getProtocols();
    }

    Set<CommunityVar> findAllCommunities(Configuration conf, CommunitySetExpr ce) {
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

    HeaderSpace getHeaderSpace() {
        return _headerSpace;
    }

    String getSliceName() {
        return _sliceName;
    }

    Context getCtx() {
        return _encoder.getCtx();
    }

    Solver getSolver() {
        return _encoder.getSolver();
    }

    List<Expr> getAllVariables() {
        return _encoder.getAllVariables();
    }

    Optimizations getOptimizations() {
        return _optimizations;
    }

    LogicalGraph getLogicalGraph() {
        return _logicalGraph;
    }

    SymbolicDecisions getSymbolicDecisions() {
        return _symbolicDecisions;
    }

    SymbolicPacket getSymbolicPacket() {
        return _symbolicPacket;
    }

    Map<Interface, BoolExpr> getIncomingAcls() {
        return _inboundAcls;
    }

    Map<Interface, BoolExpr> getOutgoingAcls() {
        return _outboundAcls;
    }

    Table2<String, GraphEdge, BoolExpr> getForwardsAcross() {
        return _forwardsAcross;
    }

    Set<CommunityVar> getAllCommunities() {
        return _allCommunities;
    }

    Map<CommunityVar, List<CommunityVar>> getCommunityDependencies() {
        return _communityDependencies;
    }

    UnsatCore getUnsatCore() {
        return _encoder.getUnsatCore();
    }

    void add(BoolExpr e) {
        _encoder.add(e);
    }

    BoolExpr False() {
        return _encoder.False();
    }

    BoolExpr Bool(boolean val) {
        return _encoder.Bool(val);
    }

    BoolExpr Not(BoolExpr e) {
        return _encoder.Not(e);
    }

    BoolExpr Or(BoolExpr... vals) {
        return _encoder.Or(vals);
    }

    BoolExpr Implies(BoolExpr e1, BoolExpr e2) {
        return getCtx().mkImplies(e1, e2);
    }

    BoolExpr Gt(Expr e1, Expr e2) {
        if (e1 instanceof ArithExpr && e2 instanceof ArithExpr) {
            return getCtx().mkGt((ArithExpr) e1, (ArithExpr) e2);
        }
        if (e1 instanceof BitVecExpr && e2 instanceof BitVecExpr) {
            return getCtx().mkBVUGT((BitVecExpr) e1, (BitVecExpr) e2);
        }
        throw new BatfishException("Invalid call the Le while encoding control plane");
    }

    ArithExpr Sub(ArithExpr e1, ArithExpr e2) {
        return _encoder.Sub(e1, e2);
    }

    BoolExpr If(BoolExpr cond, BoolExpr case1, BoolExpr case2) {
        return _encoder.If(cond, case1, case2);
    }

    ArithExpr If(BoolExpr cond, ArithExpr case1, ArithExpr case2) {
        return _encoder.If(cond, case1, case2);
    }

    boolean relevantPrefix(Prefix p) {
        return overlaps(_headerSpace, p);
    }

    private boolean overlaps(HeaderSpace h, Prefix p) {
        if (h.getDstIps().isEmpty()) {
            return true;
        }
        for (IpWildcard ipWildcard : h.getDstIps()) {
            Prefix p2 = ipWildcard.toPrefix();
            if (overlaps(p, p2)) {
                return true;
            }
        }
        return false;
    }

    private boolean overlaps(Prefix p1, Prefix p2) {
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

            for (RoutingProtocol proto : getProtocols().get(router)) {

                Map<LogicalEdge, BoolExpr> edgeMap = new HashMap<>();
                map.put(proto, edgeMap);

                for (LogicalEdge e : collectAllImportLogicalEdges(router, conf, proto)) {
                    String chName = e.getSymbolicRecord().getName() + "_choice";
                    BoolExpr choiceVar = getCtx().mkBoolConst(chName);
                    getAllVariables().add(choiceVar);
                    edgeMap.put(e, choiceVar);
                }
            }
        });
    }

    private void buildEdgeMap() {
        getGraph().getEdgeMap().forEach((router, edges) -> {
            for (RoutingProtocol p : getProtocols().get(router)) {
                _logicalGraph.getLogicalEdges().put(router, p, new ArrayList<>());
            }
        });
    }

    private void addForwardingVariables() {
        getGraph().getEdgeMap().forEach((router, edges) -> {
            for (GraphEdge edge : edges) {
                String iface = edge.getStart().getName();

                String cName = _sliceName + "control-forwarding_" + router + "_" + iface;
                BoolExpr cForward = getCtx().mkBoolConst(cName);
                getAllVariables().add(cForward);
                _symbolicDecisions.getControlForwarding().put(router, edge, cForward);

                String dName = _sliceName + "data-forwarding_" + router + "_" + iface;
                BoolExpr dForward = getCtx().mkBoolConst(dName);
                getAllVariables().add(dForward);
                _symbolicDecisions.getDataForwarding().put(router, edge, dForward);
            }
        });
    }

    List<SymbolicRecord> getAllSymbolicRecords() {
        return _encoder.getAllSymbolicRecords();
    }

    SymbolicFailures getSymbolicFailures() {
        return _encoder.getSymbolicFailures();
    }

    private void addBestVariables() {

        getGraph().getEdgeMap().forEach((router, edges) -> {

            List<RoutingProtocol> allProtos = getProtocols().get(router);

            // Overall best
            for (int len = 0; len <= BITS; len++) {
                String name = String.format("%s%s_%s_%s_%s", _sliceName, router, "OVERALL", "none", "BEST");
                String historyName = name + "_history";

                SymbolicEnum<RoutingProtocol> h = new SymbolicEnum<>(this, allProtos, historyName);

                SymbolicRecord evBest = new SymbolicRecord(this, name, router, RoutingProtocol
                        .AGGREGATE, _optimizations, getCtx(), h);
                getAllSymbolicRecords().add(evBest);
                _symbolicDecisions.getBestNeighbor().put(router, evBest);
            }

            // Best per protocol
            if (!_optimizations.getSliceHasSingleProtocol().contains(router)) {
                for (RoutingProtocol proto : getProtocols().get(router)) {
                    String name = String.format("%s%s_%s_%s_%s", _sliceName, router, proto.protocolName(),
                            "none", "BEST");
                    String historyName = name + "_history";

                    SymbolicEnum<RoutingProtocol> h = new SymbolicEnum<>(this, allProtos,
                            historyName);

                    for (int len = 0; len <= BITS; len++) {
                        SymbolicRecord evBest = new SymbolicRecord(this, name, router, proto,
                                _optimizations, getCtx(), h);
                        getAllSymbolicRecords().add(evBest);
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

            for (RoutingProtocol proto : getProtocols().get(router)) {

                boolean useSingleExport = _optimizations.getSliceCanKeepSingleExportVar().get
                        (router, proto);

                Map<GraphEdge, ArrayList<LogicalEdge>> importGraphEdgeMap = new HashMap<>();
                Map<GraphEdge, ArrayList<LogicalEdge>> exportGraphEdgeMap = new HashMap<>();

                importEnumMap.put(proto, importGraphEdgeMap);
                exportEnumMap.put(proto, exportGraphEdgeMap);

                for (GraphEdge e : edges) {

                    Configuration conf = getGraph().getConfigurations().get(router);

                    if (getGraph().isEdgeUsed(conf, proto, e)) {

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
                                    String name = String.format("%s%s_%s_%s_%s", _sliceName, router, proto
                                            .protocolName(), "", "SINGLE-EXPORT");
                                    ev1 = new SymbolicRecord(this, name, router, proto,
                                            _optimizations, getCtx(), null);
                                    singleProtoMap.put(proto, ev1);
                                    getAllSymbolicRecords().add(ev1);
                                } else {
                                    ev1 = singleVars;
                                }
                                LogicalEdge eExport = new LogicalEdge(e, EdgeType.EXPORT, ev1);
                                exportEdgeList.add(eExport);

                            } else {
                                String name = String.format("%s%s_%s_%s_%s", _sliceName, router, proto
                                        .protocolName(), ifaceName, "EXPORT");

                                SymbolicRecord ev1 = new SymbolicRecord(this, name, router,
                                        proto, _optimizations, getCtx(), null);
                                LogicalEdge eExport = new LogicalEdge(e, EdgeType.EXPORT, ev1);
                                exportEdgeList.add(eExport);
                                getAllSymbolicRecords().add(ev1);
                            }

                            boolean notNeeded = _optimizations.getSliceCanCombineImportExportVars
                                    ().get(router).get(proto).contains(e);

                            if (notNeeded) {
                                String name = String.format("%s%s_%s_%s_%s", _sliceName, router, proto
                                        .protocolName(), ifaceName, "IMPORT");
                                SymbolicRecord ev2 = new SymbolicRecord(name, proto);
                                LogicalEdge eImport = new LogicalEdge(e, EdgeType.IMPORT, ev2);
                                importEdgeList.add(eImport);
                            } else {

                                String name = String.format("%s%s_%s_%s_%s", _sliceName, router, proto
                                        .protocolName(), ifaceName, "IMPORT");
                                SymbolicRecord ev2 = new SymbolicRecord(this, name, router,
                                        proto, _optimizations, getCtx(), null);
                                LogicalEdge eImport = new LogicalEdge(e, EdgeType.IMPORT, ev2);
                                importEdgeList.add(eImport);
                                getAllSymbolicRecords().add(ev2);
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
            for (RoutingProtocol proto : getProtocols().get(router)) {

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

    private void initOptimizations() {
        _optimizations.computeOptimizations();
    }

    private void addEnvironmentVariables() {
        getGraph().getConfigurations().forEach((router, conf) -> {
            for (RoutingProtocol proto : getProtocols().get(router)) {
                if (proto == RoutingProtocol.BGP) {
                    _logicalGraph.getLogicalEdges().get(router, proto).forEach(eList -> {
                        eList.forEach(e -> {
                            if (e.getEdgeType() == EdgeType.IMPORT) {
                                BgpNeighbor n = getGraph().getEbgpNeighbors().get(e.getEdge());
                                if (n != null && e.getEdge().getEnd() == null) {
                                    String address;
                                    if (n.getAddress() == null) {
                                        address = "null";
                                    } else {
                                        address = n.getAddress().toString();
                                    }

                                    String ifaceName = "ENV-" + address;
                                    String name = String.format("%s%s_%s_%s_%s", _sliceName, router, proto
                                            .protocolName(), ifaceName, "EXPORT");
                                    SymbolicRecord vars = new SymbolicRecord(this, name, router,
                                            proto, _optimizations, getCtx(), null);

                                    getAllSymbolicRecords().add(vars);
                                    _logicalGraph.getEnvironmentVars().put(e, vars);
                                }
                            }
                        });
                    });
                }
            }
        });
    }

    private void initVariables() {
        buildEdgeMap();
        addForwardingVariables();
        addBestVariables();
        addSymbolicRecords();
        addChoiceVariables();
        addEnvironmentVariables();
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

        for (SymbolicRecord e : getAllSymbolicRecords()) {
            if (e.getAdminDist() != null) {
                add(Ge(e.getAdminDist(), zero));
                add(Lt(e.getAdminDist(), upperBound8));
            }
            if (e.getMed() != null) {
                add(Ge(e.getMed(), zero));
                add(Lt(e.getMed(), upperBound32));
            }
            if (e.getLocalPref() != null) {
                add(Ge(e.getLocalPref(), zero));
                add(Lt(e.getLocalPref(), upperBound32));
            }
            if (e.getMetric() != null) {
                add(Ge(e.getMetric(), zero));
                if (e.isEnv()) {
                    add(Lt(e.getMetric(), upperBound8));
                }
                add(Lt(e.getMetric(), upperBound16));
            }
            if (e.getPrefixLength() != null) {
                add(Ge(e.getPrefixLength(), zero));
                add(Le(e.getPrefixLength(), Int(32)));
            }
        }
    }

    private void addCommunityConstraints() {
        for (SymbolicRecord r : getAllSymbolicRecords()) {
            r.getCommunities().forEach((cvar, e) -> {
                if (cvar.getType() == CommunityVar.Type.REGEX) {
                    BoolExpr acc = False();
                    List<CommunityVar> deps = _communityDependencies.get(cvar);
                    for (CommunityVar dep : deps) {
                        BoolExpr depExpr = r.getCommunities().get(dep);
                        acc = Or(acc, depExpr);
                    }
                    add(acc);
                }
            });
        }
    }

    public BoolExpr isRelevantFor(ArithExpr prefixLen, PrefixRange range) {
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
            BoolExpr equalLen = Eq(prefixLen, Int(lower));
            return And(equalLen, lowerBitsMatch);
        } else {
            BoolExpr lengthLowerBound = Ge(prefixLen, Int(lower));
            BoolExpr lengthUpperBound = Le(prefixLen, Int(upper));
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
        return getCtx().mkEq(e1, e2);
    }

    public ArithExpr Int(long l) {
        return _encoder.Int(l);
    }

    public BoolExpr And(BoolExpr... vals) {
        return _encoder.And(vals);
    }

    public BoolExpr Ge(Expr e1, Expr e2) {
        return _encoder.Ge(e1, e2);
    }

    public BoolExpr Le(Expr e1, Expr e2) {
        return _encoder.Le(e1, e2);
    }

    public BoolExpr True() {
        return _encoder.True();
    }

    public BoolExpr Lt(Expr e1, Expr e2) {
        return _encoder.Lt(e1, e2);
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

            for (RoutingProtocol proto : getProtocols().get(router)) {

                Set<RoutingProtocol> redistributed = new HashSet<>();
                redistributed.add(proto);

                _logicalGraph.getRedistributedProtocols().put(router, proto, redistributed);

                RoutingPolicy pol = getGraph().findCommonRoutingPolicy(router, proto);
                if (pol != null) {
                    Set<RoutingProtocol> ps = findRedistributedProtocols(conf, pol, proto);
                    for (RoutingProtocol p : ps) {
                        // Make sure there is actually a routing process for the other protocol
                        // For example, it might get sliced away if not relevant
                        boolean isProto = getProtocols().get(router).contains(p);
                        if (isProto) {
                            redistributed.add(p);
                        }
                    }
                }

            }
        });
    }

    public BoolExpr isRelevantFor(Prefix p, ArithExpr ae) {
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

    public ArithExpr Sum(ArithExpr e1, ArithExpr e2) {
        return _encoder.Sum(e1, e2);
    }

    public <T> BoolExpr safeEqEnum(SymbolicEnum<T> x, T value) {
        if (x == null) {
            return True();
        }
        return x.checkIfValue(value);
    }

    public <T> BoolExpr safeEqEnum(SymbolicEnum<T> x, SymbolicEnum<T> y) {
        if (x == null) {
            return True();
        }
        return x.Eq(y);
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

    public BitVecExpr defaultOspfType() {
        // Return intra-area ospf type
        return getCtx().mkBV(0, 2);
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

    private BoolExpr equalHelper(Expr best, Expr vars, Expr defaultVal) {
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

    public BoolExpr equalHistories(RoutingProtocol proto, SymbolicRecord best, SymbolicRecord
            vars) {
        BoolExpr history;
        if (best.getProtocolHistory() == null || vars.getProtocolHistory() == null) {
            history = True();
        } else {
            history = best.getProtocolHistory().Eq(vars.getProtocolHistory());
        }
        return history;
    }

    public BoolExpr equalBgpInternal(RoutingProtocol proto, SymbolicRecord best, SymbolicRecord vars) {
        if (best.getBgpInternal() == null || vars.getBgpInternal() == null) {
            return True();
        } else  {
            return Eq(best.getBgpInternal(), vars.getBgpInternal());
        }
    }

    private BoolExpr equalAreas(SymbolicRecord best, SymbolicRecord vars, LogicalEdge e) {
        BoolExpr equalOspfArea;
        boolean hasBestArea = (best.getOspfArea() != null && best.getOspfArea().getBitVec() !=
                null);
        boolean hasVarsArea = (vars.getOspfArea() != null && vars.getOspfArea().getBitVec() !=
                null);
        if (hasBestArea) {
            Interface iface = e.getEdge().getStart();
            if (hasVarsArea) {
                equalOspfArea = best.getOspfArea().Eq(vars.getOspfArea());
            } else if (iface.getOspfAreaName() != null) {
                equalOspfArea = best.getOspfArea().checkIfValue(iface.getOspfAreaName());
            } else {
                equalOspfArea = best.getOspfArea().isDefaultValue();
            }
        } else {
            equalOspfArea = True();
        }
        return equalOspfArea;
    }

    private BoolExpr equalTypes(SymbolicRecord best, SymbolicRecord vars) {
        BoolExpr equalOspfType;
        boolean hasBestType = (best.getOspfType() != null && best.getOspfType().getBitVec() !=
                null);
        boolean hasVarsType = (vars.getOspfType() != null && vars.getOspfType().getBitVec() !=
                null);
        if (hasVarsType) {
            equalOspfType = best.getOspfType().Eq(vars.getOspfType());
        } else if (hasBestType) {
            equalOspfType = best.getOspfType().isDefaultValue();
        } else {
            equalOspfType = True();
        }
        return equalOspfType;
    }

    private BoolExpr equalIds(SymbolicRecord best, SymbolicRecord vars, Configuration conf,
            RoutingProtocol proto, LogicalEdge e) {
        BoolExpr equalId;
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
        return equalId;
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
        BoolExpr equalOspfArea;
        BoolExpr equalOspfType;
        BoolExpr equalId;
        BoolExpr equalHistory;
        BoolExpr equalBgpInternal;

        equalLen = equalHelper(best.getPrefixLength(), vars.getPrefixLength(), defaultLen);
        equalAd = equalHelper(best.getAdminDist(), vars.getAdminDist(), defaultAdmin);
        equalLp = equalHelper(best.getLocalPref(), vars.getLocalPref(), defaultLocal);
        equalMet = equalHelper(best.getMetric(), vars.getMetric(), defaultMet);
        equalMed = equalHelper(best.getMed(), vars.getMed(), defaultMed);

        equalOspfType = equalTypes(best, vars);
        equalOspfArea = equalAreas(best, vars, e);

        equalId = equalIds(best, vars, conf, proto, e);
        equalHistory = equalHistories(proto, best, vars);
        equalBgpInternal = equalBgpInternal(proto, best, vars);

        return And(equalLen, equalAd, equalLp, equalMet, equalMed, equalOspfArea, equalOspfType,
                equalId, equalHistory, equalBgpInternal);
    }

    private BoolExpr geBetterHelper(
            Expr best, Expr vars, Expr defaultVal, boolean less) {
        BoolExpr fal = False();
        if (vars == null) {
            if (best != null) {
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
            Expr best, Expr vars, Expr defaultVal) {
        if (vars == null) {
            if (best != null) {
                return Eq(best, defaultVal);
            } else {
                return True();
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
        BitVecExpr defaultOspfType = defaultOspfType();


        BoolExpr betterLen = geBetterHelper(best.getPrefixLength(), vars.getPrefixLength(),
                defaultLen, false);
        BoolExpr equalLen = geEqualHelper(best.getPrefixLength(), vars.getPrefixLength(),
                defaultLen);

        BoolExpr betterAd = geBetterHelper(best.getAdminDist(), vars.getAdminDist(),
                defaultAdmin, true);
        BoolExpr equalAd = geEqualHelper(best.getAdminDist(), vars.getAdminDist(), defaultAdmin);

        BoolExpr betterLp = geBetterHelper(best.getLocalPref(), vars.getLocalPref(),
                defaultLocal, false);
        BoolExpr equalLp = geEqualHelper(best.getLocalPref(), vars.getLocalPref(), defaultLocal);

        BoolExpr betterMet = geBetterHelper(best.getMetric(), vars.getMetric(), defaultMet, true);
        BoolExpr equalMet = geEqualHelper(best.getMetric(), vars.getMetric(), defaultMet);

        BoolExpr betterMed = geBetterHelper(best.getMed(), vars.getMed(), defaultMed, true);
        BoolExpr equalMed = geEqualHelper(best.getMed(), vars.getMed(), defaultMed);

        BitVecExpr bestType = (best.getOspfType() == null ? null : best.getOspfType().getBitVec());
        BitVecExpr varsType = (vars.getOspfType() == null ? null : vars.getOspfType().getBitVec());

        BoolExpr betterOspfType = geBetterHelper(bestType, varsType, defaultOspfType, true);
        BoolExpr equalOspfType = geEqualHelper(bestType, varsType, defaultOspfType);

        BoolExpr tiebreak;
        if (isMultipath(conf, proto)) {
            tiebreak = True();
        } else if (vars.getRouterId() != null) {
            tiebreak = Le(best.getRouterId(), vars.getRouterId());
        } else if (best.getRouterId() != null) {
            Long peerId = _logicalGraph.findRouterId(e, proto);
            tiebreak = Le(best.getRouterId(), Int(peerId));
        } else {
            tiebreak = True();
        }

        BoolExpr b = And(equalOspfType, tiebreak);
        BoolExpr b1 = Or(betterOspfType, b);
        BoolExpr b2 = And(equalMed, b1);
        BoolExpr b3 = Or(betterMed, b2);
        BoolExpr b4 = And(equalMet, b3);
        BoolExpr b5 = Or(betterMet, b4);
        BoolExpr b6 = And(equalLp, b5);
        BoolExpr b7 = Or(betterLp, b6);
        BoolExpr b8 = And(equalAd, b7);
        BoolExpr b9 = Or(betterAd, b8);
        BoolExpr b10 = And(equalLen, b9);
        return Or(betterLen, b10);
    }

    private void addBestOverallConstraints() {
        getGraph().getConfigurations().forEach((router, conf) -> {

            // These constraints will be added at the protocol-level when a single protocol
            if (!_optimizations.getSliceHasSingleProtocol().contains(router)) {

                boolean someProto = false;

                BoolExpr acc = null;
                BoolExpr somePermitted = null;
                SymbolicRecord best = _symbolicDecisions.getBestNeighbor().get(router);

                for (RoutingProtocol proto : getProtocols().get(router)) {
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

            for (RoutingProtocol proto : getProtocols().get(router)) {

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
            for (RoutingProtocol proto : getProtocols().get(router)) {
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

            for (RoutingProtocol proto : getProtocols().get(router)) {

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

    private void initAclFunctions() {
        getGraph().getEdgeMap().forEach((router, edges) -> {
            for (GraphEdge ge : edges) {
                Interface i = ge.getStart();

                IpAccessList outbound = i.getOutgoingFilter();
                if (outbound != null) {
                    String outName = router + "_" + i.getName() + "_OUTBOUND_" + outbound.getName();
                    BoolExpr outAcl = getCtx().mkBoolConst(outName);
                    BoolExpr outAclFunc = computeACL(outbound);
                    add(Eq(outAcl, outAclFunc));
                    _outboundAcls.put(i, outAcl);
                }

                IpAccessList inbound = i.getIncomingFilter();
                if (inbound != null) {
                    String inName = router + "_" + i.getName() + "_INBOUND_" + inbound.getName();
                    BoolExpr inAcl = getCtx().mkBoolConst(inName);
                    BoolExpr inAclFunc = computeACL(inbound);
                    add(Eq(inAcl, inAclFunc));
                    _inboundAcls.put(i, inAcl);
                }
            }
        });
    }

    private void initForwardingAcross() {
        _symbolicDecisions.getDataForwarding().forEach((router, edge, var) -> {
            BoolExpr inAcl;
            if (edge.getEnd() == null) {
                inAcl = True();
            } else {
                inAcl =  _inboundAcls.get(edge.getEnd());
                if (inAcl == null) {
                    inAcl = True();
                }
            }
            _forwardsAcross.put(router, edge, And(var, inAcl));
        });
    }

    private void addDataForwardingConstraints() {
        getGraph().getEdgeMap().forEach((router, edges) -> {
            for (GraphEdge ge : edges) {
                BoolExpr acl = _outboundAcls.get(ge.getStart());
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

    private BoolExpr interfaceActive(Interface iface, RoutingProtocol proto) {
        BoolExpr active = Bool(iface.getActive());
        if (proto == RoutingProtocol.OSPF) {
            active = And(active, Bool(iface.getOspfEnabled()));
        }
        return active;
    }

    private void addImportConstraint(
            LogicalEdge e, SymbolicRecord varsOther, Configuration conf, RoutingProtocol proto,
            GraphEdge ge, String router, List<Prefix> originations) {

        SymbolicRecord vars = e.getSymbolicRecord();

        Interface iface = ge.getStart();

        ArithExpr failed = getSymbolicFailures().getFailedVariable(e.getEdge());
        BoolExpr notFailed = Eq(failed, Int(0));

        if (vars.getIsUsed()) {

            if (proto == RoutingProtocol.CONNECTED) {
                Prefix p = iface.getPrefix();
                BoolExpr relevant = And(interfaceActive(iface, proto), isRelevantFor(p,
                        _symbolicPacket.getDstIp()), notFailed);
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
                    BoolExpr relevant = And(interfaceActive(iface, proto), isRelevantFor(p,
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

                    BoolExpr isRoot = relevantOrigination(originations);
                    BoolExpr active = interfaceActive(iface, proto);

                    // Handle iBGP by checking reachability to the next hop to send messages
                    boolean isIbgp = (proto == RoutingProtocol.BGP) && (getGraph().getIbgpNeighbors().containsKey(ge));
                    BoolExpr receiveMessage;
                    if (_encoder.getModelIgp() && isIbgp) {
                        String currentRouter = ge.getRouter();
                        String peerRouter = ge.getPeer();
                        receiveMessage = _encoder.getSliceReachability().get(currentRouter).get(peerRouter);
                    } else {
                        receiveMessage = notFailed;
                    }

                    BoolExpr usable = And(Not(isRoot), active, varsOther.getPermitted(), receiveMessage);

                    BoolExpr importFunction;
                    RoutingPolicy pol = getGraph().findImportRoutingPolicy(router, proto, e);

                    List<Statement> statements;
                    if (pol == null) {
                        Statements.StaticStatement s = new Statements.StaticStatement(Statements
                                .ExitAccept);
                        statements = Collections.singletonList(s);
                    } else {
                        statements = pol.getStatements();
                    }

                    TransferFunction f = new TransferFunction(this, conf, varsOther, vars,
                            proto, proto, statements, 0, ge, false);
                    importFunction = f.compute();

                    // System.out.println("IMPORT FUNCTION: " + router + " " + varsOther.getName());
                    // System.out.println(importFunction);
                    // System.out.println("IMPORT FUNCTION (simpl): " + router + " " + varsOther.getName());
                    // System.out.println(importFunction.simplify());

                    add(If(usable, importFunction, val));

                } else {
                    add(val);
                }

            }
        }
    }

    private boolean addExportConstraint(
            LogicalEdge e, SymbolicRecord varsOther, Configuration conf, RoutingProtocol proto,
            GraphEdge ge, String router, boolean usedExport, List<Prefix> originations) {

        SymbolicRecord vars = e.getSymbolicRecord();

        Interface iface = ge.getStart();

        ArithExpr failed = getSymbolicFailures().getFailedVariable(e.getEdge());
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

                Integer cost = addedCost(proto, iface);

                BoolExpr val = Not(vars.getPermitted());

                BoolExpr active = interfaceActive(iface, proto);

                // Don't re-export routes learned via iBGP
                boolean isIbgp = (proto == RoutingProtocol.BGP) && (getGraph().getIbgpNeighbors().containsKey(ge)) && varsOther.isBest();
                BoolExpr doExport = True();
                if (isIbgp) {
                    doExport = Not(varsOther.getBgpInternal());
                    cost = 0;
                }

                BoolExpr usable = And(active, doExport, varsOther.getPermitted(), notFailed);
                BoolExpr acc;
                RoutingPolicy pol = getGraph().findExportRoutingPolicy(router, proto, e);

                // We have to wrap this with the right thing for some reason
                List<Statement> statements;
                Statements.StaticStatement s1 = new Statements.StaticStatement(Statements
                        .ExitAccept);
                Statements.StaticStatement s2 = new Statements.StaticStatement(Statements
                        .ExitReject);

                if (proto == RoutingProtocol.OSPF) {
                    If i = new If();
                    List<Statement> stmts =
                            (pol == null ? Collections.singletonList(s2) : pol.getStatements());
                    i.setTrueStatements(Collections.singletonList(s1));
                    i.setFalseStatements(stmts);
                    BooleanExpr expr = new MatchProtocol(RoutingProtocol.OSPF);
                    i.setGuard(expr);
                    statements = Collections.singletonList(i);
                } else {
                    statements = (pol == null ? Collections.singletonList(s1) : pol.getStatements());
                }

                TransferFunction f = new TransferFunction(this, conf, varsOther, vars, proto,
                        proto, statements, cost, ge, true);
                acc = f.compute();

                // System.out.println("EXPORT FUNCTION: " + router + " " + varsOther.getName());
                // System.out.println(acc);
                // System.out.println("SIMPLIFIED: " + router + " " + varsOther.getName());
                // System.out.println(acc.simplify());

                acc = If(usable, acc, val);

                for (Prefix p : originations) {
                    BoolExpr relevant = And(interfaceActive(iface, proto), isRelevantFor(p,
                            _symbolicPacket.getDstIp()));
                    int adminDistance = defaultAdminDistance(conf, proto);
                    int prefixLength = p.getPrefixLength();
                    BoolExpr per = vars.getPermitted();
                    BoolExpr lp = safeEq(vars.getLocalPref(), Int(0));
                    BoolExpr ad = safeEq(vars.getAdminDist(), Int(adminDistance));
                    BoolExpr met = safeEq(vars.getMetric(), Int(cost));
                    BoolExpr med = safeEq(vars.getMed(), Int(100));
                    BoolExpr len = safeEq(vars.getPrefixLength(), Int(prefixLength));
                    BoolExpr type = safeEqEnum(vars.getOspfType(), OspfType.O);
                    BoolExpr area = safeEqEnum(vars.getOspfArea(), iface.getOspfAreaName());
                    // TODO: is this right?
                    BoolExpr internal = safeEq(vars.getBgpInternal(), False());
                    BoolExpr values = And(per, lp, ad, met, med, len, type, area, internal);
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
            for (RoutingProtocol proto : getProtocols().get(router)) {
                Boolean usedExport = false;
                List<Prefix> originations = getOriginatedNetworks(conf, proto);
                for (ArrayList<LogicalEdge> eList : _logicalGraph.getLogicalEdges().get(router,
                        proto)) {
                    for (LogicalEdge e : eList) {
                        GraphEdge ge = e.getEdge();

                        if (getGraph().isEdgeUsed(conf, proto, ge)) {
                            SymbolicRecord varsOther;
                            switch (e.getEdgeType()) {
                                case IMPORT:
                                    varsOther = _logicalGraph.findOtherVars(e);
                                    addImportConstraint(e, varsOther, conf, proto, ge, router,
                                            originations);
                                    break;

                                case EXPORT:
                                    varsOther = _symbolicDecisions.getBestNeighbor().get(router);
                                    usedExport = addExportConstraint(e, varsOther, conf, proto,
                                            ge, router, usedExport, originations);
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
            add(Implies(vars.getPermitted(), vars.getProtocolHistory().checkIfValue(proto)));
        });

        _symbolicDecisions.getBestNeighbor().forEach((router, vars) -> {
            if (_optimizations.getSliceHasSingleProtocol().contains(router)) {
                RoutingProtocol proto = getProtocols().get(router).get(0);
                add(Implies(vars.getPermitted(), vars.getProtocolHistory().checkIfValue(proto)));
            }
        });
    }

    private void addUnusedDefaultValueConstraints() {
        for (SymbolicRecord vars : getAllSymbolicRecords()) {

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
            if (vars.getOspfArea() != null) {
                add(Implies(notPermitted, vars.getOspfArea().isDefaultValue()));
            }
            if (vars.getOspfType() != null) {
                add(Implies(notPermitted, vars.getOspfType().isDefaultValue()));
            }
            if (vars.getProtocolHistory() != null) {
                add(Implies(notPermitted, vars.getProtocolHistory().isDefaultValue()));
            }
            if (vars.getBgpInternal() != null) {
                add(Implies(notPermitted, Not(vars.getBgpInternal())));
            }
            vars.getCommunities().forEach((cvar, e) -> {
                add(Implies(notPermitted, Not(e)));
            });
        }
    }

    private void addInactiveLinkConstraints() {
        _logicalGraph.getLogicalEdges().forEach((router, proto, edges) -> {
            for (ArrayList<LogicalEdge> es : edges) {
                for (LogicalEdge e : es) {
                    Interface iface = e.getEdge().getStart();
                    if (!getGraph().isInterfaceActive(proto, iface)) {
                        BoolExpr per = e.getSymbolicRecord().getPermitted();
                        if (per != null) {
                            add(Not(per));
                        }
                    }
                }
            }
        });
    }

    private BoolExpr boundConstraint(ArithExpr e, long lower, long upper) {
        if (lower > upper) {
            throw new BatfishException("Invalid range: " + lower + "-" + upper);
        } else if (lower == upper) {
            return Eq(e, Int(lower));
        } else {
            BoolExpr x = Ge(e, Int(lower));
            BoolExpr y = Le(e, Int(upper));
            return And(x, y);
        }
    }

    private BoolExpr boundConstraint(ArithExpr e, Prefix p) {
        Prefix n = p.getNetworkPrefix();
        long lower = n.getAddress().asLong();
        long upper = n.getEndAddress().asLong();
        return boundConstraint(e, lower, upper);
    }

    private BoolExpr ipWildCardBound(ArithExpr e, IpWildcard ipWildcard) {
        if (!ipWildcard.isPrefix()) {
            throw new BatfishException("Unsupported IP wildcard: " + ipWildcard);
        }
        Prefix p = ipWildcard.toPrefix().getNetworkPrefix();
        return boundConstraint(e, p);
    }

    private BoolExpr subRangeBound(ArithExpr e, SubRange r) {
        long lower = r.getStart();
        long upper = r.getEnd();
        return boundConstraint(e, lower, upper);
    }


    private void addHeaderSpaceConstraint() {

        BoolExpr acc;

        if (_headerSpace.getDstIps().size() > 0) {
            acc = False();
            for (IpWildcard ipWildcard : _headerSpace.getDstIps()) {
                BoolExpr bound = ipWildCardBound(_symbolicPacket.getDstIp(), ipWildcard);
                acc = Or(acc, bound);
            }
            add(acc);
        }

        if (_headerSpace.getNotDstIps().size() > 0) {
            acc = True();
            for (IpWildcard ipWildcard : _headerSpace.getNotDstIps()) {
                BoolExpr bound = ipWildCardBound(_symbolicPacket.getDstIp(), ipWildcard);
                acc = And(acc, Not(bound));
            }
            add(acc);
        }

        if (_headerSpace.getSrcIps().size() > 0) {
            acc = False();
            for (IpWildcard ipWildcard : _headerSpace.getSrcIps()) {
                BoolExpr bound = ipWildCardBound(_symbolicPacket.getSrcIp(), ipWildcard);
                acc = Or(acc, bound);
            }
            add(acc);
        }

        if (_headerSpace.getNotSrcIps().size() > 0) {
            acc = True();
            for (IpWildcard ipWildcard : _headerSpace.getNotSrcIps()) {
                BoolExpr bound = ipWildCardBound(_symbolicPacket.getSrcIp(), ipWildcard);
                acc = And(acc, Not(bound));
            }
            add(acc);
        }

        if (_headerSpace.getSrcOrDstIps().size() > 0) {
            acc = False();
            for (IpWildcard ipWildcard : _headerSpace.getSrcOrDstIps()) {
                BoolExpr bound1 = ipWildCardBound(_symbolicPacket.getDstIp(), ipWildcard);
                BoolExpr bound2 = ipWildCardBound(_symbolicPacket.getSrcIp(), ipWildcard);
                acc = Or(acc, bound1, bound2);
            }
            add(acc);
        }

        if (_headerSpace.getDstPorts().size() > 0) {
            acc = False();
            for (SubRange subRange : _headerSpace.getDstPorts()) {
                BoolExpr bound = subRangeBound(_symbolicPacket.getDstPort(), subRange);
                acc = Or(acc, bound);
            }
            add(acc);
        }

        if (_headerSpace.getNotDstPorts().size() > 0) {
            acc = True();
            for (SubRange subRange : _headerSpace.getNotDstPorts()) {
                BoolExpr bound = subRangeBound(_symbolicPacket.getDstPort(), subRange);
                acc = And(acc, Not(bound));
            }
            add(acc);
        }

        if (_headerSpace.getDstPorts().size() > 0) {
            acc = False();
            for (SubRange subRange : _headerSpace.getSrcPorts()) {
                BoolExpr bound = subRangeBound(_symbolicPacket.getDstPort(), subRange);
                acc = Or(acc, bound);
            }
            add(acc);
        }

        if (_headerSpace.getNotSrcPorts().size() > 0) {
            acc = True();
            for (SubRange subRange : _headerSpace.getNotSrcPorts()) {
                BoolExpr bound = subRangeBound(_symbolicPacket.getDstPort(), subRange);
                acc = And(acc, Not(bound));
            }
            add(acc);
        }

        if (_headerSpace.getSrcOrDstPorts().size() > 0) {
            acc = False();
            for (SubRange subRange : _headerSpace.getSrcOrDstPorts()) {
                BoolExpr bound1 = subRangeBound(_symbolicPacket.getDstPort(), subRange);
                BoolExpr bound2 = subRangeBound(_symbolicPacket.getSrcPort(), subRange);
                acc = Or(acc, bound1, bound2);
            }
            add(acc);
        }

        if (_headerSpace.getIcmpTypes().size() > 0) {
            acc = False();
            for (SubRange subRange : _headerSpace.getIcmpTypes()) {
                BoolExpr bound = subRangeBound(_symbolicPacket.getIcmpType(), subRange);
                acc = Or(acc, bound);
            }
            add(acc);
        }

        if (_headerSpace.getNotIcmpTypes().size() > 0) {
            acc = True();
            for (SubRange subRange : _headerSpace.getNotIcmpTypes()) {
                BoolExpr bound = subRangeBound(_symbolicPacket.getIcmpType(), subRange);
                acc = And(acc, Not(bound));
            }
            add(acc);
        }

        if (_headerSpace.getIcmpCodes().size() > 0) {
            acc = False();
            for (SubRange subRange : _headerSpace.getIcmpCodes()) {
                BoolExpr bound = subRangeBound(_symbolicPacket.getIcmpCode(), subRange);
                acc = Or(acc, bound);
            }
            add(acc);
        }

        if (_headerSpace.getNotIcmpCodes().size() > 0) {
            acc = True();
            for (SubRange subRange : _headerSpace.getNotIcmpCodes()) {
                BoolExpr bound = subRangeBound(_symbolicPacket.getIcmpCode(), subRange);
                acc = And(acc, Not(bound));
            }
            add(acc);
        }

        if (_headerSpace.getIpProtocols().size() > 0) {
            acc = False();
            for (IpProtocol ipProtocol : _headerSpace.getIpProtocols()) {
                BoolExpr bound = Eq(_symbolicPacket.getIpProtocol(), Int(ipProtocol.number()));
                acc = Or(acc, bound);
            }
            add(acc);
        }

        if (_headerSpace.getNotIpProtocols().size() > 0) {
            acc = True();
            for (IpProtocol ipProtocol : _headerSpace.getNotIpProtocols()) {
                BoolExpr bound = Eq(_symbolicPacket.getIpProtocol(), Int(ipProtocol.number()));
                acc = And(acc, Not(bound));
            }
            add(acc);
        }

        // TODO: need to implement fragment offsets, Ecns, states, etc
    }

    private void addFoo() {
        // System.out.println("ADDING FOO");
        getLogicalGraph().getEnvironmentVars().forEach((le, vars) -> {
            add(vars.getPermitted());
        });

        /* getLogicalGraph().getLogicalEdges().forEach((router, proto, es) -> {
            for (ArrayList<LogicalEdge> e : es) {
                for (LogicalEdge le : e) {
                    System.out.println("  LOGICAL EDGE: " + le.getSymbolicRecord().getName());
                    if (le.getSymbolicRecord().isEnv()) {
                        System.out.println("ADDING  !!!!!!!!!!!!!!!!!!!");
                        add(le.getSymbolicRecord().getPermitted());
                    }
                }
            }
        }); */
    }

    public void computeEncoding() {
        addBoundConstraints();
        addCommunityConstraints();
        addTransferFunction();
        addHistoryConstraints();
        addBestPerProtocolConstraints();
        addChoicePerProtocolConstraints();
        addBestOverallConstraints();
        addControlForwardingConstraints();
        addDataForwardingConstraints();
        addUnusedDefaultValueConstraints();
        addInactiveLinkConstraints();
        addHeaderSpaceConstraint();
        // addFoo();
    }
}