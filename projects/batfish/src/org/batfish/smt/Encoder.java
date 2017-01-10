package org.batfish.smt;

import com.microsoft.z3.*;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.*;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.*;
import org.batfish.datamodel.routing_policy.statement.If;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.datamodel.routing_policy.statement.Statements;

import java.util.*;
import java.util.function.Consumer;

import static org.batfish.datamodel.routing_policy.statement.Statements.ExitAccept;
import static org.batfish.datamodel.routing_policy.statement.Statements.ExitReject;

// Features:
// ---------
//   - Enable route redistribution
//   - BGP import and export filters (might need destination / mask)
//   - BGP community values (ignore regex for now)
//   - Avoid loops in BGP when non-standard (or non-common) local-pref internally
//   - iBGP by comparing local-pref internally
//     * Requires reachability, and no ACLs for loopbacks
//   - maximum path length by protocol
//   - RIP routing protocol
//
// Small items:
// ------------
//   - Compute multipath correctly (how do we handle some multipath)
//   - Most optimizations are hard-coded at the moment
//   - Can we use the length variable when we filter later on, say, communities
//     Alternatively, can we use length when we only filter for length at the border?
//
// Optimizations:
// --------------


/**
 * Class to encode the network as an SMT formula for a particular
 * destination IP address
 *
 */
public class Encoder {

    class Optimizations {
        private static final boolean ENABLE_IMPORT_EXPORT_MERGE_OPTIMIZATION = true;
        private static final boolean ENABLE_EXPORT_MERGE_OPTIMIZATION = true;
        private static final boolean ENABLE_SLICING_OPTIMIZATION = true;

        private boolean _hasEnvironment;
        private Set<String> _sliceCanDiscardStatic;
        private Set<String> _sliceCanDiscardConnected;
        private Set<String> _sliceHasSingleProtocol;
        private Map<String, EnumMap<RoutingProtocol, Boolean>> _sliceCanKeepSingleExportVar;
        private Map<String, EnumMap<RoutingProtocol, List<GraphEdge>>> _sliceCanCombineImportExportVars;
        private Map<String, EnumMap<RoutingProtocol, Boolean>> _needRouterIdProto;
        private Set<String> _needRouterId;

        private boolean _keepHopCount;
        private boolean _keepLocalPref;
        private boolean _keepAdminDist;
        private boolean _keepDataForwarding;

        private Optimizations() {
            _hasEnvironment = false;
            _sliceCanDiscardConnected = new HashSet<>();
            _sliceCanDiscardStatic = new HashSet<>();
            _sliceHasSingleProtocol = new HashSet<>();
            _sliceCanCombineImportExportVars = new HashMap<>();
            _sliceCanKeepSingleExportVar = new HashMap<>();
            _needRouterIdProto = new HashMap<>();
            _needRouterId = new HashSet<>();
            _keepHopCount = true;
            _keepLocalPref = true;
            _keepAdminDist = true;
            _keepDataForwarding = true;
        }

        private boolean needToModelStatic(Configuration conf) {
            if (Optimizations.ENABLE_SLICING_OPTIMIZATION) {
                boolean ret = false;
                for (StaticRoute sr : conf.getStaticRoutes()) {
                    Ip dest = new Ip(_destination);
                    if (sr.getNetwork() != null && sr.getNetwork().contains( dest )) {
                        ret = true;
                    }
                }
                if (!ret) {
                    _sliceCanDiscardStatic.add(conf.getName());
                }
                return ret;
            } else {
                return conf.getStaticRoutes().size() > 0;
            }
        }

        private boolean needToModelConnected(Configuration conf) {
            if (Optimizations.ENABLE_SLICING_OPTIMIZATION) {
                boolean ret = false;
                for (Map.Entry<String, Interface> e : conf.getInterfaces().entrySet()) {
                    Interface iface = e.getValue();
                    if (iface.getPrefix() != null) {
                        Prefix p = iface.getPrefix();
                        if (p.contains(new Ip(_destination))) {
                            ret = true;
                        }
                    }
                }
                if (!ret) {
                    _sliceCanDiscardConnected.add(conf.getName());
                }
                return ret;
            } else {
                return true;
            }
        }

        private void initProtocols(Map<String,Configuration> configs) {
            configs.forEach((router, conf) -> {
                _protocols.put(router, new ArrayList<>());
            });
            configs.forEach((router, conf) -> {
                List<RoutingProtocol> protos = _protocols.get(router);
                if (conf.getOspfProcess() != null) {
                    protos.add(RoutingProtocol.OSPF);
                }
                if (conf.getBgpProcess() != null) {
                    protos.add(RoutingProtocol.BGP);
                }
                if (needToModelConnected(conf)) {
                    protos.add(RoutingProtocol.CONNECTED);
                }
                if (needToModelStatic(conf)) {
                    protos.add(RoutingProtocol.STATIC);
                }
            });
        }

        // Check if we need the routerID for each router/protocol pair
        private void computeRouterIdNeeded() {
            _graph.getConfigurations().forEach((router, conf) -> {
                EnumMap<RoutingProtocol, Boolean> map = new EnumMap<>(RoutingProtocol.class);
                _needRouterIdProto.put(router, map);
                for(RoutingProtocol proto : _protocols.get(router)) {
                    if (isMultipath(conf,proto)) {
                        map.put(proto, false);
                    } else {
                        map.put(proto, true);
                        _needRouterId.add(router);
                    }

                }
            });
        }

        // Check if we can avoid keeping both a best and overall best copy?
        private void computeCanUseSingleBest() {
            _graph.getConfigurations().forEach((router, conf) -> {
                if (_protocols.get(router).size() == 1)  {
                    _sliceHasSingleProtocol.add(router);
                }
            });
        }

        // Merge export variables into a single copy when no peer-specific export
        private void computeCanMergeExportVars() {
            _graph.getConfigurations().forEach((router,conf) -> {
                EnumMap<RoutingProtocol, Boolean> map = new EnumMap<>(RoutingProtocol.class);
                _sliceCanKeepSingleExportVar.put(router, map);
                // TODO: actually compute this
                for (RoutingProtocol p : _protocols.get(router)) {
                    map.put(p, Optimizations.ENABLE_EXPORT_MERGE_OPTIMIZATION);
                }
            });
        }

        // Merge import and export variables when there is no peer-specific import
        private void computeCanMergeImportExportVars() {
            _graph.getConfigurations().forEach((router,conf) -> {
                EnumMap<RoutingProtocol, List<GraphEdge>> map = new EnumMap<>(RoutingProtocol.class);
                _sliceCanCombineImportExportVars.put(router, map);
                for (RoutingProtocol p : _protocols.get(router)) {
                    // TODO: actually compute this
                    List<GraphEdge> edges = new ArrayList<>();
                    if (Optimizations.ENABLE_IMPORT_EXPORT_MERGE_OPTIMIZATION) {
                        if (p != RoutingProtocol.CONNECTED && p != RoutingProtocol.STATIC) {
                            for (GraphEdge e : _graph.getEdgeMap().get(router)) {
                                // Don't keep import variables if no import-specific policy
                                // or if the protocol does not require it
                                // TODO actually check if neighbor is in protocol
                                if (e.getEnd() != null) {
                                    edges.add(e);
                                }
                            }
                        }
                    }
                    map.put(p, edges);
                }
            });
        }

        private void computeOptimizations() {
            // TODO: compute these
            _keepLocalPref = false;
            _keepHopCount = false;
            _keepAdminDist = true;
            _keepDataForwarding = true;
            initProtocols(_graph.getConfigurations());

            // TODO: get the actual value here
            _hasEnvironment = false;

            computeRouterIdNeeded();
            computeCanUseSingleBest();
            computeCanMergeExportVars();
            computeCanMergeImportExportVars();
        }

        Set<String> getNeedRouterId() {
            return _needRouterId;
        }

        Map<String, EnumMap<RoutingProtocol, Boolean>> getNeedRouterIdProto() {
            return _needRouterIdProto;
        }

        Map<String, EnumMap<RoutingProtocol, Boolean>> getSliceCanKeepSingleExportVar() {
            return _sliceCanKeepSingleExportVar;
        }

        Map<String, EnumMap<RoutingProtocol, List<GraphEdge>>> getSliceCanCombineImportExportVars() {
            return _sliceCanCombineImportExportVars;
        }

        boolean getKeepHopCount() {
            return _keepHopCount;
        }

        boolean getKeepLocalPref() {
            return _keepLocalPref;
        }

        boolean getKeepAdminDist() {
            return _keepAdminDist;
        }

        boolean getKeepDataForwarding() {
            return _keepDataForwarding;
        }
    }


    private static final int BITS = 0;

    private static final int DEFAULT_CISCO_VLAN_OSPF_COST = 1;
    private static final String BGP_NETWORK_FILTER_LIST_NAME = "~BGP_NETWORK_NETWORKS_FILTER~";

    private Graph _graph;

    private Map<String, List<RoutingProtocol>> _protocols;
    private Map<String, EnumMap<RoutingProtocol, EnumMap<RoutingProtocol, LogicalRedistributionEdge>>> _redistributionEdges;
    private Map<String, EnumMap<RoutingProtocol, List<ArrayList<LogicalGraphEdge>>>> _edgeVariableMap;
    private Map<String, EnumMap<RoutingProtocol, EdgeVars>> _bestNeighborPerProtocol;
    private Map<String, EdgeVars>  _bestNeighbor;

    private Map<String, EnumMap<RoutingProtocol, Map<LogicalEdge, BoolExpr>>> _choiceVariables;
    private Map<String, Map<GraphEdge, BoolExpr>> _controlForwarding;
    private Map<String, Map<GraphEdge, BoolExpr>> _dataForwarding;
    private Map<LogicalGraphEdge,LogicalGraphEdge> _otherEnd;

    private List<Expr> _allVariables;
    private List<EdgeVars> _allEdgeVars;

    private Optimizations _optimizations;

    private Context _ctx;
    private Solver _solver;
    private String _destination;
    private BitVecExpr _destinationVar;


    public Encoder(IBatfish batfish, String destination) {
        _ctx = new Context();

        _destination = destination;
        _destinationVar = _ctx.mkBVConst("destination", 32);

        Tactic t1 = _ctx.mkTactic("simplify");
        Tactic t2 = _ctx.mkTactic("solve-eqs");
        Tactic t4 = _ctx.mkTactic("smt");
        Tactic t = _ctx.then(t1, t2, t4);
        _solver = _ctx.mkSolver(t);

        _graph = new Graph(batfish);
        _protocols = new HashMap<>();
        _bestNeighbor = new HashMap<>();
        _bestNeighborPerProtocol = new HashMap<>();

        _optimizations = new Optimizations();

        _choiceVariables = new HashMap<>();
        _controlForwarding = new HashMap<>();
        _dataForwarding = new HashMap<>();

        _redistributionEdges = new HashMap<>();
        _edgeVariableMap = new HashMap<>();
        _otherEnd = new HashMap<>();

        _allEdgeVars = new ArrayList<>();
        _allVariables = new ArrayList<>();
        _allVariables.add(_destinationVar);
    }


    private void addExprs(EdgeVars e) {
        _allVariables.add(e.getPermitted());

        if (e.getAdminDist() != null) {
            _allVariables.add(e.getAdminDist());
        }
        if (e.getHopCount() != null) {
            _allVariables.add(e.getHopCount());
        }
        if (e.getLocalPref() != null) {
            _allVariables.add(e.getLocalPref());
        }
        if (e.getMetric() != null) {
            _allVariables.add(e.getMetric());
        }
        if (e.getPrefixLength() != null) {
            _allVariables.add(e.getPrefixLength());
        }
    }


    private void addChoiceVariables() {
        // add choice variables
        _graph.getEdgeMap().forEach((router,edges) -> {

            EnumMap<RoutingProtocol, Map<LogicalEdge, BoolExpr>> map = new EnumMap<>(RoutingProtocol.class);
            _choiceVariables.put(router, map);

            for (RoutingProtocol proto : _protocols.get(router)) {

                Map<LogicalEdge, BoolExpr> edgeMap = new HashMap<>();
                map.put(proto, edgeMap);

                for (LogicalEdge e : collectAllImportLogicalEdges(router, proto)) {

                    // TODO: check if edge is actually in protocol

                    String ifaceName;
                    if (e instanceof LogicalGraphEdge) {
                        LogicalGraphEdge lge = (LogicalGraphEdge) e;
                        ifaceName = lge.getEdge().getStart().getName();
                    } else {
                        LogicalRedistributionEdge lre = (LogicalRedistributionEdge) e;
                        ifaceName = "redistribute-" + lre.getFrom().protocolName();
                    }

                    String chName = "choice_" + router + "_" + proto.protocolName() + "_" + ifaceName;

                    System.out.println("ADDING: " + chName + ", " + e);

                    BoolExpr choiceVar = _ctx.mkBoolConst(chName);
                    _allVariables.add(choiceVar);
                    edgeMap.put(e, choiceVar);

                }
            }
        });
    }

    private void addForwardingVariables() {
        // add control plane, data plane
        _graph.getEdgeMap().forEach((router,edges) -> {

            EnumMap<RoutingProtocol, List<ArrayList<LogicalGraphEdge>>> map = new EnumMap<>(RoutingProtocol.class);
            for (RoutingProtocol p : _protocols.get(router)) {
                map.put(p, new ArrayList<>());
            }
            _edgeVariableMap.put(router, map);

            Map<GraphEdge, BoolExpr> cForwarding = new HashMap<>();
            Map<GraphEdge, BoolExpr> dForwarding = new HashMap<>();
            for (GraphEdge edge : edges) {
                String iface = edge.getStart().getName();
                String cName = "control_forwarding_" + router + "_" + iface;
                BoolExpr cForward = _ctx.mkBoolConst(cName);
                _allVariables.add(cForward);
                cForwarding.put(edge, cForward);

                if (_optimizations.getKeepDataForwarding()) {
                    String dName = "data_forwarding_" + router + "_" + iface;
                    BoolExpr dForward = _ctx.mkBoolConst(dName);
                    _allVariables.add(dForward);
                    dForwarding.put(edge, dForward);
                }
            }
            _controlForwarding.put(router, cForwarding);

            if (_optimizations.getKeepDataForwarding()) {
                _dataForwarding.put(router, dForwarding);
            }
        });
    }

    private void addBestVariables() {
        // add best neighbor variables
        _graph.getEdgeMap().forEach((router,edges) -> {
            for (int len = 0; len <= BITS; len++) {
                EdgeVars evBest = new EdgeVars(router, RoutingProtocol.AGGREGATE, "OVERALL", _optimizations, "none", _ctx, len, "BEST", true);
                addExprs(evBest);
                _allEdgeVars.add(evBest);
                // TODO: make 32 of these
                _bestNeighbor.put(router, evBest);
            }
        });

        // add best neighbor per protocol variables
        _graph.getEdgeMap().forEach((router,edges) -> {
            EnumMap<RoutingProtocol, EdgeVars> map = new EnumMap<>(RoutingProtocol.class);
            if (!_optimizations._sliceHasSingleProtocol.contains(router)) {
                for (RoutingProtocol proto : _protocols.get(router)) {
                    for (int len = 0; len <= BITS; len++) {
                        EdgeVars evBest = new EdgeVars(router, proto, proto.protocolName(), _optimizations, "none", _ctx, len, "BEST", true);
                        addExprs(evBest);
                        _allEdgeVars.add(evBest);
                        // TODO: make 32 of these
                        map.put(proto, evBest);
                    }
                }
            }
            _bestNeighborPerProtocol.put(router, map);
        });
    }

    private void addEdgeVariables() {
        Map<String, EnumMap<RoutingProtocol, Map<GraphEdge, ArrayList<LogicalGraphEdge>>>> importInverseMap = new HashMap<>();
        Map<String, EnumMap<RoutingProtocol, Map<GraphEdge, ArrayList<LogicalGraphEdge>>>> exportInverseMap = new HashMap<>();
        Map<String, EnumMap<RoutingProtocol, EdgeVars>> singleExportMap = new HashMap<>();

        // add edge EXPORT and IMPORT state variables
        _graph.getEdgeMap().forEach((router,edges) -> {

            EnumMap<RoutingProtocol, EdgeVars> singleProtoMap = new EnumMap<>(RoutingProtocol.class);
            EnumMap<RoutingProtocol, Map<GraphEdge, ArrayList<LogicalGraphEdge>>> importEnumMap = new EnumMap<>(RoutingProtocol.class);
            EnumMap<RoutingProtocol, Map<GraphEdge, ArrayList<LogicalGraphEdge>>> exportEnumMap = new EnumMap<>(RoutingProtocol.class);

            singleExportMap.put(router, singleProtoMap);
            importInverseMap.put(router, importEnumMap);
            exportInverseMap.put(router, exportEnumMap);

            // TODO: protocol should be on a per-router basis
            for (RoutingProtocol proto : _protocols.get(router)) {

                boolean useSingleExport = _optimizations.getSliceCanKeepSingleExportVar().get(router).get(proto);

                Map<GraphEdge, ArrayList<LogicalGraphEdge>> importGraphEdgeMap = new HashMap<>();
                Map<GraphEdge, ArrayList<LogicalGraphEdge>> exportGraphEdgeMap = new HashMap<>();

                importEnumMap.put(proto, importGraphEdgeMap);
                exportEnumMap.put(proto, exportGraphEdgeMap);

                for (GraphEdge e : edges) {

                    Interface iface = e.getStart();
                    Configuration conf = _graph.getConfigurations().get(router);

                    if (isInterfaceUsed(conf, proto, iface)) {

                        ArrayList<LogicalGraphEdge> importEdgeList = new ArrayList<>();
                        ArrayList<LogicalGraphEdge> exportEdgeList = new ArrayList<>();
                        importGraphEdgeMap.put(e, importEdgeList);
                        exportGraphEdgeMap.put(e, exportEdgeList);

                        for (int len = 0; len <= BITS; len++) {

                            String ifaceName = e.getStart().getName();

                            // If we use a single set of export variables, then make sure
                            // to reuse the existing variables instead of creating new ones
                            if (useSingleExport) {
                                EdgeVars singleVars = singleExportMap.get(router).get(proto);
                                EdgeVars ev1;
                                if (singleVars == null) {
                                    String name = proto.protocolName();
                                    ev1 = new EdgeVars(router, proto, name, _optimizations, "", _ctx, len, "SINGLE-EXPORT", false);
                                    singleProtoMap.put(proto, ev1);
                                    addExprs(ev1);
                                    _allEdgeVars.add(ev1);
                                } else {
                                    ev1 = singleVars;
                                }
                                LogicalGraphEdge eExport = new LogicalGraphEdge(e, EdgeType.EXPORT, len, ev1);
                                exportEdgeList.add(eExport);

                            } else {
                                String name = proto.protocolName();
                                EdgeVars ev1 = new EdgeVars(router, proto, name, _optimizations, ifaceName, _ctx, len, "EXPORT", false);
                                LogicalGraphEdge eExport = new LogicalGraphEdge(e, EdgeType.EXPORT, len, ev1);
                                exportEdgeList.add(eExport);
                                addExprs(ev1);
                                _allEdgeVars.add(ev1);
                            }

                            boolean notNeeded = _optimizations.getSliceCanCombineImportExportVars().get(router).get(proto).contains(e);

                            if (notNeeded) {
                                EdgeVars ev2 = new EdgeVars();
                                LogicalGraphEdge eImport = new LogicalGraphEdge(e, EdgeType.IMPORT, len, ev2);
                                importEdgeList.add(eImport);
                            } else {
                                String name = proto.protocolName();
                                EdgeVars ev2 = new EdgeVars(router, proto, name, _optimizations, ifaceName, _ctx, len, "IMPORT", false);
                                LogicalGraphEdge eImport = new LogicalGraphEdge(e, EdgeType.IMPORT, len, ev2);
                                importEdgeList.add(eImport);
                                addExprs(ev2);
                                _allEdgeVars.add(ev2);
                            }
                        }

                        List<ArrayList<LogicalGraphEdge>> es = _edgeVariableMap.get(router).get(proto);
                        ArrayList<LogicalGraphEdge> allEdges = new ArrayList<>();
                        allEdges.addAll(importEdgeList);
                        allEdges.addAll(exportEdgeList);
                        es.add(allEdges);
                    }
                }

            }
        });

        // Build a map to find the opposite of a given edge
        _edgeVariableMap.forEach((router, edgeLists) -> {
            for (RoutingProtocol proto : _protocols.get(router)) {

                for (ArrayList<LogicalGraphEdge> edgeList : edgeLists.get(proto)) {

                    for (int i = 0; i < edgeList.size(); i++) {

                        LogicalGraphEdge e = edgeList.get(i);

                        GraphEdge edge = e.getEdge();
                        Map<GraphEdge, ArrayList<LogicalGraphEdge>> m;

                        if (edge.getPeer() != null) {

                            if (e.getEdgeType() == EdgeType.IMPORT) {
                                m = exportInverseMap.get(edge.getPeer()).get(proto);

                            } else {
                                m = importInverseMap.get(edge.getPeer()).get(proto);
                            }

                            if (m != null) {
                                GraphEdge otherEdge = _graph.getOtherEnd().get(edge);
                                LogicalGraphEdge other = m.get(otherEdge).get(i / 2);
                                _otherEnd.put(e, other);
                            }

                        }

                    }
                }
            }
        });
    }

    private void visit(BooleanExpr e, Consumer<Statement> fs, Consumer<BooleanExpr> fe) {
        fe.accept(e);
        if (e instanceof Conjunction) {
            Conjunction c = (Conjunction) e;
            for (BooleanExpr be : c.getConjuncts()) {
                visit(be, fs, fe);
            }
        } else if (e instanceof Disjunction) {
            Disjunction d = (Disjunction) e;
            for (BooleanExpr be : d.getDisjuncts()) {
                visit(be, fs, fe);
            }
        }
    }

    private void visit(Statement s, Consumer<Statement> fs, Consumer<BooleanExpr> fe) {
        fs.accept(s);
        if (s instanceof If) {
            If i = (If) s;
            visit(i.getGuard(), fs, fe);
            visit(i.getTrueStatements(), fs, fe);
            visit(i.getFalseStatements(), fs, fe);
        }
    }

    private void visit(List<Statement> ss, Consumer<Statement> fs, Consumer<BooleanExpr> fe) {
        for (Statement s : ss) {
            visit(s,fs,fe);
        }
    }

    private List<RoutingProtocol> findRedistributedProtocols(RoutingPolicy pol) {
        List<RoutingProtocol> ps = new ArrayList<>();
        visit(pol.getStatements(), s -> {}, e -> {
            if (e instanceof MatchProtocol) {
                MatchProtocol mp = (MatchProtocol) e;
                ps.add(mp.getProtocol());
            }
        });
        return ps;
    }

    private RoutingPolicy findRoutingPolicy(Configuration conf, RoutingProtocol proto) {
        if (proto == RoutingProtocol.OSPF) {
            String exp = conf.getOspfProcess().getExportPolicy();
            return conf.getRoutingPolicies().get(exp);

        } else if (proto == RoutingProtocol.STATIC) {
            return null;
        } else if (proto == RoutingProtocol.CONNECTED) {
            return null;
        } else {
            throw new BatfishException("TODO: findRoutingPolicy for " + proto.protocolName());
        }
    }

    private boolean needToKeepRedistribution(String router, RoutingProtocol p) {
        return _bestNeighborPerProtocol.get(router).get(p) != null;
    }

    private void addRedistributionEdgeVariables() {
        _graph.getConfigurations().forEach((router,conf) -> {
            EnumMap<RoutingProtocol, EnumMap<RoutingProtocol, LogicalRedistributionEdge>> map1 = new EnumMap<>(RoutingProtocol.class);
            _redistributionEdges.put(router, map1);
            for (RoutingProtocol proto : _protocols.get(router)) {
                EnumMap<RoutingProtocol, LogicalRedistributionEdge> map2 = new EnumMap<>(RoutingProtocol.class);
                map1.put(proto, map2);
                RoutingPolicy pol = findRoutingPolicy(conf, proto);
                if (pol != null) {
                    List<RoutingProtocol> ps = findRedistributedProtocols(pol);
                    for (RoutingProtocol p : ps) {
                        if (needToKeepRedistribution(router, p)) {
                            String name = "REDIST_FROM_" + p.protocolName().toUpperCase();
                            String ifaceName = "none";
                            int len = 0;
                            EdgeVars e = new EdgeVars(router, proto, proto.protocolName(), _optimizations, ifaceName, _ctx, len, name, false);
                            _allEdgeVars.add(e);
                            addExprs(e);
                            map2.put(p, new LogicalRedistributionEdge(p, EdgeType.IMPORT, 0, e));
                        }
                    }
                }

            }
        });
    }

    /**
     * Initialize encoding variables for each edge and map
     * the logical variables to their opposite edge from their peer
     *
     */
    private void addVariables() {
        addForwardingVariables();
        addBestVariables();
        addEdgeVariables();
        addRedistributionEdgeVariables();
        addChoiceVariables();
    }

    /**
     * Print the result of the SMT encoding as either
     * satisfiable with the model, or unsatisfiable.
     *
     */
    private void debug(String filter, boolean summary, boolean full) {

        System.out.println("Number of variables:   " + _allVariables.size());
        System.out.println("Number of constraints: " + _solver.getAssertions().length);
        System.out.println("Number of nodes: " + _graph.getConfigurations().size());

        int edges = 0;
        for (Map.Entry<String, Set<String>> e : _graph.getNeighbors().entrySet()) {
            for (String n : e.getValue()) {
                edges++;
            }
        }
        System.out.println("Number of edges: " + edges);

        long start = System.currentTimeMillis();
        Status status = _solver.check();
        long total = System.currentTimeMillis() - start;
        System.out.println("Solving time: " + total);

        if (full) {
            System.out.println("================= Variables ==================");
            for (Expr e : _allVariables) {
                System.out.println(e.toString());
            }

            System.out.println("================= Constraints ==================");
            for (BoolExpr be : _solver.getAssertions()) {
                if (filter == null || be.toString().contains(filter)) {
                    System.out.println(be);
                }
            }
        }

        if (status == Status.UNSATISFIABLE) {
            System.out.println("unsat");
        }
        else if (status == Status.UNKNOWN) {
            System.out.println("unknown");
        }
        if (status == Status.SATISFIABLE) {
            Model m = _solver.getModel();
            System.out.println("================= Model ================");

            if (summary) {
                Map<String, Map<GraphEdge, BoolExpr>> forwarding = (_optimizations.getKeepDataForwarding() ? _dataForwarding : _controlForwarding);

                forwarding.forEach((router, map) -> {
                    map.forEach((edge, e) -> {
                        Expr val = m.evaluate(e, false);
                        if (val.isTrue()) {
                            System.out.println(edge);
                        }
                    });
                });
                System.out.println("");

            }
            if (full) {
                for (Expr e : _allVariables) {
                    String name = e.toString();
                    if (filter == null || name.contains(filter)) {
                        Expr val = _solver.getModel().evaluate(e, false);
                        if (!val.equals(e)) {
                            System.out.println(name + " = " + val);
                        }
                    }
                }
            }
        }

        System.out.println("===========================================");

    }

    /**
     * Add the constraint that each variable:
     *  - administrative distance
     *  - local preference
     *  - hop count
     *  - protocol metric
     *
     *  all have a lower bound  -2 < v. We allow v = -1 for when an
     *  edge is not permitted. This simplifies the computation of the best path
     *
     */
    private void addLowerBoundConstraints() {
        for (EdgeVars e : _allEdgeVars) {
            if (e.getAdminDist() != null) {
                _solver.add(_ctx.mkGe(e.getAdminDist(), _ctx.mkInt(0)) );
            }
            if (e.getHopCount() != null) {
                _solver.add(_ctx.mkGe(e.getHopCount(), _ctx.mkInt(0)));

            }
            if (e.getLocalPref() != null) {
                _solver.add(_ctx.mkGe(e.getLocalPref(), _ctx.mkInt(0)));
            }
            if (e.getMetric() != null) {
                _solver.add(_ctx.mkGe(e.getMetric(), _ctx.mkInt(0)));
            }
            if (e.getPrefixLength() != null) {
                _solver.add(_ctx.mkGe(e.getPrefixLength(), _ctx.mkInt(0)));
                _solver.add(_ctx.mkLe(e.getPrefixLength(), _ctx.mkInt(32)));
            }
        }
    }

    private boolean hasProtocol(Statement s) {
        Boolean[] val = new Boolean[1];
        val[0] = false;
        visit(s, stmt -> {}, expr -> {
            if (expr instanceof MatchProtocol) {
                val[0] = true;
            }
        });
        return val[0];
    }

    private boolean matchesProtocol(Statement s, RoutingProtocol proto) {
        Boolean[] val = new Boolean[1];
        val[0] = false;
        visit(s, stmt -> {}, expr -> {
            if (expr instanceof MatchProtocol) {
                MatchProtocol mp = (MatchProtocol) expr;
                val[0] = (mp.getProtocol() == proto);
            }
        });
        return val[0];
    }

    private List<Statement> relevantStatements(List<Statement> statements, RoutingProtocol to, RoutingProtocol from) {
        List<Statement> acc = new ArrayList<>();
        if (to == from) {
            for (Statement s : statements) {
                if (hasProtocol(s)) {
                    acc.add(s);
                }
            }
        } else {
            for (Statement s : statements) {
                if (hasProtocol(s)) {
                    if (matchesProtocol(s, from)) {
                        acc.add(s);
                        break;
                    }
                } else {
                    acc.add(s);
                }
            }
        }
        return acc;
    }


    private BoolExpr computeTransferFunction(EdgeVars other, EdgeVars current, List<Statement> acc, BooleanExpr expr) {
        if (expr instanceof Conjunction) {
            Conjunction c = (Conjunction) expr;
            BoolExpr v = _ctx.mkBool(true);
            for (BooleanExpr x : c.getConjuncts()) {
                v = _ctx.mkAnd(v, computeTransferFunction(other, current, acc, x));
            }
            return v;

        } else if (expr instanceof Disjunction) {
            Disjunction d = (Disjunction) expr;
            if (d.getDisjuncts().size() == 0) {
                return _ctx.mkBool(true);
            }
            BoolExpr v = _ctx.mkBool(false);
            for (BooleanExpr x : d.getDisjuncts()) {
                v = _ctx.mkOr(v, computeTransferFunction(other, current, acc, x));
            }
            return v;

        } else if (expr instanceof MatchProtocol) {
            return _ctx.mkBool(true);

        } else {
            return _ctx.mkBool(true);
        }
    }

    // TODO: should we create a new variable to model the semantics of every assignment
    // TODO: since these can impact the selection criteria? E.g., local preference
    private BoolExpr computeTransferFunction(EdgeVars other, EdgeVars current, Configuration conf, RoutingProtocol to, RoutingProtocol from, List<Statement> acc, List<Statement> statements) {

        Iterator<Statement> it = statements.iterator();

        while (it.hasNext()) {
            Statement s = it.next();

            if (s instanceof Statements.StaticStatement) {
                Statements.StaticStatement ss = (Statements.StaticStatement) s;
                if (ss.getType() == ExitAccept) {
                    ArithExpr defaultLen = _ctx.mkInt(defaultLength(from));
                    ArithExpr defaultAd = _ctx.mkInt(defaultAdminDistance(conf, from));
                    ArithExpr defaultLp = _ctx.mkInt(defaultLocalPref(from));
                    ArithExpr defaultMet = _ctx.mkInt(defaultMetric(from));
                    ArithExpr defaultId = _ctx.mkInt(defaultId(from));

                    // TODO: apply accumulated actions

                    // TODO

                    // TODO

                    // TODO
                    return _ctx.mkAnd(
                                    safeEq(current.getPermitted(), other.getPermitted()),
                                    safeEq(current.getPrefixLength(), (other.getPrefixLength() == null ? defaultLen : other.getPrefixLength())),
                                    safeEq(current.getAdminDist(), (other.getAdminDist() == null ? defaultAd : other.getAdminDist() )),
                                    safeEq(current.getLocalPref(), (other.getLocalPref() == null ? defaultLp : other.getLocalPref() )),
                                    safeEq(current.getMetric(), (other.getMetric() == null ? defaultMet : other.getMetric() )),
                                    safeEq(current.getRouterId(), (other.getRouterId() == null ? defaultId : other.getRouterId() )));

                } else if (ss.getType() == ExitReject) {
                    return _ctx.mkNot(current.getPermitted());

                } else {
                    throw new BatfishException("TODO: computeTransferFunction: " + ss.getType());
                }
            }

            if (s instanceof If) {
                If i = (If) s;
                List<Statement> accx = new ArrayList<>(acc);
                List<Statement> accy = new ArrayList<>(acc);
                List<Statement> remainingx = new ArrayList<>(i.getTrueStatements());
                List<Statement> remainingy = new ArrayList<>(i.getFalseStatements());
                it.forEachRemaining(remainingx::add);
                it.forEachRemaining(remainingy::add);
                BoolExpr guard = computeTransferFunction(other, current, acc, i.getGuard());
                BoolExpr trueBranch = computeTransferFunction(other, current, conf, to, from, accx, remainingx);
                BoolExpr falseBranch = computeTransferFunction(other, current, conf, to, from, accy, remainingy);
                return If(guard, trueBranch, falseBranch);

            } else {
                acc.add(s);
            }
        }
        return _ctx.mkBool(true);
    }

    private BoolExpr transferFunction(EdgeVars other, EdgeVars current, RoutingPolicy pol, Configuration conf, RoutingProtocol to, RoutingProtocol from) {
        List<Statement> relevant = relevantStatements(pol.getStatements(), to, from);
        System.out.println("---- RELEVANT STATEMENTS ----");
        System.out.println("to " + to.protocolName() + ", from " + from.protocolName());
        for (Statement s : relevant) {
            System.out.println(s);
        }
        System.out.println("-----------------------------");

        BoolExpr transfunc = computeTransferFunction(other, current, conf, to, from, new ArrayList<>(), relevant);

        System.out.println(transfunc);

        return transfunc;
    }


    private void addRedistributionConstraints() {
        _graph.getConfigurations().forEach((router, conf) -> {
            for (RoutingProtocol proto : _protocols.get(router)) {
                RoutingPolicy pol = findRoutingPolicy(conf, proto);
                if (pol != null) {
                    EnumMap<RoutingProtocol, LogicalRedistributionEdge> map = _redistributionEdges.get(router).get(proto);
                    map.forEach((fromProto, vars) -> {
                        EdgeVars current = vars.getEdgeVars();
                        EdgeVars other = _bestNeighborPerProtocol.get(router).get(fromProto);
                        BoolExpr be = transferFunction(other, current, pol, conf, proto, fromProto);
                        _solver.add(be);
                    });
                }
            }
        });
    }

    /**
     * TODO:
     * This was copied from BdpDataPlanePlugin.java
     * to make things easier for now.
     */
    private void initOspfInterfaceCosts(Configuration conf) {
        if (conf.getOspfProcess() != null) {
            conf.getInterfaces().forEach((interfaceName, i) -> {
                if (i.getActive()) {
                    Integer ospfCost = i.getOspfCost();
                    if (ospfCost == null) {
                        if (interfaceName.startsWith("Vlan")) {
                            // TODO: fix for non-cisco
                            ospfCost = DEFAULT_CISCO_VLAN_OSPF_COST;
                        }
                        else {
                            if (i.getBandwidth() != null) {
                                ospfCost = Math.max(
                                        (int) (conf.getOspfProcess().getReferenceBandwidth()
                                                / i.getBandwidth()),
                                        1);
                            }
                            else {
                                throw new BatfishException(
                                        "Expected non-null interface bandwidth for \""
                                                + conf.getHostname() + "\":\"" + interfaceName
                                                + "\"");
                            }
                        }
                    }
                    i.setOspfCost(ospfCost);
                }
            });
        }
    }


    private BoolExpr appliesToDestination(BitVecExpr prefix, BitVecExpr mask) {
        BitVecExpr x = _ctx.mkBVAND(prefix, mask);
        BitVecExpr y = _ctx.mkBVAND(_destinationVar, mask);
        return _ctx.mkEq(x,y);
    }

    private List<Prefix> getOriginatedNetworks(Configuration conf, RoutingProtocol proto) {
        List<Prefix> acc = new ArrayList<>();
        switch (proto) {
            case OSPF:
                conf.getOspfProcess().getAreas().forEach((areaID, area) -> {
                    if (areaID == 0) {
                        for (Interface iface : area.getInterfaces()) {
                            if (iface.getActive() && iface.getOspfEnabled()) {
                                acc.add(iface.getPrefix());
                            }
                        }
                    } else {
                        throw new BatfishException("Error: only support area 0 at the moment");
                    }
                });
                break;

            case BGP:
                conf.getRouteFilterLists().forEach((name, list) -> {
                    for (RouteFilterLine line : list.getLines()) {
                        if (name.equals(BGP_NETWORK_FILTER_LIST_NAME)) {
                            acc.add(line.getPrefix());
                        }
                    }
                });
                break;
        }
        return acc;
    }

    private boolean isInterfaceUsed(Configuration conf, RoutingProtocol proto, Interface iface) {
        if (proto == RoutingProtocol.STATIC) {
            List<StaticRoute> srs = _graph.getStaticRoutes().get(conf.getName()).get(iface.getName());
            return iface.getActive() && srs != null && srs.size() > 0;
        }
        return true;
    }

    private BoolExpr If(BoolExpr cond, BoolExpr case1, BoolExpr case2) {
        return _ctx.mkAnd(_ctx.mkImplies(cond, case1), _ctx.mkImplies(_ctx.mkNot(cond), case2));
        // return (BoolExpr) _ctx.mkITE(cond, case1, case2);
    }

    private BoolExpr safeEq(Expr x, Expr value) {
        if (x == null) {
            return _ctx.mkBool(true);
        }
        return _ctx.mkEq(x, value);
    }

    private BoolExpr safeEqAdd(Expr x, ArithExpr value, int cost) {
        if (x == null) {
            return _ctx.mkBool(true);
        }
        return _ctx.mkEq(x, _ctx.mkAdd(value, _ctx.mkInt(cost)));
    }

    // TODO: specialize by vendor
    private int defaultId(RoutingProtocol proto) {
        return 0;
    }

    private int defaultMetric(RoutingProtocol proto) {
        if (proto == RoutingProtocol.CONNECTED) {
            return 0;
        }
        if (proto == RoutingProtocol.STATIC) {
            return 0;
        }
        return 0;
    }

    private int defaultLocalPref(RoutingProtocol proto) {
        if (proto == RoutingProtocol.CONNECTED) {
            return 0;
        }
        if (proto == RoutingProtocol.STATIC) {
            return 0;
        }
        return 0;
    }

    private int defaultLength(RoutingProtocol proto) {
        if (proto == RoutingProtocol.CONNECTED) {
            return 0;
        }
        if (proto == RoutingProtocol.STATIC) {
            return 0;
        }
        return 0;
    }

    private boolean isMultipath(Configuration conf, RoutingProtocol proto) {
        if (proto == RoutingProtocol.CONNECTED) {
            return true;
        } else if (proto == RoutingProtocol.STATIC) {
            return true;
        } else if (proto == RoutingProtocol.OSPF) {
            return true;
        } else {
            return false;
        }
    }

    private EdgeVars correctVars(LogicalEdge e) {
        if (e instanceof LogicalGraphEdge) {
            LogicalGraphEdge lge = (LogicalGraphEdge) e;
            EdgeVars vars = e.getEdgeVars();
            if (!vars.getIsUsed()) {
                return _otherEnd.get(e).getEdgeVars();
            }
            return vars;
        } else {
            return e.getEdgeVars();
        }
    }

    // TODO: what about external neighbors? probably need another case
    private String findNeighbor(LogicalGraphEdge e) {
        if (e == null) {
            return null;
        }
        LogicalGraphEdge other = _otherEnd.get(e);
        if (other == null) {
            return null;
        } else {
            return other.getEdge().getRouter();
        }
    }

    private long routerId(Configuration conf, RoutingProtocol proto) {
        if (proto == RoutingProtocol.BGP) {
            return conf.getBgpProcess().getRouterId().asLong();
        }
        if (proto == RoutingProtocol.OSPF) {
            return conf.getOspfProcess().getRouterId().asLong();
        }
        // TODO: what to use in ISIS
        // Doesn't matter since not compared here
        return 0;
    }

    private Long findRouterId(LogicalEdge e, RoutingProtocol proto) {
        if (e instanceof LogicalGraphEdge) {
            LogicalGraphEdge lge = (LogicalGraphEdge) e;
            String peer = findNeighbor(lge);
            if (peer == null) {
                return null;
            }
            Configuration pc = _graph.getConfigurations().get(peer);
            return routerId(pc, proto);
        } else {
            return null;
        }
    }


    private BoolExpr equal(Configuration conf, RoutingProtocol proto, EdgeVars best, EdgeVars vars, LogicalEdge e) {
        BoolExpr tru = _ctx.mkBool(true);

        ArithExpr defaultLocal = _ctx.mkInt(defaultLocalPref(proto));
        ArithExpr defaultAdmin = _ctx.mkInt(defaultAdminDistance(conf, proto));
        ArithExpr defaultMet = _ctx.mkInt(defaultMetric(proto));
        ArithExpr defaultLen = _ctx.mkInt(defaultLength(proto));

        BoolExpr equalLen;
        BoolExpr equalAd;
        BoolExpr equalLp;
        BoolExpr equalMet;
        BoolExpr equalId;

        if (vars.getPrefixLength() == null) {
            if (best.getPrefixLength() != null) {
                equalLen = _ctx.mkEq(best.getPrefixLength(), defaultLen);
            } else {
                equalLen = tru;
            }
        } else {
            equalLen = _ctx.mkEq(best.getPrefixLength(), vars.getPrefixLength());
        }

        if (vars.getAdminDist() == null) {
            if (best.getAdminDist() != null && _optimizations.getKeepAdminDist()) {
                equalAd = _ctx.mkEq(best.getAdminDist(), defaultAdmin);
            } else {
                equalAd = tru;
            }
        } else {
            equalAd = _ctx.mkEq(best.getAdminDist(), vars.getAdminDist());
        }

        if (vars.getLocalPref() == null) {
            if (best.getLocalPref() != null && _optimizations.getKeepLocalPref()) {
                equalLp = _ctx.mkEq(best.getLocalPref(), defaultLocal);
            } else {
                equalLp = tru;
            }
        } else {
            equalLp = _ctx.mkEq(best.getLocalPref(), vars.getLocalPref());
        }

        if (vars.getMetric() == null) {
            if (best.getMetric() != null) {
                equalMet = _ctx.mkEq(best.getMetric(), defaultMet);
            } else {
                equalMet = tru;
            }
        } else {
            equalMet = _ctx.mkEq(best.getMetric(), vars.getMetric());
        }

        if (vars.getRouterId() == null) {
            if (best.getRouterId() == null) {
                equalId = tru;
            } else {
                Long peerId = findRouterId(e, proto);
                if (peerId == null) {
                    equalId = tru;
                } else {
                    equalId = _ctx.mkEq( best.getRouterId(), _ctx.mkInt(peerId) );
                }
            }
        } else {
            equalId = _ctx.mkEq( best.getRouterId(), vars.getRouterId() );
        }

        return _ctx.mkAnd(equalLen, equalAd, equalLp, equalMet, equalId);
    }

    // TODO: add router ID
    private BoolExpr greaterOrEqual(Configuration conf, EdgeVars best, EdgeVars vars, RoutingProtocol proto, LogicalEdge e) {
        BoolExpr tru = _ctx.mkBool(true);
        BoolExpr fal = _ctx.mkBool(false);

        ArithExpr defaultLocal = _ctx.mkInt(defaultLocalPref(proto));
        ArithExpr defaultAdmin = _ctx.mkInt(defaultAdminDistance(conf, proto));
        ArithExpr defaultMet = _ctx.mkInt(defaultMetric(proto));
        ArithExpr defaultLen = _ctx.mkInt(defaultLength(proto));

        BoolExpr betterLen;
        BoolExpr equalLen;
        BoolExpr betterAd;
        BoolExpr equalAd;
        BoolExpr betterLp;
        BoolExpr equalLp;
        BoolExpr betterMet;
        BoolExpr equalMet;
        BoolExpr tiebreak;

        if (vars.getPrefixLength() == null) {
            if (best.getPrefixLength() != null) {
                betterLen = _ctx.mkGt(best.getPrefixLength(), defaultLen);
                equalLen = _ctx.mkEq(best.getPrefixLength(), defaultLen);
            } else {
                betterLen = fal;
                equalLen = tru;
            }
        } else {
            betterLen = _ctx.mkGt(best.getPrefixLength(), vars.getPrefixLength());
            equalLen = _ctx.mkEq(best.getPrefixLength(), vars.getPrefixLength());
        }

        if (vars.getAdminDist() == null) {
            if (best.getAdminDist() != null && _optimizations.getKeepAdminDist()) {
                betterAd = _ctx.mkLt(best.getAdminDist(), defaultAdmin);
                equalAd = _ctx.mkEq(best.getAdminDist(), defaultAdmin);
            } else {
                betterAd = fal;
                equalAd = tru;
            }
        } else {
            betterAd = _ctx.mkLt(best.getAdminDist(), vars.getAdminDist());
            equalAd = _ctx.mkEq(best.getAdminDist(), vars.getAdminDist());
        }

        if (vars.getLocalPref() == null) {
            if (best.getLocalPref() != null && _optimizations.getKeepLocalPref()) {
                betterLp = _ctx.mkGt(best.getLocalPref(), defaultLocal);
                equalLp = _ctx.mkEq(best.getLocalPref(), defaultLocal);
            } else {
                betterLp = fal;
                equalLp = tru;
            }
        } else {
            betterLp = _ctx.mkGt(best.getLocalPref(), vars.getLocalPref());
            equalLp = _ctx.mkEq(best.getLocalPref(), vars.getLocalPref());
        }

        if (vars.getMetric() == null) {
            if (best.getMetric() != null) {
                betterMet = _ctx.mkLt(best.getMetric(), defaultMet);
                equalMet = _ctx.mkEq(best.getMetric(), defaultMet);
            } else {
                betterMet = fal;
                equalMet = tru;
            }
        } else {
            betterMet = _ctx.mkLt(best.getMetric(), vars.getMetric());
            equalMet = _ctx.mkEq(best.getMetric(), vars.getMetric());
        }

        if (vars.getRouterId() == null) {
            if (best.getRouterId() == null) {
                tiebreak = tru;
            } else {
                Long peerId = findRouterId(e, proto);
                if (peerId == null) {
                    tiebreak = tru;
                } else {
                    tiebreak = _ctx.mkGe(best.getRouterId(), _ctx.mkInt(peerId));
                }
            }
        } else {
            tiebreak = _ctx.mkGe(best.getRouterId(), vars.getRouterId());
        }

        BoolExpr b0 = _ctx.mkAnd(equalMet, tiebreak );
        BoolExpr b1 = _ctx.mkOr(betterMet, b0);
        BoolExpr b2 = _ctx.mkAnd(equalLp, b1);
        BoolExpr b3 = _ctx.mkOr(betterLp, b2);
        BoolExpr b4 = _ctx.mkAnd(equalAd, b3);
        BoolExpr b5 = _ctx.mkOr(betterAd, b4);
        BoolExpr b6 = _ctx.mkAnd(equalLen, b5);
        return _ctx.mkOr(betterLen, b6);
    }

    /**
     * Add constraints that constraint the best choice for a router.
     * The best choice will have the following constraints:
     *
     * best >= neighbor_1 && ... && best >= neighbor_i
     * best == neighbor_1 || ... || best == neighbor_i
     *
     */
    private void addBestOverallConstraints() {
        _graph.getConfigurations().forEach((router, conf) -> {

            // These constraints will be added at the protocol-level when a single protocol
            if (!_optimizations._sliceHasSingleProtocol.contains(router)) {

                boolean someProto = false;

                BoolExpr acc = null;
                BoolExpr somePermitted = null;
                EdgeVars best = _bestNeighbor.get(router);

                for (RoutingProtocol proto : _protocols.get(router)) {

                    someProto = true;

                    // TODO: must do this for each of 32 lens

                    EdgeVars bestVars = getBestVars(router, proto);

                    if (somePermitted == null) {
                        somePermitted = bestVars.getPermitted();
                    } else {
                        somePermitted = _ctx.mkOr(somePermitted, bestVars.getPermitted());
                    }

                    if (acc == null) {
                        acc = equal(conf, proto, best, bestVars, null);
                    } else {
                        acc = _ctx.mkOr(acc, equal(conf, proto, best, bestVars, null));
                    }
                    _solver.add(_ctx.mkImplies(bestVars.getPermitted(), greaterOrEqual(conf, best, bestVars, proto, null)));

                }

                if (someProto) {
                    if (acc != null) {
                        _solver.add(_ctx.mkEq(somePermitted, best.getPermitted()));
                        _solver.add(_ctx.mkImplies(somePermitted, acc));
                    }
                } else {
                    _solver.add(_ctx.mkNot(best.getPermitted()));
                }
            }
        });
    }

    private List<LogicalEdge> collectAllImportLogicalEdges(String router, RoutingProtocol proto) {
        List<LogicalEdge> eList = new ArrayList<>();
        for (ArrayList<LogicalGraphEdge> es : _edgeVariableMap.get(router).get(proto)) {
            for (LogicalGraphEdge lge : es) {
                if (lge.getEdgeType() == EdgeType.IMPORT) {
                    eList.add(lge);
                }
            }
        }
        _redistributionEdges.get(router).get(proto).forEach((fromProto,edge) -> {
            eList.add(edge);
        });
        return eList;
    }

    private boolean isEdgeUsed(Configuration conf, RoutingProtocol proto, LogicalEdge e) {
        if (e instanceof LogicalGraphEdge) {
            LogicalGraphEdge lge = (LogicalGraphEdge) e;
            GraphEdge ge = lge.getEdge();
            Interface iface = ge.getStart();
            return isInterfaceUsed(conf, proto, iface);
        } else {
            return true;
        }
    }

    /**
     * Add constraints that constraint the best choice for a router.
     * The best choice will have the following constraints:
     *
     * best >= neighbor_1 && ... && best >= neighbor_i
     * best == neighbor_1 || ... || best == neighbor_i
     *
     */
    private void addBestPerProtocolConstraints() {
        _graph.getConfigurations().forEach((router, conf) -> {

            for (RoutingProtocol proto : _protocols.get(router)) {

                // TODO: must do this for each of 32 lens
                EdgeVars bestVars = getBestVars(router, proto);
                BoolExpr acc = null;
                BoolExpr somePermitted = null;

                for (LogicalEdge e : collectAllImportLogicalEdges(router, proto)) {

                    EdgeVars vars = correctVars(e);
                    if (isEdgeUsed(conf, proto, e)) {

                        if (somePermitted == null) {
                            somePermitted = vars.getPermitted();
                        } else {
                            somePermitted = _ctx.mkOr(somePermitted, vars.getPermitted());
                        }

                        BoolExpr v = _ctx.mkAnd(vars.getPermitted(), equal(conf, proto, bestVars, vars, e));
                        if (acc == null) {
                            acc = v;
                        } else {
                            acc = _ctx.mkOr(acc, v);
                        }
                        _solver.add(_ctx.mkImplies(vars.getPermitted(), greaterOrEqual(conf, bestVars, vars, proto, e)));
                    }
                }

                if (acc != null) {
                    _solver.add(_ctx.mkEq(somePermitted, bestVars.getPermitted()));
                    // best is one of the allowed ones
                    _solver.add(_ctx.mkImplies(somePermitted, acc));
                }
            }

        });
    }

    /**
     * Add constraints to ensure that a neighbor is used if
     * it is the best choice (i.e., neighbor == best).
     *
     */
    private void addChoicePerProtocolConstraints() {
        _graph.getConfigurations().forEach((router, conf) -> {
            for (RoutingProtocol proto : _protocols.get(router)) {
                EdgeVars bestVars = getBestVars(router, proto);
                for (LogicalEdge e : collectAllImportLogicalEdges(router, proto)) {
                    EdgeVars vars = correctVars(e);
                    BoolExpr choice = _choiceVariables.get(router).get(proto).get(e);
                    if (isEdgeUsed(conf, proto, e) && e.getEdgeType() == EdgeType.IMPORT) {
                        BoolExpr isBest = equal(conf, proto, bestVars, vars, e);
                        BoolExpr falseBranch = _ctx.mkNot(choice);
                        BoolExpr trueBranch = _ctx.mkIff(choice, isBest);
                        BoolExpr val = If( vars.getPermitted(), trueBranch, falseBranch );
                        _solver.add( val );
                    }
                }

            }
        });
    }

    /**
     * The control plane forwards from x to y
     *
     */
    private void addControlForwardingConstraints() {
        _graph.getConfigurations().forEach((router, conf) -> {

            EdgeVars best = _bestNeighbor.get(router);
            Map<GraphEdge, BoolExpr> cfExprs = new HashMap<>();

            for (RoutingProtocol proto : _protocols.get(router)) {

                for (LogicalEdge e : collectAllImportLogicalEdges(router, proto)) {

                    if (isEdgeUsed(conf, proto, e) && e.getEdgeType() == EdgeType.IMPORT) {

                        EdgeVars vars = correctVars(e);

                        BoolExpr choice = _choiceVariables.get(router).get(proto).get(e);
                        BoolExpr isBest = _ctx.mkAnd( choice, equal(conf, proto, best, vars, e) );

                        if (e instanceof LogicalGraphEdge) {
                            LogicalGraphEdge lge = (LogicalGraphEdge) e;
                            GraphEdge ge = lge.getEdge();
                            BoolExpr cForward = _controlForwarding.get(router).get(ge);
                            _solver.add( _ctx.mkImplies(isBest, cForward) );

                            // record the negation as well
                            BoolExpr existing = cfExprs.get(ge);
                            if (existing == null) {
                                cfExprs.put(ge, isBest);
                            } else {
                                cfExprs.put(ge, _ctx.mkOr(existing, isBest));
                            }

                        } else {
                            LogicalRedistributionEdge lre = (LogicalRedistributionEdge) e;
                            RoutingProtocol protoFrom = lre.getFrom();

                            _edgeVariableMap.get(router).get(protoFrom).forEach(eList -> {
                                for (LogicalGraphEdge lge : eList) {
                                    if (lge.getEdgeType() == EdgeType.IMPORT) {

                                        GraphEdge ge = lge.getEdge();
                                        BoolExpr cForward = _controlForwarding.get(router).get(ge);
                                        BoolExpr otherProtoChoice = _choiceVariables.get(router).get(protoFrom).get(lge);
                                        _solver.add(_ctx.mkImplies(_ctx.mkAnd(isBest, otherProtoChoice), cForward));

                                        // record the negation as well
                                        BoolExpr existing = cfExprs.get(ge);
                                        BoolExpr both = _ctx.mkAnd(isBest, otherProtoChoice);
                                        if (existing == null) {
                                            cfExprs.put(ge, both);
                                        } else {
                                            cfExprs.put(ge, _ctx.mkOr(existing, both));
                                        }
                                    }
                                }
                            });
                        }
                    }
                }
            }

            _edgeVariableMap.get(router).forEach((proto, eList) -> {
                eList.forEach(edges -> {
                    edges.forEach(le -> {
                        GraphEdge ge = le.getEdge();
                        BoolExpr expr = cfExprs.get(ge);
                        BoolExpr cForward = _controlForwarding.get(router).get(ge);
                        if (expr != null) {
                            _solver.add(_ctx.mkImplies(_ctx.mkNot(expr), _ctx.mkNot(cForward)));
                        } else {
                            _solver.add( _ctx.mkNot(cForward) );
                        }
                    });
                });
            });

            /* if (someProto) {
                // if it was the best across protocols, then we do not forward along the edge
                cfExprs.forEach((e, expr) -> {
                    BoolExpr cForward = _controlForwarding.get(router).get(e);
                    _solver.add(_ctx.mkImplies(_ctx.mkNot(expr), _ctx.mkNot(cForward)));
                });
            } else {
                _controlForwarding.get(router).forEach((edge, e) -> {
                    _solver.add( _ctx.mkNot(e) );
                });
            } */
        });

    }

    private void addDataForwardingConstraints() {
        if (_optimizations.getKeepDataForwarding()) {
            _graph.getConfigurations().forEach((router, conf) -> {
                for (RoutingProtocol proto : _protocols.get(router)) {
                    for (ArrayList<LogicalGraphEdge> eList : _edgeVariableMap.get(router).get(proto)) {
                        for (LogicalGraphEdge e : eList) {
                            Interface iface = e.getEdge().getStart();
                            if (isInterfaceUsed(conf, proto, iface)) {
                                if (e.getEdgeType() == EdgeType.IMPORT) {
                                    BoolExpr cForward = _controlForwarding.get(router).get(e.getEdge());
                                    BoolExpr dForward = _dataForwarding.get(router).get(e.getEdge());
                                    _solver.add(_ctx.mkEq(cForward, dForward));
                                }
                            }
                        }
                    }
                }
            });
        }
    }

    private EdgeVars getBestVars(String router, RoutingProtocol proto) {
        if (_optimizations._sliceHasSingleProtocol.contains(router)) {
            return _bestNeighbor.get(router);
        } else {
            return _bestNeighborPerProtocol.get(router).get(proto);
        }
    }

    private BoolExpr relevantOrigination(List<Prefix> prefixes) {
        BoolExpr acc = _ctx.mkBool(false);
        for (Prefix p : prefixes) {
            long network = p.getNetworkAddress().asLong();
            long mask = p.getSubnetMask().asLong();
            BitVecExpr x = _ctx.mkBV(network, 32);
            BitVecExpr y = _ctx.mkBV(mask, 32);
            BoolExpr relevant = appliesToDestination(x, y);
            acc = _ctx.mkOr(acc, relevant);
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

    private int defaultAdminDistance(Configuration conf, RoutingProtocol proto) {
        return proto.getDefaultAdministrativeCost(conf.getConfigurationFormat());
    }

    private BoolExpr isRelevantFor(Prefix p) {
        long network = p.getNetworkAddress().asLong();
        long mask = p.getSubnetMask().asLong();
        BitVecExpr x = _ctx.mkBV(network, 32);
        BitVecExpr y = _ctx.mkBV(mask, 32);
        return appliesToDestination(x, y);
    }

    private void addImportConstraint(LogicalGraphEdge e, LogicalGraphEdge other, RoutingProtocol proto, EdgeVars vars, Interface iface, String router, BoolExpr isRoot, boolean noPeer) {
        // Check if we even need import-specific variables
        // If not, then we will just use the export variables when
        // determining the best option at each router
        if (vars.getIsUsed()) {

            if (proto == RoutingProtocol.CONNECTED) {
                Prefix p = iface.getPrefix();
                BoolExpr relevant = _ctx.mkAnd(_ctx.mkBool(iface.getActive()), isRelevantFor(p));
                BoolExpr values =
                        _ctx.mkAnd(
                                vars.getPermitted(),
                                safeEq(vars.getPrefixLength(), _ctx.mkInt(p.getPrefixLength())),
                                safeEq(vars.getAdminDist(), _ctx.mkInt(1)),
                                safeEq(vars.getLocalPref(), _ctx.mkInt(0)),
                                safeEq(vars.getHopCount(), _ctx.mkInt(0)),
                                safeEq(vars.getMetric(), _ctx.mkInt(0))
                        );
                _solver.add( If(relevant, values, _ctx.mkNot(vars.getPermitted())) );
            }

            if (proto == RoutingProtocol.STATIC) {
                List<StaticRoute> srs = _graph.getStaticRoutes().get(router).get(iface.getName()); // should exist
                assert(srs != null);

                BoolExpr acc = _ctx.mkNot(vars.getPermitted());
                for (StaticRoute sr : srs) {
                    Prefix p = sr.getNetwork();
                    BoolExpr relevant = _ctx.mkAnd(_ctx.mkBool(iface.getActive()), isRelevantFor(p));
                    BoolExpr values =
                            _ctx.mkAnd(
                                    vars.getPermitted(),
                                    safeEq(vars.getPrefixLength(), _ctx.mkInt(p.getPrefixLength())),
                                    safeEq(vars.getAdminDist(), _ctx.mkInt(sr.getAdministrativeCost())),
                                    safeEq(vars.getLocalPref(), _ctx.mkInt(0)),
                                    safeEq(vars.getHopCount(), _ctx.mkInt(0)),
                                    safeEq(vars.getMetric(), _ctx.mkInt(0))
                            );
                    acc = If(relevant, values, acc);
                }

              _solver.add( acc );
            }

            if (proto == RoutingProtocol.OSPF || proto == RoutingProtocol.BGP) {

                BoolExpr val =  _ctx.mkNot(vars.getPermitted());

                if (noPeer) {
                    _solver.add( val );
                } else {

                    if (other != null) {
                        EdgeVars varsOther = other.getEdgeVars();

                        // just copy the export policy in ospf
                        BoolExpr usable = _ctx.mkAnd(_ctx.mkBool(iface.getActive()), varsOther.getPermitted());
                        BoolExpr permitted = _ctx.mkAnd(_ctx.mkNot(isRoot), usable);

                        BoolExpr per = _ctx.mkEq(vars.getPermitted(), varsOther.getPermitted());
                        BoolExpr lp = safeEq(vars.getLocalPref(), varsOther.getLocalPref());
                        BoolExpr hops = safeEq(vars.getHopCount(), varsOther.getHopCount());
                        BoolExpr ad = safeEq(vars.getAdminDist(), varsOther.getAdminDist());
                        BoolExpr met = safeEq(vars.getMetric(), varsOther.getMetric());
                        BoolExpr len = safeEq(vars.getPrefixLength(), varsOther.getPrefixLength());
                        _solver.add( If(permitted, _ctx.mkAnd(per, lp, hops, ad, met, len), val) );
                    } else {
                        // TODO: when the router has no neighbor in the protocol?
                        System.out.println("ERROR: missing neighbor in protocol");
                    }
                }
            }
        }
    }

    private boolean addExportConstraint(Configuration conf, RoutingProtocol proto, EdgeVars vars, Interface iface, String router, boolean usedExport, List<Prefix> originations) {
        // only add constraints once when using a single copy of export variables
        if (!_optimizations.getSliceCanKeepSingleExportVar().get(router).get(proto) || !usedExport) {

            if (proto == RoutingProtocol.CONNECTED) {
                BoolExpr val = _ctx.mkNot(vars.getPermitted());
                _solver.add(val);
            }

            if (proto == RoutingProtocol.STATIC) {
                BoolExpr val = _ctx.mkNot(vars.getPermitted());
                _solver.add(val);
            }

            if (proto == RoutingProtocol.OSPF || proto == RoutingProtocol.BGP) {
                // originated routes
                Integer cost = addedCost(proto, iface);
                BoolExpr val = _ctx.mkNot(vars.getPermitted());
                // default is to propagate the "best" route

                EdgeVars best = getBestVars(router,proto);
                BoolExpr usable = _ctx.mkAnd(_ctx.mkBool(iface.getActive()), best.getPermitted());
                BoolExpr acc =
                        _ctx.mkAnd(
                                _ctx.mkEq(vars.getPermitted(), best.getPermitted()),
                                safeEq(vars.getPrefixLength(), best.getPrefixLength()),
                                safeEq(vars.getAdminDist(), best.getAdminDist()),
                                safeEq(vars.getLocalPref(), best.getLocalPref()),
                                safeEqAdd(vars.getMetric(), best.getMetric(), cost),
                                safeEqAdd(vars.getHopCount(), best.getHopCount(), 1)
                        );
                acc = If(usable, acc, val);

                // TODO: super inefficient to repeat this for every interface
                for (Prefix p : originations) {
                    BoolExpr relevant = _ctx.mkAnd(_ctx.mkBool(iface.getActive()), isRelevantFor(p));
                    int adminDistance = defaultAdminDistance(conf, proto);
                    int prefixLength = p.getPrefixLength();
                    BoolExpr values =
                            _ctx.mkAnd(
                                    vars.getPermitted(),
                                    safeEq(vars.getLocalPref(), _ctx.mkInt(0)),
                                    safeEq(vars.getHopCount(), _ctx.mkInt(1)),
                                    safeEq(vars.getAdminDist(), _ctx.mkInt(adminDistance)),
                                    safeEq(vars.getMetric(), _ctx.mkInt(cost)),
                                    safeEq(vars.getPrefixLength(), _ctx.mkInt(prefixLength))
                            );
                    acc = If(relevant, values, acc);
                }
                _solver.add( acc );
            }
            return true;
        }
        return false;
    }

    private void addTransferFunction() {

        for (Map.Entry<String, Configuration> entry : _graph.getConfigurations().entrySet()) {
            String router = entry.getKey();
            Configuration conf = entry.getValue();

            for (RoutingProtocol proto : _protocols.get(router)) {
                Boolean usedExport = false;
                List<Prefix> originations = getOriginatedNetworks(conf, proto);
                BoolExpr isRoot = relevantOrigination(originations);

                for (ArrayList<LogicalGraphEdge> eList : _edgeVariableMap.get(router).get(proto)) {
                    for (LogicalGraphEdge e : eList) {
                        LogicalGraphEdge other = _otherEnd.get(e);
                        GraphEdge ge = e.getEdge();
                        Interface iface = ge.getStart();
                        boolean noPeer = (ge.getEnd() == null);
                        EdgeVars vars = e.getEdgeVars();

                        if (isInterfaceUsed(conf, proto, iface)) {
                            switch (e.getEdgeType()) {
                                case IMPORT:
                                    addImportConstraint(e, other, proto, vars, iface, router, isRoot, noPeer);
                                    break;

                                case EXPORT:
                                    usedExport = addExportConstraint(conf, proto, vars, iface, router, usedExport, originations);
                                    break;
                            }
                        }
                    }

                }

            }
        }

    }

    private void addUnusedDefaultValueConstraints() {
        for (EdgeVars vars : _allEdgeVars) {

            BoolExpr notPermitted = _ctx.mkNot(vars.getPermitted());

            if (vars.getAdminDist() != null) {
                _solver.add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getAdminDist(), _ctx.mkInt(0))) );
            }
            if (vars.getLocalPref() != null) {
                _solver.add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getLocalPref(), _ctx.mkInt(0))) );
            }
            if (vars.getPrefixLength() != null) {
                _solver.add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getPrefixLength(), _ctx.mkInt(0))) );
            }
            if (vars.getMetric() != null) {
                _solver.add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getMetric(), _ctx.mkInt(0))) );
            }
            if (vars.getHopCount() != null) {
                _solver.add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getHopCount(), _ctx.mkInt(0))) );
            }
        }
    }

    private void addDestinationConstraint() {
        BitVecExpr value = _ctx.mkBV( new Ip(_destination).asLong() ,32);
        _solver.add( _ctx.mkEq(_destinationVar, value) );
    }

    private void addPropertyConstraint() {
        BoolExpr acc = _ctx.mkBool(false);
        for (EdgeVars vars : _allEdgeVars) {

            // check all ToRs reachable
            if (vars.getName().contains("ToR") && vars.getName().contains("OVERALL") && vars.getName().contains("BEST")) {
                acc = _ctx.mkOr(acc, _ctx.mkNot(vars.getPermitted()));
            }

            //check a single ToR reachable
            //if (vars.getName().equals("Pod_0_ToR_14_OVERALL_none_0_BEST")) {
            //    System.out.println("FOUND");
            //    _solver.add( _ctx.mkNot(vars.getPermitted()) );
            //}
        }
        _solver.add( acc );
    }

    private void initConfigurations() {
        _graph.getConfigurations().forEach((router,conf) -> {
            initOspfInterfaceCosts(conf);
        });
    }

    public void computeEncoding() {
        System.out.println(_graph.toString());
        initConfigurations();
        _optimizations.computeOptimizations();
        addVariables();
        addLowerBoundConstraints();
        addRedistributionConstraints();
        addTransferFunction();
        addBestPerProtocolConstraints();
        addChoicePerProtocolConstraints();
        addBestOverallConstraints();
        addControlForwardingConstraints();
        addDataForwardingConstraints();
        addUnusedDefaultValueConstraints();
        addDestinationConstraint();
        // addPropertyConstraint();
        debug(null, true, true);
    }

}
