package org.batfish.smt;

import com.microsoft.z3.*;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.*;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.*;
import org.batfish.datamodel.routing_policy.expr.IntExpr;
import org.batfish.datamodel.routing_policy.statement.*;

import java.util.*;
import java.util.function.Consumer;

import static org.batfish.datamodel.routing_policy.statement.Statements.*;

// Features:
// ---------
//   - BGP community values (ignore regex for now)
//   - Avoid loops in BGP when non-standard (or non-common) local-pref internally
//   - iBGP by comparing local-pref internally
//     * Requires reachability, and no ACLs for loopbacks
//   - maximum path length by protocol
//   - RIP routing protocol
//
// Environment stuff:
// ------------------
//   - Is Local preference transitive? Only inside?
//   - Maximum path length on entry?
//
//
// Small items:
// ------------
//   - Don't allow transitive route redistribution
//   - Ensure distance is transfered over with redistribution
//   - Compute multipath correctly (how do we handle some multipath)
//   - Can we use the length variable when we filter later on, say, communities
//     Alternatively, can we use length when we only filter for length at the border?


/**
 * Class to encode the network as an SMT formula for a particular
 * destination IP address
 *
 */
public class Encoder {

    class Optimizations {

        private static final boolean ENABLE_PREFIX_ELIMINATION = true;
        private static final boolean ENABLE_IMPORT_EXPORT_MERGE_OPTIMIZATION = true;
        private static final boolean ENABLE_EXPORT_MERGE_OPTIMIZATION = true;
        private static final boolean ENABLE_SLICING_OPTIMIZATION = true;

        private boolean _hasEnvironment;
        private Set<String> _sliceHasSingleProtocol;
        private Map<String, EnumMap<RoutingProtocol, Boolean>> _sliceCanKeepSingleExportVar;
        private Map<String, EnumMap<RoutingProtocol, List<GraphEdge>>> _sliceCanCombineImportExportVars;
        private Map<String, EnumMap<RoutingProtocol, Boolean>> _needRouterIdProto;
        private Set<String> _needRouterId;

        private boolean _keepLocalPref;
        private boolean _keepAdminDist;
        private boolean _keepMed;

        private Optimizations() {
            _hasEnvironment = false;
            _sliceHasSingleProtocol = new HashSet<>();
            _sliceCanCombineImportExportVars = new HashMap<>();
            _sliceCanKeepSingleExportVar = new HashMap<>();
            _needRouterIdProto = new HashMap<>();
            _needRouterId = new HashSet<>();
            _keepLocalPref = true;
            _keepAdminDist = true;
            _keepMed = true;
        }

        private boolean hasRelevantOriginatedRoute(Configuration conf, RoutingProtocol proto) {
            List<Prefix> prefixes =  getOriginatedNetworks(conf, proto);
            for (Prefix p1 : prefixes) {
                for (Prefix p2 : _destinations) {
                    if (overlaps(p1, p2)) {
                        return true;
                    }
                }
            }
            return false;
        }

        private boolean needToModelStatic(Configuration conf) {
            if (Optimizations.ENABLE_SLICING_OPTIMIZATION) {
                return hasRelevantOriginatedRoute(conf, RoutingProtocol.STATIC);
            } else {
                return conf.getDefaultVrf().getStaticRoutes().size() > 0;
            }
        }

        private boolean needToModelConnected(Configuration conf) {
            if (Optimizations.ENABLE_SLICING_OPTIMIZATION) {
                return hasRelevantOriginatedRoute(conf, RoutingProtocol.CONNECTED);
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
                if (conf.getDefaultVrf().getOspfProcess() != null) {
                    protos.add(RoutingProtocol.OSPF);
                }
                if (conf.getDefaultVrf().getBgpProcess() != null) {
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

        private boolean computeHasEnvironment() {
            Boolean[] val = new Boolean[1];
            val[0] = false;
            _graph.getEdgeMap().forEach((router, edges) -> {
                for (GraphEdge ge : edges) {
                    if (ge.getEnd() == null && _bgpNeighbors.containsKey(ge)) {
                        val[0] = true;
                    }
                }
            });
            return val[0];
        }

        private boolean computeKeepLocalPref() {
            if (!Optimizations.ENABLE_SLICING_OPTIMIZATION) {
                return true;
            }
            Boolean[] val = new Boolean[1];
            val[0] = false;
            _graph.getConfigurations().forEach((router, conf) -> {
                conf.getRoutingPolicies().forEach((name,pol) -> {
                    visit(pol.getStatements(), stmt -> {
                        if (stmt instanceof SetLocalPreference) {
                            val[0] = true;
                        }
                    }, expr -> {});
                });
            });
            return val[0];
        }

        private boolean computeKeepAdminDistance() {
            if (!Optimizations.ENABLE_SLICING_OPTIMIZATION) {
                return true;
            }
            Boolean[] val = new Boolean[1];
            val[0] = false;
            _graph.getConfigurations().forEach((router, conf) -> {
                conf.getRoutingPolicies().forEach((name,pol) -> {
                    visit(pol.getStatements(), stmt -> {
                        // TODO: how is admin distance set?
                        if (stmt instanceof SetMetric) {
                            val[0] = true;
                        }
                    }, expr -> {});
                });
            });
            return val[0];
        }

        // TODO: also check if med never set
        private boolean computeKeepMed() {
            return !Optimizations.ENABLE_SLICING_OPTIMIZATION;
            /* if (!Optimizations.ENABLE_SLICING_OPTIMIZATION) {
                return true;
            }
            return _hasEnvironment; */
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

        private boolean isDefaultBgpExport(Configuration conf, BgpNeighbor n) {

            // Check if valid neighbor
            if (n == null || n.getExportPolicy() == null) {
                return true;
            }

            // Ensure a single if statement
            RoutingPolicy pol = conf.getRoutingPolicies().get(n.getExportPolicy());
            List<Statement> stmts = pol.getStatements();
            if (stmts.size() != 1) {
                return false;
            }
            Statement s = stmts.get(0);
            if (!(s instanceof If)) {
                return false;
            }

            // Ensure that the true branch accepts and the false branch rejects
            If i = (If) s;
            BooleanExpr be = i.getGuard();
            List<Statement> trueStmts = i.getTrueStatements();
            List<Statement> falseStmts = i.getFalseStatements();

            if (trueStmts.size() != 1 || falseStmts.size() != 1) {
                return false;
            }
            Statement s1 = trueStmts.get(0);
            Statement s2 = falseStmts.get(0);
            if (!(s1 instanceof StaticStatement) || !(s2 instanceof StaticStatement)) {
                return false;
            }
            StaticStatement x = (StaticStatement) s1;
            StaticStatement y = (StaticStatement) s2;
            if (x.getType() != Statements.ExitAccept || y.getType() != Statements.ExitReject) {
                return false;
            }

            // Ensure condition just hands off to the common export policy
            if (!(be instanceof CallExpr)) {
                return false;
            }

            CallExpr ce = (CallExpr) be;
            return ce.getCalledPolicyName().contains(BGP_COMMON_FILTER_LIST_NAME);
        }

        // Merge export variables into a single copy when no peer-specific export
        private void computeCanMergeExportVars() {
            _graph.getConfigurations().forEach((router,conf) -> {
                EnumMap<RoutingProtocol, Boolean> map = new EnumMap<>(RoutingProtocol.class);
                _sliceCanKeepSingleExportVar.put(router, map);

                // Can be no peer-specific export, which includes dropping due to
                // the neighbor already being the root of the tree.
                // TODO: actually compute this
                for (RoutingProtocol proto : _protocols.get(router)) {
                    if (proto == RoutingProtocol.CONNECTED || proto == RoutingProtocol.STATIC || proto == RoutingProtocol.OSPF) {
                        map.put(proto, Optimizations.ENABLE_EXPORT_MERGE_OPTIMIZATION);
                    } else {
                        boolean allDefault = true;
                        for (Map.Entry<Prefix, BgpNeighbor> e : conf.getDefaultVrf().getBgpProcess().getNeighbors().entrySet()) {
                            BgpNeighbor n = e.getValue();
                            if (!isDefaultBgpExport(conf, n)) {
                                allDefault = false;
                                break;
                            }
                        }
                        map.put(proto, allDefault && Optimizations.ENABLE_EXPORT_MERGE_OPTIMIZATION);
                    }
                }
            });
        }

        // Make sure the neighbor uses the same protocol
        // and is configured to use the corresponding interface.
        // This makes sure that the export variables will exist.
        private boolean hasExportVariables(GraphEdge e, RoutingProtocol proto) {
            if (e.getEnd() != null) {
                String peer = e.getPeer();
                List<RoutingProtocol> peerProtocols = _protocols.get(peer);
                if (peerProtocols.contains(proto)) {
                    Configuration peerConf = _graph.getConfigurations().get(peer);
                    if (isInterfaceUsed(peerConf, proto, e.getEnd())) {
                        return true;
                    }
                }
            }
            return false;
        }

        // Merge import and export variables when there is no peer-specific import
        private void computeCanMergeImportExportVars() {

            _graph.getConfigurations().forEach((router,conf) -> {
                EnumMap<RoutingProtocol, List<GraphEdge>> map = new EnumMap<>(RoutingProtocol.class);
                _sliceCanCombineImportExportVars.put(router, map);
                for (RoutingProtocol proto : _protocols.get(router)) {

                    List<GraphEdge> edges = new ArrayList<>();
                    if (Optimizations.ENABLE_IMPORT_EXPORT_MERGE_OPTIMIZATION) {

                        boolean relevantProto = (proto != RoutingProtocol.CONNECTED && proto != RoutingProtocol.STATIC);
                        if (relevantProto) {

                            boolean isNotRoot = !hasRelevantOriginatedRoute(conf, proto);
                            if (isNotRoot) {
                                for (GraphEdge e : _graph.getEdgeMap().get(router)) {
                                    if (hasExportVariables(e, proto)) {
                                        edges.add(e);
                                    }
                                }
                            }
                        }
                    }
                    map.put(proto, edges);
                }
            });
        }

        private void computeOptimizations() {
            _hasEnvironment = computeHasEnvironment();
            _keepLocalPref = computeKeepLocalPref();
            _keepAdminDist = computeKeepAdminDistance();
            _keepMed = computeKeepMed();
            initProtocols(_graph.getConfigurations());
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

        boolean getKeepPrefix() {
            return !Optimizations.ENABLE_PREFIX_ELIMINATION;
        }

        boolean getKeepLocalPref() {
            return _keepLocalPref;
        }

        boolean getKeepAdminDist() {
            return _keepAdminDist;
        }

        boolean getKeepMed() {
            return _keepMed;
        }

    }


    private static final boolean ENABLE_DEBUGGING = true;
    private static final int BITS = 0;
    private static final int DEFAULT_CISCO_VLAN_OSPF_COST = 1;
    private static final String BGP_NETWORK_FILTER_LIST_NAME = "BGP_NETWORK_NETWORKS_FILTER";
    private static final String BGP_COMMON_FILTER_LIST_NAME = "BGP_COMMON_EXPORT_POLICY";
    private static final String BGP_AGGREGATE_FILTER_LIST_NAME = "BGP_AGGREGATE_NETWORKS_FILTER";

    private Graph _graph;

    private Map<String, List<RoutingProtocol>> _protocols;
    private Map<String, EnumMap<RoutingProtocol, EnumMap<RoutingProtocol, LogicalRedistributionEdge>>> _redistributionEdges;
    private Map<String, EnumMap<RoutingProtocol, List<ArrayList<LogicalGraphEdge>>>> _edgeVariableMap;
    private Map<String, EnumMap<RoutingProtocol, EdgeVars>> _bestNeighborPerProtocol;
    private Map<String, EdgeVars> _bestNeighbor;
    private Map<String, EnumMap<RoutingProtocol, Map<LogicalEdge, BoolExpr>>> _choiceVariables;
    private Map<String, Map<GraphEdge, BoolExpr>> _controlForwarding;
    private Map<String, Map<GraphEdge, BoolExpr>> _dataForwarding;

    private Map<LogicalGraphEdge, LogicalGraphEdge> _otherEnd;
    private Map<LogicalGraphEdge, EdgeVars> _environmentVars;
    private Map<GraphEdge, BgpNeighbor> _bgpNeighbors;
    private List<Expr> _allVariables;
    private List<EdgeVars> _allEdgeVars;

    private Optimizations _optimizations;

    private Context _ctx;
    private Solver _solver;
    private List<Prefix> _destinations;

    private ArithExpr _dstIp;
    private ArithExpr _srcIp;
    private ArithExpr _dstPort;
    private ArithExpr _srcPort;
    private ArithExpr _icmpCode;
    private ArithExpr _icmpType;
    private BoolExpr _tcpAck;
    private BoolExpr _tcpCwr;
    private BoolExpr _tcpEce;
    private BoolExpr _tcpFin;
    private BoolExpr _tcpPsh;
    private BoolExpr _tcpRst;
    private BoolExpr _tcpSyn;
    private BoolExpr _tcpUrg;
    private ArithExpr _ipProtocol;

    // Debugging information for tracking assertions for unsat core
    private Map<String, BoolExpr> _trackingVars;
    private int _trackingNum;



    public Encoder(IBatfish batfish, List<Prefix> destinations) {
        this(destinations, new Graph(batfish));
    }

    public Encoder(List<Prefix> destinations, Graph graph) {
        this(destinations, graph, null, null, null);
    }

    public Encoder(Encoder e, Graph graph) {
        this(e.getDestinations(), graph, e.getCtx(), e.getSolver(), e.getAllVariables());
    }

    private Encoder(List<Prefix> destinations, Graph graph, Context ctx, Solver solver, List<Expr> vars) {
        HashMap<String, String> cfg = new HashMap<>();

        // Allow for unsat core when debugging
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
                // Tactic t3 = _ctx.mkTactic("normalize-bounds");
                // Tactic t4 = _ctx.mkTactic("lia2pb");
                Tactic t5 = _ctx.mkTactic("smt");
                Tactic t = _ctx.then(t1, t2, t5);
                _solver = _ctx.mkSolver(t);
            }
        } else {
            _solver = solver;
        }

        _destinations = destinations;

        _dstIp = _ctx.mkIntConst("dst-ip");
        _srcIp = _ctx.mkIntConst("src-ip");
        _dstPort = _ctx.mkIntConst("dst-port");
        _srcPort = _ctx.mkIntConst("src-port");
        _icmpCode = _ctx.mkIntConst("icmp-code");
        _icmpType = _ctx.mkIntConst("icmp-type");
        _tcpAck = _ctx.mkBoolConst("tcp-ack");
        _tcpCwr = _ctx.mkBoolConst("tcp-cwr");
        _tcpEce = _ctx.mkBoolConst("tcp-ece");
        _tcpFin = _ctx.mkBoolConst("tcp-fin");
        _tcpPsh = _ctx.mkBoolConst("tcp-psh");
        _tcpRst = _ctx.mkBoolConst("tcp-rst");
        _tcpSyn = _ctx.mkBoolConst("tcp-syn");
        _tcpUrg = _ctx.mkBoolConst("tcp-urg");
        _ipProtocol = _ctx.mkIntConst("ip-protocol");

        _graph = graph;
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
        _environmentVars = new HashMap<>();
        _bgpNeighbors = new HashMap<>();

        _allEdgeVars = new ArrayList<>();

        if (vars == null) {
            _allVariables = new ArrayList<>();
            _allVariables.add(_dstIp);
            _allVariables.add(_srcIp);
            _allVariables.add(_dstPort);
            _allVariables.add(_srcPort);
            _allVariables.add(_icmpCode);
            _allVariables.add(_icmpType);

            _allVariables.add(_tcpAck);
            _allVariables.add(_tcpCwr);
            _allVariables.add(_tcpEce);
            _allVariables.add(_tcpFin);
            _allVariables.add(_tcpPsh);
            _allVariables.add(_tcpRst);
            _allVariables.add(_tcpSyn);
            _allVariables.add(_tcpUrg);
            _allVariables.add(_ipProtocol);
        } else {
            _allVariables = vars;
        }

        _trackingVars = new HashMap<>();
        _trackingNum = 0;

    }

    public Graph getGraph() {
        return _graph;
    }

    public Map<String, List<RoutingProtocol>> getProtocols() {
        return _protocols;
    }

    public Map<String, EnumMap<RoutingProtocol, EnumMap<RoutingProtocol, LogicalRedistributionEdge>>> getRedistributionEdges() {
        return _redistributionEdges;
    }

    public Map<String, EnumMap<RoutingProtocol, List<ArrayList<LogicalGraphEdge>>>> getEdgeVariableMap() {
        return _edgeVariableMap;
    }

    public Map<String, EnumMap<RoutingProtocol, EdgeVars>> getBestNeighborPerProtocol() {
        return _bestNeighborPerProtocol;
    }

    public Map<String, EdgeVars> getBestNeighbor() {
        return _bestNeighbor;
    }

    public Map<String, EnumMap<RoutingProtocol, Map<LogicalEdge, BoolExpr>>> getChoiceVariables() {
        return _choiceVariables;
    }

    public Map<String, Map<GraphEdge, BoolExpr>> getControlForwarding() {
        return _controlForwarding;
    }

    public Map<String, Map<GraphEdge, BoolExpr>> getDataForwarding() {
        return _dataForwarding;
    }

    public Map<LogicalGraphEdge, LogicalGraphEdge> getOtherEnd() {
        return _otherEnd;
    }

    public Map<LogicalGraphEdge, EdgeVars> getEnvironmentVars() {
        return _environmentVars;
    }

    public Map<GraphEdge, BgpNeighbor> getBgpNeighbors() {
        return _bgpNeighbors;
    }

    public List<Expr> getAllVariables() {
        return _allVariables;
    }

    public List<EdgeVars> getAllEdgeVars() {
        return _allEdgeVars;
    }

    public Optimizations getOptimizations() {
        return _optimizations;
    }

    public Context getCtx() {
        return _ctx;
    }

    public Solver getSolver() {
        return _solver;
    }

    public List<Prefix> getDestinations() {
        return _destinations;
    }

    public ArithExpr getDstIp() {
        return _dstIp;
    }

    public ArithExpr getSrcIp() {
        return _srcIp;
    }

    public ArithExpr getDstPort() {
        return _dstPort;
    }

    public ArithExpr getSrcPort() {
        return _srcPort;
    }

    public ArithExpr getIcmpCode() {
        return _icmpCode;
    }

    public ArithExpr getIcmpType() {
        return _icmpType;
    }


    public Map<String, BoolExpr> getTrackingVars() {
        return _trackingVars;
    }

    private void add(BoolExpr e) {
        BoolExpr be = (BoolExpr) e; //.simplify();
        String name = "Pred" + _trackingNum;
        _trackingNum = _trackingNum + 1;
        _trackingVars.put(name, be);
        // System.out.println("Tracking var: " + name);
        _solver.assertAndTrack(be, _ctx.mkBoolConst(name));
        // _solver.add(be);
    }

    public boolean overlaps(Prefix p1, Prefix p2) {
        long l1 = p1.getNetworkPrefix().getAddress().asLong();
        long l2 = p2.getNetworkPrefix().getAddress().asLong();
        long u1 = p1.getNetworkPrefix().getEndAddress().asLong();
        long u2 = p2.getNetworkPrefix().getEndAddress().asLong();
        return (l1 >= l2 && l1 <= u2) ||
                (u1 <= u2 && u1 >= l2) ||
                (u2 >= l1 && u2 <= u1) ||
                (l2 >= l1 && l2 <= u1);
    }

    private void addExprs(EdgeVars e) {
        _allVariables.add(e.getPermitted());

        if (e.getPrefix() != null) {
            _allVariables.add(e.getPrefix());
        }
        if (e.getAdminDist() != null) {
            _allVariables.add(e.getAdminDist());
        }
        if (e.getMed() != null) {
            _allVariables.add(e.getMed());
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
        if (e.getRouterId() != null) {
            _allVariables.add(e.getRouterId());
        }
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
        } else if (e instanceof Not) {
            Not n = (Not) e;
            visit(n.getExpr(), fs, fe);
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

    private List<RoutingProtocol> findRedistributedProtocols(RoutingPolicy pol, RoutingProtocol proto) {
        List<RoutingProtocol> ps = new ArrayList<>();
        visit(pol.getStatements(), s -> {}, e -> {
            if (e instanceof MatchProtocol) {
                MatchProtocol mp = (MatchProtocol) e;
                if (mp.getProtocol() != proto) {
                    ps.add(mp.getProtocol());
                }
            }
        });
        return ps;
    }

    private RoutingPolicy findImportRoutingPolicy(Configuration conf, RoutingProtocol proto, LogicalGraphEdge e) {
        if (proto == RoutingProtocol.CONNECTED) {
            return null;
        }
        if (proto == RoutingProtocol.STATIC) {
            return null;
        }
        if (proto == RoutingProtocol.OSPF) {
            return null;
        }
        if (proto == RoutingProtocol.BGP) {
            BgpNeighbor n = _bgpNeighbors.get(e.getEdge());
            if (n == null || n.getImportPolicy() == null) {
                return null;
            }
            return conf.getRoutingPolicies().get(n.getImportPolicy());
        }
        throw new BatfishException("TODO: findImportRoutingPolicy: " + proto.protocolName());
    }

    private RoutingPolicy findExportRoutingPolicy(Configuration conf, RoutingProtocol proto, LogicalGraphEdge e) {
        if (proto == RoutingProtocol.CONNECTED) {
            return null;
        }
        if (proto == RoutingProtocol.STATIC) {
            return null;
        }
        if (proto == RoutingProtocol.OSPF) {
            String exp = conf.getDefaultVrf().getOspfProcess().getExportPolicy();
            return conf.getRoutingPolicies().get(exp);
        }
        if (proto == RoutingProtocol.BGP) {
            BgpNeighbor n = _bgpNeighbors.get(e.getEdge());

            // if no neighbor (e.g., loopback), or no export policy
            if (n == null || n.getExportPolicy() == null) {
                return null;
            }
            return conf.getRoutingPolicies().get(n.getExportPolicy());
        }
        throw new BatfishException("TODO: findExportRoutingPolicy for " + proto.protocolName());
    }

    private RoutingPolicy findCommonRoutingPolicy(Configuration conf, RoutingProtocol proto) {
        if (proto == RoutingProtocol.OSPF) {
            String exp = conf.getDefaultVrf().getOspfProcess().getExportPolicy();
            return conf.getRoutingPolicies().get(exp);
        }
        if (proto == RoutingProtocol.BGP) {
            for (Map.Entry<String, RoutingPolicy> entry : conf.getRoutingPolicies().entrySet()) {
                String name = entry.getKey();
                if (name.contains(BGP_COMMON_FILTER_LIST_NAME)) {
                    return entry.getValue();
                }
            }
            return null;
        }
        if (proto == RoutingProtocol.STATIC) {
            return null;
        }
        if (proto == RoutingProtocol.CONNECTED) {
            return null;
        }
        throw new BatfishException("TODO: findCommonRoutingPolicy for " + proto.protocolName());
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

                    String chName = "choice_" + e.getEdgeVars().getName();
                    BoolExpr choiceVar = _ctx.mkBoolConst(chName);
                    _allVariables.add(choiceVar);
                    edgeMap.put(e, choiceVar);

                }
            }
        });
    }

    private void buildEdgeMap() {
        _graph.getEdgeMap().forEach((router,edges) -> {
            EnumMap<RoutingProtocol, List<ArrayList<LogicalGraphEdge>>> map = new EnumMap<>(RoutingProtocol.class);
            for (RoutingProtocol p : _protocols.get(router)) {
                map.put(p, new ArrayList<>());
            }
            _edgeVariableMap.put(router, map);
        });
    }

    private void addForwardingVariables() {
        // add control plane, data plane
        _graph.getEdgeMap().forEach((router,edges) -> {
            Map<GraphEdge, BoolExpr> cForwarding = new HashMap<>();
            Map<GraphEdge, BoolExpr> dForwarding = new HashMap<>();
            for (GraphEdge edge : edges) {
                String iface = edge.getStart().getName();
                String cName = "control-forwarding_" + router + "_" + iface;
                BoolExpr cForward = _ctx.mkBoolConst(cName);
                _allVariables.add(cForward);
                cForwarding.put(edge, cForward);

                String dName = "data-forwarding_" + router + "_" + iface;
                BoolExpr dForward = _ctx.mkBoolConst(dName);
                _allVariables.add(dForward);
                dForwarding.put(edge, dForward);

            }
            _controlForwarding.put(router, cForwarding);
            _dataForwarding.put(router, dForwarding);
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
                                EdgeVars ev2 = new EdgeVars(router, proto.protocolName(), ifaceName, len, "IMPORT");
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

        //_otherEnd.forEach((e1,e2) -> {
        //    System.out.println("START: " + e1.getEdgeVars());
        //    System.out.println("END:   " + e2.getEdgeVars());
        //    System.out.println("");
        //});

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
                RoutingPolicy pol = findCommonRoutingPolicy(conf, proto);
                if (pol != null) {
                    List<RoutingProtocol> ps = findRedistributedProtocols(pol, proto);
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

    private void computeBgpNeighbors() {
        List<Ip> ips = new ArrayList<>();
        List<BgpNeighbor> neighbors = new ArrayList<>();

        _graph.getConfigurations().forEach((router,conf) -> {
            if (conf.getDefaultVrf().getBgpProcess() != null) {
                conf.getDefaultVrf().getBgpProcess().getNeighbors().forEach((pfx, neighbor) -> {
                    ips.add(neighbor.getAddress());
                    neighbors.add(neighbor);
                });
            }
        });

        _graph.getConfigurations().forEach((router,conf) -> {
            if (conf.getDefaultVrf().getBgpProcess() != null) {
                _graph.getEdgeMap().get(router).forEach(ge -> {
                    for (int i = 0; i < ips.size(); i++) {
                        Ip ip = ips.get(i);
                        BgpNeighbor n = neighbors.get(i);
                        if (ge.getStart().getPrefix().contains(ip)) {
                            _bgpNeighbors.put(ge, n);
                        }
                    }
                });
            }
        });
    }

    private void computeOptimizations() {
        _optimizations.computeOptimizations();
    }

    private void addEnvironmentVariables() {
        _graph.getConfigurations().forEach((router, conf) -> {
            for (RoutingProtocol proto : _protocols.get(router)) {
                if (proto == RoutingProtocol.BGP) {
                    _edgeVariableMap.get(router).get(proto).forEach(eList -> {
                        eList.forEach(e -> {
                            if (e.getEdgeType() == EdgeType.IMPORT) {
                                BgpNeighbor n = _bgpNeighbors.get(e.getEdge());
                                if (n != null && e.getEdge().getEnd() == null) {
                                    String address;
                                    if (n.getAddress() == null) {
                                        address = "null";
                                    } else {
                                        address = n.getAddress().toString();
                                    }

                                    EdgeVars vars = new EdgeVars(router, proto, "ENV", _optimizations, address, _ctx, 0, "EXPORT", false);
                                    addExprs(vars);
                                    _allEdgeVars.add(vars);
                                    _environmentVars.put(e, vars);
                                }
                            }
                        });
                    });
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
        buildEdgeMap();
        addForwardingVariables();
        addBestVariables();
        addEdgeVariables();
        addRedistributionEdgeVariables();
        addChoiceVariables();
        addEnvironmentVariables();
    }

    private void addLowerBoundConstraints() {

        ArithExpr upperBound4 = _ctx.mkInt( (long) Math.pow(2,4) );
        ArithExpr upperBound8 = _ctx.mkInt( (long) Math.pow(2,8) );
        ArithExpr upperBound16 = _ctx.mkInt( (long) Math.pow(2,16) );
        ArithExpr upperBound32 = _ctx.mkInt( (long) Math.pow(2,32) );
        ArithExpr zero = _ctx.mkInt(0);

        // Valid 32 bit integers
        add(_ctx.mkGe(_dstIp, zero));
        add(_ctx.mkGe(_srcIp, zero));
        add(_ctx.mkLt(_dstIp, upperBound32));
        add(_ctx.mkLt(_srcIp, upperBound32));

        // Valid 16 bit integer
        add(_ctx.mkGe(_dstPort,zero));
        add(_ctx.mkGe(_srcPort,zero));
        add(_ctx.mkLt(_dstPort,upperBound16));
        add(_ctx.mkLt(_srcPort,upperBound16));

        // Valid 8 bit integer
        add(_ctx.mkGe(_icmpType, zero));
        add(_ctx.mkGe(_ipProtocol,zero));
        add(_ctx.mkLt(_icmpType, upperBound8));
        add(_ctx.mkLt(_ipProtocol,upperBound8));

        // Valid 4 bit integer
        add(_ctx.mkGe(_icmpCode, zero));
        add(_ctx.mkLt(_icmpCode, upperBound4));

        for (EdgeVars e : _allEdgeVars) {
            if (e.getAdminDist() != null) {
                add(_ctx.mkGe(e.getAdminDist(), zero));
                //_solver.add(_ctx.mkLe(e.getAdminDist(), _ctx.mkInt(200)));
            }
            if (e.getMed() != null) {
                add(_ctx.mkGe(e.getMed(), zero));
                //_solver.add(_ctx.mkLe(e.getMed(), _ctx.mkInt(100)));
            }
            if (e.getLocalPref() != null) {
                add(_ctx.mkGe(e.getLocalPref(), zero));
                //_solver.add(_ctx.mkLe(e.getLocalPref(), _ctx.mkInt(100)));
            }
            if (e.getMetric() != null) {
                add(_ctx.mkGe(e.getMetric(), zero));
                //_solver.add(_ctx.mkLe(e.getMetric(), _ctx.mkInt(200)));
            }
            if (e.getPrefixLength() != null) {
                add(_ctx.mkGe(e.getPrefixLength(), zero));
                add(_ctx.mkLe(e.getPrefixLength(), _ctx.mkInt(32)));
            }
            //if (e.getRouterId() != null) {
            //    _solver.add(_ctx.mkGe(e.getRouterId(), zero));
            //    _solver.add(_ctx.mkLe(e.getRouterId(), _ctx.mkInt(upperBound)));
            //}
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

    private BoolExpr firstBitsEqual(ArithExpr x, long y, int n) {
        assert(n >= 0 && n <= 32);
        if (n == 0) {
            return _ctx.mkBool(true);
        }
        long bound = (long) Math.pow(2,32-n);
        ArithExpr upperBound = _ctx.mkInt(y + bound);
        // ArithExpr lowerBound = _ctx.mkInt(-bound);
        // ArithExpr diff = _ctx.mkSub(x,y);
        return _ctx.mkAnd(_ctx.mkGe(x, _ctx.mkInt(y)), _ctx.mkLt(x, upperBound));
    }

    private BoolExpr isRelevantFor(EdgeVars vars, PrefixRange range) {
        Prefix p = range.getPrefix();
        SubRange r = range.getLengthRange();
        long pfx = p.getNetworkAddress().asLong();
        int len = p.getPrefixLength();
        int lower = r.getStart();
        int upper = r.getEnd();

        // well formed prefix
        assert(p.getPrefixLength() < lower && lower <= upper);

        BoolExpr lowerBitsMatch = firstBitsEqual(_dstIp, pfx, len);
        if (lower == upper) {
            BoolExpr equalLen = _ctx.mkEq(vars.getPrefixLength(), _ctx.mkInt(lower));
            return _ctx.mkAnd( equalLen, lowerBitsMatch );
        } else {
            BoolExpr lengthLowerBound = _ctx.mkGe(vars.getPrefixLength(), _ctx.mkInt(lower));
            BoolExpr lengthUpperBound = _ctx.mkLe(vars.getPrefixLength(), _ctx.mkInt(upper));
            return _ctx.mkAnd( lengthLowerBound, lengthUpperBound, lowerBitsMatch );
        }
    }

    private BoolExpr matchFilterList(EdgeVars other, RouteFilterList x) {
        BoolExpr acc = _ctx.mkBool(false);

        List<RouteFilterLine> lines = new ArrayList<>(x.getLines());
        Collections.reverse(lines);

        for (RouteFilterLine line : lines) {
            Prefix p = line.getPrefix();
            SubRange r = line.getLengthRange();
            PrefixRange range = new PrefixRange(p, r);
            BoolExpr matches = isRelevantFor(other, range);

            switch (line.getAction()) {
                case ACCEPT:
                    acc = If(matches, _ctx.mkBool(true), acc);
                    break;

                case REJECT:
                    acc = If(matches, _ctx.mkBool(false), acc);
                    break;
            }
        }
        return acc;
    }

    private BoolExpr matchPrefixSet(Configuration conf, EdgeVars other, PrefixSetExpr e) {
        if (e instanceof ExplicitPrefixSet) {
            ExplicitPrefixSet x = (ExplicitPrefixSet) e;

            Set<PrefixRange> ranges = x.getPrefixSpace().getPrefixRanges();
            if (ranges.isEmpty()) {
                return _ctx.mkBool(true);
            }

            BoolExpr acc = _ctx.mkBool(false);
            for (PrefixRange range : ranges) {
                acc = _ctx.mkOr(acc, isRelevantFor(other, range));
            }
            return acc;

        } else if (e instanceof NamedPrefixSet) {
            NamedPrefixSet x = (NamedPrefixSet) e;
            String name = x.getName();
            RouteFilterList fl = conf.getRouteFilterLists().get(name);
            return matchFilterList(other, fl);

        } else {
            throw new BatfishException("TODO: match prefix set: " + e);
        }
    }

    private BoolExpr computeTransferFunction(EdgeVars other, EdgeVars current, Configuration conf, RoutingProtocol to, RoutingProtocol from, Modifications mods, BooleanExpr expr, Integer addedCost, boolean inCall) {

        if (expr instanceof Conjunction) {
            Conjunction c = (Conjunction) expr;
            if (c.getConjuncts().size() == 0) {
                return _ctx.mkBool(false);
            }
            BoolExpr v = _ctx.mkBool(true);
            for (BooleanExpr x : c.getConjuncts()) {
                v = _ctx.mkAnd(v, computeTransferFunction(other, current, conf, to, from, mods, x, addedCost, inCall));
            }
            return v;
        }
        if (expr instanceof Disjunction) {
            Disjunction d = (Disjunction) expr;
            if (d.getDisjuncts().size() == 0) {
                return _ctx.mkBool(true);
            }
            BoolExpr v = _ctx.mkBool(false);
            for (BooleanExpr x : d.getDisjuncts()) {
                v = _ctx.mkOr(v, computeTransferFunction(other, current, conf, to, from, mods, x, addedCost, inCall));
            }
            return v;
        }
        if (expr instanceof  Not) {
            Not n = (Not) expr;
            BoolExpr v = computeTransferFunction(other, current, conf, to, from, mods, n.getExpr(), addedCost, inCall);
            return _ctx.mkNot(v);
        }
        if (expr instanceof MatchProtocol) {
            // TODO: is this right?
            MatchProtocol mp = (MatchProtocol) expr;
            return _ctx.mkBool(mp.getProtocol() == from);
        }
        if (expr instanceof MatchPrefixSet) {
            MatchPrefixSet m = (MatchPrefixSet) expr;
            return matchPrefixSet(conf, other, m.getPrefixSet());
        }
        if (expr instanceof CallExpr) {
            CallExpr c = (CallExpr) expr;
            String name = c.getCalledPolicyName();
            RoutingPolicy pol = conf.getRoutingPolicies().get(name);

            // TODO: we really need some sort of SSA form
            // TODO: modifications will not be kept because it depends on the branch choosen
            // Do not copy modifications to keep
            return computeTransferFunction(other, current, conf, to, from, mods, pol.getStatements(), addedCost, true);
        }
        if (expr instanceof WithEnvironmentExpr) {
            // TODO: this is not correct
            WithEnvironmentExpr we = (WithEnvironmentExpr) expr;
            return computeTransferFunction(other, current, conf, to, from, mods, we.getExpr(), addedCost, inCall);
        }

        throw new BatfishException("TODO: compute expr transfer function: " + expr);
    }

    private ArithExpr getOrDefault(ArithExpr x, ArithExpr d) {
        if (x != null) {
            return x;
        }
        return d;
    }

    private ArithExpr applyIntExprModification(ArithExpr x, IntExpr e) {
        if (e instanceof LiteralInt) {
            LiteralInt z = (LiteralInt) e;
            return _ctx.mkInt(z.getValue());
        }
        if (e instanceof DecrementMetric) {
            DecrementMetric z = (DecrementMetric) e;
            return _ctx.mkSub(x, _ctx.mkInt(z.getSubtrahend()));
        }
        if (e instanceof IncrementMetric) {
            IncrementMetric z = (IncrementMetric) e;
            return _ctx.mkAdd(x, _ctx.mkInt(z.getAddend()));
        }
        if (e instanceof IncrementLocalPreference) {
            IncrementLocalPreference z = (IncrementLocalPreference) e;
            return _ctx.mkAdd(x, _ctx.mkInt(z.getAddend()));
        }
        if (e instanceof DecrementLocalPreference) {
            DecrementLocalPreference z = (DecrementLocalPreference) e;
            return _ctx.mkSub(x, _ctx.mkInt(z.getSubtrahend()));
        }
        throw new BatfishException("TODO: int expr transfer function: " + e);
    }


    private BoolExpr applyModifications(Configuration conf, RoutingProtocol to, RoutingProtocol from, Modifications mods, EdgeVars current, EdgeVars other, Integer addedCost) {
        ArithExpr defaultLen = _ctx.mkInt(defaultLength(from));
        ArithExpr defaultAd = _ctx.mkInt(defaultAdminDistance(conf, from));
        ArithExpr defaultMed = _ctx.mkInt(defaultMed(from));
        ArithExpr defaultLp = _ctx.mkInt(defaultLocalPref(from));
        ArithExpr defaultId = _ctx.mkInt(defaultId(from));
        ArithExpr defaultMet = _ctx.mkInt(defaultMetric(from));
        BitVecExpr defaultPrefix = _ctx.mkBV(0,32);

        BoolExpr met;
        ArithExpr otherMet = getOrDefault(other.getMetric(), defaultMet);
        if (mods.getSetMetric() == null) {
            met = safeEqAdd(current.getMetric(), otherMet, addedCost);
        } else {
            IntExpr ie = mods.getSetMetric().getMetric();
            ArithExpr val = applyIntExprModification(otherMet, ie);
            met = safeEqAdd(current.getMetric(), val, addedCost);
        }

        BoolExpr lp;
        ArithExpr otherLp = getOrDefault(other.getLocalPref(), defaultLp);
        if (mods.getSetLp() == null) {
            lp = safeEq(current.getLocalPref(), otherLp);
        } else {
            IntExpr ie = mods.getSetLp().getLocalPreference();
            lp = safeEq(current.getLocalPref(), applyIntExprModification(otherLp, ie));
        }

        BoolExpr per = safeEq(current.getPermitted(), other.getPermitted());
        BoolExpr len = safeEq(current.getPrefixLength(), getOrDefault(other.getPrefixLength(), defaultLen));
        BoolExpr id = safeEq(current.getRouterId(), getOrDefault(other.getRouterId(), defaultId));

        // TODO: handle AD correctly
        // TODO: handle MED correctly
        // TODO: what about transitivity?
        // TODO: communities are transmitted to neighbors?
        return _ctx.mkAnd(
                per,
                len,
                safeEq(current.getPrefix(), (other.getPrefix() == null ? defaultPrefix : other.getPrefix())),
                safeEq(current.getAdminDist(), (other.getAdminDist() == null ? defaultAd : other.getAdminDist() )),
                safeEq(current.getMed(), (other.getMed() == null ? defaultMed : other.getMed())),
                lp,
                met,
                id);

    }

    private BoolExpr computeTransferFunction(
            EdgeVars other, EdgeVars current, Configuration conf,
            RoutingProtocol to, RoutingProtocol from, Modifications mods,
            List<Statement> statements, Integer addedCost, boolean inCall) {

        ListIterator<Statement> it = statements.listIterator();
        while (it.hasNext()) {
            Statement s = it.next();

            if (s instanceof Statements.StaticStatement) {
                Statements.StaticStatement ss = (Statements.StaticStatement) s;
                if (ss.getType() == ExitAccept) {
                    return applyModifications(conf, to, from, mods, current, other, addedCost);
                }
                else if (ss.getType() == ExitReject) {
                    return _ctx.mkNot(current.getPermitted());
                }
                else if (ss.getType() == ReturnTrue) {
                    if (inCall) {
                        return _ctx.mkBool(true);
                    } else {
                        return applyModifications(conf, to, from, mods, current, other, addedCost);
                    }
                }
                else if (ss.getType() == ReturnFalse) {
                    if (inCall) {
                        return _ctx.mkBool(false);
                    } else {
                        return _ctx.mkNot(current.getPermitted());
                    }
                }
                else if (ss.getType() == SetDefaultActionAccept) {
                    mods.addModification(s);
                }
                else if (ss.getType() == SetDefaultActionReject) {
                    mods.addModification(s);
                }
                // TODO: need to set local default action in an environment
                else if (ss.getType() == ReturnLocalDefaultAction) {
                    return _ctx.mkBool(false);
                }

                else {
                    throw new BatfishException("TODO: computeTransferFunction: " + ss.getType());
                }
            }

            else if (s instanceof If) {
                If i = (If) s;
                List<Statement> remainingx = new ArrayList<>(i.getTrueStatements());
                List<Statement> remainingy = new ArrayList<>(i.getFalseStatements());

                // Copy the remaining statements along both branches
                if (it.hasNext()) {
                    ListIterator<Statement> ix = statements.listIterator(it.nextIndex());
                    ListIterator<Statement> iy = statements.listIterator(it.nextIndex());
                    while (ix.hasNext()) {
                        remainingx.add(ix.next());
                        remainingy.add(iy.next());
                    }
                }

                Modifications modsTrue = new Modifications(mods);
                Modifications modsFalse = new Modifications(mods);
                BoolExpr guard = computeTransferFunction(other, current, conf, to, from, mods, i.getGuard(), addedCost, inCall);
                BoolExpr trueBranch = computeTransferFunction(other, current, conf, to, from, modsTrue, remainingx, addedCost, inCall);
                BoolExpr falseBranch = computeTransferFunction(other, current, conf, to, from, modsFalse, remainingy, addedCost, inCall);
                return If(guard, trueBranch, falseBranch);

            } else if (s instanceof SetOspfMetricType || s instanceof SetMetric) {
                mods.addModification(s);

            } else {
                throw new BatfishException("TODO: statement transfer function: " + s);
            }
        }

        if (mods.getDefaultAccept()) {
            return applyModifications(conf, to, from, mods, current, other, addedCost);
        } else {
            return _ctx.mkNot(current.getPermitted());
        }
    }


    private BoolExpr computeTransferFunction(EdgeVars other, EdgeVars current, Configuration conf, RoutingProtocol to, RoutingProtocol from, List<Statement> statements, Integer addedCost) {
        return computeTransferFunction(other, current, conf, to, from, new Modifications(), statements, addedCost, false);
    }


    private BoolExpr transferFunction(EdgeVars other, EdgeVars current, RoutingPolicy pol, Configuration conf, RoutingProtocol to, RoutingProtocol from) {
        if (ENABLE_DEBUGGING) {
            System.out.println("------ REDISTRIBUTION ------");
            System.out.println("From: " + to.protocolName());
            System.out.println("To: " + from.protocolName());
        }
        /* if (ENABLE_DEBUGGING) {
            System.out.println("Transfer function for " + conf.getName());
            System.out.println(transfunc.simplify());
            System.out.println("-----------------------------");
        } */
        return computeTransferFunction(other, current, conf, to, from, pol.getStatements(), null);
    }


    private void addRedistributionConstraints() {
        _graph.getConfigurations().forEach((router, conf) -> {
            for (RoutingProtocol proto : _protocols.get(router)) {
                RoutingPolicy pol = findCommonRoutingPolicy(conf, proto);
                if (pol != null) {
                    EnumMap<RoutingProtocol, LogicalRedistributionEdge> map = _redistributionEdges.get(router).get(proto);
                    map.forEach((fromProto, vars) -> {
                        EdgeVars current = vars.getEdgeVars();
                        EdgeVars other = _bestNeighborPerProtocol.get(router).get(fromProto);
                        BoolExpr be = transferFunction(other, current, pol, conf, proto, fromProto);
                        add(be);
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
        if (conf.getDefaultVrf().getOspfProcess() != null) {
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
                                        (int) (conf.getDefaultVrf().getOspfProcess().getReferenceBandwidth()
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


    private BoolExpr isRelevantFor(Prefix p, ArithExpr ae) {
        long pfx = p.getNetworkAddress().asLong();
        return firstBitsEqual(ae, pfx,  p.getPrefixLength());
    }


    public List<Prefix> getOriginatedNetworks(Configuration conf, RoutingProtocol proto) {
        List<Prefix> acc = new ArrayList<>();

        if (proto == RoutingProtocol.OSPF) {
            conf.getDefaultVrf().getOspfProcess().getAreas().forEach((areaID, area) -> {
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
            conf.getInterfaces().forEach((name,iface) -> {
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

        throw new BatfishException("TODO: getOriginatedNetworks: " + proto.protocolName());

    }

    private boolean isInterfaceUsed(Configuration conf, RoutingProtocol proto, Interface iface) {
        if (proto == RoutingProtocol.STATIC) {
            List<StaticRoute> srs = _graph.getStaticRoutes().get(conf.getName()).get(iface.getName());
            return iface.getActive() && srs != null && srs.size() > 0;
        }
        return true;
    }

    private BoolExpr If(BoolExpr cond, BoolExpr case1, BoolExpr case2) {
        // return _ctx.mkAnd(_ctx.mkImplies(cond, case1), _ctx.mkImplies(_ctx.mkNot(cond), case2));
        return (BoolExpr) _ctx.mkITE(cond, case1, case2);
    }

    private BoolExpr safeEq(Expr x, Expr value) {
        if (x == null) {
            return _ctx.mkBool(true);
        }
        return _ctx.mkEq(x, value);
    }

    private BoolExpr safeEqAdd(ArithExpr x, ArithExpr value, Integer cost) {
        if (x == null) {
            return _ctx.mkBool(true);
        }
        if (cost == null) {
            return _ctx.mkEq(x, value);
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

    private int defaultMed(RoutingProtocol proto) {
        if (proto == RoutingProtocol.BGP) {
            return 100;
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
            return true;
        }
    }

    private EdgeVars correctVars(LogicalEdge e) {
        if (e instanceof LogicalGraphEdge) {
            EdgeVars vars = e.getEdgeVars();
            if (!vars.getIsUsed()) {
                return _otherEnd.get(e).getEdgeVars();
            }
            return vars;
        } else {
            return e.getEdgeVars();
        }
    }


    private long routerId(Configuration conf, RoutingProtocol proto) {
        if (proto == RoutingProtocol.BGP) {
            return conf.getDefaultVrf().getBgpProcess().getRouterId().asLong();
        }
        if (proto == RoutingProtocol.OSPF) {
            return conf.getDefaultVrf().getOspfProcess().getRouterId().asLong();
        } else {
            return 0;
        }
    }

    private Long findRouterId(LogicalEdge e, RoutingProtocol proto) {
        if (e instanceof LogicalGraphEdge) {
            LogicalGraphEdge lge = (LogicalGraphEdge) e;
            LogicalGraphEdge lgeOther = _otherEnd.get(lge);

            if (lgeOther != null) {
                String peer = lgeOther.getEdge().getRouter();
                Configuration peerConf = _graph.getConfigurations().get(peer);
                return routerId(peerConf, proto);
            }

            BgpNeighbor n = _bgpNeighbors.get(lge.getEdge());
            if (n != null && n.getAddress() != null) {
                return n.getAddress().asLong();
            }

            return null;

        } else {
            return null;
        }
    }

    private BoolExpr equalHelper(ArithExpr best, ArithExpr vars, ArithExpr defaultVal) {
        BoolExpr tru = _ctx.mkBool(true);
        if (vars == null) {
            if (best != null) {
                return _ctx.mkEq(best, defaultVal);
            } else {
                return tru;
            }
        } else {
            return _ctx.mkEq(best, vars);
        }
    }

    public BoolExpr equal(Configuration conf, RoutingProtocol proto, EdgeVars best, EdgeVars vars, LogicalEdge e) {

        BoolExpr tru = _ctx.mkBool(true);

        ArithExpr defaultLocal = _ctx.mkInt(defaultLocalPref(proto));
        ArithExpr defaultAdmin = _ctx.mkInt(defaultAdminDistance(conf, proto));
        ArithExpr defaultMet = _ctx.mkInt(defaultMetric(proto));
        ArithExpr defaultMed = _ctx.mkInt(defaultMed(proto));
        ArithExpr defaultLen = _ctx.mkInt(defaultLength(proto));

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
            if (best.getRouterId() == null) {
                equalId = tru;
            } else {
                Long peerId = findRouterId(e, proto);
                if (isMultipath(conf,proto) || peerId == null) {
                    equalId = tru;
                } else {
                    equalId = _ctx.mkEq( best.getRouterId(), _ctx.mkInt(peerId) );
                }
            }
        } else {
            equalId = _ctx.mkEq( best.getRouterId(), vars.getRouterId() );
        }

        return _ctx.mkAnd(equalLen, equalAd, equalLp, equalMet, equalMed, equalId);
    }

    private BoolExpr geBetterHelper(ArithExpr best, ArithExpr vars, ArithExpr defaultVal, boolean less, boolean bestCond) {
        BoolExpr fal = _ctx.mkBool(false);
        if (vars == null) {
            if (best != null && bestCond) {
                if (less) {
                    return _ctx.mkLt(best, defaultVal);
                } else {
                    return _ctx.mkGt(best, defaultVal);
                }
            } else {
                return fal;
            }
        } else {
            if (less) {
                return _ctx.mkLt(best, vars);
            } else {
                return _ctx.mkGt(best, vars);
            }
        }
    }

    private BoolExpr geEqualHelper(ArithExpr best, ArithExpr vars, ArithExpr defaultVal, boolean bestCond) {
        BoolExpr tru = _ctx.mkBool(true);
        if (vars == null) {
            if (best != null && bestCond) {
                return _ctx.mkEq(best, defaultVal);
            } else {
                return tru;
            }
        } else {
            return _ctx.mkEq(best, vars);
        }
    }


    private BoolExpr greaterOrEqual(Configuration conf, RoutingProtocol proto, EdgeVars best, EdgeVars vars, LogicalEdge e) {

        BoolExpr tru = _ctx.mkBool(true);

        ArithExpr defaultLocal = _ctx.mkInt(defaultLocalPref(proto));
        ArithExpr defaultAdmin = _ctx.mkInt(defaultAdminDistance(conf, proto));
        ArithExpr defaultMet = _ctx.mkInt(defaultMetric(proto));
        ArithExpr defaultMed = _ctx.mkInt(defaultMed(proto));
        ArithExpr defaultLen = _ctx.mkInt(defaultLength(proto));

        BoolExpr betterLen = geBetterHelper(best.getPrefixLength(), vars.getPrefixLength(), defaultLen, false, true);
        BoolExpr equalLen = geEqualHelper(best.getPrefixLength(), vars.getPrefixLength(), defaultLen,true);

        boolean keepAd = _optimizations.getKeepAdminDist();
        BoolExpr betterAd = geBetterHelper(best.getAdminDist(), vars.getAdminDist(), defaultAdmin, true, keepAd);
        BoolExpr equalAd = geEqualHelper(best.getAdminDist(), vars.getAdminDist(), defaultAdmin, keepAd);

        boolean keepLp = _optimizations.getKeepLocalPref();
        BoolExpr betterLp = geBetterHelper(best.getLocalPref(), vars.getLocalPref(), defaultLocal, false, keepLp);
        BoolExpr equalLp = geEqualHelper(best.getLocalPref(), vars.getLocalPref(), defaultLocal, keepLp);

        BoolExpr betterMet = geBetterHelper(best.getMetric(), vars.getMetric(), defaultMet, true, true);
        BoolExpr equalMet = geEqualHelper(best.getMetric(), vars.getMetric(), defaultMet, true);

        BoolExpr betterMed = geBetterHelper(best.getMed(), vars.getMed(), defaultMed, true, true);
        BoolExpr equalMed = geEqualHelper(best.getMed(), vars.getMed(), defaultMed, true);

        BoolExpr tiebreak;
        if (vars.getRouterId() == null) {
            if (best.getRouterId() == null) {
                tiebreak = tru;
            } else {
                Long peerId = findRouterId(e, proto);
                if (isMultipath(conf, proto) || peerId == null) {
                    tiebreak = tru;
                } else {
                    tiebreak = _ctx.mkLe(best.getRouterId(), _ctx.mkInt(peerId));
                }
            }
        } else {
            tiebreak = _ctx.mkLe(best.getRouterId(), vars.getRouterId());
        }

        BoolExpr b = _ctx.mkAnd(equalMed, tiebreak);
        BoolExpr b0 = _ctx.mkOr(betterMed, b);
        BoolExpr b1 = _ctx.mkAnd(equalMet, b0);
        BoolExpr b2 = _ctx.mkOr(betterMet, b1);
        BoolExpr b3 = _ctx.mkAnd(equalLp, b2);
        BoolExpr b4 = _ctx.mkOr(betterLp, b3);
        BoolExpr b5 = _ctx.mkAnd(equalAd, b4);
        BoolExpr b6 = _ctx.mkOr(betterAd, b5);
        BoolExpr b7 = _ctx.mkAnd(equalLen, b6);
        return _ctx.mkOr(betterLen, b7);
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

                    BoolExpr val = _ctx.mkAnd(bestVars.getPermitted(), equal(conf, proto, best, bestVars, null));
                    if (acc == null) {
                        acc = val;
                    } else {
                        acc = _ctx.mkOr(acc, val);
                    }
                    add(_ctx.mkImplies(bestVars.getPermitted(), greaterOrEqual(conf, proto, best, bestVars, null)));
                }

                if (someProto) {
                    if (acc != null) {
                        add(_ctx.mkEq(somePermitted, best.getPermitted()));
                        add(_ctx.mkImplies(somePermitted, acc));
                    }
                } else {
                    add(_ctx.mkNot(best.getPermitted()));
                }
            }
        });
    }

    private Set<LogicalEdge> collectAllImportLogicalEdges(String router, RoutingProtocol proto) {
        Set<LogicalEdge> eList = new HashSet<>();
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
                        add(_ctx.mkImplies(vars.getPermitted(), greaterOrEqual(conf, proto, bestVars, vars, e)));
                    }
                }

                if (acc != null) {
                    add(_ctx.mkEq(somePermitted, bestVars.getPermitted()));
                    // best is one of the allowed ones
                    add(_ctx.mkImplies(somePermitted, acc));
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

                    /* System.out.println("Router: " + router);
                    System.out.println("Proto:  " + proto.protocolName());
                    System.out.println("Edge:   " + e.getEdgeVars().getName() + "," + e.getEdgeType() + "," + e.getPrefixLen() + "," + e.getClass());
                    if (e instanceof LogicalGraphEdge) {
                        LogicalGraphEdge lge = (LogicalGraphEdge) e;
                        System.out.println("Graph Edge: " + lge.getEdge());
                    }
                    System.out.println("Choice: " + choice.toString());
                    System.out.println("Vars:   " + vars.getName());
                    System.out.println(""); */

                    if (isEdgeUsed(conf, proto, e) && e.getEdgeType() == EdgeType.IMPORT) {
                        BoolExpr isBest = equal(conf, proto, bestVars, vars, e);

                        add( _ctx.mkEq(choice, _ctx.mkAnd(vars.getPermitted(), isBest)) );
                        /* BoolExpr falseBranch = _ctx.mkNot(choice);
                        BoolExpr trueBranch = _ctx.mkIff(choice, isBest);
                        BoolExpr val = If( vars.getPermitted(), trueBranch, falseBranch );
                        add( val ); */
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

            boolean someEdge = false;

            EdgeVars best = _bestNeighbor.get(router);
            Map<GraphEdge, BoolExpr> cfExprs = new HashMap<>();

            for (RoutingProtocol proto : _protocols.get(router)) {

                for (LogicalEdge e : collectAllImportLogicalEdges(router, proto)) {

                    if (isEdgeUsed(conf, proto, e) && e.getEdgeType() == EdgeType.IMPORT) {

                        someEdge = true;

                        EdgeVars vars = correctVars(e);
                        BoolExpr choice = _choiceVariables.get(router).get(proto).get(e);
                        BoolExpr isBest = _ctx.mkAnd( choice, equal(conf, proto, best, vars, e) );

                        if (e instanceof LogicalGraphEdge) {
                            LogicalGraphEdge lge = (LogicalGraphEdge) e;
                            GraphEdge ge = lge.getEdge();
                            BoolExpr cForward = _controlForwarding.get(router).get(ge);
                            add( _ctx.mkImplies(isBest, cForward) );

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
                                        add(_ctx.mkImplies(_ctx.mkAnd(isBest, otherProtoChoice), cForward));

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

            // Handle the case that the router has no protocol running
            if (!someEdge) {
                for (GraphEdge ge : _graph.getEdgeMap().get(router)) {
                    BoolExpr cForward = _controlForwarding.get(router).get(ge);
                    add( _ctx.mkNot(cForward) );
                }
            }
            else {
                _edgeVariableMap.get(router).forEach((proto, eList) -> {
                    eList.forEach(edges -> {
                        edges.forEach(le -> {
                            GraphEdge ge = le.getEdge();
                            BoolExpr expr = cfExprs.get(ge);
                            BoolExpr cForward = _controlForwarding.get(router).get(ge);
                            if (expr != null) {
                                add(_ctx.mkImplies(_ctx.mkNot(expr), _ctx.mkNot(cForward)));
                            } else {
                                add(_ctx.mkNot(cForward));
                            }
                        });
                    });
                });
            }
        });

    }


    private BoolExpr computeWildcardMatch(Set<IpWildcard> wcs, ArithExpr field) {
        BoolExpr acc = _ctx.mkBool(false);
        for (IpWildcard wc : wcs) {
            if (!wc.isPrefix()) {
                throw new BatfishException("ERROR: computeDstWildcards, non sequential mask detected");
            }
            acc = _ctx.mkOr(acc, isRelevantFor(wc.toPrefix(), field));
        }
        return (BoolExpr) acc.simplify();
    }

    private BoolExpr computeValidRange(Set<SubRange> ranges, ArithExpr field) {
        BoolExpr acc = _ctx.mkBool(false);
        for (SubRange range : ranges) {
            int start = range.getStart();
            int end = range.getEnd();
            if (start == end) {
                BoolExpr val = _ctx.mkEq(field, _ctx.mkInt(start));
                acc = _ctx.mkOr(acc, val);
            } else {
                BoolExpr val1 = _ctx.mkGe(field, _ctx.mkInt(start));
                BoolExpr val2 = _ctx.mkLe(field, _ctx.mkInt(end));
                acc = _ctx.mkOr(acc, _ctx.mkAnd(val1,val2));
            }
        }
        return (BoolExpr) acc.simplify();
    }

    private BoolExpr computeTcpFlags(TcpFlags flags) {
        BoolExpr acc = _ctx.mkBool(true);
        if (flags.getUseAck()) {
            acc = _ctx.mkAnd(acc, _ctx.mkEq(_tcpAck, _ctx.mkBool(flags.getAck()))  );
        }
        if (flags.getUseCwr()) {
            acc = _ctx.mkAnd(acc, _ctx.mkEq(_tcpCwr, _ctx.mkBool(flags.getCwr()))  );
        }
        if (flags.getUseEce()) {
            acc = _ctx.mkAnd(acc, _ctx.mkEq(_tcpEce, _ctx.mkBool(flags.getEce()))  );
        }
        if (flags.getUseFin()) {
            acc = _ctx.mkAnd(acc, _ctx.mkEq(_tcpFin, _ctx.mkBool(flags.getFin()))  );
        }
        if (flags.getUsePsh()) {
            acc = _ctx.mkAnd(acc, _ctx.mkEq(_tcpPsh, _ctx.mkBool(flags.getPsh()))  );
        }
        if (flags.getUseRst()) {
            acc = _ctx.mkAnd(acc, _ctx.mkEq(_tcpRst, _ctx.mkBool(flags.getRst()))  );
        }
        if (flags.getUseSyn()) {
            acc = _ctx.mkAnd(acc, _ctx.mkEq(_tcpSyn, _ctx.mkBool(flags.getSyn()))  );
        }
        if (flags.getUseUrg()) {
            acc = _ctx.mkAnd(acc, _ctx.mkEq(_tcpUrg, _ctx.mkBool(flags.getUrg()))  );
        }
        return (BoolExpr) acc.simplify();
    }

    private BoolExpr computeTcpFlags(List<TcpFlags> flags) {
        BoolExpr acc = _ctx.mkBool(false);
        for (TcpFlags fs : flags) {
            acc = _ctx.mkOr(acc, computeTcpFlags(fs));
        }
        return (BoolExpr) acc.simplify();
    }


    private BoolExpr computeIpProtocols(Set<IpProtocol> ipProtos) {
        BoolExpr acc = _ctx.mkBool(false);
        for (IpProtocol proto : ipProtos) {
            ArithExpr protoNum = _ctx.mkInt(proto.number());
            acc = _ctx.mkOr(acc, _ctx.mkEq(protoNum, _ipProtocol));
        }
        return (BoolExpr) acc.simplify();
    }


    private BoolExpr computeACL(IpAccessList acl) {
        // Check if there is an ACL first
        if (acl == null) {
            return _ctx.mkBool(true);
        }

        BoolExpr acc = _ctx.mkBool(false);

        List<IpAccessListLine> lines = new ArrayList<>(acl.getLines());
        Collections.reverse(lines);

        for (IpAccessListLine l : lines) {
            BoolExpr local = null;

            // System.out.println("NAME: " + l.getName());

            if (l.getDstIps() != null) {
                BoolExpr val = computeWildcardMatch(l.getDstIps(), _dstIp);
                // System.out.println("  DST IP: " + val);
                local = (local == null ? val : _ctx.mkAnd(local, val));
            }

            if (l.getSrcIps() != null) {
                BoolExpr val = computeWildcardMatch(l.getSrcIps(), _srcIp);
                // System.out.println("  SRC IP: " + val);
                local = (local == null ? val : _ctx.mkAnd(local, val));
            }

            if (l.getDscps() != null && !l.getDscps().isEmpty()) {
                throw new BatfishException("detected dscps");
            }

            if (l.getDstPorts() != null && !l.getDstPorts().isEmpty()) {
                BoolExpr val = computeValidRange(l.getDstPorts(), _dstPort);
                // System.out.println("  DST PORTS: " + val);
                local = (local == null ? val : _ctx.mkAnd(local, val));
            }

            if (l.getSrcPorts() != null && !l.getSrcPorts().isEmpty()) {
                BoolExpr val = computeValidRange(l.getSrcPorts(), _srcPort);
                // System.out.println("  SRC PORTS: " + val);
                local = (local == null ? val : _ctx.mkAnd(local, val));
            }

            if (l.getEcns() != null && !l.getEcns().isEmpty()) {
                throw new BatfishException("detected ecns");
            }

            if (l.getTcpFlags() != null && !l.getTcpFlags().isEmpty()) {
                BoolExpr val = computeTcpFlags(l.getTcpFlags());
                // System.out.println("  TCP FLAGS: " + val);
                local = (local == null ? val : _ctx.mkAnd(local, val));
            }

            if (l.getFragmentOffsets() != null && !l.getFragmentOffsets().isEmpty()) {
                throw new BatfishException("detected fragment offsets");
            }

            if (l.getIcmpCodes() != null && !l.getIcmpCodes().isEmpty()) {
                BoolExpr val = computeValidRange(l.getIcmpCodes(), _icmpCode);
                // System.out.println("  ICMP CODE: " + val);
                local = (local == null ? val : _ctx.mkAnd(local, val));
            }

            if (l.getIcmpTypes() != null && !l.getIcmpTypes().isEmpty()) {
                BoolExpr val = computeValidRange(l.getIcmpTypes(), _icmpType);
                // System.out.println("  ICMP TYPE: " + val);
                local = (local == null ? val : _ctx.mkAnd(local, val));
            }

            if (l.getStates() != null && !l.getStates().isEmpty()) {
                throw new BatfishException("detected states");
            }

            if (l.getIpProtocols() != null && !l.getIpProtocols().isEmpty()) {
                BoolExpr val = computeIpProtocols(l.getIpProtocols());
                local = (local == null ? val : _ctx.mkAnd(local, val));
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
                // System.out.println("  LOCAL: " + local.simplify());
                BoolExpr ret;
                if (l.getAction() == LineAction.ACCEPT) {
                    ret = _ctx.mkBool(true);
                } else {
                    ret = _ctx.mkBool(false);
                }

                if (l.getNegate()) {
                    local = _ctx.mkNot(local);
                }

                acc = If(local, ret, acc);
            }
        }

        // System.out.println("ACL RESULT: " + acc.simplify());

        return acc;
    }


    // TODO: too much rightward drift, refactor into lambda
    private void addDataForwardingConstraints() {
        _graph.getConfigurations().forEach((router, conf) -> {
            for (RoutingProtocol proto : _protocols.get(router)) {
                for (ArrayList<LogicalGraphEdge> eList : _edgeVariableMap.get(router).get(proto)) {
                    for (LogicalGraphEdge e : eList) {
                        Interface iface = e.getEdge().getStart();
                        if (isInterfaceUsed(conf, proto, iface)) {
                            if (e.getEdgeType() == EdgeType.IMPORT) {
                                GraphEdge ge = e.getEdge();

                                IpAccessList inbound = ge.getStart().getOutgoingFilter();

                                // System.out.println("Router: " + router);
                                // System.out.println("Interface: " + ge.getStart().getName());

                                BoolExpr acl = computeACL(inbound);

                                BoolExpr cForward = _controlForwarding.get(router).get(ge);
                                BoolExpr dForward = _dataForwarding.get(router).get(ge);
                                BoolExpr notBlocked = _ctx.mkAnd(cForward, acl);

                                add(_ctx.mkEq(notBlocked, dForward));
                            }
                        }
                    }
                }
            }
        });
    }

    private EdgeVars getBestVars(String router, RoutingProtocol proto) {
        if (_optimizations._sliceHasSingleProtocol.contains(router)) {
            return _bestNeighbor.get(router);
        } else {
            return _bestNeighborPerProtocol.get(router).get(proto);
        }
    }

    public BoolExpr relevantOrigination(List<Prefix> prefixes) {
        BoolExpr acc = _ctx.mkBool(false);
        for (Prefix p : prefixes) {
            acc = _ctx.mkOr(acc, isRelevantFor(p, _dstIp));
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

    private void addImportConstraint(LogicalGraphEdge e, EdgeVars varsOther, Configuration conf, RoutingProtocol proto, Interface iface, String router, List<Prefix> originations) {
        // Check if we even need import-specific variables
        // If not, then we will just use the export variables when
        // determining the best option at each router
        EdgeVars vars = e.getEdgeVars();

        if (vars.getIsUsed()) {

            if (proto == RoutingProtocol.CONNECTED) {
                Prefix p = iface.getPrefix();
                BoolExpr relevant = _ctx.mkAnd(_ctx.mkBool(iface.getActive()), isRelevantFor(p, _dstIp));
                BoolExpr values =
                        _ctx.mkAnd(
                                vars.getPermitted(),
                                safeEq(vars.getPrefix(), _ctx.mkBV(p.getNetworkAddress().asLong(), 32)),
                                safeEq(vars.getPrefixLength(), _ctx.mkInt(p.getPrefixLength())),
                                safeEq(vars.getAdminDist(), _ctx.mkInt(1)),
                                safeEq(vars.getLocalPref(), _ctx.mkInt(0)),
                                safeEq(vars.getMetric(), _ctx.mkInt(0))
                        );
                add( If(relevant, values, _ctx.mkNot(vars.getPermitted())) );
            }

            if (proto == RoutingProtocol.STATIC) {
                List<StaticRoute> srs = _graph.getStaticRoutes().get(router).get(iface.getName()); // should exist
                assert(srs != null);
                BoolExpr acc = _ctx.mkNot(vars.getPermitted());
                for (StaticRoute sr : srs) {
                    Prefix p = sr.getNetwork();
                    BoolExpr relevant = _ctx.mkAnd(_ctx.mkBool(iface.getActive()), isRelevantFor(p, _dstIp));
                    BoolExpr values =
                            _ctx.mkAnd(
                                    vars.getPermitted(),
                                    safeEq(vars.getPrefix(), _ctx.mkBV(p.getNetworkAddress().asLong(),32)),
                                    safeEq(vars.getPrefixLength(), _ctx.mkInt(p.getPrefixLength())),
                                    safeEq(vars.getAdminDist(), _ctx.mkInt(sr.getAdministrativeCost())),
                                    safeEq(vars.getLocalPref(), _ctx.mkInt(0)),
                                    safeEq(vars.getMetric(), _ctx.mkInt(0))
                            );
                    acc = If(relevant, values, acc);
                }
              add( acc );
            }

            if (proto == RoutingProtocol.OSPF || proto == RoutingProtocol.BGP) {
                BoolExpr val =  _ctx.mkNot(vars.getPermitted());
                if (varsOther != null) {
                    // Get the import policy for a given network, can return null if none,
                    // in which case we just will copy over the old variables.
                    BoolExpr isRoot = relevantOrigination(originations);
                    BoolExpr usable = _ctx.mkAnd(_ctx.mkNot(isRoot), _ctx.mkBool(iface.getActive()), varsOther.getPermitted());
                    BoolExpr importFunction;
                    RoutingPolicy pol = findImportRoutingPolicy(conf, proto, e);
                    if (pol != null) {
                        importFunction = computeTransferFunction(varsOther, vars, conf, proto, proto, pol.getStatements(), null);
                        // System.out.println("----------------- transfer for " + pol.getName() + "--------------");
                        // System.out.println(v);
                    } else {
                        // just copy the export policy in ospf/bgp
                        BoolExpr per = _ctx.mkEq(vars.getPermitted(), varsOther.getPermitted());
                        BoolExpr pfx = safeEq(vars.getPrefix(), varsOther.getPrefix());
                        BoolExpr lp = safeEq(vars.getLocalPref(), varsOther.getLocalPref());
                        BoolExpr ad = safeEq(vars.getAdminDist(), varsOther.getAdminDist());
                        BoolExpr met = safeEq(vars.getMetric(), varsOther.getMetric());
                        BoolExpr med = safeEq(vars.getMed(), varsOther.getMed());
                        BoolExpr len = safeEq(vars.getPrefixLength(), varsOther.getPrefixLength());
                        importFunction = _ctx.mkAnd(per, pfx, lp, ad, met, med, len);
                    }

                    /* if (router.equals("hk2-x3sb-xcg-2-1b")) {
                        System.out.println("ROUTER: " + conf.getName());
                        System.out.println("IFACE: " + e.getEdge().getStart().getName());
                        System.out.println("PEER: " + e.getEdge().getPeer());
                        System.out.println("IMPORT FUNCTION: " + importFunction);
                    } */

                    add( If(usable, importFunction, val) );
                } else {
                    add( val );
                }

            }
        }
    }


    private boolean addExportConstraint(LogicalGraphEdge e, EdgeVars varsOther, Configuration conf, RoutingProtocol proto, Interface iface, String router, boolean usedExport, List<Prefix> originations) {

        EdgeVars vars = e.getEdgeVars();

        // only add constraints once when using a single copy of export variables
        if (!_optimizations.getSliceCanKeepSingleExportVar().get(router).get(proto) || !usedExport) {

            if (proto == RoutingProtocol.CONNECTED) {
                BoolExpr val = _ctx.mkNot(vars.getPermitted());
                add(val);
            }

            if (proto == RoutingProtocol.STATIC) {
                BoolExpr val = _ctx.mkNot(vars.getPermitted());
                add(val);
            }

            if (proto == RoutingProtocol.OSPF || proto == RoutingProtocol.BGP) {
                // originated routes
                Integer cost = addedCost(proto, iface);
                BoolExpr val = _ctx.mkNot(vars.getPermitted());

                // default is to propagate the "best" route
                EdgeVars best = getBestVars(router,proto);

                // If the export is usable, then we propagate the best route after incrementing the metric
                BoolExpr usable = _ctx.mkAnd(_ctx.mkBool(iface.getActive()), best.getPermitted());

                BoolExpr acc;
                RoutingPolicy pol = findExportRoutingPolicy(conf, proto, e);
                 if (pol != null) {
                     acc = computeTransferFunction(varsOther, vars, conf, proto, proto, pol.getStatements(), cost);

                     /* if (conf.getName().equals("hk2-x3sb-xcg-2-1a")) {
                         System.out.println("ROUTER: " + conf.getName());
                         System.out.println("IFACE: " + e.getEdge().getStart().getName());
                         System.out.println("PEER: " + e.getEdge().getPeer());
                         System.out.println("EXPORT FUNCTION: " + acc.simplify());
                     } */

                } else {

                     acc = _ctx.mkAnd(
                            _ctx.mkEq(vars.getPermitted(), _ctx.mkBool(true)),
                            safeEq(vars.getPrefix(), best.getPrefix()),
                            safeEq(vars.getPrefixLength(), best.getPrefixLength()),
                            safeEq(vars.getAdminDist(), best.getAdminDist()),
                            safeEq(vars.getMed(), best.getMed()),
                            safeEq(vars.getLocalPref(), best.getLocalPref()),
                            safeEqAdd(vars.getMetric(), best.getMetric(), cost));
                }

                acc = If(usable, acc, val);

                // TODO: super inefficient to repeat this for every interface?
                // TODO: but each prefix sets the length accordingly

                for (Prefix p : originations) {
                    BoolExpr relevant = _ctx.mkAnd(_ctx.mkBool(iface.getActive()), isRelevantFor(p, _dstIp));
                    int adminDistance = defaultAdminDistance(conf, proto);
                    int prefixLength = p.getPrefixLength();
                    BoolExpr values =
                            _ctx.mkAnd(
                                    vars.getPermitted(),
                                    safeEq(vars.getPrefix(), _ctx.mkBV(p.getNetworkAddress().asLong(),32)),
                                    safeEq(vars.getLocalPref(), _ctx.mkInt(0)),
                                    safeEq(vars.getAdminDist(), _ctx.mkInt(adminDistance)),
                                    safeEq(vars.getMetric(), _ctx.mkInt(cost)),
                                    safeEq(vars.getMed(), _ctx.mkInt(100)),
                                    safeEq(vars.getPrefixLength(), _ctx.mkInt(prefixLength)));

                    acc = If(relevant, values, acc);

                }

                /* if (router.contains("hk2-x3sb-xcg-2-1a")) {
                    System.out.println("Origination:");
                    System.out.println(acc);
                } */

                add( acc );
            }
            return true;
        }
        return false;
    }


    private EdgeVars findOtherVars(LogicalGraphEdge e) {
        LogicalGraphEdge other = _otherEnd.get(e);
        if (other != null) {
            return other.getEdgeVars();
        }
        return _environmentVars.get(e);
    }

    private void addTransferFunction() {
        _graph.getConfigurations().forEach((router, conf) -> {
            for (RoutingProtocol proto : _protocols.get(router)) {
                Boolean usedExport = false;
                List<Prefix> originations = getOriginatedNetworks(conf, proto);
                for (ArrayList<LogicalGraphEdge> eList : _edgeVariableMap.get(router).get(proto)) {
                    for (LogicalGraphEdge e : eList) {
                        GraphEdge ge = e.getEdge();
                        Interface iface = ge.getStart();
                        if (isInterfaceUsed(conf, proto, iface)) {
                            EdgeVars varsOther;
                            switch (e.getEdgeType()) {
                                case IMPORT:
                                    varsOther = findOtherVars(e);
                                    addImportConstraint(e, varsOther, conf, proto, iface, router, originations);
                                    break;

                                case EXPORT:
                                    // TODO: refactor this into the getter?
                                    if (_optimizations._sliceHasSingleProtocol.contains(router)) {
                                        varsOther = _bestNeighbor.get(router);
                                    } else {
                                        varsOther = _bestNeighborPerProtocol.get(router).get(proto);
                                    }

                                    usedExport = addExportConstraint(e, varsOther, conf, proto, iface, router, usedExport, originations);
                                    break;
                            }
                        }
                    }

                }

            }
        });

    }

    private void addUnusedDefaultValueConstraints() {
        for (EdgeVars vars : _allEdgeVars) {

            BoolExpr notPermitted = _ctx.mkNot(vars.getPermitted());
            ArithExpr zero = _ctx.mkInt(0);

            if (vars.getAdminDist() != null) {
                add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getAdminDist(), zero)) );
            }
            if (vars.getPrefix() != null) {
                add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getPrefix(), _ctx.mkBV(0,32))) );
            }
            if (vars.getMed() != null) {
                add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getMed(), zero)) );
            }
            if (vars.getLocalPref() != null) {
                add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getLocalPref(), zero)) );
            }
            if (vars.getPrefixLength() != null) {
                add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getPrefixLength(), zero)) );
            }
            if (vars.getMetric() != null) {
                add( _ctx.mkImplies(notPermitted, _ctx.mkEq(vars.getMetric(), zero)) );
            }
        }
    }

    private void addDestinationConstraint() {
        BoolExpr validDestRange = _ctx.mkBool(false);
        for (Prefix p : _destinations) {
            long lower = p.getAddress().asLong();
            long upper = p.getEndAddress().asLong();
            BoolExpr constraint;
            if (lower == upper) {
                constraint = _ctx.mkEq(_dstIp, _ctx.mkInt(lower));
                // add( _ctx.mkEq(_dstIp, _ctx.mkInt(lower)) );
            } else {
                BoolExpr x = _ctx.mkGe(_dstIp, _ctx.mkInt(lower));
                BoolExpr y = _ctx.mkLe(_dstIp, _ctx.mkInt(upper));
                constraint = _ctx.mkAnd(x,y);
                // add( _ctx.mkGe(_dstIp, _ctx.mkInt(lower)) );
                // add( _ctx.mkLe(_dstIp, _ctx.mkInt(upper)) );
            }
            validDestRange = _ctx.mkOr(validDestRange, constraint);
        }

        add( validDestRange );
    }

    private BoolExpr prefixEdgeApplies(EdgeVars e) {
        BitVecExpr mask = _ctx.mkBVConst("mask_" + e.getName(), 32);
        _allVariables.add(mask);
        for (int i = 0; i <= 32; i++) {
            long val = (((long) Math.pow(2,32)) - 1) - (((long) Math.pow(2,i)) - 1) ;
            BoolExpr rightLen = _ctx.mkEq(e.getPrefixLength(), _ctx.mkInt(i));
            BoolExpr rightMask = _ctx.mkEq(mask, _ctx.mkBV(val,32) );
            BoolExpr impl = _ctx.mkImplies(rightLen,rightMask);
            add( impl );
        }
        BitVecExpr b = _ctx.mkInt2BV(32, (com.microsoft.z3.IntExpr) _dstIp);
        BoolExpr both = _ctx.mkEq( _ctx.mkBVAND(b, mask) , _ctx.mkBVAND(e.getPrefix(),mask));

        return both;
        /*
        ArithExpr i = _ctx.mkBV2Int(e.getPrefix(), false);
        return _ctx.mkEq(_dstIp, i); */
    }

    private void addPrefixConstraints() {
        for (EdgeVars e : _allEdgeVars) {
            if (e.getPrefix() != null) {
                BoolExpr doesApply = prefixEdgeApplies(e);
                add( _ctx.mkImplies(e.getPermitted(), doesApply) );
            }
        }
    }


    private void initConfigurations() {
        _graph.getConfigurations().forEach((router,conf) -> {
            initOspfInterfaceCosts(conf);
        });
    }

    public VerificationResult verify() {
        int numVariables = _allVariables.size();
        int numConstraints = _solver.getAssertions().length;
        int numNodes = _graph.getConfigurations().size();
        int numEdges = 0;
        for (Map.Entry<String, Set<String>> e : _graph.getNeighbors().entrySet()) {
            for (String n : e.getValue()) {
                numEdges++;
            }
        }
        long start = System.currentTimeMillis();
        Status status = _solver.check();
        long time = System.currentTimeMillis() - start;

        VerificationStats stats = new VerificationStats(numNodes, numEdges, numVariables, numConstraints, time);

        if (status == Status.UNSATISFIABLE) {
            return new VerificationResult(this, true, null, stats);
        }
        else if (status == Status.UNKNOWN) {
            return new VerificationResult(this, false, null, stats);
        }
        else {
            Model m = _solver.getModel();
            Map<String, String> model = new HashMap<>();
            for (Expr e : _allVariables) {
                String name = e.toString();
                Expr val = m.evaluate(e, false);
                if (!val.equals(e)) {
                    model.put(name, val.toString());
                }
            }
            return new VerificationResult(this, false, model, stats);
        }
    }

    public void computeEncoding() {
        if (ENABLE_DEBUGGING) {
            // System.out.println(_graph.toString());
        }
        initConfigurations();
        computeBgpNeighbors();
        computeOptimizations();
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
        addPrefixConstraints();
    }

}
