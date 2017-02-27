package org.batfish.smt;


import org.batfish.common.BatfishException;
import org.batfish.datamodel.*;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.BooleanExpr;
import org.batfish.datamodel.routing_policy.expr.CallExpr;
import org.batfish.datamodel.routing_policy.statement.*;

import java.util.*;

class Optimizations {

    private static final boolean ENABLE_IMPORT_EXPORT_MERGE_OPTIMIZATION = true;

    private static final boolean ENABLE_EXPORT_MERGE_OPTIMIZATION = true;

    private static final boolean ENABLE_SLICING_OPTIMIZATION = true;

    private Encoder _encoder;

    private boolean _hasEnvironment;

    private Set<String> _sliceHasSingleProtocol;

    private Set<Long> _areaIds;

    // TODO: convert to Table2
    private Map<String, EnumMap<RoutingProtocol, Boolean>> _sliceCanKeepSingleExportVar;

    private Map<String, EnumMap<RoutingProtocol, List<GraphEdge>>> _sliceCanCombineImportExportVars;

    private Map<String, EnumMap<RoutingProtocol, Boolean>> _needRouterIdProto;

    private Set<String> _needRouterId;

    private boolean _keepLocalPref;

    private boolean _keepAdminDist;

    private boolean _keepMed;

    private boolean _keepOspfType;

    Optimizations(Encoder encoder) {
        _encoder = encoder;
        _hasEnvironment = false;
        _areaIds = new HashSet<>();
        _sliceHasSingleProtocol = new HashSet<>();
        _sliceCanCombineImportExportVars = new HashMap<>();
        _sliceCanKeepSingleExportVar = new HashMap<>();
        _needRouterIdProto = new HashMap<>();
        _needRouterId = new HashSet<>();
        _keepLocalPref = true;
        _keepAdminDist = true;
        _keepMed = true;
        _keepOspfType = true;
    }

    void computeOptimizations() {
        computeAreaIds();
        _hasEnvironment = computeHasEnvironment();
        _keepLocalPref = computeKeepLocalPref();
        _keepAdminDist = computeKeepAdminDistance();
        _keepMed = computeKeepMed();
        _keepOspfType = computeKeepOspfType();
        initProtocols();
        computeRouterIdNeeded();
        computeCanUseSingleBest();
        computeCanMergeExportVars();
        computeCanMergeImportExportVars();
    }

    private boolean computeHasEnvironment() {
        Boolean[] val = new Boolean[1];
        val[0] = false;
        _encoder.getGraph().getEdgeMap().forEach((router, edges) -> {
            for (GraphEdge ge : edges) {
                if (ge.getEnd() == null && _encoder.getGraph().getBgpNeighbors().containsKey(ge)) {
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
        _encoder.getGraph().getConfigurations().forEach((router, conf) -> {
            conf.getRoutingPolicies().forEach((name, pol) -> {
                AstVisitor v = new AstVisitor();
                v.visit(conf, pol.getStatements(), stmt -> {
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
        AstVisitor v = new AstVisitor();
        Boolean[] val = new Boolean[1];
        val[0] = false;
        _encoder.getGraph().getConfigurations().forEach((router, conf) -> {
            conf.getRoutingPolicies().forEach((name, pol) -> {
                v.visit(conf, pol.getStatements(), stmt -> {
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

    private void computeAreaIds() {
        // Next check if the there are multiple ospf areas
        _encoder.getGraph().getConfigurations().forEach((router, conf) -> {
            Set<Long> ids = _encoder.getGraph().getAreaIds().get(router);
            _areaIds.addAll(ids);
        });
    }

    private boolean computeKeepOspfType() {
        if (!Optimizations.ENABLE_SLICING_OPTIMIZATION) {
            return true;
        }
        // First check if the ospf metric type is ever set
        AstVisitor v = new AstVisitor();
        Boolean[] val = new Boolean[1];
        val[0] = false;
        _encoder.getGraph().getConfigurations().forEach((router, conf) -> {
            conf.getRoutingPolicies().forEach((name, pol) -> {
                v.visit(conf, pol.getStatements(), stmt -> {
                    if (stmt instanceof SetOspfMetricType) {
                        val[0] = true;
                    }
                }, expr -> {});
            });
        });
        if (val[0]) {
            return true;
        }

        // Next see if the there are multiple ospf areas
        return _areaIds.size() > 1;
    }

    private void initProtocols() {
        Graph g = _encoder.getGraph();
        g.getConfigurations().forEach((router, conf) -> {
            g.getProtocols().put(router, new ArrayList<>());
        });
        g.getConfigurations().forEach((router, conf) -> {
            List<RoutingProtocol> protos = _encoder.getGraph().getProtocols().get(router);
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

    // Check if we need the routerID for each router/protocol pair
    private void computeRouterIdNeeded() {
        _encoder.getGraph().getConfigurations().forEach((router, conf) -> {
            EnumMap<RoutingProtocol, Boolean> map = new EnumMap<>(RoutingProtocol.class);
            _needRouterIdProto.put(router, map);
            for (RoutingProtocol proto : _encoder.getGraph().getProtocols().get(router)) {
                if (_encoder.isMultipath(conf, proto)) {
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
        _encoder.getGraph().getConfigurations().forEach((router, conf) -> {
            if (_encoder.getGraph().getProtocols().get(router).size() == 1) {
                _sliceHasSingleProtocol.add(router);
            }
        });
    }

    // Merge export variables into a single copy when no peer-specific export
    private void computeCanMergeExportVars() {
        Graph g = _encoder.getGraph();

        _encoder.getGraph().getConfigurations().forEach((router, conf) -> {
            EnumMap<RoutingProtocol, Boolean> map = new EnumMap<>(RoutingProtocol.class);
            _sliceCanKeepSingleExportVar.put(router, map);

            // Can be no peer-specific export, which includes dropping due to
            // the neighbor already being the root of the tree.
            for (RoutingProtocol proto : _encoder.getGraph().getProtocols().get(router)) {
                if (proto == RoutingProtocol.CONNECTED || proto == RoutingProtocol.STATIC) {
                    map.put(proto, Optimizations.ENABLE_EXPORT_MERGE_OPTIMIZATION);

                } else if (proto == RoutingProtocol.OSPF) {
                    // Ensure all interfaces are active
                    boolean allIfacesActive = true;
                    for (GraphEdge edge : g.getEdgeMap().get(router)) {
                        Interface iface = edge.getStart();
                        allIfacesActive = allIfacesActive && g.isInterfaceActive(proto, iface);
                    }

                    // Ensure single area for this router
                    boolean singleArea = _encoder.getGraph().getAreaIds().get(router).size() <= 1;

                    map.put(proto, allIfacesActive && singleArea && Optimizations.ENABLE_EXPORT_MERGE_OPTIMIZATION);

                } else if (proto == RoutingProtocol.BGP) {
                    boolean allDefault = true;
                    for (Map.Entry<Prefix, BgpNeighbor> e : conf.getDefaultVrf().getBgpProcess()
                                                                .getNeighbors().entrySet()) {
                        BgpNeighbor n = e.getValue();
                        if (!isDefaultBgpExport(conf, n)) {
                            allDefault = false;
                            break;
                        }
                    }
                    map.put(proto, allDefault && Optimizations.ENABLE_EXPORT_MERGE_OPTIMIZATION);

                } else {
                    throw new BatfishException("Error: unkown protocol: " + proto.protocolName());
                }
            }
        });
    }

    // Merge import and export variables when there is no peer-specific import
    private void computeCanMergeImportExportVars() {

        _encoder.getGraph().getConfigurations().forEach((router, conf) -> {
            EnumMap<RoutingProtocol, List<GraphEdge>> map = new EnumMap<>(RoutingProtocol.class);
            _sliceCanCombineImportExportVars.put(router, map);
            for (RoutingProtocol proto : _encoder.getGraph().getProtocols().get(router)) {

                List<GraphEdge> edges = new ArrayList<>();
                if (Optimizations.ENABLE_IMPORT_EXPORT_MERGE_OPTIMIZATION) {

                    boolean relevantProto = (proto != RoutingProtocol.CONNECTED && proto !=
                            RoutingProtocol.STATIC);
                    if (relevantProto) {

                        boolean isNotRoot = !hasRelevantOriginatedRoute(conf, proto);
                        if (isNotRoot) {
                            for (GraphEdge e : _encoder.getGraph().getEdgeMap().get(router)) {
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

    private boolean needToModelConnected(Configuration conf) {
        if (Optimizations.ENABLE_SLICING_OPTIMIZATION) {
            return hasRelevantOriginatedRoute(conf, RoutingProtocol.CONNECTED);
        } else {
            return true;
        }
    }

    private boolean needToModelStatic(Configuration conf) {
        if (Optimizations.ENABLE_SLICING_OPTIMIZATION) {
            return hasRelevantOriginatedRoute(conf, RoutingProtocol.STATIC);
        } else {
            return conf.getDefaultVrf().getStaticRoutes().size() > 0;
        }
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
        if (!(s1 instanceof Statements.StaticStatement) || !(s2 instanceof Statements
                .StaticStatement)) {
            return false;
        }
        Statements.StaticStatement x = (Statements.StaticStatement) s1;
        Statements.StaticStatement y = (Statements.StaticStatement) s2;
        if (x.getType() != Statements.ExitAccept || y.getType() != Statements.ExitReject) {
            return false;
        }

        // Ensure condition just hands off to the common export policy
        if (!(be instanceof CallExpr)) {
            return false;
        }

        CallExpr ce = (CallExpr) be;

        return ce.getCalledPolicyName().contains(Encoder.BGP_COMMON_FILTER_LIST_NAME);
    }

    private boolean hasRelevantOriginatedRoute(Configuration conf, RoutingProtocol proto) {
        List<Prefix> prefixes = _encoder.getOriginatedNetworks(conf, proto);
        for (Prefix p1 : prefixes) {
            for (IpWildcard ipWildcard : _encoder.getHeaderSpace().getDstIps()) {
                Prefix p2 = ipWildcard.toPrefix();
                if (_encoder.overlaps(p1, p2)) {
                    return true;
                }
            }
        }
        return false;
    }

    // Make sure the neighbor uses the same protocol
    // and is configured to use the corresponding interface.
    // This makes sure that the export variables will exist.
    private boolean hasExportVariables(GraphEdge e, RoutingProtocol proto) {
        if (e.getEnd() != null) {
            String peer = e.getPeer();
            List<RoutingProtocol> peerProtocols = _encoder.getGraph().getProtocols().get(peer);
            if (peerProtocols.contains(proto)) {
                Configuration peerConf = _encoder.getGraph().getConfigurations().get(peer);
                if (_encoder.getGraph().isInterfaceUsed(peerConf, proto, e.getEnd())) {
                    return true;
                }
            }
        }
        return false;
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

    Set<String> getSliceHasSingleProtocol() {
        return _sliceHasSingleProtocol;
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

    public boolean getKeepOspfType() {
        return _keepOspfType;
    }
}