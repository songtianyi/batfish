package org.batfish.smt;


import com.microsoft.z3.*;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.HeaderSpace;
import org.batfish.datamodel.Interface;
import org.batfish.datamodel.Ip;
import org.batfish.datamodel.Prefix;

import java.util.*;

public class Encoder {

    static final boolean ENABLE_DEBUGGING = false;

    static int encodingId = 0;

    private Map<String, EncoderSlice> _slices;

    private SymbolicFailures _symbolicFailures;

    private List<Expr> _allVariables;

    private List<SymbolicRecord> _allSymbolicRecords;

    private Graph _graph;

    private Context _ctx;

    private Solver _solver;

    private UnsatCore _unsatCore;


    public Encoder(HeaderSpace h, IBatfish batfish) {
        this(h, new Graph(batfish));
    }

    public Encoder(HeaderSpace h, Graph graph) {
        this(h, graph, null, null, null);
    }

    private Encoder(HeaderSpace h, Graph graph, Context ctx, Solver solver, List<Expr> vars) {

        _graph = graph;

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

        _symbolicFailures = new SymbolicFailures();
        _allSymbolicRecords = new ArrayList<>();

        if (vars == null) {
            _allVariables = new ArrayList<>();
        } else {
            _allVariables = vars;
        }

        if (ENABLE_DEBUGGING) {
            System.out.println(graph.toString());
        }

        _unsatCore = new UnsatCore(ENABLE_DEBUGGING);

        _slices = new HashMap<>();
        _slices.put("main", new EncoderSlice(this, h, graph));

        initFailedLinkVariables();
    }

    Encoder(Encoder e, Graph g) {
        this(e.getMainSlice().getHeaderSpace(), g, e.getCtx(), e.getSolver(), e.getAllVariables());
    }

    void add(BoolExpr e) {
        _unsatCore.track(_solver, _ctx, e);
    }

    BoolExpr Bool(boolean val) {
        return getCtx().mkBool(val);
    }

    BoolExpr Not(BoolExpr e) {
        return getCtx().mkNot(e);
    }

    BoolExpr Or(BoolExpr... vals) {
        return getCtx().mkOr(vals);
    }

    BoolExpr Implies(BoolExpr e1, BoolExpr e2) {
        return getCtx().mkImplies(e1, e2);
    }

    BoolExpr Eq(Expr e1, Expr e2) {
        return getCtx().mkEq(e1, e2);
    }

    ArithExpr Int(long l) {
        return getCtx().mkInt(l);
    }

    BoolExpr And(BoolExpr... vals) {
        return getCtx().mkAnd(vals);
    }

    BoolExpr Ge(Expr e1, Expr e2) {
        if (e1 instanceof ArithExpr && e2 instanceof ArithExpr) {
            return getCtx().mkGe((ArithExpr) e1, (ArithExpr) e2);
        }
        if (e1 instanceof BitVecExpr && e2 instanceof BitVecExpr) {
            return getCtx().mkBVUGE((BitVecExpr) e1, (BitVecExpr) e2);
        }
        throw new BatfishException("Invalid call the Le while encoding control plane");
    }

    BoolExpr Le(Expr e1, Expr e2) {
        if (e1 instanceof ArithExpr && e2 instanceof ArithExpr) {
            return getCtx().mkLe((ArithExpr) e1, (ArithExpr) e2);
        }
        if (e1 instanceof BitVecExpr && e2 instanceof BitVecExpr) {
            return getCtx().mkBVULE((BitVecExpr) e1, (BitVecExpr) e2);
        }
        throw new BatfishException("Invalid call the Le while encoding control plane");
    }

    BoolExpr True() {
        return getCtx().mkBool(true);
    }

    BoolExpr False() {
        return getCtx().mkBool(false);
    }

    BoolExpr Lt(Expr e1, Expr e2) {
        if (e1 instanceof ArithExpr && e2 instanceof ArithExpr) {
            return getCtx().mkLt((ArithExpr) e1, (ArithExpr) e2);
        }
        if (e1 instanceof BitVecExpr && e2 instanceof BitVecExpr) {
            return getCtx().mkBVULT((BitVecExpr) e1, (BitVecExpr) e2);
        }
        throw new BatfishException("Invalid call the Le while encoding control plane");
    }

    ArithExpr Sum(ArithExpr e1, ArithExpr e2) {
        return getCtx().mkAdd(e1, e2);
    }

    ArithExpr Sub(ArithExpr e1, ArithExpr e2) {
        return getCtx().mkSub(e1, e2);
    }

    BoolExpr If(BoolExpr cond, BoolExpr case1, BoolExpr case2) {
        return (BoolExpr) getCtx().mkITE(cond, case1, case2);
    }

    ArithExpr If(BoolExpr cond, ArithExpr case1, ArithExpr case2) {
        return (ArithExpr) getCtx().mkITE(cond, case1, case2);
    }


    private void initFailedLinkVariables() {
        _graph.getEdgeMap().forEach((router, edges) -> {
            for (GraphEdge ge : edges) {
                if (ge.getPeer() == null) {
                    Interface i = ge.getStart();
                    String name = "failed-edge_" + ge.getRouter() + "_" + i.getName();
                    ArithExpr var = getCtx().mkIntConst(name);
                    _symbolicFailures.getFailedEdgeLinks().put(ge, var);
                }
            }
        });
        _graph.getNeighbors().forEach((router, peers) -> {
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

    private void addFailedConstraints(int k) {
        List<ArithExpr> vars = new ArrayList<>();
        getSymbolicFailures().getFailedInternalLinks().forEach((router, peer, var) -> {
            vars.add(var);
        });
        getSymbolicFailures().getFailedEdgeLinks().forEach((ge, var) -> {
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


    public VerificationResult verify() {

        EncoderSlice slice = _slices.get("main");

        int numVariables = _allVariables.size();
        int numConstraints = _solver.getAssertions().length;
        int numNodes = slice.getGraph().getConfigurations().size();
        int numEdges = 0;
        for (Map.Entry<String, Set<String>> e : slice.getGraph().getNeighbors().entrySet()) {
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
            SymbolicPacket p = slice.getSymbolicPacket();
            String dstIp = valuation.get(p.getDstIp());
            String srcIp = valuation.get(p.getSrcIp());
            String dstPt = valuation.get(p.getDstPort());
            String srcPt = valuation.get(p.getSrcPort());
            String icmpCode = valuation.get(p.getIcmpCode());
            String icmpType = valuation.get(p.getIcmpType());
            String ipProtocol = valuation.get(p.getIpProtocol());
            String tcpAck = valuation.get(p.getTcpAck());
            String tcpCwr = valuation.get(p.getTcpCwr());
            String tcpEce = valuation.get(p.getTcpEce());
            String tcpFin = valuation.get(p.getTcpFin());
            String tcpPsh = valuation.get(p.getTcpPsh());
            String tcpRst = valuation.get(p.getTcpRst());
            String tcpSyn = valuation.get(p.getTcpSyn());
            String tcpUrg = valuation.get(p.getTcpUrg());

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
                packetModel.put("icmpCode", icmpCode);
            }
            if (icmpType != null && !icmpType.equals("0")) {
                packetModel.put("icmpType", icmpType);
            }
            if (ipProtocol != null && !ipProtocol.equals("0")) {
                packetModel.put("ipProtocol", ipProtocol);
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
            slice.getLogicalGraph().getEnvironmentVars().forEach((lge, r) -> {

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
                    if (r.getOspfArea() != null && r.getOspfArea().getBitVec() != null) {
                        String x = valuation.get(r.getOspfArea().getBitVec());
                        if (x != null) {
                            Integer i = Integer.parseInt(x);
                            Long area = r.getOspfArea().value(i);
                            recordMap.put("OSPF Area", area.toString());
                        }
                    }
                    if (r.getOspfType() != null && r.getOspfType().getBitVec() != null) {
                        String x = valuation.get(r.getOspfType().getBitVec());
                        if (x != null) {
                            Integer i = Integer.parseInt(x);
                            OspfType type = r.getOspfType().value(i);
                            recordMap.put("OSPF Type", type.toString());
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
            slice.getSymbolicDecisions().getDataForwarding().forEach((router, edge, e) -> {
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
        addFailedConstraints(0);
        _slices.forEach((name, slice) -> {
            slice.computeEncoding();
        });
    }

    public EncoderSlice getMainSlice() {
        return _slices.get("main");
    }

    public SymbolicFailures getSymbolicFailures() {
        return _symbolicFailures;
    }

    public List<Expr> getAllVariables() {
        return _allVariables;
    }

    public List<SymbolicRecord> getAllSymbolicRecords() {
        return _allSymbolicRecords;
    }

    public Context getCtx() {
        return _ctx;
    }

    public Solver getSolver() {
        return _solver;
    }

    public UnsatCore getUnsatCore() {
        return _unsatCore;
    }
}
