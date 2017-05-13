package org.batfish.smt;


import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import org.batfish.common.BatfishException;
import org.batfish.common.Pair;
import org.batfish.datamodel.*;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.*;
import org.batfish.datamodel.routing_policy.statement.*;
import org.batfish.smt.collections.PList;

import java.util.*;

import static org.batfish.datamodel.routing_policy.statement.Statements.*;

/**
 * Class that computes a symbolic transfer function between
 * two symbolic control plane records. The transfer function
 * is used to encode both import and export filters.
 *
 * Batfish represents the AST much like vendors where there
 * is a simple imperative language for matching fields and
 * making modifications to fields. Since this is not a good
 * fit for a declarative symbolic encoding of the network,
 * we convert this stateful representation into a stateless representation
 *
 * The TransferFunctionSSA class makes policies stateless by converting
 * the vendor-independent format to a Single Assignment (SSA) form where all updates are
 * reflected in new variables. Rather than create a full control flow
 * graph (CFG) as is typically done in SSA, we use a simple conversion based on adding join points
 * for every variable modified in an If statement. Since functions can have side effects, we treat
 * the route variables as global across function calls.
 *
 * The joint point defined as the [phi] function from SSA merges variables that may differ across
 * different branches of an If statement. For example, if there is the following filter:
 *
 * If match(c1) then
 *   add community c2
 * else
 *   prepend path 2
 *
 * Then this function will introduce a new variable at the end of the If statement that
 * updates the value of each variable modified based on the branch taken. For example:
 *
 * c2' = (c1 ? true : c2)
 * metric' = (c1 ? metric : metric + 2)
 *
 * To model the return value of functions, we introduce two new variables: [returnValue] and [returnAssigned].
 * For example, if we have the following AST function in Batfish:
 *
 * function foo()
 *   if match(c1) then
 *      reject
 *   accept
 *
 * This is modeled by introducing [returnValue] - the value that the function returns, and the
 * [returnAssigned] variable - whether a return has been hit so far in the control flow.
 * For the foo function, we would have the following:
 *
 * function foo()
 *   [returnValue = False]
 *   [returnAssigned = False]
 *   if match(c1) then
 *      reject
 *      [returnValue' = False]
 *      [returnAssigned' = True]
 *   [returnValue'' = (c1 and not returnAssigned ? returnValue' : returnValue)]
 *   [returnAssigned'' = (c1 ? True : returnAssigned)]
 *   accept
 *   [returnValue''' = (returnAssigned'' ? returnValue'' : True)]
 *   [returnAssigned'' = True]
 *
 * This encoding will then be inlined and simplified by z3 to the simpler expression:
 * [returnValue''' = not c1], which removes many such intermediate variables
 *
 * @author Ryan Beckett
 */


class TransferFunctionSSA {

    private static int id = 0;

    private EncoderSlice _enc;

    private Configuration _conf;

    private SymbolicRecord _current;

    private SymbolicRecord _other;

    private Protocol _to;

    private Protocol _from;

    private List<Statement> _statements;

    private Integer _addedCost;

    private Interface _iface;

    private GraphEdge _graphEdge;

    private Map<Prefix, Boolean> _aggregates;

    private boolean _isExport;

    public TransferFunctionSSA(EncoderSlice encoderSlice, Configuration conf, SymbolicRecord other,
                        SymbolicRecord current, Protocol to, Protocol from, List<Statement> statements,
                        Integer addedCost, GraphEdge ge, boolean isExport) {
        _enc = encoderSlice;
        _conf = conf;
        _current = current;
        _other = other;
        _to = to;
        _from = from;
        _statements = statements;
        _addedCost = addedCost;
        _graphEdge = ge;
        _iface = ge.getStart();
        _isExport = isExport;
        _aggregates = null;
    }

    /*
     * Returns and increments a unique id for adding additional SSA variables
     */
    private static int generateId() {
        int result = TransferFunctionSSA.id;
        TransferFunctionSSA.id = result + 1;
        return result;
    }

    /*
     * Determines whether to model each aggregate route as
     * suppressing a more specific, or including the more specific
     */
    private Map<Prefix, Boolean> aggregateRoutes() {
        Map<Prefix, Boolean> acc = new HashMap<>();
        String name = _conf.getName();
        List<GeneratedRoute> aggregates = _enc.getOptimizations().getRelevantAggregates().get(name);
        Set<Prefix> suppressed = _enc.getOptimizations().getSuppressedAggregates().get(name);
        for (GeneratedRoute gr : aggregates) {
            Prefix p = gr.getNetwork();
            acc.put(p, suppressed.contains(p));
        }
        return acc;
    }

    /*
     * Converts a route filter list to a boolean expression.
     */
    private BoolExpr matchFilterList(RouteFilterList x, SymbolicRecord other) {
        BoolExpr acc = _enc.False();

        List<RouteFilterLine> lines = new ArrayList<>(x.getLines());
        Collections.reverse(lines);

        for (RouteFilterLine line : lines) {
            Prefix p = line.getPrefix();
            SubRange r = line.getLengthRange();
            PrefixRange range = new PrefixRange(p, r);
            BoolExpr matches = _enc.isRelevantFor(other.getPrefixLength(), range);
            BoolExpr action = _enc.Bool(line.getAction() == LineAction.ACCEPT);
            acc = _enc.If(matches, action, acc);
        }
        return acc;
    }

    /*
     * Converts a prefix set to a boolean expression.
     */
    private BoolExpr matchPrefixSet(Configuration conf, PrefixSetExpr e, SymbolicRecord other) {
        if (e instanceof ExplicitPrefixSet) {
            ExplicitPrefixSet x = (ExplicitPrefixSet) e;

            Set<PrefixRange> ranges = x.getPrefixSpace().getPrefixRanges();
            if (ranges.isEmpty()) {
                return _enc.True();
            }

            BoolExpr acc = _enc.False();
            for (PrefixRange range : ranges) {
                acc = _enc.Or(acc, _enc.isRelevantFor(other.getPrefixLength(), range));
            }
            return acc;

        } else if (e instanceof NamedPrefixSet) {
            NamedPrefixSet x = (NamedPrefixSet) e;
            String name = x.getName();
            RouteFilterList fl = conf.getRouteFilterLists().get(name);
            return matchFilterList(fl, other);

        } else {
            throw new BatfishException("TODO: match prefix set: " + e);
        }
    }

    /*
     * Converts a community list to a boolean expression.
     */
    private BoolExpr matchCommunityList(CommunityList cl, SymbolicRecord other) {
        List<CommunityListLine> lines = new ArrayList<>(cl.getLines());
        Collections.reverse(lines);
        BoolExpr acc = _enc.False();
        for (CommunityListLine line : lines) {
            boolean action = (line.getAction() == LineAction.ACCEPT);
            CommunityVar cvar = new CommunityVar(CommunityVar.Type.REGEX, line.getRegex(), null);
            BoolExpr c = other.getCommunities().get(cvar);
            acc = _enc.If(c, _enc.Bool(action), acc);
        }
        return acc;
    }

    /*
     * Converts a community set to a boolean expression
     */
    private BoolExpr matchCommunitySet(Configuration conf, CommunitySetExpr e, SymbolicRecord other) {
        if (e instanceof InlineCommunitySet) {
            Set<CommunityVar> comms = _enc.findAllCommunities(conf, e);
            BoolExpr acc = _enc.True();
            for (CommunityVar comm : comms) {
                BoolExpr c = other.getCommunities().get(comm);
                if (c == null) {
                    throw new BatfishException("matchCommunitySet: should not be null");
                }
                acc = _enc.And(acc, c);
            }
            return acc;
        }

        if (e instanceof NamedCommunitySet) {
            NamedCommunitySet x = (NamedCommunitySet) e;
            CommunityList cl = conf.getCommunityLists().get(x.getName());
            return matchCommunityList(cl, other);
        }

        throw new BatfishException("TODO: match community set");
    }

    /*
     * Wrap a simple boolean expression return value in a transfer function result
     */
    private TransferFunctionResult fromExpr(BoolExpr b) {
        return new TransferFunctionResult()
                .setReturnAssignedValue(_enc.True())
                .setReturnValue(b);
    }

    /*
     * Convert a Batfish AST boolean expression to a symbolic Z3 boolean expression
     * by performing inlining of stateful side effects.
     */
    private TransferFunctionResult compute(BooleanExpr expr, TransferFunctionParam p) {

        // TODO: right now everything is IPV4
        if (expr instanceof MatchIpv4) {
            p.debug("MatchIpv4");
            return fromExpr(_enc.True());
        }
        if (expr instanceof  MatchIpv6) {
            p.debug("MatchIpv6");
            return fromExpr(_enc.False());
        }

        if (expr instanceof Conjunction) {
            p.debug("Conjunction");
            Conjunction c = (Conjunction) expr;
            BoolExpr acc = _enc.True();
            TransferFunctionResult result = new TransferFunctionResult();
            for (BooleanExpr be : c.getConjuncts()) {
                TransferFunctionResult r = compute(be,p);
                result = result.addChangedVariables(r);
                acc = _enc.And(acc, r.getReturnValue());
            }
            return result.setReturnValue(acc);
        }

        if (expr instanceof Disjunction) {
            p.debug("Disjunction");
            Disjunction d = (Disjunction) expr;
            BoolExpr acc = _enc.False();
            TransferFunctionResult result = new TransferFunctionResult();
            for (BooleanExpr be : d.getDisjuncts()) {
                TransferFunctionResult r = compute(be,p);
                result = result.addChangedVariables(r);
                acc = _enc.Or(acc, r.getReturnValue());
            }
            return result.setReturnValue(acc);
        }

        if (expr instanceof ConjunctionChain) {
            p.debug("ConjunctionChain");
            ConjunctionChain d = (ConjunctionChain) expr;
            List<BooleanExpr> conjuncts = new ArrayList<>(d.getSubroutines());
            if (p.getDefaultPolicy() != null) {
                BooleanExpr be = new CallExpr(p.getDefaultPolicy().getDefaultPolicy());
                conjuncts.add(be);
            }
            if (conjuncts.size() == 0) {
                return fromExpr(_enc.True());
            } else {
                TransferFunctionResult result = new TransferFunctionResult();
                BoolExpr acc = _enc.True();
                for (BooleanExpr conjunct : conjuncts) {
                    TransferFunctionParam param = p.setDefaultPolicy(null).setChainContext(TransferFunctionParam.ChainContext.CONJUNCTION);
                    TransferFunctionResult r = compute(conjunct, param);
                    result.addChangedVariables(r);
                    acc = _enc.And(acc, r.getReturnValue());
                }
                return result.setReturnValue(acc);
            }
        }

        if (expr instanceof DisjunctionChain) {
            p.debug("DisjunctionChain");
            DisjunctionChain d = (DisjunctionChain) expr;
            List<BooleanExpr> disjuncts = new ArrayList<>(d.getSubroutines());
            if (p.getDefaultPolicy() != null) {
                BooleanExpr be = new CallExpr(p.getDefaultPolicy().getDefaultPolicy());
                disjuncts.add(be);
            }
            if (disjuncts.size() == 0) {
                return fromExpr(_enc.True());
            } else {
                TransferFunctionResult result = new TransferFunctionResult();
                BoolExpr acc = _enc.False();
                for (BooleanExpr disjunct : disjuncts) {
                    TransferFunctionParam param =  p.setDefaultPolicy(null).setChainContext(TransferFunctionParam.ChainContext.DISJUNCTION);
                    TransferFunctionResult r = compute(disjunct, param);
                    result.addChangedVariables(r);
                    acc = _enc.Or(acc, r.getReturnValue());
                }
                return result.setReturnValue(acc);
            }
        }

        if (expr instanceof Not) {
            p.debug("Not");
            Not n = (Not) expr;
            TransferFunctionResult result = compute(n.getExpr(), p);
            return result.setReturnValue( _enc.Not(result.getReturnValue()) );
        }

        if (expr instanceof MatchProtocol) {
            MatchProtocol mp = (MatchProtocol) expr;
            Protocol proto = Protocol.fromRoutingProtocol(mp.getProtocol());
            if (proto == null) {
                p.debug("MatchProtocol(" + mp.getProtocol().protocolName() + "): false");
                return fromExpr(_enc.False());
            }
            if (_other.getProtocolHistory() == null) {
                BoolExpr protoMatch = _enc.Bool(proto.equals(_from));
                p.debug("MatchProtocol(" + mp.getProtocol().protocolName() + "): " + protoMatch);
                return fromExpr(protoMatch);
            }
            BoolExpr protoMatch = _other.getProtocolHistory().checkIfValue(proto);
            p.debug("MatchProtocol(" + mp.getProtocol().protocolName() + "): " + protoMatch);
            return fromExpr(protoMatch);
        }

        if (expr instanceof MatchPrefixSet) {
            p.debug("MatchPrefixSet");
            MatchPrefixSet m = (MatchPrefixSet) expr;
            return fromExpr(matchPrefixSet(_conf, m.getPrefixSet(), p.getOther()));

        // TODO: implement me
        } else if (expr instanceof MatchPrefix6Set) {
            p.debug("MatchPrefix6Set");
            return fromExpr(_enc.False());

        } else if (expr instanceof CallExpr) {
            p.debug("CallExpr");
            // TODO: the call can modify certain fields, need to keep track of these variables
            CallExpr c = (CallExpr) expr;
            String name = c.getCalledPolicyName();
            RoutingPolicy pol = _conf.getRoutingPolicies().get(name);
            p = p.setCallContext(TransferFunctionParam.CallContext.EXPR_CALL);
            return compute(pol.getStatements(), p.indent().enterScope(name));

        } else if (expr instanceof WithEnvironmentExpr) {
            p.debug("WithEnvironmentExpr");
            // TODO: this is not correct
            WithEnvironmentExpr we = (WithEnvironmentExpr) expr;
            return compute(we.getExpr(), p);

        } else if (expr instanceof MatchCommunitySet) {
            p.debug("MatchCommunitySet");
            MatchCommunitySet mcs = (MatchCommunitySet) expr;
            return fromExpr(matchCommunitySet(_conf, mcs.getExpr(), p.getOther()));

        } else if (expr instanceof BooleanExprs.StaticBooleanExpr) {
            BooleanExprs.StaticBooleanExpr b = (BooleanExprs.StaticBooleanExpr) expr;
            switch (b.getType()) {
                case CallExprContext:
                    p.debug("CallExprContext");
                    return fromExpr(_enc.Bool(p.getCallContext() == TransferFunctionParam.CallContext.EXPR_CALL));
                case CallStatementContext:
                    p.debug("CallStmtContext");
                    return fromExpr(_enc.Bool(p.getCallContext() == TransferFunctionParam.CallContext.STMT_CALL));
                case True:
                    p.debug("True");
                    return fromExpr(_enc.True());
                case False:
                    p.debug("False");
                    return fromExpr(_enc.False());
            }

        }

        throw new BatfishException("TODO: compute expr transfer function: " + expr);
    }

    /*
     * Deal with the possibility of null variables due to optimizations
     */
    private ArithExpr getOrDefault(ArithExpr x, ArithExpr d) {
        if (x != null) {
            return x;
        }
        return d;
    }

    /*
     * Apply the effect of modifying an integer value (e.g., to set the local pref)
     */
    private ArithExpr applyIntExprModification(ArithExpr x, IntExpr e) {
        if (e instanceof LiteralInt) {
            LiteralInt z = (LiteralInt) e;
            return _enc.Int(z.getValue());
        }
        if (e instanceof DecrementMetric) {
            DecrementMetric z = (DecrementMetric) e;
            return _enc.Sub(x, _enc.Int(z.getSubtrahend()));
        }
        if (e instanceof IncrementMetric) {
            IncrementMetric z = (IncrementMetric) e;
            return _enc.Sum(x, _enc.Int(z.getAddend()));
        }
        if (e instanceof IncrementLocalPreference) {
            IncrementLocalPreference z = (IncrementLocalPreference) e;
            return _enc.Sum(x, _enc.Int(z.getAddend()));
        }
        if (e instanceof DecrementLocalPreference) {
            DecrementLocalPreference z = (DecrementLocalPreference) e;
            return _enc.Sub(x, _enc.Int(z.getSubtrahend()));
        }
        throw new BatfishException("TODO: int expr transfer function: " + e);
    }

    /*
     * Create a constraint that the metric field does not overflow
     * for a given routing protocol.
     */
    private BoolExpr noOverflow(ArithExpr metric, Protocol proto) {
        if (proto.isConnected()) {
            return _enc.True();
        }
        if (proto.isStatic()) {
            return _enc.True();
        }
        if (proto.isOspf()) {
            return _enc.Le(metric, _enc.Int(65535));
        }
        if (proto.isBgp()) {
            return _enc.Le(metric, _enc.Int(255));
        }
        throw new BatfishException("Encoding[noOverflow]: unrecognized protocol: " + proto.name());
    }

    /*
     * Compute how many times to prepend to a path from the AST
     */
    private int prependLength(AsPathListExpr expr) {
        if (expr instanceof MultipliedAs) {
            MultipliedAs x = (MultipliedAs) expr;
            IntExpr e = x.getNumber();
            LiteralInt i = (LiteralInt) e;
            return i.getValue();
        }
        if (expr instanceof LiteralAsList) {
            LiteralAsList x = (LiteralAsList) expr;
            return x.getList().size();
        }
        throw new BatfishException("Error[prependLength]: unreachable");
    }

    /*
     * Get the BgpNeighbor object given the current
     * graph edge and protocol information
     */
    private BgpNeighbor getBgpNeighbor() {
        Graph g = _enc.getGraph();
        if (_graphEdge.isAbstract()) {
            return g.getIbgpNeighbors().get(_graphEdge);
        } else {
            return g.getEbgpNeighbors().get(_graphEdge);
        }
    }

    /*
     * Determine if BGP communities should be
     * sent to/from the neighboring BGP peer.
     */
    private boolean sendCommunity() {
        if (_to.isBgp()) {
            BgpNeighbor n = getBgpNeighbor();
            return n.getSendCommunity();
        } else {
            return false;
        }
    }

    /*
     * Relate the symbolic control plane route variables
     */
    private BoolExpr relateVariables(TransferFunctionParam p, TransferFunctionResult result) {
        ArithExpr defaultLen = _enc.Int(_enc.defaultLength());
        ArithExpr defaultAd = _enc.Int(_enc.defaultAdminDistance(_conf, _from));
        ArithExpr defaultMed = _enc.Int(_enc.defaultMed(_from));
        ArithExpr defaultLp = _enc.Int(_enc.defaultLocalPref());
        ArithExpr defaultId = _enc.Int(_enc.defaultId());
        ArithExpr defaultMet = _enc.Int(_enc.defaultMetric());

        // TODO: remove all isChanged calls with actual symbolic values that test for a change

        boolean isIbgp = _graphEdge.isAbstract() && _to.isBgp();

        // Update prefix length when aggregation
        BoolExpr len = _enc.safeEq(_current.getPrefixLength(), getOrDefault(p.getOther().getPrefixLength(), defaultLen));
        BoolExpr per = _enc.safeEq(_current.getPermitted(), p.getOther().getPermitted());
        BoolExpr id = _enc.safeEq(_current.getRouterId(), getOrDefault(p.getOther().getRouterId(), defaultId));

        // Update OSPF area id
        BoolExpr area;
        if (p.getOther().getOspfArea() == null || _iface.getOspfAreaName() == null) {
            area = _enc.True();
        } else {
            area = _enc.safeEqEnum(_current.getOspfArea(), _iface.getOspfAreaName());
        }

        // Set the IGP metric accordingly
        BoolExpr igpMet = _enc.True();
        if (_graphEdge.isAbstract() && _current.getIgpMetric() != null) {
            String router = _graphEdge.getRouter();
            String peer = _graphEdge.getPeer();
            EncoderSlice s = _enc.getEncoder().getSlice(peer);
            SymbolicRecord r = s.getSymbolicDecisions().getBestNeighbor().get(router);
            igpMet = _enc.Eq(_current.getIgpMetric(), r.getMetric());
        }

        // Set whether or not is iBGP or not on import
        BoolExpr isInternal = _enc.safeEq(_current.getBgpInternal(), _enc.Bool(isIbgp));

        // Update OSPF type
        BoolExpr type;
        if (result.isChanged("OSPF-TYPE")) {
            type = _enc.safeEqEnum(_current.getOspfType(), p.getOther().getOspfType());
        } else {
            boolean hasAreaIface = _iface.getOspfAreaName() != null;
            boolean hasArea = p.getOther().getOspfArea() != null;
            boolean hasType = p.getOther().getOspfType() != null;
            boolean areaPossiblyChanged = hasType && hasArea && hasAreaIface;
            // Check if area changed
            if (areaPossiblyChanged) {
                BoolExpr internal = p.getOther().getOspfType().isInternal();
                BoolExpr same = p.getOther().getOspfArea().checkIfValue(_iface.getOspfAreaName());
                BoolExpr update = _enc.And(internal, _enc.Not(same));
                BoolExpr copyOld = _enc.safeEqEnum(_current.getOspfType(), p.getOther().getOspfType());
                type = _enc.If(update, _current.getOspfType().checkIfValue(OspfType.OIA), copyOld);
            } else {
                type = _enc.safeEqEnum(_current.getOspfType(), p.getOther().getOspfType());
            }
        }


        BoolExpr comms = _enc.True();
        // regex matches that now match due to the concrete added value
        // update all community values
        for (Map.Entry<CommunityVar, BoolExpr> entry : _current.getCommunities().entrySet()) {
            CommunityVar cvar = entry.getKey();
            BoolExpr e = entry.getValue();
            BoolExpr eOther = p.getOther().getCommunities().get(cvar);
            // Update the communities if they should be sent
            if (sendCommunity()) {
                if (cvar.getType() != CommunityVar.Type.REGEX) {
                    comms = _enc.And(comms, _enc.Eq(e, eOther));
                }
            } else {
                comms = _enc.And(comms, _enc.Not(e));
            }
        }

        // TODO: handle MED correctly (AS-specific? always-compare-med? deterministic-med?)
        ArithExpr otherAd = (p.getOther().getAdminDist() == null ? defaultAd : p.getOther().getAdminDist());
        ArithExpr otherMed = (p.getOther().getMed() == null ? defaultMed : p.getOther().getMed());
        ArithExpr otherMet = getOrDefault(p.getOther().getMetric(), defaultMet);
        ArithExpr otherLp = getOrDefault(p.getOther().getLocalPref(), defaultLp);

        BoolExpr ad = _enc.safeEq(_current.getAdminDist(), otherAd);
        BoolExpr history = _enc.equalHistories(_current, p.getOther());
        BoolExpr med = _enc.safeEq(_current.getMed(), otherMed);
        BoolExpr  met = _enc.safeEq(_current.getMetric(), otherMet);
        BoolExpr lp = _enc.safeEq(_current.getLocalPref(), otherLp);

        BoolExpr updates = _enc.And(per, len, ad, med, lp, met, id, type, area, comms, history, isInternal, igpMet);
        BoolExpr noOverflow = noOverflow(otherMet, _to);
        return _enc.If(noOverflow, updates, _enc.Not(_current.getPermitted()));
    }

    /*
     * Create a new variable reflecting the final return value of the function
     */
    private TransferFunctionResult returnValue(TransferFunctionParam p, TransferFunctionResult r, boolean val) {
        BoolExpr b = _enc.If(r.getReturnAssignedValue(), r.getReturnValue(), _enc.Bool(val));
        BoolExpr newRet = createBoolVariableWith(p, "RETURN", b);
        return r.setReturnValue(newRet)
                .setReturnAssignedValue(_enc.True())
                .addChangedVariable("RETURN", newRet);
    }


    /*
     * The [phi] function from SSA that merges variables that may differ across
     * different branches of an If statement.
     */
    private Pair<Expr,Expr> joinPoint(TransferFunctionParam p, TransferFunctionResult r, BoolExpr guard, Pair<String,Pair<Expr,Expr>> values) {
        String variableName = values.getFirst();
        Expr trueBranch = values.getSecond().getFirst();
        Expr falseBranch = values.getSecond().getSecond();

        if (variableName.equals("RETURN")) {
            Expr t = (trueBranch == null ? r.getReturnValue() : trueBranch);
            Expr f = (falseBranch == null ? r.getReturnValue() : falseBranch);
            BoolExpr newValue = _enc.If(guard, (BoolExpr) t, (BoolExpr) f);
            BoolExpr ret = createBoolVariableWith(p, "RETURN", newValue);
            Expr tass = (trueBranch == null ? r.getReturnAssignedValue() : _enc.True());
            Expr fass = (falseBranch == null ? r.getReturnAssignedValue() : _enc.True());
            BoolExpr newAss = _enc.If(guard, (BoolExpr) tass, (BoolExpr) fass);
            BoolExpr retAss = createBoolVariableWith(p, "ASSIGNED", newAss);
            return new Pair<>(ret, retAss);
        }

        if (variableName.equals("PREFIX-LEN")) {
            Expr t = (trueBranch == null ? p.getOther().getPrefixLength() : trueBranch);
            Expr f = (falseBranch == null ? p.getOther().getPrefixLength() : falseBranch);
            ArithExpr newValue = _enc.If(guard, (ArithExpr) t, (ArithExpr) f);
            newValue = _enc.If(r.getReturnAssignedValue(), p.getOther().getPrefixLength(), newValue);
            ArithExpr ret = createArithVariableWith(p, "PREFIX-LEN", newValue);
            p.getOther().setPrefixLength(ret);
            return new Pair<>(ret, null);
        }
        if (variableName.equals("ADMIN-DIST")) {
            Expr t = (trueBranch == null ? p.getOther().getAdminDist() : trueBranch);
            Expr f = (falseBranch == null ? p.getOther().getAdminDist() : falseBranch);
            ArithExpr newValue = _enc.If(guard, (ArithExpr) t, (ArithExpr) f);
            newValue = _enc.If(r.getReturnAssignedValue(), p.getOther().getAdminDist(), newValue);
            ArithExpr ret = createArithVariableWith(p, "ADMIN-DIST", newValue);
            p.getOther().setAdminDist(ret);
            return new Pair<>(ret, null);
        }
        if (variableName.equals("LOCAL-PREF")) {
            Expr t = (trueBranch == null ? p.getOther().getLocalPref() : trueBranch);
            Expr f = (falseBranch == null ? p.getOther().getLocalPref() : falseBranch);
            ArithExpr newValue = _enc.If(guard, (ArithExpr) t, (ArithExpr) f);
            newValue = _enc.If(r.getReturnAssignedValue(), p.getOther().getLocalPref(), newValue);
            ArithExpr ret = createArithVariableWith(p, "LOCAL-PREF", newValue);
            p.getOther().setLocalPref(ret);
            return new Pair<>(ret, null);
        }
        if (variableName.equals("METRIC")) {
            Expr t = (trueBranch == null ? p.getOther().getMetric() : trueBranch);
            Expr f = (falseBranch == null ? p.getOther().getMetric() : falseBranch);
            ArithExpr newValue = _enc.If(guard, (ArithExpr) t, (ArithExpr) f);
            newValue = _enc.If(r.getReturnAssignedValue(), p.getOther().getMetric(), newValue);
            ArithExpr ret = createArithVariableWith(p, "METRIC", newValue);
            p.getOther().setMetric(ret);
            return new Pair<>(ret, null);
        }
        if (variableName.equals("OSPF-TYPE")) {
            Expr t = (trueBranch == null ? p.getOther().getOspfType().getBitVec() : trueBranch);
            Expr f = (falseBranch == null ? p.getOther().getOspfType().getBitVec() : falseBranch);
            BitVecExpr newValue = _enc.If(guard, (BitVecExpr) t, (BitVecExpr) f);
            newValue = _enc.If(r.getReturnAssignedValue(), p.getOther().getOspfType().getBitVec(), newValue);
            BitVecExpr ret = createBitVecVariableWith(p, "OSPF-TYPE", 2, newValue);
            p.getOther().getOspfType().setBitVec(ret);
            return new Pair<>(ret, null);
        }

        for (Map.Entry<CommunityVar, BoolExpr> entry : p.getOther().getCommunities().entrySet()) {
            CommunityVar cvar = entry.getKey();
            if (variableName.equals(cvar.getValue())) {
                Expr t = (trueBranch == null ? p.getOther().getCommunities().get(cvar) : trueBranch);
                Expr f = (falseBranch == null ? p.getOther().getCommunities().get(cvar) : falseBranch);
                BoolExpr newValue = _enc.If(guard, (BoolExpr) t, (BoolExpr) f);
                newValue = _enc.If(r.getReturnAssignedValue(), p.getOther().getCommunities().get(cvar), newValue);
                BoolExpr ret = createBoolVariableWith(p, cvar.getValue(), newValue);
                p.getOther().getCommunities().put(cvar, ret);
                return new Pair<>(ret, null);
            }
        }

        throw new BatfishException("[joinPoint]: unhandled case for " + variableName);
    }


    // TODO: make fewer copies of mods
    /*
     * Convert a list of statements into a Z3 boolean expression for the transfer function.
     */
    private TransferFunctionResult compute(List<Statement> statements, TransferFunctionParam p) {

        // initialize the return variable
        TransferFunctionResult result = new TransferFunctionResult()
                .setReturnValue(_enc.False())
                .setReturnAssignedValue(_enc.False());

        boolean doesReturn = false;

        for (Statement stmt : statements) {

            if (stmt instanceof StaticStatement) {
                StaticStatement ss = (StaticStatement) stmt;

                switch (ss.getType()) {
                    case ExitAccept:
                        doesReturn = true;
                        p.debug("ExitAccept");
                        result = returnValue(p, result, true);
                        break;

                    case ReturnTrue:
                        doesReturn = true;
                        p.debug("ReturnTrue");
                        result = returnValue(p, result, true);
                        break;

                    case ExitReject:
                        doesReturn = true;
                        p.debug("ExitReject");
                        result = returnValue(p, result, false);
                        break;

                    case ReturnFalse:
                        doesReturn = true;
                        p.debug("ReturnFalse");
                        result = returnValue(p, result, false);
                        break;

                    case SetDefaultActionAccept:
                        p.debug("SetDefaulActionAccept");
                        p = p.setDefaultAccept(true);
                        break;

                    case SetDefaultActionReject:
                        p.debug("SetDefaultActionReject");
                        p = p.setDefaultAccept(false);
                        break;

                    case SetLocalDefaultActionAccept:
                        p.debug("SetLocalDefaultActionAccept");
                        p = p.setDefaultAcceptLocal(true);
                        break;

                    case SetLocalDefaultActionReject:
                        p.debug("SetLocalDefaultActionReject");
                        p = p.setDefaultAcceptLocal(false);
                        break;

                    case ReturnLocalDefaultAction:
                        p.debug("ReturnLocalDefaultAction");
                        // TODO: need to set local default action in an environment
                        if (p.getDefaultAcceptLocal()) {
                            result = returnValue(p, result, true);
                        } else {
                            result = returnValue(p, result, false);
                        }
                        break;

                    case FallThrough:
                        p.debug("Fallthrough");
                        switch (p.getChainContext()) {
                            case NONE:
                                throw new BatfishException("Fallthrough found without chain context");
                            case CONJUNCTION:
                                result = returnValue(p, result, true);
                                break;
                            case DISJUNCTION:
                                result = returnValue(p, result, false);
                                break;
                        }
                        break;

                    case Return:
                        // TODO: I'm assumming this happens at the end of the function, so it is ignored for now.
                        p.debug("Return");
                        break;

                    default:
                        throw new BatfishException("TODO: computeTransferFunction: " + ss.getType());
                }


            } else if (stmt instanceof If) {
                p.debug("If");
                If i = (If) stmt;
                TransferFunctionResult r = compute(i.getGuard(), p);
                result = result.addChangedVariables(r);
                BoolExpr guard = r.getReturnValue();
                p.debug("guard: " + guard.simplify());
                p.debug("True Branch");
                TransferFunctionResult trueBranch = compute(i.getTrueStatements(), p.indent().copyRecord());
                p.debug("False Branch");
                TransferFunctionResult falseBranch = compute(i.getFalseStatements(), p.indent().copyRecord());
                p.debug("JOIN");
                PList<Pair<String, Pair<Expr,Expr>>> pairs = trueBranch.mergeChangedVariables(falseBranch);

                // Extract and deal with the return value first so that other
                // variables have this reflected in their value
                int idx = pairs.find(pair -> pair.getFirst().equals("RETURN"));
                if (idx >= 0) {
                    Pair<String, Pair<Expr,Expr>> ret = pairs.get(idx);
                    pairs = pairs.minus(idx);
                    pairs = pairs.plus(pairs.size(), ret);
                }

                for (Pair<String, Pair<Expr, Expr>> pair : pairs) {
                    String s = pair.getFirst();
                    Pair<Expr,Expr> x = joinPoint(p, result, guard, pair);
                    result = result.addChangedVariable(s, x.getFirst());
                    if (s.equals("RETURN")) {
                        result = result
                                .setReturnValue((BoolExpr) x.getFirst())
                                .setReturnAssignedValue((BoolExpr) x.getSecond());
                    }
                }

            } else if (stmt instanceof SetDefaultPolicy) {
                p.debug("SetDefaultPolicy");
                p = p.setDefaultPolicy((SetDefaultPolicy) stmt);

            } else if (stmt instanceof SetMetric) {
                p.debug("SetMetric");
                SetMetric sm = (SetMetric) stmt;
                IntExpr ie = sm.getMetric();
                ArithExpr newValue = applyIntExprModification(p.getOther().getMetric(), ie);
                newValue = _enc.If(result.getReturnAssignedValue(), p.getOther().getMetric(), newValue);
                ArithExpr x = createArithVariableWith(p, "METRIC", newValue);
                p.getOther().setMetric(x);
                result = result.addChangedVariable("METRIC", x);

            } else if (stmt instanceof SetOspfMetricType) {
                p.debug("SetOspfMetricType");
                SetOspfMetricType somt = (SetOspfMetricType) stmt;
                OspfMetricType mt = somt.getMetricType();
                SymbolicOspfType t;
                if (mt == OspfMetricType.E1) {
                    t = new SymbolicOspfType(_enc, OspfType.E1);
                } else {
                    t = new SymbolicOspfType(_enc, OspfType.E2);
                }
                BitVecExpr newValue = t.getBitVec();
                newValue = _enc.If(result.getReturnAssignedValue(), p.getOther().getOspfType().getBitVec(), newValue);
                BitVecExpr x = createBitVecVariableWith(p, "OSPF-TYPE", 2, newValue);
                p.getOther().getOspfType().setBitVec(x);
                result = result.addChangedVariable("OSPF-TYPE", x);


            } else if (stmt instanceof SetLocalPreference) {
                p.debug("SetLocalPreference");
                SetLocalPreference slp = (SetLocalPreference) stmt;
                IntExpr ie = slp.getLocalPreference();
                ArithExpr newValue = applyIntExprModification(p.getOther().getLocalPref(), ie);
                newValue = _enc.If(result.getReturnAssignedValue(), p.getOther().getLocalPref(), newValue);
                ArithExpr x = createArithVariableWith(p, "LOCAL-PREF", newValue);
                p.getOther().setLocalPref(x);
                result = result.addChangedVariable("LOCAL-PREF", x);

            } else if (stmt instanceof AddCommunity) {
                p.debug("AddCommunity");
                AddCommunity ac = (AddCommunity) stmt;
                Set<CommunityVar> comms = _enc.findAllCommunities(_conf, ac.getExpr());
                for (CommunityVar cvar : comms) {
                    BoolExpr newValue = _enc.If(result.getReturnAssignedValue(), p.getOther().getCommunities().get(cvar), _enc.True());
                    BoolExpr x = createBoolVariableWith(p, cvar.getValue(), newValue);
                    p.getOther().getCommunities().put(cvar, x);
                    result = result.addChangedVariable(cvar.getValue(), x);
                }

            } else if (stmt instanceof DeleteCommunity) {
                p.debug("DeleteCommunity");
                DeleteCommunity ac = (DeleteCommunity) stmt;
                Set<CommunityVar> comms = _enc.findAllCommunities(_conf, ac.getExpr());
                for (CommunityVar cvar : comms) {
                    BoolExpr newValue = _enc.If(result.getReturnAssignedValue(), p.getOther().getCommunities().get(cvar), _enc.False());
                    BoolExpr x = createBoolVariableWith(p, cvar.getValue(), newValue);
                    p.getOther().getCommunities().put(cvar, x);
                    result = result.addChangedVariable(cvar.getValue(), x);
                }

            } else if (stmt instanceof RetainCommunity) {
                p.debug("RetainCommunity");
                // no op

            } else if (stmt instanceof PrependAsPath) {
                p.debug("PrependAsPath");
                PrependAsPath pap = (PrependAsPath) stmt;
                Integer prependCost = prependLength(pap.getExpr());
                ArithExpr newValue = _enc.Sum(p.getOther().getMetric(), _enc.Int(prependCost));
                newValue = _enc.If(result.getReturnAssignedValue(), p.getOther().getMetric(), newValue);
                ArithExpr x = createArithVariableWith(p, "METRIC", newValue);
                p.getOther().setMetric(x);
                result = result.addChangedVariable("METRIC", x);

            } else if (stmt instanceof SetOrigin) {
                p.debug("SetOrigin");
                // TODO: implement me

            } else {
                throw new BatfishException("TODO: statement transfer function: " + stmt);
            }
        }

        // If this is the outermost call, then we relate the variables
        if (p.getInitialCall()) {
            p.debug("InitialCall finalizing");

            // Apply the default action
            if (!doesReturn) {
                p.debug("Applying default action: " + p.getDefaultAccept());
                if (p.getDefaultAccept()) {
                    result = returnValue(p, result, true);
                } else {
                    result = returnValue(p, result, false);
                }
            }

            BoolExpr related = relateVariables(p, result);
            BoolExpr retValue = _enc.If(result.getReturnValue(), related, _enc.Not(_current.getPermitted()) );
            result = result.setReturnValue(retValue);
        }
        return result;
    }


    /*
     * A collection of functions to create new SSA variables on-the-fly,
     * while also simultaneously setting their value based on an old value.
     */
    private ArithExpr createArithVariableWith(TransferFunctionParam p, String name, ArithExpr e) {
        String s = "SSA_" + name + generateId();
        ArithExpr x = _enc.getCtx().mkIntConst(s);
        // _enc.getAllVariables().add(x);
        BoolExpr eq = _enc.Eq(x, e.simplify());
        _enc.add(eq);
        p.debug(eq.toString());
        return x;
    }

    private BoolExpr createBoolVariableWith(TransferFunctionParam p, String name, BoolExpr e) {
        String s = "SSA_" + name + generateId();
        BoolExpr x = _enc.getCtx().mkBoolConst(s);
        // _enc.getAllVariables().add(x);
        BoolExpr eq = _enc.Eq(x, e.simplify());
        _enc.add(eq);
        p.debug(eq.toString());;
        return x;
    }

    private BitVecExpr createBitVecVariableWith(TransferFunctionParam p, String name, int size, BitVecExpr e) {
        String s = "SSA_" + name + generateId();
        BitVecExpr x = _enc.getCtx().mkBVConst(s, size);
        // _enc.getAllVariables().add(x);
        BoolExpr eq = _enc.Eq(x, e.simplify());
        _enc.add(eq);
        p.debug(eq.toString());
        return x;
    }


    /*
     * Create a new variable representing the new prefix length after
     * applying the effect of aggregation.
     */
    private void computeIntermediatePrefixLen(TransferFunctionParam param) {
        ArithExpr prefixLen = param.getOther().getPrefixLength();
        if (_isExport) {
            _aggregates = aggregateRoutes();
            if (_aggregates.size() > 0) {
                for (Map.Entry<Prefix, Boolean> entry : _aggregates.entrySet()) {
                    Prefix prefix = entry.getKey();
                    Boolean isSuppressed = entry.getValue();
                    Prefix p = prefix.getNetworkPrefix();
                    ArithExpr len = _enc.Int(p.getPrefixLength());
                    BoolExpr relevantPfx = _enc.isRelevantFor(p, _enc.getSymbolicPacket().getDstIp());
                    BoolExpr relevantLen = _enc.Gt(param.getOther().getPrefixLength(), len);
                    BoolExpr relevant = _enc.And(relevantPfx, relevantLen, _enc.Bool(isSuppressed));
                    prefixLen = _enc.If(relevant, len, prefixLen);
                }
                ArithExpr i = createArithVariableWith(param, "PREFIX-LEN", prefixLen);
                param.getOther().setPrefixLength(i);
            }
        }
    }

    private void applyMetricUpdate(TransferFunctionParam p) {
        if (_isExport) {
            ArithExpr newValue = _enc.Sum(p.getOther().getMetric(), _enc.Int(_addedCost));
            p.getOther().setMetric(newValue);
        }
    }

    private void setDefaultLocalPref(TransferFunctionParam p) {
        // must be the case that it is an environment variable
        if (p.getOther().getLocalPref() == null) {
            p.getOther().setLocalPref(_enc.Int(100));
        }
    }

    // TODO use better data structure to merge join points on if statements
    public BoolExpr compute() {
        SymbolicRecord o = new SymbolicRecord(_other);
        TransferFunctionParam p = new TransferFunctionParam(o);
        computeIntermediatePrefixLen(p);
        applyMetricUpdate(p);
        setDefaultLocalPref(p);
        TransferFunctionResult result = compute(_statements, p);
        return result.getReturnValue();
    }

}