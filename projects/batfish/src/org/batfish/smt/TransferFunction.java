package org.batfish.smt;


import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.*;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.expr.*;
import org.batfish.datamodel.routing_policy.statement.*;

import java.util.*;

import static org.batfish.datamodel.routing_policy.statement.Statements.*;

/**
 * <p>Class that computes a symbolic transfer function between
 * two symbolic control plane records. The transfer function
 * is used to encode both import and export filters.</p>
 *
 * <p>Batfish represents the AST much like vendors where there
 * is a simple imperative language for matching fields and
 * making modifications to fields. Since this is not a good
 * fit for a declarative symbolic encoding of the network,
 * we convert this stateful representation into a stateless
 * representation using a form of continuation passing style.</p>
 *
 * <p>The TransferFunction class makes policies stateless by inlining
 * the result of function calls. The _contTrue and _contFalse contexts
 * maintain the "remaining" policy statements that need to be inlined
 * as the policy is converted to a stateless form. While traversing the
 * ast, a collection of modifications are accumulated before being applied
 * when the AST exits successfully.</p>
 *
 * @author Ryan Beckett
 */
class TransferFunction {

    private EncoderSlice _enc;

    private Configuration _conf;

    private SymbolicRecord _other;

    private SymbolicRecord _current;

    private Protocol _to;

    private Protocol _from;

    private List<Statement> _statements;

    private Integer _addedCost;

    private Interface _iface;

    private GraphEdge _graphEdge;

    private Stack<Queue<BooleanExpr>> _conjOperands;

    private Stack<List<Statement>> _contTrue;

    private Stack<List<Statement>> _contFalse;

    private Map<Prefix, Boolean> _aggregates;

    private ArithExpr _prefixLen;

    private boolean _isExport;

    TransferFunction(EncoderSlice encoderSlice, Configuration conf, SymbolicRecord other,
            SymbolicRecord current, Protocol to, Protocol from, List<Statement>
            statements, Integer addedCost, GraphEdge ge, boolean isExport) {
        _enc = encoderSlice;
        _conf = conf;
        _other = other;
        _current = current;
        _to = to;
        _from = from;
        _statements = statements;
        _addedCost = addedCost;
        _graphEdge = ge;
        _iface = ge.getStart();
        _isExport = isExport;
        _aggregates = null;
        _prefixLen = null;
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
    private BoolExpr matchFilterList(RouteFilterList x) {
        BoolExpr acc = _enc.False();

        List<RouteFilterLine> lines = new ArrayList<>(x.getLines());
        Collections.reverse(lines);

        for (RouteFilterLine line : lines) {
            Prefix p = line.getPrefix();
            SubRange r = line.getLengthRange();
            PrefixRange range = new PrefixRange(p, r);
            BoolExpr matches = _enc.isRelevantFor(_prefixLen, range);
            BoolExpr action = _enc.Bool(line.getAction() == LineAction.ACCEPT);
            acc = _enc.If(matches, action, acc);
        }
        return acc;
    }

    /*
     * Converts a prefix set to a boolean expression.
     */
    private BoolExpr matchPrefixSet(Configuration conf, PrefixSetExpr e) {
        if (e instanceof ExplicitPrefixSet) {
            ExplicitPrefixSet x = (ExplicitPrefixSet) e;

            Set<PrefixRange> ranges = x.getPrefixSpace().getPrefixRanges();
            if (ranges.isEmpty()) {
                return _enc.True();
            }

            BoolExpr acc = _enc.False();
            for (PrefixRange range : ranges) {
                acc = _enc.Or(acc, _enc.isRelevantFor(_prefixLen, range));
            }
            return acc;

        } else if (e instanceof NamedPrefixSet) {
            NamedPrefixSet x = (NamedPrefixSet) e;
            String name = x.getName();
            RouteFilterList fl = conf.getRouteFilterLists().get(name);
            return matchFilterList(fl);

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
    private BoolExpr matchCommunitySet(Configuration conf, CommunitySetExpr e, SymbolicRecord
            other) {
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
     * Wrap a boolean expression as an equivalent If statement
     * to convert back and forth between these representations.
     */
    private List<Statement> wrapExpr(BooleanExpr expr) {
        If i = new If();
        List<Statement> tru = new ArrayList<>();
        List<Statement> fal = new ArrayList<>();
        tru.add(new Statements.StaticStatement(ReturnTrue));
        fal.add(new Statements.StaticStatement(ReturnFalse));
        i.setGuard(expr);
        i.setTrueStatements(tru);
        i.setFalseStatements(fal);
        return Collections.singletonList(i);
    }

    /*
     * Convert a Batfish AST boolean expression to a symbolic Z3 boolean expression
     * by performing inlining of stateful side effects.
     */
    private BoolExpr compute(BooleanExpr expr, Modifications mods, boolean pure, boolean
            inExprCall, boolean inStmtCall) {

        Modifications freshMods = new Modifications(mods);

        if (expr instanceof Conjunction) {
            Conjunction c = (Conjunction) expr;
            if (pure) {
                BoolExpr v = _enc.True();
                for (BooleanExpr x : c.getConjuncts()) {
                    v = _enc.And(v, compute(x, freshMods, pure, inExprCall, inStmtCall));
                }
                return v;
            } else {
                Queue<BooleanExpr> queue = new ArrayDeque<>(c.getConjuncts());
                BooleanExpr x = queue.remove();
                _conjOperands.push(queue);
                BoolExpr ret = compute(wrapExpr(x), freshMods, inExprCall, inStmtCall);
                _conjOperands.pop();
                return ret;
            }
        }

        if (expr instanceof Disjunction) {
            Disjunction d = (Disjunction) expr;
            BoolExpr v = _enc.False();
            for (BooleanExpr x : d.getDisjuncts()) {
                v = _enc.Or(v, compute(x, freshMods, pure, inExprCall, inStmtCall));
            }
            return v;
        }

        if (expr instanceof DisjunctionChain) {
            DisjunctionChain d = (DisjunctionChain) expr;
            // Add the default policy
            List<BooleanExpr> disjuncts = new ArrayList<>(d.getSubroutines());
            if (mods.getSetDefaultPolicy() != null) {
                BooleanExpr be = new CallExpr(mods.getSetDefaultPolicy().getDefaultPolicy());
                disjuncts.add(be);
            }
            // TODO: I'm not entirely sure how to handle this due to the side effects
            if (disjuncts.size() == 0) {
                return _enc.True();
            } else if (disjuncts.size() == 1) {
                return compute(disjuncts.get(0), freshMods, pure, true, inStmtCall);
            } else {
                System.out.println("Router: " + _conf.getName());
                throw new BatfishException("TODO: disjunct chain longer than length 1");
            }
        }

        if (expr instanceof Not) {
            Not n = (Not) expr;
            BoolExpr v = compute(n.getExpr(), mods, pure, inExprCall, inStmtCall);
            return _enc.Not(v);
        }

        if (expr instanceof MatchProtocol) {
            MatchProtocol mp = (MatchProtocol) expr;

            Protocol p = Protocol.fromRoutingProtocol(mp.getProtocol());
            if (p == null) {
                return _enc.False();
            }

            if (_other.getProtocolHistory() == null) {
                return _enc.Bool(p.equals(_from));
            }
            return _other.getProtocolHistory().checkIfValue(p);
        }

        if (expr instanceof MatchPrefixSet) {
            MatchPrefixSet m = (MatchPrefixSet) expr;
            return matchPrefixSet(_conf, m.getPrefixSet());

        // TODO: implement me
        } else if (expr instanceof MatchPrefix6Set) {
            return _enc.False();

        } else if (expr instanceof CallExpr) {
            CallExpr c = (CallExpr) expr;
            String name = c.getCalledPolicyName();
            RoutingPolicy pol = _conf.getRoutingPolicies().get(name);
            return compute(pol.getStatements(), freshMods, inExprCall, true);

        } else if (expr instanceof WithEnvironmentExpr) {
            // TODO: this is not correct
            WithEnvironmentExpr we = (WithEnvironmentExpr) expr;
            return compute(we.getExpr(), freshMods, pure, inExprCall, inStmtCall);

        } else if (expr instanceof MatchCommunitySet) {
            MatchCommunitySet mcs = (MatchCommunitySet) expr;
            return matchCommunitySet(_conf, mcs.getExpr(), _other);

        } else if (expr instanceof BooleanExprs.StaticBooleanExpr) {
            BooleanExprs.StaticBooleanExpr b = (BooleanExprs.StaticBooleanExpr) expr;
            switch (b.getType()) {
                case CallExprContext:
                    return _enc.Bool(inExprCall);
                case CallStatementContext:
                    return _enc.Bool(inStmtCall);
                case True:
                    return _enc.True();
                case False:
                    return _enc.False();
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
     * Determine if BGP should transmit the
     * local preference attribute to the neighboring peer.
     */
    private boolean sendLocalPref() {
        return !_to.isBgp() || _graphEdge.isAbstract();
    }

    /*
     * Apply the effect of the accumulated modifications
     */
    private BoolExpr applyModifications(Modifications mods) {
        ArithExpr defaultLen = _enc.Int(_enc.defaultLength());
        ArithExpr defaultAd = _enc.Int(_enc.defaultAdminDistance(_conf, _from));
        ArithExpr defaultMed = _enc.Int(_enc.defaultMed(_from));
        ArithExpr defaultLp = _enc.Int(_enc.defaultLocalPref());
        ArithExpr defaultId = _enc.Int(_enc.defaultId());
        ArithExpr defaultMet = _enc.Int(_enc.defaultMetric(_from));

        BoolExpr met;
        ArithExpr metValue;
        ArithExpr otherMet = getOrDefault(_other.getMetric(), defaultMet);

        // Update the path metric
        if (mods.getSetMetric() == null) {
            Integer addedCost;

            if (mods.getPrependPath() != null) {
                addedCost = _addedCost + prependLength(mods.getPrependPath().getExpr());
            } else {
                addedCost = _addedCost;
            }

            metValue = _enc.Sum(otherMet, _enc.Int(addedCost));
            met = _enc.safeEqAdd(_current.getMetric(), otherMet, addedCost);
        } else {
            IntExpr ie = mods.getSetMetric().getMetric();
            metValue = applyIntExprModification(otherMet, ie);

            if (mods.getPrependPath() != null) {
                Integer prependCost = prependLength(mods.getPrependPath().getExpr());
                metValue = _enc.Sum(metValue, _enc.Int(prependCost));
            }

            met = _enc.safeEq(_current.getMetric(), metValue);
        }


        boolean isIbgp = _graphEdge.isAbstract() && _to.isBgp();

        // Update local preference
        BoolExpr lp;
        ArithExpr otherLp = getOrDefault(_other.getLocalPref(), defaultLp);
        if (mods.getSetLp() == null) {
            // If it is an ibgp edge, then copy local preference
            if (isIbgp) {
                lp = _enc.safeEq(_current.getLocalPref(), otherLp);
            }
            // Otherwise, we use the default local preference value
            else {
                // Use a value of 100 for export too since we might merge records
                lp = _enc.safeEq(_current.getLocalPref(), _enc.Int(100));
            }
        } else {
            IntExpr ie = mods.getSetLp().getLocalPreference();
            lp = _enc.safeEq(_current.getLocalPref(), applyIntExprModification(otherLp, ie));
        }

        // Update prefix length when aggregation
        BoolExpr len = _enc.safeEq(_current.getPrefixLength(), getOrDefault(_prefixLen,
                defaultLen));

        BoolExpr per = _enc.safeEq(_current.getPermitted(), _other.getPermitted());

        BoolExpr id = _enc.safeEq(_current.getRouterId(), getOrDefault(_other.getRouterId(),
                defaultId));

        // Update OSPF area id
        BoolExpr area;
        if (_other.getOspfArea() == null || _iface.getOspfAreaName() == null) {
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
        if (mods.getSetOspfMetricType() != null) {
            OspfMetricType mt = mods.getSetOspfMetricType().getMetricType();
            if (mt == OspfMetricType.E1) {
                type = _current.getOspfType().checkIfValue(OspfType.E1);
            } else {
                type = _current.getOspfType().checkIfValue(OspfType.E2);
            }
        } else {
            boolean hasAreaIface = _iface.getOspfAreaName() != null;
            boolean hasArea = _other.getOspfArea() != null;
            boolean hasType = _other.getOspfType() != null;
            boolean areaPossiblyChanged = hasType && hasArea && hasAreaIface;
            // Check if area changed
            if (areaPossiblyChanged) {
                BoolExpr internal = _other.getOspfType().isInternal();
                BoolExpr same = _other.getOspfArea().checkIfValue(_iface.getOspfAreaName());
                BoolExpr update = _enc.And(internal, _enc.Not(same));
                BoolExpr copyOld = _enc.safeEqEnum(_current.getOspfType(), _other.getOspfType());
                type = _enc.If(update, _current.getOspfType().checkIfValue(OspfType.OIA), copyOld);
            } else {
                type = _enc.safeEqEnum(_current.getOspfType(), _other.getOspfType());
            }
        }

        BoolExpr comms = _enc.True();

        // regex matches that now match due to the concrete added value
        // update all community values
        for (Map.Entry<CommunityVar, BoolExpr> entry : _current.getCommunities().entrySet()) {
            CommunityVar cvar = entry.getKey();
            BoolExpr e = entry.getValue();
            BoolExpr eOther = _other.getCommunities().get(cvar);
            // Update the communities if they should be sent
            if (sendCommunity()) {
                if (mods.getPositiveCommunities().contains(cvar)) {
                    comms = _enc.And(comms, e);
                } else if (mods.getNegativeCommunities().contains(cvar)) {
                    comms = _enc.And(comms, _enc.Not(e));
                } else if (cvar.getType() != CommunityVar.Type.REGEX) {
                    comms = _enc.And(comms, _enc.Eq(e, eOther));
                }
            } else {
                comms = _enc.And(comms, _enc.Not(e));
            }
        }

        // TODO: handle MED correctly (AS-specific? always-compare-med? deterministic-med?)
        ArithExpr otherAd = (_other.getAdminDist() == null ? defaultAd : _other.getAdminDist());
        ArithExpr otherMed = (_other.getMed() == null ? defaultMed : _other.getMed());

        // Update the administrative distance
        BoolExpr ad = _enc.safeEq(_current.getAdminDist(), otherAd);

        BoolExpr history = _enc.equalHistories(_from, _current, _other);
        BoolExpr med = _enc.safeEq(_current.getMed(), otherMed);

        BoolExpr updates = _enc.And(per, len, ad, med, lp, met, id, type, area, comms, history, isInternal, igpMet);
        BoolExpr noOverflow = noOverflow(metValue, _to);

        return _enc.If(noOverflow, updates, _enc.Not(_current.getPermitted()));
    }

    /*
     * Determine if a boolean expression has side effects
     */
    private boolean isNotPure(BooleanExpr be) {
        AstVisitor v = new AstVisitor();
        Boolean[] val = new Boolean[1];
        val[0] = false;
        v.visit(_conf, be, stmt -> {
            val[0] = true;
        }, expr -> {
            if (expr instanceof DisjunctionChain || expr instanceof ConjunctionChain) {
                val[0] = true;
            }
        });
        return val[0];
    }

    /*
     * Handle a return true statement
     */
    private BoolExpr returnTrue(Modifications mods, boolean inExprCall, boolean inStmtCall) {
        Modifications newMods = new Modifications(mods);
        // TODO: we might introduce a returnTrue, so this might not be right
        newMods.setDefaultAcceptLocal(false);
        if (!_conjOperands.isEmpty() && !_conjOperands.peek().isEmpty()) {
            Queue<BooleanExpr> queue = _conjOperands.peek();
            BooleanExpr x = queue.poll();
            return compute(wrapExpr(x), mods, inExprCall, inStmtCall);
        } else if (!_contTrue.isEmpty()) {
            List<Statement> t = _contTrue.pop();
            List<Statement> f = _contFalse.pop();
            BoolExpr ret = compute(t, mods, inExprCall, inStmtCall);
            _contTrue.push(t);
            _contFalse.push(f);
            return ret;
        } else {
            return applyModifications(mods);
        }
    }

    /*
     * Handle a return false statement
     */
    private BoolExpr returnFalse(Modifications mods, boolean inExprCall, boolean inStmtCall) {
        Modifications newMods = new Modifications(mods);
        newMods.setDefaultAcceptLocal(false);
        /* if (!_conjOperands.isEmpty() && !_conjOperands.peek().isEmpty()) {
            Queue<BooleanExpr> queue = _conjOperands.peek();
            BooleanExpr x = queue.poll();
            return compute(wrapExpr(x), mods, inExprCall, inStmtCall);
        } else */ if (!_contFalse.isEmpty()) {
            List<Statement> t = _contTrue.pop();
            List<Statement> f = _contFalse.pop();
            BoolExpr ret = compute(f, mods, inExprCall, inStmtCall);
            _contTrue.push(t);
            _contFalse.push(f);
            return ret;
        } else {
            return _enc.Not(_current.getPermitted());
        }
    }


    // TODO: make fewer copies of mods
    /*
     * Convert a list of statements into a Z3 boolean expression for the transfer function.
     */
    private BoolExpr compute(List<Statement> statements, Modifications mods, boolean inExprCall,
            boolean inStmtCall) {
        Modifications freshMods = new Modifications(mods);

        ListIterator<Statement> it = statements.listIterator();
        while (it.hasNext()) {
            Statement s = it.next();

            if (s instanceof Statements.StaticStatement) {
                Statements.StaticStatement ss = (Statements.StaticStatement) s;

                if (ss.getType() == ExitAccept || ss.getType() == ReturnTrue) {
                    return returnTrue(freshMods, inExprCall, inStmtCall);

                } else if (ss.getType() == ExitReject || ss.getType() == ReturnFalse) {
                    return returnFalse(freshMods, inExprCall, inStmtCall);

                } else if (ss.getType() == SetDefaultActionAccept) {
                    freshMods.addModification(s);

                } else if (ss.getType() == SetDefaultActionReject) {
                    freshMods.addModification(s);

                } else if (ss.getType() == SetLocalDefaultActionAccept) {
                    freshMods.addModification(s);

                } else if (ss.getType() == SetLocalDefaultActionReject) {
                    freshMods.addModification(s);

                } else if (ss.getType() == ReturnLocalDefaultAction) {
                    // TODO: need to set local default action in an environment
                    if (freshMods.getDefaultAcceptLocal()) {
                        return returnTrue(freshMods, inExprCall, inStmtCall);
                    } else {
                        return returnFalse(freshMods, inExprCall, inStmtCall);
                    }

                } else {
                    throw new BatfishException("TODO: computeTransferFunction: " + ss.getType());
                }

            } else if (s instanceof If) {
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

                if (isNotPure(i.getGuard())) {
                    _contTrue.push(remainingx);
                    _contFalse.push(remainingy);
                    BoolExpr ret = compute(i.getGuard(), freshMods, false, inExprCall, inStmtCall);
                    _contTrue.pop();
                    _contFalse.pop();
                    return ret;
                } else {
                    Modifications modsTrue = new Modifications(freshMods);
                    Modifications modsFalse = new Modifications(freshMods);
                    BoolExpr trueBranch = compute(remainingx, modsTrue, inExprCall, inStmtCall);
                    BoolExpr falseBranch = compute(remainingy, modsFalse, inExprCall, inStmtCall);
                    BoolExpr guard = compute(i.getGuard(), freshMods, true, inExprCall, inStmtCall);
                    return _enc.If(guard, trueBranch, falseBranch);
                }

            } else if (s instanceof SetDefaultPolicy) {
                freshMods.addModification(s);

            } else if (s instanceof SetMetric) {
                freshMods.addModification(s);

            } else if (s instanceof SetOspfMetricType) {
                freshMods.addModification(s);

            } else if (s instanceof SetLocalPreference) {
                freshMods.addModification(s);

            } else if (s instanceof AddCommunity) {
                freshMods.addModification(s);

            } else if (s instanceof DeleteCommunity) {
                freshMods.addModification(s);

            } else if (s instanceof RetainCommunity) {
                freshMods.addModification(s);

            } else if (s instanceof PrependAsPath) {
                freshMods.addModification(s);

            // TODO: implement me
            } else if (s instanceof SetOrigin) {

            } else {
                throw new BatfishException("TODO: statement transfer function: " + s);
            }
        }

        if (freshMods.getDefaultAccept()) {
            return returnTrue(freshMods, inExprCall, inStmtCall);
        } else {
            return returnFalse(freshMods, inExprCall, inStmtCall);
        }
    }

    /*
     * Create a new variable representing the new prefix length after
     * applying the effect of aggregation.
     */
    private void computeIntermediatePrefixLen() {
        _prefixLen = _other.getPrefixLength();

        if (_isExport) {
            _aggregates = aggregateRoutes();

            if (_aggregates.size() > 0) {
                String otherName = _other.getName();
                String name = (otherName == null ? ("TEMP" + _enc.generateId()) : otherName);

                ArithExpr i = _enc.getCtx().mkIntConst(name + "_NEW-LEN(" + _iface
                        .getName() + ")");
                _enc.getAllVariables().add(i);

                _aggregates.forEach((prefix, isSuppressed) -> {
                    Prefix p = prefix.getNetworkPrefix();
                    ArithExpr len = _enc.Int(p.getPrefixLength());
                    BoolExpr relevantPfx = _enc.isRelevantFor(p, _enc.getSymbolicPacket().getDstIp());
                    BoolExpr relevantLen = _enc.Gt(_other.getPrefixLength(), len);
                    BoolExpr relevant = _enc.And(relevantPfx, relevantLen, _enc.Bool(isSuppressed));
                    _prefixLen = _enc.If(relevant, len, _prefixLen);
                });

                _enc.add(_enc.Eq(i, _prefixLen));
                _prefixLen = i;
            }
        }
    }

    BoolExpr compute() {
        computeIntermediatePrefixLen();
        Modifications mods = new Modifications(_enc, _conf);
        _conjOperands = new Stack<>();
        _contTrue = new Stack<>();
        _contFalse = new Stack<>();
        return compute(_statements, mods, false, false);
    }

}
