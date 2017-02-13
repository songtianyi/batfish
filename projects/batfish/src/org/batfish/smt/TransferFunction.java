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

public class TransferFunction {

    private Encoder _enc;

    private Configuration _conf;

    private SymbolicRecord _other;

    private SymbolicRecord _current;

    private RoutingProtocol _to;

    private RoutingProtocol _from;

    private List<Statement> _statements;

    private Integer _addedCost;

    private Stack<Queue<BooleanExpr>> _operands;

    private Stack<List<Statement>> _contTrue;

    private Stack<List<Statement>> _contFalse;

    public TransferFunction(Encoder encoder, Configuration conf, SymbolicRecord other, SymbolicRecord current, RoutingProtocol to, RoutingProtocol from, List<Statement> statements, Integer addedCost) {
        _enc = encoder;
        _conf = conf;
        _other = other;
        _current = current;
        _to = to;
        _from = from;
        _statements = statements;
        _addedCost = addedCost;
    }

    private BoolExpr matchFilterList(RouteFilterList x) {
        BoolExpr acc = _enc.False();

        List<RouteFilterLine> lines = new ArrayList<>(x.getLines());
        Collections.reverse(lines);

        for (RouteFilterLine line : lines) {
            Prefix p = line.getPrefix();
            SubRange r = line.getLengthRange();
            PrefixRange range = new PrefixRange(p, r);
            BoolExpr matches = _enc.isRelevantFor(_other, range);
            BoolExpr action = _enc.Bool(line.getAction() == LineAction.ACCEPT);
            acc = _enc.If(matches, action, acc);
        }
        return acc;
    }

    private BoolExpr matchPrefixSet(Configuration conf, PrefixSetExpr e) {
        if (e instanceof ExplicitPrefixSet) {
            ExplicitPrefixSet x = (ExplicitPrefixSet) e;

            Set<PrefixRange> ranges = x.getPrefixSpace().getPrefixRanges();
            if (ranges.isEmpty()) {
                return _enc.True();
            }

            BoolExpr acc = _enc.False();
            for (PrefixRange range : ranges) {
                acc = _enc.Or(acc, _enc.isRelevantFor(_other, range));
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

    private BoolExpr compute(BooleanExpr expr, Modifications mods) {

        Modifications freshMods = new Modifications(mods);

        if (expr instanceof Conjunction) {
            Conjunction c = (Conjunction) expr;
            Queue<BooleanExpr> queue = new ArrayDeque<>(c.getConjuncts());
            BooleanExpr x = queue.remove();
            _operands.push(queue);
            BoolExpr ret = compute(wrapExpr(x), freshMods);
            _operands.pop();
            return ret;
        }
        if (expr instanceof Disjunction) {
            Disjunction d = (Disjunction) expr;
            BoolExpr v = _enc.False();
            for (BooleanExpr x : d.getDisjuncts()) {
                v = _enc.Or(v, compute(x, freshMods));
            }
            return v;
        }
        if (expr instanceof Not) {
            Not n = (Not) expr;
            //return compute(wrapExpr(n.getExpr()), freshMods);
            BoolExpr v = compute(n.getExpr(), mods);
            return _enc.Not(v);
        }
        if (expr instanceof MatchProtocol) {
            MatchProtocol mp = (MatchProtocol) expr;
            RoutingProtocol p = mp.getProtocol();
            if (_other.getProtocolHistory() == null) {
                return _enc.Bool(mp.getProtocol() == _from);
            }
            return _other.getProtocolHistory().checkIfValue(p);
        }
        if (expr instanceof MatchPrefixSet) {
            MatchPrefixSet m = (MatchPrefixSet) expr;
            return matchPrefixSet(_conf, m.getPrefixSet());
        }
        else if (expr instanceof CallExpr) {
            CallExpr c = (CallExpr) expr;
            String name = c.getCalledPolicyName();
            RoutingPolicy pol = _conf.getRoutingPolicies().get(name);
            return compute(pol.getStatements(), freshMods);
        }
        else if (expr instanceof WithEnvironmentExpr) {
            // TODO: this is not correct
            WithEnvironmentExpr we = (WithEnvironmentExpr) expr;
            return compute(we.getExpr(), freshMods);
        }
        else if (expr instanceof MatchCommunitySet) {
            MatchCommunitySet mcs = (MatchCommunitySet) expr;
            return matchCommunitySet(_conf, mcs.getExpr(), _other);
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

    private BoolExpr applyModifications(Modifications mods) {
        ArithExpr defaultLen = _enc.Int(_enc.defaultLength());
        ArithExpr defaultAd = _enc.Int(_enc.defaultAdminDistance(_conf, _from));
        ArithExpr defaultMed = _enc.Int(_enc.defaultMed(_from));
        ArithExpr defaultLp = _enc.Int(_enc.defaultLocalPref());
        ArithExpr defaultId = _enc.Int(_enc.defaultId());
        ArithExpr defaultMet = _enc.Int(_enc.defaultMetric(_from));

        BoolExpr met;
        ArithExpr otherMet = getOrDefault(_other.getMetric(), defaultMet);
        if (mods.getSetMetric() == null) {
            met = _enc.safeEqAdd(_current.getMetric(), otherMet, _addedCost);
        } else {
            IntExpr ie = mods.getSetMetric().getMetric();
            ArithExpr val = applyIntExprModification(otherMet, ie);
            met = _enc.safeEq(_current.getMetric(), val);
        }

        BoolExpr lp;
        ArithExpr otherLp = getOrDefault(_other.getLocalPref(), defaultLp);
        if (mods.getSetLp() == null) {
            lp = _enc.safeEq(_current.getLocalPref(), otherLp);
        } else {
            IntExpr ie = mods.getSetLp().getLocalPreference();
            lp = _enc.safeEq(_current.getLocalPref(), applyIntExprModification(otherLp, ie));
        }

        BoolExpr per = _enc.safeEq(_current.getPermitted(), _other.getPermitted());
        BoolExpr len =
                _enc.safeEq(_current.getPrefixLength(), getOrDefault(_other.getPrefixLength(), defaultLen));
        BoolExpr id = _enc.safeEq(_current.getRouterId(), getOrDefault(_other.getRouterId(), defaultId));

        BoolExpr comms = _enc.True();

        // regex matches that now match due to the concrete added value
        // update all community values
        for (Map.Entry<CommunityVar, BoolExpr> entry : _current.getCommunities().entrySet()) {
            CommunityVar cvar = entry.getKey();
            BoolExpr e = entry.getValue();
            BoolExpr eOther = _other.getCommunities().get(cvar);

            if (mods.getPositiveCommunities().contains(cvar)) {
                comms = _enc.And(comms, e);
            }
            else if (mods.getNegativeCommunities().contains(cvar)) {
                comms = _enc.And(comms, _enc.Not(e));
            }
            else if (cvar.getType() != CommunityVar.Type.REGEX) {
                comms = _enc.And(comms, _enc.Eq(e, eOther));
            }
            // Note: regexes are defined implicitly in terms of OTHER/EXACT
        }

        // TODO: handle AD correctly
        // TODO: handle MED correctly
        // TODO: what about transitivity?
        // TODO: communities are transmitted to neighbors?
        ArithExpr otherAd = (_other.getAdminDist() == null ? defaultAd : _other.getAdminDist());
        ArithExpr otherMed = (_other.getMed() == null ? defaultMed : _other.getMed());

        // Set the protocol histories equal if needed

        BoolExpr history = _enc.equalHistories(_from, _current, _other);
        BoolExpr ad = _enc.safeEq(_current.getAdminDist(), otherAd);
        BoolExpr med = _enc.safeEq(_current.getMed(), otherMed);

        return _enc.And(per, len, ad, med, lp, met, id, comms, history);
    }

    private boolean hasStatement(BooleanExpr be) {
        AstVisitor v = new AstVisitor();
        Boolean[] val = new Boolean[1];
        val[0] = false;
        v.visit(_conf, be, stmt -> {
            val[0] = true;
        }, expr -> {});
        return val[0];
    }

    private BoolExpr returnTrue(Modifications mods) {
        if (!_operands.isEmpty() && !_operands.peek().isEmpty()) {
            Queue<BooleanExpr> queue = _operands.peek();
            BooleanExpr x = queue.poll();
            return compute(wrapExpr(x), mods);
        }
        else if (!_contTrue.isEmpty()) {
            List<Statement> t = _contTrue.pop();
            List<Statement> f = _contFalse.pop();
            BoolExpr ret = compute(t, mods);
            _contTrue.push(t);
            _contFalse.push(f);
            return ret;
        } else {
            return applyModifications(mods);
        }
    }

    private BoolExpr returnFalse(Modifications mods) {
        if (!_operands.isEmpty() && !_operands.peek().isEmpty()) {
            return compute(_contFalse.peek(), mods);
        }
        else if (!_contFalse.isEmpty()) {
            List<Statement> t = _contTrue.pop();
            List<Statement> f = _contFalse.pop();
            BoolExpr ret = compute(f, mods);
            _contTrue.push(t);
            _contFalse.push(f);
            return ret;
        } else {
            return _enc.Not(_current.getPermitted());
        }
    }

    // TODO: make fewer copies of mods
    private BoolExpr compute(List<Statement> statements, Modifications mods) {
        Modifications freshMods = new Modifications(mods);

        ListIterator<Statement> it = statements.listIterator();
        while (it.hasNext()) {
            Statement s = it.next();

            if (s instanceof Statements.StaticStatement) {
                Statements.StaticStatement ss = (Statements.StaticStatement) s;

                if (ss.getType() == ExitAccept || ss.getType() == ReturnTrue) {
                    return returnTrue(freshMods);

                } else if (ss.getType() == ExitReject || ss.getType() == ReturnFalse) {
                    return returnFalse(freshMods);

                } else if (ss.getType() == SetDefaultActionAccept) {
                    freshMods.addModification(s);

                } else if (ss.getType() == SetDefaultActionReject) {
                    freshMods.addModification(s);

                } else if (ss.getType() == ReturnLocalDefaultAction) {
                    // TODO: need to set local default action in an environment
                    if (freshMods.getDefaultAcceptLocal()) {
                        return returnTrue(freshMods);
                    } else {
                        return returnFalse(freshMods);
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

                if (hasStatement(i.getGuard())) {
                    _contTrue.push(remainingx);
                    _contFalse.push(remainingy);
                    BoolExpr ret = compute(i.getGuard(), freshMods);
                    _contTrue.pop();
                    _contFalse.pop();
                    return ret;
                } else {
                    Modifications modsTrue = new Modifications(freshMods);
                    Modifications modsFalse = new Modifications(freshMods);
                    BoolExpr trueBranch = compute(remainingx, modsTrue);
                    BoolExpr falseBranch = compute(remainingy, modsFalse);
                    BoolExpr guard = compute(i.getGuard(), freshMods);
                    return _enc.If(guard, trueBranch, falseBranch);
                }

            } else if (s instanceof SetOspfMetricType || s instanceof SetMetric) {
                freshMods.addModification(s);

            } else if (s instanceof SetLocalPreference) {
                freshMods.addModification(s);

            } else if (s instanceof AddCommunity) {
                freshMods.addModification(s);

            } else if (s instanceof DeleteCommunity) {
                freshMods.addModification(s);

            } else if (s instanceof  RetainCommunity) {
                freshMods.addModification(s);

            } else {
                throw new BatfishException("TODO: statement transfer function: " + s);
            }
        }

        if (freshMods.getDefaultAccept()) {
            return returnTrue(mods);
        } else {
            return returnFalse(mods);
        }
    }

    public BoolExpr compute() {
        Modifications mods = new Modifications(_enc, _conf);
        _operands = new Stack<>();
        _contTrue = new Stack<>();
        _contFalse = new Stack<>();
        return compute(_statements, mods);
    }

}
