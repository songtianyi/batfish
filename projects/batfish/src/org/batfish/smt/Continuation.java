package org.batfish.smt;


import org.batfish.datamodel.routing_policy.expr.BooleanExpr;
import org.batfish.smt.collections.PList;

import java.util.List;

public class Continuation {

    public enum ChainContext {CONJUNCTION, DISJUNCTION, NONE}

    public PList<String> trace;

    public PList<ChainContext> continuationChainContexts;

    public PList<PList<BooleanExpr>> continuationChain;

    Continuation() {
        this.trace = PList.empty();
        this.continuationChainContexts = PList.empty();
        this.continuationChain = PList.empty();
    }

    private Continuation(Continuation c) {
        this.trace = c.trace;
        this.continuationChainContexts = c.continuationChainContexts;
        this.continuationChain = c.continuationChain;
    }

    public Continuation addConjunctionChain(List<BooleanExpr> exprs) {
        Continuation ret = new Continuation(this);
        PList<BooleanExpr> es = PList.from(exprs);
        ret.continuationChain = ret.continuationChain.plus(es);
        ret.continuationChainContexts = ret.continuationChainContexts.plus(ChainContext.CONJUNCTION);
        return ret;
    }


    public Continuation addDisjunctionChain(List<BooleanExpr> exprs) {
        Continuation ret = new Continuation(this);
        PList<BooleanExpr> es = PList.from(exprs);
        ret.continuationChain = ret.continuationChain.plus(es);
        ret.continuationChainContexts = ret.continuationChainContexts.plus(ChainContext.DISJUNCTION);
        return ret;
    }

    public Continuation popChainElement() {
        Continuation ret = new Continuation(this);
        PList<BooleanExpr> elem = ret.continuationChain.get(0);
        PList<BooleanExpr> remaining = elem.minus(0);
        if (remaining.isEmpty()) {
            ret.continuationChain = ret.continuationChain.minus(0);
            ret.continuationChainContexts = ret.continuationChainContexts.minus(0);
        } else {
            ret.continuationChain = ret.continuationChain.with(0, remaining);
        }
        return ret;
    }

    public boolean isConjunctionChainContext() {
        return this.continuationChainContexts.get(0) == ChainContext.CONJUNCTION;
    }

    public boolean isDisjunctionChainContext() {
        return this.continuationChainContexts.get(0) == ChainContext.DISJUNCTION;
    }

    public BooleanExpr peekChainElement() {
        return this.continuationChain.get(0).get(0);
    }

    public Continuation indent(String n) {
        Continuation ret = new Continuation(this);
        if (n != null) {
            ret.trace = ret.trace.plus(n);
        }
        return ret;
    }

    public void println(String s) {
        if (Encoder.ENABLE_DEBUGGING) {
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < this.trace.size(); i++) {
                sb.append(" ");
            }
            sb.append("[");
            String str;
            if (this.trace.isEmpty()) {
                str = "";
            } else {
                str = this.trace.get(0);
            }
            sb.append(str);
            sb.append("]: ");
            sb.append(s);
            System.out.println(sb.toString());
        }
    }

    private String chainContextString(ChainContext cc) {
        if (cc == ChainContext.CONJUNCTION) {
            return "CONJUNCTION";
        }
        if (cc == ChainContext.DISJUNCTION) {
            return "DISJUNCTION";
        }
        return "NONE";
    }

    public String debug() {
        StringBuilder sb = new StringBuilder();
        sb.append("-------------------------------------------\n");
        for(int i = 0; i < this.continuationChain.size(); i++) {
            PList<BooleanExpr> exprs = this.continuationChain.get(i);
            ChainContext cc = this.continuationChainContexts.get(i);
            sb.append(chainContextString(cc));
            sb.append("\n");
            for (BooleanExpr expr : exprs) {
                sb.append(expr);
                sb.append(",");
            }
            sb.append("\n");
        }
        sb.append("-------------------------------------------\n");
        return sb.toString();
    }

}
