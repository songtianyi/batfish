package org.batfish.smt;


import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;

import java.util.HashMap;
import java.util.Map;

public class UnsatCore {

    private boolean _doTrack;

    private Map<String, BoolExpr> _trackingVars;

    private int _trackingNum;

    public UnsatCore(boolean doTrack) {
        _doTrack = doTrack;
        _trackingVars = new HashMap<>();
        _trackingNum = 0;
    }

    public void track(Solver solver, Context ctx, BoolExpr be) {
        String name = "Pred" + _trackingNum;
        _trackingNum = _trackingNum + 1;
        _trackingVars.put(name, be);
        if (_doTrack) {
            solver.assertAndTrack(be, ctx.mkBoolConst(name));
        } else {
            solver.add(be);
        }
    }
}
