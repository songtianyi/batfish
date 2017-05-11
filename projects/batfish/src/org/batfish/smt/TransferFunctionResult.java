package org.batfish.smt;


import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import org.batfish.common.Pair;
import org.batfish.smt.collections.PList;

public class TransferFunctionResult {

    private PList<Pair<String,Expr>> _changedVariables; // should be a map

    private BoolExpr _returnVariable;

    private BoolExpr _returnAssignedVariable;

    public TransferFunctionResult() {
        this._changedVariables = PList.empty();
        this._returnVariable = null;
        this._returnAssignedVariable = null;
    }

    public TransferFunctionResult(TransferFunctionResult other) {
        this._changedVariables = other._changedVariables;
        this._returnVariable = other._returnVariable;
        this._returnAssignedVariable = other._returnAssignedVariable;
    }

    public PList<Pair<String, Pair<Expr,Expr>>> commonChangedVariables(TransferFunctionResult other) {
        PList<Pair<String, Pair<Expr,Expr>>> vars = PList.empty();
        for (Pair<String, Expr> cv1 : this._changedVariables) {
            for (Pair<String, Expr> cv2 : other._changedVariables) {
                if (cv1.getFirst().equals(cv2.getFirst())) {
                    Pair<Expr,Expr> x = new Pair<>(cv1.getSecond(), cv2.getSecond());
                    vars = vars.plus( new Pair<>(cv1.getFirst(), x) );
                }
            }
        }
        return vars;
    }

    public PList<Pair<String,Expr>> getChangedVariables() {
        return _changedVariables;
    }

    public BoolExpr getReturnVariable() {
        return _returnVariable;
    }

    public BoolExpr getReturnAssignedVariable() {
        return _returnAssignedVariable;
    }

    public TransferFunctionResult addChangedVariable(String s, Expr x) {
        TransferFunctionResult ret = new TransferFunctionResult(this);
        ret._changedVariables = ret._changedVariables.plus(new Pair<>(s,x));
        return ret;
    }

    public boolean isChanged(String s) {
        for (Pair<String, Expr> pair : this._changedVariables) {
            if (pair.getFirst().equals(s)) {
                return true;
            }
        }
        return false;
    }

    public TransferFunctionResult setReturnVariable(BoolExpr x) {
        TransferFunctionResult ret = new TransferFunctionResult(this);
        ret._returnVariable = x;
        return ret;
    }

    public TransferFunctionResult setReturnAssignedVariable(BoolExpr x) {
        TransferFunctionResult ret = new TransferFunctionResult(this);
        ret._returnAssignedVariable = x;
        return ret;
    }
}
