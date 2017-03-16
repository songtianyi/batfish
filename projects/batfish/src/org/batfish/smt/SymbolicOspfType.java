package org.batfish.smt;

import com.microsoft.z3.BoolExpr;

import java.util.List;

public class SymbolicOspfType extends SymbolicEnum<OspfType> {

    public SymbolicOspfType(EncoderSlice enc, List<OspfType> values, String name) {
        super(enc, values, name);
    }

    public BoolExpr isExternal() {
        if (this._bitvec == null) {
            return _enc.False();
        }
        return _enc.getCtx().mkBVUGE(_bitvec, _enc.getCtx().mkBV(2, 2));
    }

    public BoolExpr isInternal() {
        if (this._bitvec == null) {
            return _enc.True();
        }
        return _enc.getCtx().mkBVULE(_bitvec, _enc.getCtx().mkBV(1, 2));
    }

}
