package org.batfish.smt;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import org.batfish.common.BatfishException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Represents which protocol was choosen by the selection process for a given routing
 * process. This is used to accurately apply an export filter, which may match on the
 * protocol used (e.g., as in Juniper).
 *
 * For optimization purposes, we use a small domain bitvector to represent the possble
 * choices. For most cases where a single protocol is redistributed, this will result
 * in a single new bit added to the record.
 *
 */
public class SymbolicEnum<T> {

    private Encoder _enc;

    private BitVecExpr _bitvec;

    private int _numBits;

    private List<T> _values;

    private Map<T, BitVecExpr> _valueMap;

    // TODO: encode bounds if not power of two
    public SymbolicEnum(Encoder enc, List<T> values, String name) {

        _enc = enc;

        // Calculate the number of bits needed
        int size = values.size();
        // System.out.println("Number of protocols: " + size);

        double log = Math.log((double) size);
        double base = Math.log((double) 2);

        _numBits = ((int) Math.ceil(log / base));
        // System.out.println("Number of bits: " + _numBits);

        int i = 0;
        _values = new ArrayList<>();
        _valueMap = new HashMap<>();
        for (T value : values) {
            _values.add(value);
            if (_numBits > 0) {
                _valueMap.put(value, _enc.getCtx().mkBV(i, _numBits));
            }
            i++;
        }

        if (_numBits == 0) {
            _bitvec = null;
        } else {
            _bitvec = _enc.getCtx().mkBVConst(name, _numBits);
            enc.getAllVariables().add(_bitvec);

            if (!isPowerOfTwo(size)) {
                BitVecExpr maxValue = enc.getCtx().mkBV(size-1, _numBits);
                BoolExpr constraint = enc.getCtx().mkBVULE(_bitvec, maxValue);
                enc.add( constraint );
            }

        }
    }

    private boolean isPowerOfTwo(int x) {
        return (x & -x) == x;
    }

    public BoolExpr mkEqual(SymbolicEnum other) {
        if (_bitvec == null || other._bitvec == null) {
            throw new BatfishException("Error: null bitvector");
        }
        return _enc.Eq(_bitvec, other._bitvec);
    }

    public BoolExpr checkIfValue(T p) {
        if (_bitvec == null) {
            T q = _values.get(0);
            return _enc.Bool(p == q);
        }

        BitVecExpr bv = _valueMap.get(p);
        if (bv == null) {
            return _enc.False();
        }

        return _enc.Eq(_bitvec, bv);
    }

    public BoolExpr isDefaultValue() {
        if (_bitvec == null) {
            return _enc.True();
        }
        return _enc.Eq(_bitvec, _enc.getCtx().mkBV(0, _numBits));
    }

}
