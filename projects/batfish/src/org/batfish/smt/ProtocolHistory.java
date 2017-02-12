package org.batfish.smt;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.RoutingProtocol;

import java.util.*;

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
public class ProtocolHistory {

    private Encoder _enc;

    private BitVecExpr _bitvec;

    private int _numBits;

    private List<RoutingProtocol> _protocols;

    private Map<RoutingProtocol, BitVecExpr> _protocolMap;

    public ProtocolHistory(Encoder enc, List<RoutingProtocol> protocols, String name) {

        _enc = enc;

        // System.out.println("Name: " + name);

        // Calculate the number of bits needed
        int size = protocols.size();
        // System.out.println("Number of protocols: " + size);

        double log = Math.log((double) size);
        double base = Math.log((double) 2);

        _numBits = ((int) Math.ceil(log / base));
        // System.out.println("Number of bits: " + _numBits);

        int i = 0;
        _protocols = new ArrayList<>();
        _protocolMap = new HashMap<>();
        for (RoutingProtocol proto : protocols) {
            _protocols.add(proto);
            if (_numBits > 0) {
                _protocolMap.put(proto, _enc.getCtx().mkBV(i, _numBits));
            }
            i++;
        }

        if (_numBits == 0) {
            _bitvec = null;
        } else {
            _bitvec = _enc.getCtx().mkBVConst(name, _numBits);
        }
    }

    public BoolExpr mkEqual(ProtocolHistory other) {
        if (_bitvec == null || other._bitvec == null) {
            throw new BatfishException("Error: protocol history null bitvector");
        }
        return _enc.Eq(_bitvec, other._bitvec);
    }

    public BoolExpr checkIfProtocol(RoutingProtocol p) {
        if (_bitvec == null) {
            RoutingProtocol q = _protocols.get(0);
            return _enc.Bool(p == q);
        }

        BitVecExpr bv = _protocolMap.get(p);
        if (bv == null) {
            return _enc.False();
        }

        return _enc.Eq(_bitvec, bv);
    }

    public BitVecExpr getBitvec() {
        return _bitvec;
    }

    public int getNumBits() {
        return _numBits;
    }
}
