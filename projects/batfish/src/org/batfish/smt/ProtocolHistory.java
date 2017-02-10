package org.batfish.smt;

import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
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

    private RoutingProtocol _protocol;

    private Map<RoutingProtocol, BitVecExpr> _protocolMap;

    // TODO: need unique name
    public ProtocolHistory(Encoder enc, RoutingProtocol p, Set<RoutingProtocol> protocols, String name) {

        _enc = enc;
        _protocol = p;

        // Keep the original protocol around as well
        List<RoutingProtocol> protos = new ArrayList<>(protocols);
        if (!protos.contains(p)) {
            protos.add(p);
        }

        if (protos.size() == 1) {

            _bitvec = null;
            _protocolMap = null;

        } else {

            // Calculate the number of bits needed
            int size = protocols.size() + 1;
            // System.out.println("Number of protocols: " + size);

            double log = Math.log((double) size);
            double base = Math.log((double) 2);

            int numBits = ((int) Math.ceil(log / base));
            // System.out.println("Number of bits: " + numBits);

            // Initialize the map from protocol to number
            int i = 0;
            _protocolMap = new HashMap<>();
            for (RoutingProtocol proto : protos) {
               //  System.out.println("" + proto.protocolName() + " --> " + _enc.getCtx().mkBV(i, numBits).toString());
                _protocolMap.put(proto, _enc.getCtx().mkBV(i, numBits));
                i++;
            }

            _bitvec = _enc.getCtx().mkBVConst(name, numBits);
        }

    }

    public BoolExpr mkEqual(ProtocolHistory other) {
        if (_bitvec == null || other._bitvec == null) {
            return _enc.True();
        }
        return _enc.Eq(_bitvec, other._bitvec);
    }

    public BoolExpr checkIfProtocol(RoutingProtocol p) {
        if (_protocolMap == null || _bitvec == null) {
            return _enc.Bool(p == _protocol);
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
}
