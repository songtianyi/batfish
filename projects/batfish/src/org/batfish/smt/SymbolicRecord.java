package org.batfish.smt;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


/**
 * <p>A symbolic record of control plane message attributes.
 * Attributes are specialized based on the protocol, and
 * which optimizations are applicable to the network. </p>
 *
 * @author Ryan Beckett
 */
class SymbolicRecord {

    private String _name;

    private Protocol _proto;

    private boolean _isUsed;

    private boolean _isEnv;

    private boolean _isBest;

    private boolean _isBestOverall;

    private BoolExpr _permitted;

    private ArithExpr _prefixLength;

    private ArithExpr _adminDist;

    private ArithExpr _metric;

    private ArithExpr _med;

    private ArithExpr _localPref;

    private BoolExpr _bgpInternal;

    private SymbolicEnum<Long> _ospfArea;

    private SymbolicOspfType _ospfType;

    private ArithExpr _routerId;

    private SymbolicEnum<Protocol> _protocolHistory;

    private Map<CommunityVar, BoolExpr> _communities;


    SymbolicRecord(String name, Protocol proto) {
        _name = name;
        _proto = proto;
        _isUsed = false;
        _isBest = false;
        _isBestOverall = false;
        _isEnv = false;
        _prefixLength = null;
        _metric = null;
        _adminDist = null;
        _med = null;
        _localPref = null;
        _bgpInternal = null;
        _routerId = null;
        _permitted = null;
        _ospfType = null;
        _protocolHistory = null;
    }

    SymbolicRecord(
            EncoderSlice enc, String name, String router, Protocol proto, Optimizations
            opts, Context ctx, SymbolicEnum<Protocol> h) {

        _name = name;
        _proto = proto;
        _isUsed = true;
        _isEnv = _name.contains("_ENV-");
        _isBest = _name.contains("_BEST");
        _isBestOverall = (_isBest && _name.contains("_OVERALL"));

        boolean hasOspf = enc.getProtocols().get(router).contains(Protocol.OSPF);
        boolean hasBgp = enc.getProtocols().get(router).contains(Protocol.BGP);
        boolean multipleProtos = enc.getProtocols().get(router).size() > 1;
        boolean modelAd = (_isBestOverall && multipleProtos) || opts.getKeepAdminDist();
        boolean modelIbgp = (opts.getNeedBgpMark().contains(router));

        _protocolHistory = h;
        _ospfArea = null;
        _ospfType = null;

        // Represent best variables as the aggregate protocol. Total hack.
        if (proto.isBest()) {
            _metric = ctx.mkIntConst(_name + "_metric");
            _localPref = (opts.getKeepLocalPref() ? ctx.mkIntConst(_name + "_localPref") : null);
            _adminDist = (modelAd ? ctx.mkIntConst(_name + "_adminDist") : null);
            _med = (opts.getKeepMed() ? ctx.mkIntConst(_name + "_med") : null);
            _bgpInternal = (modelIbgp ? ctx.mkBoolConst(_name + "_bgpInternal") : null);

            if (hasOspf && opts.getKeepOspfType()) {
                _ospfType = new SymbolicOspfType(enc, OspfType.values, _name + "_ospfType");
            }

            // Set OSPF area only for best OSPF or OVERALL choice
            if (hasOspf && (_isBestOverall || _name.contains("_OSPF_"))) {
                List<Long> areaIds = new ArrayList<>(enc.getGraph().getAreaIds().get(router));
                if (areaIds.size() > 1) {
                    _ospfArea = new SymbolicEnum<>(enc, areaIds, _name + "_ospfArea");
                }
            }

            if (opts.getNeedBgpMark().contains(router)) {

            }


        } else if (proto.isConnected()) {
            _metric = null;
            _localPref = null;
            _adminDist = null;
            _med = null;
            _bgpInternal = null;
            _ospfArea = null;
            _ospfType = null;

        } else if (proto.isStatic()) {
            _metric = null;
            _localPref = null;
            _adminDist = null;
            _med = null;
            _bgpInternal = null;
            _ospfArea = null;
            _ospfType = null;

        } else if (proto.isBgp()) {
            _metric = ctx.mkIntConst(_name + "_metric");
            _localPref = (opts.getKeepLocalPref() ? ctx.mkIntConst(_name + "_localPref") : null);
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst(_name + "_adminDist") : null);
            _med = (opts.getKeepMed() ? ctx.mkIntConst(_name + "_med") : null);
            _bgpInternal = (modelIbgp ? ctx.mkBoolConst(_name + "_bgpInternal") : null);
            _ospfArea = null;
            _ospfType = null;

        } else if (proto.isOspf()) {
            _metric = ctx.mkIntConst(_name + "_metric");
            _localPref = (opts.getKeepLocalPref() ? ctx.mkIntConst(_name + "_localPref") : null);
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst(_name + "_adminDist") : null);
            _med = null;
            _bgpInternal = null;

            if (opts.getKeepOspfType()) {
                _ospfType = new SymbolicOspfType(enc, OspfType.values, _name + "_ospfType");
            }
        }

        boolean needId;
        if (proto.isBest()) {
            needId = _isBest && opts.getNeedRouterId().contains(router);
        } else {
            needId = _isBest && opts.getNeedRouterIdProto().get(router).get(proto);
        }

        if (needId) {
            _routerId = ctx.mkIntConst(_name + "_routerID");
        } else {
            _routerId = null;
        }

        _prefixLength = ctx.mkIntConst(_name + "_prefixLength");
        _permitted = ctx.mkBoolConst(_name + "_permitted");

        _communities = new HashMap<>();
        if (proto.isBgp() || (hasBgp && proto.isBest())) {
            for (CommunityVar cvar : enc.getAllCommunities()) {
                String s = cvar.getValue();
                if (cvar.getType() == CommunityVar.Type.OTHER) {
                    s = s + "_OTHER";
                }
                _communities.put(cvar, ctx.mkBoolConst(_name + "_community_" + s));
            }
        }

        addExprs(enc);
    }

    private void addExprs(EncoderSlice enc) {
        List<Expr> all = enc.getAllVariables();

        all.add(_permitted);
        if (_adminDist != null) {
            all.add(_adminDist);
        }
        if (_med != null) {
            all.add(_med);
        }
        if (_localPref != null) {
            all.add(_localPref);
        }
        if (_metric != null) {
            all.add(_metric);
        }
        if (_prefixLength != null) {
            all.add(_prefixLength);
        }
        if (_routerId != null) {
            all.add(_routerId);
        }
        if (_bgpInternal != null) {
            all.add(_bgpInternal);
        }
        _communities.forEach((name, var) -> {
            all.add(var);
        });
    }




    boolean getIsUsed() {
        return _isUsed;
    }

    String getName() {
        return _name;
    }

    boolean isBest() {
        return _isBest;
    }

    boolean isEnv() {
        return _isEnv;
    }

    BoolExpr getPermitted() {
        return _permitted;
    }

    ArithExpr getMetric() {
        return _metric;
    }

    ArithExpr getLocalPref() {
        return _localPref;
    }

    ArithExpr getAdminDist() {
        return _adminDist;
    }

    ArithExpr getMed() {
        return _med;
    }

    ArithExpr getRouterId() {
        return _routerId;
    }

    ArithExpr getPrefixLength() {
        return _prefixLength;
    }

    SymbolicEnum<Long> getOspfArea() {
        return _ospfArea;
    }

    SymbolicOspfType getOspfType() {
        return _ospfType;
    }

    Map<CommunityVar, BoolExpr> getCommunities() {
        return _communities;
    }

    SymbolicEnum<Protocol> getProtocolHistory() {
        return _protocolHistory;
    }

    BoolExpr getBgpInternal() {
        return _bgpInternal;
    }

    Protocol getProto() {
        return _proto;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        SymbolicRecord that = (SymbolicRecord) o;

        return (this._name.equals(that._name));
    }

    @Override
    public int hashCode() {
        return _name.hashCode();
    }
}


