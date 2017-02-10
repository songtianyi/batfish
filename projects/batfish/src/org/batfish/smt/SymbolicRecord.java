package org.batfish.smt;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import org.batfish.datamodel.RoutingProtocol;

import java.util.HashMap;
import java.util.Map;


public class SymbolicRecord {

    private String _name;

    private boolean _isUsed;

    private boolean _isBest;

    private boolean _isEnv;

    private ArithExpr _prefixLength;

    private ArithExpr _adminDist;

    private ArithExpr _localPref;

    private ArithExpr _metric;

    private ArithExpr _med;

    private ArithExpr _routerId;

    private BoolExpr _permitted;

    private ProtocolHistory _protocolHistory;

    private Map<CommunityVar, BoolExpr> _communities;


    public SymbolicRecord(String name) {
        _name = name;
        _isUsed = false;
        _isBest = false;
        _isEnv = false;
        _prefixLength = null;
        _metric = null;
        _localPref = null;
        _adminDist = null;
        _med = null;
        _routerId = null;
        _permitted = null;
        _protocolHistory = null;
    }

    public SymbolicRecord(
            Encoder enc, String name, String router, RoutingProtocol proto, Optimizations opts, Context ctx, ProtocolHistory h) {

        _name = name;

        _isUsed = true;
        _isBest = _name.contains("_BEST_");
        _isEnv = _name.contains("_ENV_");

        _protocolHistory = h;

        // Represent best variables as the aggregate protocol. Total hack.
        if (proto == RoutingProtocol.AGGREGATE) {
            _metric = ctx.mkIntConst(_name + "_metric");
            _localPref = (opts.getKeepLocalPref() ? ctx.mkIntConst(_name + "_localPref") : null);
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst(_name + "_adminDist") : null);
            _med = (opts.getKeepMed() ? ctx.mkIntConst(_name + "_med") : null);
        } else if (proto == RoutingProtocol.CONNECTED) {
            _metric = null;
            _localPref = null;
            _adminDist = null;
            _med = null;
        } else if (proto == RoutingProtocol.STATIC) {
            _metric = null;
            _localPref = null;
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst(_name + "_adminDist") : null);
            _med = null;
        } else {
            _metric = ctx.mkIntConst(_name + "_metric");
            _localPref = (opts.getKeepLocalPref() ? ctx.mkIntConst(_name + "_localPref") : null);
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst(_name + "_adminDist") : null);
            _med = (opts.getKeepMed() ? ctx.mkIntConst(_name + "_med") : null);
        }

        boolean needId;
        if (proto == RoutingProtocol.AGGREGATE) {
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
        if (proto == RoutingProtocol.BGP) {
            for (CommunityVar cvar : enc.getAllCommunities()) {
                String s = cvar.getValue();
                if (cvar.getType() == CommunityVar.Type.OTHER) {
                    s = s + "_OTHER";
                }
                _communities.put(cvar, ctx.mkBoolConst(_name + "_community_" + s));
            }
        }
    }


    public boolean getIsUsed() {
        return _isUsed;
    }

    public String getName() {
        return _name;
    }

    public boolean isBest() {
        return _isBest;
    }

    public boolean isEnv() {
        return _isEnv;
    }

    public ArithExpr getMetric() {
        return _metric;
    }

    public ArithExpr getLocalPref() {
        return _localPref;
    }

    public ArithExpr getAdminDist() {
        return _adminDist;
    }

    public ArithExpr getMed() {
        return _med;
    }

    public ArithExpr getRouterId() {
        return _routerId;
    }

    public ArithExpr getPrefixLength() {
        return _prefixLength;
    }

    public BoolExpr getPermitted() {
        return _permitted;
    }

    public Map<CommunityVar, BoolExpr> getCommunities() {
        return _communities;
    }

    public ProtocolHistory getProtocolHistory() {
        return _protocolHistory;
    }
}
