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

    private ArithExpr _prefixLength;

    private ArithExpr _adminDist;

    private ArithExpr _localPref;

    private ArithExpr _metric;

    private ArithExpr _med;

    private ArithExpr _routerId;

    private BoolExpr _permitted;

    private Map<CommunityVar, BoolExpr> _communities;


    public SymbolicRecord(
            String router, String protoName, String ifaceName, int prefixLen, String export) {
        _name = String.format("%s_%s_%s_%d_%s", router, protoName, ifaceName, prefixLen, export);
        _isUsed = false;
        _isBest = false;
        _prefixLength = null;
        _metric = null;
        _localPref = null;
        _adminDist = null;
        _med = null;
        _routerId = null;
        _permitted = null;
    }

    public SymbolicRecord(
            Encoder enc, String router, RoutingProtocol proto, String name, Optimizations opts,
            String iface, Context ctx, int prefixLen, String export, boolean isBest) {
        _name = String.format("%s_%s_%s_%d_%s", router, name, iface, prefixLen, export);
        _isUsed = true;
        _isBest = isBest;

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
}
