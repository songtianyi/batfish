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

    public SymbolicRecord(String router, String protoName, String ifaceName, int prefixLen,
            String export) {
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

    public SymbolicRecord(Encoder enc, String router, RoutingProtocol proto, String name, Optimizations opts,
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
            for (CommunityVar comm : enc.getAllCommunities()) {
                String s = comm.getValue();
                _communities.put(comm, ctx.mkBoolConst(_name + "_community_" + s));
            }
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        SymbolicRecord that = (SymbolicRecord) o;

        if (_isUsed != that._isUsed)
            return false;
        if (_isBest != that._isBest)
            return false;
        if (_name != null ? !_name.equals(that._name) : that._name != null)
            return false;
        if (_prefixLength != null ? !_prefixLength.equals(that._prefixLength) : that
                ._prefixLength != null)
            return false;
        if (_adminDist != null ? !_adminDist.equals(that._adminDist) : that._adminDist != null)
            return false;
        if (_localPref != null ? !_localPref.equals(that._localPref) : that._localPref != null)
            return false;
        if (_metric != null ? !_metric.equals(that._metric) : that._metric != null)
            return false;
        if (_med != null ? !_med.equals(that._med) : that._med != null)
            return false;
        if (_routerId != null ? !_routerId.equals(that._routerId) : that._routerId != null)
            return false;
        if (_permitted != null ? !_permitted.equals(that._permitted) : that._permitted != null)
            return false;
        return _communities != null ? _communities.equals(that._communities) : that._communities
                == null;
    }

    @Override
    public int hashCode() {
        int result = _name != null ? _name.hashCode() : 0;
        result = 31 * result + (_isUsed ? 1 : 0);
        result = 31 * result + (_isBest ? 1 : 0);
        result = 31 * result + (_prefixLength != null ? _prefixLength.hashCode() : 0);
        result = 31 * result + (_adminDist != null ? _adminDist.hashCode() : 0);
        result = 31 * result + (_localPref != null ? _localPref.hashCode() : 0);
        result = 31 * result + (_metric != null ? _metric.hashCode() : 0);
        result = 31 * result + (_med != null ? _med.hashCode() : 0);
        result = 31 * result + (_routerId != null ? _routerId.hashCode() : 0);
        result = 31 * result + (_permitted != null ? _permitted.hashCode() : 0);
        result = 31 * result + (_communities != null ? _communities.hashCode() : 0);
        return result;
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
