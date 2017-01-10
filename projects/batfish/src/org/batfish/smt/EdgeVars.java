package org.batfish.smt;

import com.microsoft.z3.*;
import org.batfish.datamodel.RoutingProtocol;


public class EdgeVars {

    private String _name;
    private boolean _isUsed;
    private boolean _isBest;
    private ArithExpr _prefixLength;
    private ArithExpr _hopCount;
    private ArithExpr _metric;
    private ArithExpr _localPref;
    private ArithExpr _adminDist;
    private ArithExpr _routerId;
    private BoolExpr _permitted;

    EdgeVars() {
        _isUsed = false;
        _isBest = false;
        _prefixLength = null;
        _hopCount = null;
        _metric = null;
        _localPref = null;
        _adminDist = null;
        _routerId = null;
        _permitted = null;
    }

    EdgeVars(String router, RoutingProtocol proto, String name, Encoder.Optimizations opts, String iface, Context ctx, int prefixLen, String export, boolean isBest) {
        _name = String.format("%s_%s_%s_%d_%s", router, name, iface, prefixLen, export);
        _isUsed = true;
        _isBest = isBest;

        // Represent best variables as the aggregate protocol. Total hack.
        if (proto == RoutingProtocol.AGGREGATE) {
            _hopCount = (opts.getKeepHopCount() ? ctx.mkIntConst("hopCount_" + _name) : null);
            _metric = ctx.mkIntConst("metric_" + _name);
            _localPref = (opts.getKeepLocalPref() ? ctx.mkIntConst("localPref_" + _name) : null );
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst("adminDist_" + _name) : null);
        } else if (proto == RoutingProtocol.CONNECTED) {
            _hopCount = null;
            _metric = null;
            _localPref = null;
            _adminDist = null;
        } else if (proto == RoutingProtocol.STATIC) {
            _hopCount = null;
            _metric = null;
            _localPref = null;
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst("adminDist_" + _name) : null);
        } else {
            _hopCount = (opts.getKeepHopCount() ? ctx.mkIntConst("hopCount_" + _name) : null);
            _metric = ctx.mkIntConst("metric_" + _name);
            _localPref = (opts.getKeepLocalPref() ? ctx.mkIntConst("localPref_" + _name) : null );
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst("adminDist_" + _name) : null);
        }

        boolean needId;
        if (proto == RoutingProtocol.AGGREGATE) {
            needId = _isBest && opts.getNeedRouterId().contains(router);
        } else {
            needId = _isBest && opts.getNeedRouterIdProto().get(router).get(proto);
        }

        if (needId) {
            _routerId = ctx.mkIntConst("routerID_" + _name);
        } else {
            _routerId = null;
        }

        _prefixLength = ctx.mkIntConst("prefixLength_" + _name);
        _permitted = ctx.mkBoolConst("permitted_" + _name);
    }

    boolean getIsUsed() {
        return _isUsed;
    }

    String getName() {
        return _name;
    }

    ArithExpr getHopCount() {
        return _hopCount;
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

    ArithExpr getRouterId() {
        return _routerId;
    }

    ArithExpr getPrefixLength() {
        return _prefixLength;
    }

    BoolExpr getPermitted() {
        return _permitted;
    }

    @Override
    public String toString() {
        return "EdgeVars{" +
                "_name='" + _name + '\'' +
                ", _isUsed=" + _isUsed +
                ", _prefixLength=" + _prefixLength +
                ", _hopCount=" + _hopCount +
                ", _metric=" + _metric +
                ", _localPref=" + _localPref +
                ", _adminDist=" + _adminDist +
                ", _routerID=" + _routerId +
                ", _permitted=" + _permitted +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        EdgeVars edgeVars = (EdgeVars) o;

        if (_isUsed != edgeVars._isUsed) return false;
        if (_name != null ? !_name.equals(edgeVars._name) : edgeVars._name != null) return false;
        if (_prefixLength != null ? !_prefixLength.equals(edgeVars._prefixLength) : edgeVars._prefixLength != null)
            return false;
        if (_hopCount != null ? !_hopCount.equals(edgeVars._hopCount) : edgeVars._hopCount != null) return false;
        if (_metric != null ? !_metric.equals(edgeVars._metric) : edgeVars._metric != null) return false;
        if (_localPref != null ? !_localPref.equals(edgeVars._localPref) : edgeVars._localPref != null) return false;
        if (_adminDist != null ? !_adminDist.equals(edgeVars._adminDist) : edgeVars._adminDist != null) return false;
        if (_routerId != null ? !_routerId.equals(edgeVars._routerId) : edgeVars._routerId != null) return false;
        return _permitted != null ? _permitted.equals(edgeVars._permitted) : edgeVars._permitted == null;
    }

    @Override
    public int hashCode() {
        int result = _name != null ? _name.hashCode() : 0;
        result = 31 * result + (_isUsed ? 1 : 0);
        result = 31 * result + (_prefixLength != null ? _prefixLength.hashCode() : 0);
        result = 31 * result + (_hopCount != null ? _hopCount.hashCode() : 0);
        result = 31 * result + (_metric != null ? _metric.hashCode() : 0);
        result = 31 * result + (_localPref != null ? _localPref.hashCode() : 0);
        result = 31 * result + (_adminDist != null ? _adminDist.hashCode() : 0);
        result = 31 * result + (_routerId != null ? _routerId.hashCode() : 0);
        result = 31 * result + (_permitted != null ? _permitted.hashCode() : 0);
        return result;
    }
}
