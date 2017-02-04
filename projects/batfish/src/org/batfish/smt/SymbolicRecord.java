package org.batfish.smt;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import org.batfish.datamodel.RoutingProtocol;


public class SymbolicRecord {

    private String _name;
    private boolean _isUsed;
    private boolean _isBest;
    private ArithExpr _prefixLength;
    private ArithExpr _metric;
    private ArithExpr _localPref;
    private ArithExpr _adminDist;
    private ArithExpr _med;
    private ArithExpr _routerId;
    private BoolExpr _permitted;

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

    public SymbolicRecord(String router, RoutingProtocol proto, String name, Optimizations opts,
            String iface, Context ctx, int prefixLen, String export, boolean isBest) {
        _name = String.format("%s_%s_%s_%d_%s", router, name, iface, prefixLen, export);
        _isUsed = true;
        _isBest = isBest;

        // Represent best variables as the aggregate protocol. Total hack.
        if (proto == RoutingProtocol.AGGREGATE) {
            _metric = ctx.mkIntConst("metric_" + _name);
            _localPref = (opts.getKeepLocalPref() ? ctx.mkIntConst("localPref_" + _name) : null);
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst("adminDist_" + _name) : null);
            _med = (opts.getKeepMed() ? ctx.mkIntConst("med_" + _name) : null);
        } else if (proto == RoutingProtocol.CONNECTED) {
            _metric = null;
            _localPref = null;
            _adminDist = null;
            _med = null;
        } else if (proto == RoutingProtocol.STATIC) {
            _metric = null;
            _localPref = null;
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst("adminDist_" + _name) : null);
            _med = null;
        } else {
            _metric = ctx.mkIntConst("metric_" + _name);
            _localPref = (opts.getKeepLocalPref() ? ctx.mkIntConst("localPref_" + _name) : null);
            _adminDist = (opts.getKeepAdminDist() ? ctx.mkIntConst("adminDist_" + _name) : null);
            _med = (opts.getKeepMed() ? ctx.mkIntConst("med_" + _name) : null);
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

    @Override
    public int hashCode() {
        int result = _name != null ? _name.hashCode() : 0;
        result = 31 * result + (_isUsed ? 1 : 0);
        result = 31 * result + (_isBest ? 1 : 0);
        result = 31 * result + (_prefixLength != null ? _prefixLength.hashCode() : 0);
        result = 31 * result + (_metric != null ? _metric.hashCode() : 0);
        result = 31 * result + (_localPref != null ? _localPref.hashCode() : 0);
        result = 31 * result + (_adminDist != null ? _adminDist.hashCode() : 0);
        result = 31 * result + (_med != null ? _med.hashCode() : 0);
        result = 31 * result + (_routerId != null ? _routerId.hashCode() : 0);
        result = 31 * result + (_permitted != null ? _permitted.hashCode() : 0);
        return result;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        SymbolicRecord symbolicRecord = (SymbolicRecord) o;

        if (_isUsed != symbolicRecord._isUsed)
            return false;
        if (_isBest != symbolicRecord._isBest)
            return false;
        if (_name != null ? !_name.equals(symbolicRecord._name) : symbolicRecord._name != null)
            return false;
        if (_prefixLength != null ? !_prefixLength.equals(symbolicRecord._prefixLength) :
                symbolicRecord._prefixLength != null)
            return false;
        if (_metric != null ? !_metric.equals(symbolicRecord._metric) : symbolicRecord._metric !=
                null)
            return false;
        if (_localPref != null ? !_localPref.equals(symbolicRecord._localPref) : symbolicRecord
                ._localPref != null)
            return false;
        if (_adminDist != null ? !_adminDist.equals(symbolicRecord._adminDist) : symbolicRecord
                ._adminDist != null)
            return false;
        if (_med != null ? !_med.equals(symbolicRecord._med) : symbolicRecord._med != null)
            return false;
        if (_routerId != null ? !_routerId.equals(symbolicRecord._routerId) : symbolicRecord
                ._routerId != null)
            return false;
        return _permitted != null ? _permitted.equals(symbolicRecord._permitted) : symbolicRecord
                ._permitted == null;
    }

    @Override
    public String toString() {
        return "SymbolicRecord{" + "_name='" + _name + '\'' + ", _isUsed=" + _isUsed + ", " +
                "_isBest=" + _isBest + ", _prefixLength=" + _prefixLength + ", _metric=" +
                _metric + ", _localPref=" + _localPref + ", _adminDist=" + _adminDist + ", _med="
                + _med + ", _routerId=" + _routerId + ", _permitted=" + _permitted + '}';
    }
}
