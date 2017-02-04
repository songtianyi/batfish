package org.batfish.smt;


import org.batfish.datamodel.routing_policy.statement.*;

import java.util.ArrayList;
import java.util.List;

public class Modifications {

    private boolean _defaultAccept;
    private boolean _defaultAcceptLocal;
    private PrependAsPath _prependPath;
    private SetLocalPreference _setLp;
    private SetMetric _setMetric;
    private SetWeight _setWeight;
    private SetNextHop _setNextHop;
    private List<AddCommunity> _addCommunities;
    private List<SetCommunity> _setCommunities;
    private List<DeleteCommunity> _deleteCommunities;

    Modifications() {
        _defaultAccept = true;
        _defaultAcceptLocal = false;
        _prependPath = null;
        _setLp = null;
        _setMetric = null;
        _setWeight = null;
        _setNextHop = null;
        _addCommunities = new ArrayList<>();
        _setCommunities = new ArrayList<>();
        _deleteCommunities = new ArrayList<>();
    }

    Modifications(Modifications other) {
        PrependAsPath a = other.getPrependPath();
        SetLocalPreference b = other.getSetLp();
        SetMetric c = other.getSetMetric();
        SetWeight d = other.getSetWeight();
        SetNextHop e = other.getSetNextHop();
        List<AddCommunity> f = other.getAddCommunities();
        List<SetCommunity> g = other.getSetCommunities();
        List<DeleteCommunity> h = other.getDeleteCommunities();
        _defaultAccept = true;
        _defaultAcceptLocal = false;
        _prependPath = (a == null ? null : new PrependAsPath(a.getExpr()));
        _setLp = (b == null ? null : new SetLocalPreference(b.getLocalPreference()));
        _setMetric = (c == null ? null : new SetMetric(c.getMetric()));
        _setWeight = (d == null ? null : new SetWeight(d.getWeight()));
        _setNextHop = (e == null ? null : new SetNextHop(e.getExpr(), e.getDestinationVrf()));
        _addCommunities = (f == null ? null : new ArrayList<>(f));
        _setCommunities = (g == null ? null : new ArrayList<>(g));
        _deleteCommunities = (h == null ? null : new ArrayList<>(h));
    }

    public PrependAsPath getPrependPath() {
        return _prependPath;
    }

    public SetLocalPreference getSetLp() {
        return _setLp;
    }

    public SetMetric getSetMetric() {
        return _setMetric;
    }

    public SetWeight getSetWeight() {
        return _setWeight;
    }

    public SetNextHop getSetNextHop() {
        return _setNextHop;
    }

    public List<AddCommunity> getAddCommunities() {
        return _addCommunities;
    }

    public List<SetCommunity> getSetCommunities() {
        return _setCommunities;
    }

    public List<DeleteCommunity> getDeleteCommunities() {
        return _deleteCommunities;
    }

    void addModification(Statement stmt) {
        if (stmt instanceof Statements.StaticStatement) {
            Statements.StaticStatement ss = (Statements.StaticStatement) stmt;
            if (ss.getType() == Statements.SetDefaultActionAccept) {
                _defaultAccept = true;
            }
            if (ss.getType() == Statements.SetDefaultActionReject) {
                _defaultAccept = false;
            }
        }

        if (stmt instanceof PrependAsPath) {
            _prependPath = (PrependAsPath) stmt;
        }
        if (stmt instanceof SetLocalPreference) {
            _setLp = (SetLocalPreference) stmt;
        }
        if (stmt instanceof SetMetric) {
            _setMetric = (SetMetric) stmt;
        }
        if (stmt instanceof SetWeight) {
            _setWeight = (SetWeight) stmt;
        }
        if (stmt instanceof SetNextHop) {
            _setNextHop = (SetNextHop) stmt;
        }

        // TODO: not quite right
        if (stmt instanceof AddCommunity) {
            if (_addCommunities == null) {
                _addCommunities = new ArrayList<>();
            }
            _addCommunities.add((AddCommunity) stmt);
        }
        if (stmt instanceof SetCommunity) {
            if (_setCommunities == null) {
                _setCommunities = new ArrayList<>();
            }
            _setCommunities.add((SetCommunity) stmt);
        }
        if (stmt instanceof DeleteCommunity) {
            if (_deleteCommunities == null) {
                _deleteCommunities = new ArrayList<>();
            }
            _deleteCommunities.add((DeleteCommunity) stmt);
        }
    }

    public boolean getDefaultAccept() {
        return _defaultAccept;
    }

    @Override
    public int hashCode() {
        int result = (_defaultAccept ? 1 : 0);
        result = 31 * result + (_prependPath != null ? _prependPath.hashCode() : 0);
        result = 31 * result + (_setLp != null ? _setLp.hashCode() : 0);
        result = 31 * result + (_setMetric != null ? _setMetric.hashCode() : 0);
        result = 31 * result + (_setWeight != null ? _setWeight.hashCode() : 0);
        result = 31 * result + (_setNextHop != null ? _setNextHop.hashCode() : 0);
        result = 31 * result + (_addCommunities != null ? _addCommunities.hashCode() : 0);
        result = 31 * result + (_setCommunities != null ? _setCommunities.hashCode() : 0);
        result = 31 * result + (_deleteCommunities != null ? _deleteCommunities.hashCode() : 0);
        return result;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        Modifications that = (Modifications) o;

        if (_defaultAccept != that._defaultAccept)
            return false;
        if (_prependPath != null ? !_prependPath.equals(that._prependPath) : that._prependPath !=
                null)
            return false;
        if (_setLp != null ? !_setLp.equals(that._setLp) : that._setLp != null)
            return false;
        if (_setMetric != null ? !_setMetric.equals(that._setMetric) : that._setMetric != null)
            return false;
        if (_setWeight != null ? !_setWeight.equals(that._setWeight) : that._setWeight != null)
            return false;
        if (_setNextHop != null ? !_setNextHop.equals(that._setNextHop) : that._setNextHop != null)
            return false;
        if (_addCommunities != null ? !_addCommunities.equals(that._addCommunities) : that
                ._addCommunities != null)
            return false;
        if (_setCommunities != null ? !_setCommunities.equals(that._setCommunities) : that
                ._setCommunities != null)
            return false;
        return _deleteCommunities != null ? _deleteCommunities.equals(that._deleteCommunities) :
                that._deleteCommunities == null;
    }

    @Override
    public String toString() {
        return "Modifications{" + "_defaultAccept=" + _defaultAccept + ", _prependPath=" +
                _prependPath + ", _setLp=" + _setLp + ", _setMetric=" + _setMetric + ", " +
                "_setWeight=" + _setWeight + ", _setNextHop=" + _setNextHop + ", " +
                "_addCommunities=" + _addCommunities + ", _setCommunities=" + _setCommunities +
                ", _deleteCommunities=" + _deleteCommunities + '}';
    }
}
