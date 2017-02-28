package org.batfish.smt;


import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.routing_policy.statement.*;

import java.util.HashSet;
import java.util.Set;

public class Modifications {

    private Encoder _encoder;

    private Configuration _conf;

    private boolean _defaultAccept;

    private boolean _defaultAcceptLocal;

    private SetDefaultPolicy _defaultPolicy;

    private PrependAsPath _prependPath;

    private SetLocalPreference _setLp;

    private SetMetric _setMetric;

    private SetOspfMetricType _setOspfMetricType;

    private SetWeight _setWeight;

    private SetNextHop _setNextHop;

    private Set<CommunityVar> _positiveCommunities;

    private Set<CommunityVar> _negativeCommunities;

    public Modifications(Encoder encoder, Configuration conf) {
        _encoder = encoder;
        _conf = conf;
        _defaultPolicy = null;
        _defaultAccept = false;
        _defaultAcceptLocal = false;
        _prependPath = null;
        _setLp = null;
        _setMetric = null;
        _setOspfMetricType = null;
        _setWeight = null;
        _setNextHop = null;
        _positiveCommunities = new HashSet<>();
        _negativeCommunities = new HashSet<>();
    }

    public Modifications(Modifications other) {
        PrependAsPath a = other.getPrependPath();
        SetLocalPreference b = other.getSetLp();
        SetMetric c = other.getSetMetric();
        SetWeight d = other.getSetWeight();
        SetNextHop e = other.getSetNextHop();
        Set<CommunityVar> f = other.getPositiveCommunities();
        Set<CommunityVar> g = other.getNegativeCommunities();
        SetOspfMetricType h = other.getSetOspfMetricType();
        SetDefaultPolicy i = other.getSetDefaultPolicy();

        _encoder = other._encoder;
        _conf = other._conf;
        _defaultPolicy = (i == null ? null : new SetDefaultPolicy(i.getDefaultPolicy()));
        _defaultAccept = other._defaultAccept;
        _defaultAcceptLocal = other._defaultAcceptLocal;
        _prependPath = (a == null ? null : new PrependAsPath(a.getExpr()));
        _setLp = (b == null ? null : new SetLocalPreference(b.getLocalPreference()));
        _setMetric = (c == null ? null : new SetMetric(c.getMetric()));
        _setWeight = (d == null ? null : new SetWeight(d.getWeight()));
        _setNextHop = (e == null ? null : new SetNextHop(e.getExpr(), e.getDestinationVrf()));
        _positiveCommunities = (f == null ? null : new HashSet<>(f));
        _negativeCommunities = (g == null ? null : new HashSet<>(g));
        _setOspfMetricType = (h == null ? null : new SetOspfMetricType(h.getMetricType()));
    }

    private void addPositiveCommunities(Set<CommunityVar> cs) {
        for (CommunityVar c : cs) {
            _positiveCommunities.add(c);
            _negativeCommunities.remove(c);
        }
    }

    private void addNegativeCommunities(Set<CommunityVar> cs) {
        for (CommunityVar c : cs) {
            _positiveCommunities.remove(c);
            _negativeCommunities.add(c);
        }
    }

    public void addModification(Statement stmt) {

        if (stmt instanceof Statements.StaticStatement) {
            Statements.StaticStatement ss = (Statements.StaticStatement) stmt;
            if (ss.getType() == Statements.SetDefaultActionAccept) {
                _defaultAccept = true;
            }
            if (ss.getType() == Statements.SetDefaultActionReject) {
                _defaultAccept = false;
            }
        }

        if (stmt instanceof SetDefaultPolicy) {
            _defaultPolicy = (SetDefaultPolicy) stmt;
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

        if (stmt instanceof SetOspfMetricType) {
            _setOspfMetricType = (SetOspfMetricType) stmt;
        }

        if (stmt instanceof SetWeight) {
            _setWeight = (SetWeight) stmt;
        }

        if (stmt instanceof SetNextHop) {
            _setNextHop = (SetNextHop) stmt;
        }

        if (stmt instanceof AddCommunity) {
            AddCommunity x = (AddCommunity) stmt;
            Set<CommunityVar> comms = _encoder.findAllCommunities(_conf, x.getExpr());
            addPositiveCommunities(comms);
        }

        if (stmt instanceof SetCommunity) {
            SetCommunity x = (SetCommunity) stmt;
            Set<CommunityVar> comms = _encoder.findAllCommunities(_conf, x.getExpr());
            addPositiveCommunities(comms);
        }

        if (stmt instanceof DeleteCommunity) {
            DeleteCommunity x = (DeleteCommunity) stmt;
            Set<CommunityVar> comms = _encoder.findAllCommunities(_conf, x.getExpr());
            addNegativeCommunities(comms);
        }

        if (stmt instanceof RetainCommunity) {
            // TODO
        }
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

    public SetOspfMetricType getSetOspfMetricType() {
        return _setOspfMetricType;
    }

    public SetWeight getSetWeight() {
        return _setWeight;
    }

    public SetNextHop getSetNextHop() {
        return _setNextHop;
    }

    public Set<CommunityVar> getPositiveCommunities() {
        return _positiveCommunities;
    }

    public Set<CommunityVar> getNegativeCommunities() {
        return _negativeCommunities;
    }

    public boolean getDefaultAccept() {
        return _defaultAccept;
    }

    public boolean getDefaultAcceptLocal() {
        return _defaultAcceptLocal;
    }

    public SetDefaultPolicy getSetDefaultPolicy() {
        return _defaultPolicy;
    }
}
