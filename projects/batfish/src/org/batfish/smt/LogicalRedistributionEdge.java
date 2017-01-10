package org.batfish.smt;

import org.batfish.datamodel.RoutingProtocol;


public class LogicalRedistributionEdge extends LogicalEdge {

    private RoutingProtocol _from;

    LogicalRedistributionEdge(RoutingProtocol from, EdgeType type, int prefixLen, EdgeVars edgeVars) {
        super(type, prefixLen, edgeVars);
        _from = from;
    }

    RoutingProtocol getFrom() {
        return _from;
    }

    @Override
    public String toString() {
        return "LogicalRedistributionEdge{" +
                "_from=" + _from +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        LogicalRedistributionEdge that = (LogicalRedistributionEdge) o;

        return _from == that._from;
    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + (_from != null ? _from.hashCode() : 0);
        return result;
    }
}
