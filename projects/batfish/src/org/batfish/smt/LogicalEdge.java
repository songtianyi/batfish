package org.batfish.smt;


public class LogicalEdge {

    private EdgeType _type;
    private int _prefixLen;
    private EdgeVars _edgeVars;


    public LogicalEdge(EdgeType type, int prefixLen, EdgeVars edgeVars) {
        _type = type;
        _prefixLen = prefixLen;
        _edgeVars = edgeVars;
    }

    public EdgeType getEdgeType() {
        return _type;
    }

    public int getPrefixLen() {
        return _prefixLen;
    }

    public EdgeVars getEdgeVars () {
        return _edgeVars;
    }

    @Override
    public String toString() {
        return "LogicalEdge{" +
                "_type=" + _type +
                ", _prefixLen=" + _prefixLen +
                ", _edgeVars=" + _edgeVars +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        LogicalEdge that = (LogicalEdge) o;

        if (_prefixLen != that._prefixLen) return false;
        if (_type != that._type) return false;
        return _edgeVars != null ? _edgeVars.equals(that._edgeVars) : that._edgeVars == null;
    }

    @Override
    public int hashCode() {
        int result = _type != null ? _type.hashCode() : 0;
        result = 31 * result + _prefixLen;
        result = 31 * result + (_edgeVars != null ? _edgeVars.hashCode() : 0);
        return result;
    }
}

