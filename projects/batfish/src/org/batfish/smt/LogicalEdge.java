package org.batfish.smt;


public class LogicalEdge {

    private EdgeType _type;
    private int _prefixLen;
    private SymbolicRecord _symbolicRecord;


    public LogicalEdge(EdgeType type, int prefixLen, SymbolicRecord symbolicRecord) {
        _type = type;
        _prefixLen = prefixLen;
        _symbolicRecord = symbolicRecord;
    }

    public EdgeType getEdgeType() {
        return _type;
    }

    public int getPrefixLen() {
        return _prefixLen;
    }

    public SymbolicRecord getSymbolicRecord() {
        return _symbolicRecord;
    }

    @Override
    public int hashCode() {
        int result = _type != null ? _type.hashCode() : 0;
        result = 31 * result + _prefixLen;
        result = 31 * result + (_symbolicRecord != null ? _symbolicRecord.hashCode() : 0);
        return result;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        LogicalEdge that = (LogicalEdge) o;

        if (_prefixLen != that._prefixLen)
            return false;
        if (_type != that._type)
            return false;
        return _symbolicRecord != null ? _symbolicRecord.equals(that._symbolicRecord) : that
                ._symbolicRecord == null;
    }

    @Override
    public String toString() {
        return "LogicalEdge{" + "_type=" + _type + ", _prefixLen=" + _prefixLen + ", " +
                "_symbolicRecord=" + _symbolicRecord + '}';
    }
}

