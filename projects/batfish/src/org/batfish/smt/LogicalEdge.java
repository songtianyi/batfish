package org.batfish.smt;


public class LogicalEdge {

    private GraphEdge _edge;

    private EdgeType _type;

    private SymbolicRecord _symbolicRecord;

    public LogicalEdge(GraphEdge edge, EdgeType type, SymbolicRecord symbolicRecord) {
        _edge = edge;
        _type = type;
        _symbolicRecord = symbolicRecord;
    }

    EdgeType getEdgeType() {
        return _type;
    }

    SymbolicRecord getSymbolicRecord() {
        return _symbolicRecord;
    }

    GraphEdge getEdge() {
        return _edge;
    }

    boolean isAbstract() {
        return _edge.isAbstract();
    }


    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        LogicalEdge that = (LogicalEdge) o;

        if (_edge != null ? !_edge.equals(that._edge) : that._edge != null)
            return false;
        if (_type != that._type)
            return false;
        return _symbolicRecord != null ? _symbolicRecord.equals(that._symbolicRecord) : that
                ._symbolicRecord == null;
    }

    @Override
    public int hashCode() {
        int result = _edge != null ? _edge.hashCode() : 0;
        result = 31 * result + (_type != null ? _type.hashCode() : 0);
        result = 31 * result + (_symbolicRecord != null ? _symbolicRecord.hashCode() : 0);
        return result;
    }

}

