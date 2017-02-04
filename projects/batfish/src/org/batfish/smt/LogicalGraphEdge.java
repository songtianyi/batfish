package org.batfish.smt;

public class LogicalGraphEdge extends LogicalEdge {

    private GraphEdge _edge;

    public LogicalGraphEdge(GraphEdge edge, EdgeType type, int prefixLen, SymbolicRecord symbolicRecord) {
        super(type, prefixLen, symbolicRecord);
        _edge = edge;
    }

    public GraphEdge getEdge() {
        return _edge;
    }

    @Override
    public String toString() {
        return "LogicalGraphEdge{" +
                "_edge=" + _edge +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        if (!super.equals(o)) return false;

        LogicalGraphEdge that = (LogicalGraphEdge) o;

        return _edge != null ? _edge.equals(that._edge) : that._edge == null;
    }

    @Override
    public int hashCode() {
        int result = super.hashCode();
        result = 31 * result + (_edge != null ? _edge.hashCode() : 0);
        return result;
    }
}
