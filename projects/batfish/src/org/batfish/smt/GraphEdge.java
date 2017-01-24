package org.batfish.smt;

import org.batfish.datamodel.Interface;
import org.batfish.datamodel.collections.NodeInterfacePair;


public class GraphEdge {

    private Interface _start;
    private Interface _end;
    private String _router;
    private String _peer;

    public GraphEdge(Interface start, Interface end, String router, String peer) {
        _start = start;
        _end = end;
        _router = router;
        _peer = peer;
    }

    public Interface getStart() {
        return _start;
    }

    public Interface getEnd() {
        return _end;
    }

    public String getRouter() {
        return _router;
    }

    public String getPeer() {
        return _peer;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        GraphEdge graphEdge = (GraphEdge) o;

        if (_start != null ? !_start.equals(graphEdge._start) : graphEdge._start != null) return false;
        if (_end != null ? !_end.equals(graphEdge._end) : graphEdge._end != null) return false;
        if (_router != null ? !_router.equals(graphEdge._router) : graphEdge._router != null) return false;
        return _peer != null ? _peer.equals(graphEdge._peer) : graphEdge._peer == null;
    }

    @Override
    public int hashCode() {
        int result = _start != null ? _start.hashCode() : 0;
        result = 31 * result + (_end != null ? _end.hashCode() : 0);
        result = 31 * result + (_router != null ? _router.hashCode() : 0);
        result = 31 * result + (_peer != null ? _peer.hashCode() : 0);
        return result;
    }

    @Override
    public String toString() {
        return _router + "," + _start.getName() + " --> " +
                (_peer == null ? "_" : _peer) + "," +
                (_end == null ? "_" : _end.getName());
    }

}
