package org.batfish.smt;


import org.batfish.datamodel.BgpNeighbor;
import org.batfish.datamodel.Configuration;
import org.batfish.smt.utils.Table2;

import java.util.*;

public class LogicalGraph {

    private Graph _graph;

    private Map<LogicalEdge, LogicalEdge> _otherEnd;

    private Table2<String, Protocol, List<ArrayList<LogicalEdge>>> _logicalEdges;

    private Table2<String, Protocol, Set<Protocol>> _redistributedProtocols;

    private Map<LogicalEdge, SymbolicRecord> _environmentVars;

    public LogicalGraph(Graph g) {
        _graph = g;
        _logicalEdges = new Table2<>();
        _redistributedProtocols = new Table2<>();
        _otherEnd = new HashMap<>();
        _environmentVars = new HashMap<>();
    }

    public Table2<String, Protocol, List<ArrayList<LogicalEdge>>>
    getLogicalEdges() {
        return _logicalEdges;
    }

    public Table2<String, Protocol, Set<Protocol>> getRedistributedProtocols() {
        return _redistributedProtocols;
    }

    public Map<LogicalEdge, LogicalEdge> getOtherEnd() {
        return _otherEnd;
    }

    public Map<LogicalEdge, SymbolicRecord> getEnvironmentVars() {
        return _environmentVars;
    }

    public SymbolicRecord findOtherVars(LogicalEdge e) {
        LogicalEdge other = _otherEnd.get(e);
        if (other != null) {
            return other.getSymbolicRecord();
        }
        return _environmentVars.get(e);
    }

    public boolean isEdgeUsed(Configuration conf, Protocol proto, LogicalEdge e) {
        GraphEdge ge = e.getEdge();
        return _graph.isEdgeUsed(conf, proto, ge);
    }

    public Graph getGraph() {
        return _graph;
    }

    public Long findRouterId(LogicalEdge e, Protocol proto) {
        LogicalEdge eOther = _otherEnd.get(e);
        if (eOther != null) {
            String peer = eOther.getEdge().getRouter();
            Configuration peerConf = getGraph().getConfigurations().get(peer);
            return routerId(peerConf, proto);
        }
        BgpNeighbor n = getGraph().getEbgpNeighbors().get(e.getEdge());
        if (n != null && n.getAddress() != null) {
            return n.getAddress().asLong();
        }
        return null;
    }

    private long routerId(Configuration conf, Protocol proto) {
        if (proto.isBgp()) {
            return conf.getDefaultVrf().getBgpProcess().getRouterId().asLong();
        }
        if (proto.isOspf()) {
            return conf.getDefaultVrf().getOspfProcess().getRouterId().asLong();
        } else {
            return 0;
        }
    }

}
