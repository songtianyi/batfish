package org.batfish.smt;


import org.batfish.datamodel.BgpNeighbor;
import org.batfish.datamodel.Configuration;
import org.batfish.datamodel.Interface;
import org.batfish.datamodel.RoutingProtocol;
import org.batfish.smt.utils.Table2;
import org.batfish.smt.utils.Table3;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class LogicalGraph {

    private Graph _graph;

    private Map<LogicalGraphEdge, LogicalGraphEdge> _otherEnd;

    private Table3<String, RoutingProtocol, RoutingProtocol, LogicalRedistributionEdge>
            _redistributionEdges;

    private Table2<String, RoutingProtocol, List<ArrayList<LogicalGraphEdge>>> _logicalGraphEdges;

    private Map<LogicalGraphEdge, SymbolicRecord> _environmentVars;

    public LogicalGraph(Graph g) {
        _graph = g;
        _redistributionEdges = new Table3<>();
        _logicalGraphEdges = new Table2<>();
        _otherEnd = new HashMap<>();
        _environmentVars = new HashMap<>();
    }

    public Table3<String, RoutingProtocol, RoutingProtocol, LogicalRedistributionEdge>
    getRedistributionEdges() {
        return _redistributionEdges;
    }

    public Table2<String, RoutingProtocol, List<ArrayList<LogicalGraphEdge>>>
    getLogicalGraphEdges() {
        return _logicalGraphEdges;
    }

    public Map<LogicalGraphEdge, LogicalGraphEdge> getOtherEnd() {
        return _otherEnd;
    }

    public Map<LogicalGraphEdge, SymbolicRecord> getEnvironmentVars() {
        return _environmentVars;
    }

    public SymbolicRecord findOtherVars(LogicalGraphEdge e) {
        LogicalGraphEdge other = _otherEnd.get(e);
        if (other != null) {
            return other.getSymbolicRecord();
        }
        return _environmentVars.get(e);
    }

    public boolean isEdgeUsed(Configuration conf, RoutingProtocol proto, LogicalEdge e) {
        if (e instanceof LogicalGraphEdge) {
            LogicalGraphEdge lge = (LogicalGraphEdge) e;
            GraphEdge ge = lge.getEdge();
            Interface iface = ge.getStart();
            return _graph.isInterfaceUsed(conf, proto, iface);
        } else {
            return true;
        }
    }

    public Graph getGraph() {
        return _graph;
    }

    public Long findRouterId(LogicalEdge e, RoutingProtocol proto) {
        if (e instanceof LogicalGraphEdge) {
            LogicalGraphEdge lge = (LogicalGraphEdge) e;
            LogicalGraphEdge lgeOther = _otherEnd.get(lge);
            if (lgeOther != null) {
                String peer = lgeOther.getEdge().getRouter();
                Configuration peerConf = getGraph().getConfigurations().get(peer);
                return routerId(peerConf, proto);
            }
            BgpNeighbor n = getGraph().getBgpNeighbors().get(lge.getEdge());
            if (n != null && n.getAddress() != null) {
                return n.getAddress().asLong();
            }
            return null;
        } else {
            return null;
        }
    }

    private long routerId(Configuration conf, RoutingProtocol proto) {
        if (proto == RoutingProtocol.BGP) {
            return conf.getDefaultVrf().getBgpProcess().getRouterId().asLong();
        }
        if (proto == RoutingProtocol.OSPF) {
            return conf.getDefaultVrf().getOspfProcess().getRouterId().asLong();
        } else {
            return 0;
        }
    }


}
