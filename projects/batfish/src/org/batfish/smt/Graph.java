package org.batfish.smt;

import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.*;
import org.batfish.datamodel.collections.EdgeSet;
import org.batfish.datamodel.collections.NodeInterfacePair;

import java.util.*;


public class Graph {

    private IBatfish _batfish;

    private Map<String, Configuration> _configurations;

    private Map<String, Map<String, List<StaticRoute>>> _staticRoutes;

    private Map<String, Set<String>> _neighbors;

    private Map<String, List<GraphEdge>> _edgeMap;

    private Map<GraphEdge, GraphEdge> _otherEnd;

    private void initGraph() {
        Topology topology = _batfish.computeTopology(_configurations);
        Map<NodeInterfacePair, Interface> ifaceMap = new HashMap<>();
        Map<String, Set<NodeInterfacePair>> routerIfaceMap = new HashMap<>();

        _configurations.forEach((router, conf) -> {
            Set<NodeInterfacePair> ifacePairs = new HashSet<>();
            conf.getInterfaces().forEach((name,iface) -> {
                NodeInterfacePair nip = new NodeInterfacePair(router, name);
                ifacePairs.add(nip);
                ifaceMap.put(nip, iface);
            });
            routerIfaceMap.put(router, ifacePairs);
        });

        Map<NodeInterfacePair, EdgeSet> ifaceEdges = topology.getInterfaceEdges();

        _neighbors = new HashMap<>();
        routerIfaceMap.forEach((router, nips) -> {
            List<GraphEdge> graphEdges = new ArrayList<>();

            Set<String> neighs = new HashSet<>();
            nips.forEach((nip) -> {
                EdgeSet es = ifaceEdges.get(nip);
                Interface i1 = ifaceMap.get(nip);
                boolean hasNoOtherEnd = (es == null && i1.getPrefix() != null);
                if (hasNoOtherEnd) {
                    GraphEdge ge = new GraphEdge(i1, null, router, null);
                    graphEdges.add(ge);
                }

                if (es != null) {
                    boolean hasMultipleEnds = (es.size() > 2);
                    if (hasMultipleEnds) {
                        GraphEdge ge = new GraphEdge(i1, null, router, null);
                        graphEdges.add(ge);
                        // System.out.println("Warning: edge " + ge + " has multiple ends");
                    } else {
                    // System.out.println("NIP: " + nip.toString());

                        for (Edge e : es) {
                            // System.out.println("  edge: " + e.toString());
                            if (!router.equals(e.getNode2())) {
                                Interface i2 = ifaceMap.get(e.getInterface2());
                                String neighbor = e.getNode2();
                                GraphEdge ge1 = new GraphEdge(i1, i2, router, neighbor);
                                GraphEdge ge2 = new GraphEdge(i2, i1, neighbor, router);
                                _otherEnd.put(ge1, ge2);
                                graphEdges.add(ge1);
                                neighs.add(neighbor);
                            }
                        }
                    }
                }
            });

            _edgeMap.put(router, graphEdges);
            _neighbors.put(router, neighs);
        });
    }

    private void initStaticRoutes() {
        _configurations.forEach((router, conf) -> {
            Map<String, List<StaticRoute>> map = new HashMap<>();
            _staticRoutes.put(router, map);
            for(GraphEdge ge : _edgeMap.get(router)) {
                Interface here = ge.getStart();
                Interface there = ge.getEnd();
                for (StaticRoute sr : conf.getDefaultVrf().getStaticRoutes()) {

                    String hereName = here.getName();
                    if (hereName.equals(sr.getNextHopInterface())) {
                        List<StaticRoute> srs = map.getOrDefault(hereName, new ArrayList<>());
                        srs.add(sr);
                        map.put(hereName, srs);
                    }

                    Ip nhIp = sr.getNextHopIp();
                    boolean isNextHop =
                            nhIp != null &&
                            there != null &&
                            there.getPrefix() != null &&
                            there.getPrefix().getAddress().equals(nhIp);

                    if (isNextHop) {
                        List<StaticRoute> srs = map.getOrDefault(hereName, new ArrayList<>());
                        srs.add(sr);
                        map.put(there.getName(), srs);
                    }
                }
            }
        });
    }

    public Graph(IBatfish batfish, Set<String> routers) {
        _batfish = batfish;
        _configurations = new HashMap<>(_batfish.loadConfigurations());
        _edgeMap = new HashMap<>();
        _otherEnd = new HashMap<>();
        _staticRoutes = new HashMap<>();
        _neighbors = new HashMap<>();

        // Remove the routers we don't want to model
        if (routers != null) {
            List<String> toRemove = new ArrayList<>();
            _configurations.forEach((router, conf) -> {
                if (!routers.contains(router)) {
                    toRemove.add(router);
                }
            });
            for (String router : toRemove) {
                _configurations.remove(router);
            }
        }

        initGraph();
        initStaticRoutes();
    }

    public Graph(IBatfish batfish) {
        this(batfish, null);
    }

    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("=======================================================\n");
        sb.append("---------- Router to edges map ----------\n");
        _edgeMap.forEach((router, graphEdges) -> {
            sb.append("Router: ").append(router).append("\n");
            graphEdges.forEach(edge -> {
                sb.append("  edge from: ").append(edge.getStart().getName());
                if (edge.getEnd() == null) {
                    sb.append(" to: null \n");
                } else {
                    sb.append(" to: ").append(edge.getEnd().getName()).append("\n");
                }
            });
        });

        sb.append("---------- Neighbors of each router ----------\n");
        _neighbors.forEach((router, peers) -> {
            sb.append("Router: ").append(router).append("\n");
            for (String peer : peers) {
                sb.append("  peer: ").append(peer).append("\n");
            }
        });

        //sb.append("---------- Other End of Edge ----------\n");
        //_otherEnd.forEach((e1, e2) -> {
        //    sb.append(e1).append(" maps to ").append(e2).append("\n");
        //});


        sb.append("---------- Static Routes by Interface ----------\n");
        _staticRoutes.forEach((router, map) -> {
            map.forEach((iface, srs) -> {
                for (StaticRoute sr : srs) {
                    sb.append("Router: " + router + ", Interface: " + iface + " --> " + sr.getNetwork().toString() + "\n");
                }
            });
        });

        sb.append("=======================================================\n");
        return sb.toString();
    }


    public Map<String, Configuration> getConfigurations() {
        return _configurations;
    }

    public Map<String, Map<String, List<StaticRoute>>> getStaticRoutes() {
        return _staticRoutes;
    }

    public Map<String, Set<String>> getNeighbors() {
        return _neighbors;
    }

    public Map<String, List<GraphEdge>> getEdgeMap() {
        return _edgeMap;
    }

    public Map<GraphEdge, GraphEdge> getOtherEnd() {
        return _otherEnd;
    }
}
