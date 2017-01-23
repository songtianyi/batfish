package org.batfish.smt.utils;


import org.batfish.datamodel.Interface;
import org.batfish.smt.Encoder;
import org.batfish.smt.Graph;
import org.batfish.smt.GraphEdge;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class PatternUtils {


    public static List<String> findMatchingNodes(Graph graph, Pattern nodeP) {
        List<String> acc = new ArrayList<>();
        graph.getConfigurations().forEach((router, conf) -> {
            Matcher m = nodeP.matcher(router);
            if (m.matches()) {
                acc.add(router);
            }
        });
        return acc;
    }


    public static List<GraphEdge> findMatchingEdge(Graph graph, Pattern nodeP, Pattern ifaceP) {
        List<GraphEdge> acc = new ArrayList<>();
        graph.getEdgeMap().forEach((router, edges) -> {
            Matcher m1 = nodeP.matcher(router);
            if (m1.matches()) {
                for (GraphEdge edge : edges) {
                    Interface i = edge.getStart();
                    String ifaceName = i.getName();
                    Matcher m2 = ifaceP.matcher(ifaceName);
                    if (m2.matches()) {
                        acc.add(edge);
                    }
                }
            }
        });
        return acc;
    }

}
