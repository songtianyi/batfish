package org.batfish.smt;


import com.microsoft.z3.ArithExpr;
import org.batfish.smt.utils.Table2;

import java.util.HashMap;
import java.util.Map;

public class SymbolicFailures {

    private Table2<String, String, ArithExpr> _failedInternalLinks;

    private Map<GraphEdge, ArithExpr> _failedEdgeLinks;

    public SymbolicFailures() {
        _failedInternalLinks = new Table2<>();
        _failedEdgeLinks = new HashMap<>();
    }

    public Table2<String, String, ArithExpr> getFailedInternalLinks() {
        return _failedInternalLinks;
    }

    public Map<GraphEdge, ArithExpr> getFailedEdgeLinks() {
        return _failedEdgeLinks;
    }

    public ArithExpr getFailedVariable(GraphEdge ge) {
        if (ge.getPeer() == null) {
            return _failedEdgeLinks.get(ge);
        }
        String router = ge.getRouter();
        String peer = ge.getPeer();
        return _failedInternalLinks.get(router, peer);
    }

}
