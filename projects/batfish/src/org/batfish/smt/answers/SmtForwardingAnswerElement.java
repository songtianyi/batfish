package org.batfish.smt.answers;

import com.fasterxml.jackson.core.JsonProcessingException;
import org.batfish.smt.GraphEdge;

import java.util.Set;


public class SmtForwardingAnswerElement extends SmtOneAnswerElement {

    private Set<GraphEdge> _edges;

    public Set<GraphEdge> getEdges() {
        return _edges;
    }

    public void setEdges(Set<GraphEdge> _edges) {
        this._edges = _edges;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        StringBuilder sb = new StringBuilder();
        if (_result.getVerified()) {
            sb.append("No stable forwarding paths exist.");
        } else {
            for (GraphEdge ge : _edges) {
                sb.append(ge).append("\n");
            }
        }
        return sb.toString();
    }
}
