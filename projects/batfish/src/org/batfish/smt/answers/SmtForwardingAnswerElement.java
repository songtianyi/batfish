package org.batfish.smt.answers;

import com.fasterxml.jackson.core.JsonProcessingException;

import java.util.List;


public class SmtForwardingAnswerElement extends SmtOneAnswerElement {

    private List<String> _edges;

    public List<String> getEdges() {
        return _edges;
    }

    public void setEdges(List<String> _edges) {
        this._edges = _edges;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        StringBuilder sb = new StringBuilder();
        if (_result.getVerified()) {
            sb.append("No stable forwarding paths exist.");
        } else {
            for (String s : _edges) {
                sb.append(s).append("\n");
            }
        }
        return sb.toString();
    }
}
