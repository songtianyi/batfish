package org.batfish.smt.answers;

import com.fasterxml.jackson.core.JsonProcessingException;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.smt.VerificationResult;

import java.util.Map;

public class SmtManyAnswerElement implements AnswerElement {

    protected Map<String,VerificationResult> _result;

    public Map<String,VerificationResult> getResult() {
        return _result;
    }

    public void setResult(Map<String,VerificationResult> result) {
        _result = result;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        if (_result != null) {
            for (Map.Entry<String, VerificationResult> e : _result.entrySet()) {
                VerificationResult r = e.getValue();
                if (!r.getVerified()) {
                    StringBuilder sb = new StringBuilder();
                    r.getModel().forEach((var, val) -> {
                        sb.append(var).append(" -> ").append(val).append("\n");
                    });
                    return sb.toString();
                }
            }
        }
        return "verified";
    }

}
