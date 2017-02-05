package org.batfish.smt.answers;

import com.fasterxml.jackson.core.JsonProcessingException;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.smt.VerificationResult;

public class SmtOneAnswerElement implements AnswerElement {

    protected VerificationResult _result;

    public VerificationResult getResult() {
        return _result;
    }

    public void setResult(VerificationResult _result) {
        this._result = _result;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        if (_result.getVerified()) {
            return "verified";
        } else {
            StringBuilder sb = new StringBuilder();
            _result.getModel().forEach((var, val) -> {
                sb.append(var).append(" -> ").append(val).append("\n");
            });
            return sb.toString();
        }
    }
}
