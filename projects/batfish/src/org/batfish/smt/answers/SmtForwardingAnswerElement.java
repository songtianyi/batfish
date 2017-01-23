package org.batfish.smt.answers;

import com.fasterxml.jackson.core.JsonProcessingException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.smt.Encoder;
import org.batfish.smt.VerificationResult;

import java.util.Collections;


public class SmtForwardingAnswerElement implements AnswerElement {

    private VerificationResult _result;

    public SmtForwardingAnswerElement(IBatfish batfish, String destination) {
        Prefix prefix = new Prefix(destination);
        Encoder encoder = new Encoder(batfish, Collections.singletonList(prefix));
        encoder.computeEncoding();
        if (encoder.getEnvironmentVars().size() > 0) {
            System.out.println("Warning: forwarding computed for only a single concrete environment");
        }

        VerificationResult result = encoder.verify();
        _result = result;
        result.debug();
    }

    public VerificationResult getResult() {
        return _result;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        return "FORWARDING PRETTY PRINT";
    }
}
