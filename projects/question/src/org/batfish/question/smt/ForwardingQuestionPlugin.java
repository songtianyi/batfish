package org.batfish.question.smt;

import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.common.util.BatfishObjectMapper;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.questions.Question;
import org.batfish.question.QuestionPlugin;
import org.codehaus.jettison.json.JSONException;
import org.codehaus.jettison.json.JSONObject;

import java.util.Iterator;


public class ForwardingQuestionPlugin extends QuestionPlugin {

    public static class ForwardingAnswerer extends Answerer {

        public ForwardingAnswerer(Question question, IBatfish batfish) {
            super(question, batfish);
        }

        @Override
        public AnswerElement answer() {
            ForwardingQuestion q = (ForwardingQuestion) _question;
            return _batfish.smtForwarding(q.getDestination());
        }
    }

    public static class ForwardingQuestion extends Question {

        private static final String DESTINATION_VAR = "destination";

        private String _destinationStr;

        public ForwardingQuestion() {
            _destinationStr = "0.0.0.0/0";
        }

        @Override
        public void setJsonParameters(JSONObject parameters) {
            super.setJsonParameters(parameters);

            Iterator<?> paramKeys = parameters.keys();

            while (paramKeys.hasNext()) {
                String paramKey = (String) paramKeys.next();
                if (isBaseParamKey(paramKey)) {
                    continue;
                }

                try {
                    switch (paramKey) {
                        case DESTINATION_VAR:
                            setDestination(parameters.getString(paramKey));
                            break;
                        default:
                            throw new BatfishException("Unknown key in "
                                    + getClass().getSimpleName() + ": " + paramKey);
                    }
                }
                catch (JSONException e) {
                    throw new BatfishException("JSONException in parameters", e);
                }
            }
        }

        @JsonProperty(DESTINATION_VAR)
        public String getDestination() {
            return _destinationStr;
        }

        @Override
        public boolean getDataPlane() {
            return false;
        }

        @Override
        public String getName() {
            return "smt-forwarding";
        }

        @Override
        public boolean getTraffic() {
            return false;
        }

        public void setDestination(String dst) {
            _destinationStr = dst;
        }
    }


    @Override
    protected Answerer createAnswerer(Question question, IBatfish batfish) {
        return new ForwardingAnswerer(question, batfish);
    }

    @Override
    protected Question createQuestion() {
        return new ForwardingQuestion();
    }
}
