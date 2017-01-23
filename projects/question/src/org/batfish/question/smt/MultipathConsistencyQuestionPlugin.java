package org.batfish.question.smt;

import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.core.JsonProcessingException;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.questions.Question;
import org.batfish.question.QuestionPlugin;
import org.codehaus.jettison.json.JSONException;
import org.codehaus.jettison.json.JSONObject;

import java.util.Iterator;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;


public class MultipathConsistencyQuestionPlugin extends QuestionPlugin {

    public static class MulipathConsistencyAnswerElement implements AnswerElement {
        @Override
        public String prettyPrint() throws JsonProcessingException {
            return "REACHABILITY";
            // ObjectMapper mapper = new BatfishObjectMapper();
            // return mapper.writeValueAsString(this);
        }
    }

    public static class MulipathConsistencyAnswerer extends Answerer {

        public MulipathConsistencyAnswerer(Question question, IBatfish batfish) {
            super(question, batfish);
        }

        @Override
        public AnswerElement answer() {
            MultipathConsistencyQuestion q = (MultipathConsistencyQuestion) _question;

            Pattern node1Regex;
            Pattern ifaceRegex;

            try {
                node1Regex = Pattern.compile(q.getNode1Regex());
                ifaceRegex = Pattern.compile(q.getIfaceRegex());
            }
            catch (PatternSyntaxException e) {
                throw new BatfishException(String.format(
                        "One of the supplied regexes (%s  OR  %s OR %s) is not a valid java regex.",
                        q.getNode1Regex(), q.getIfaceRegex(), q.getNode2Regex()), e);
            }

            return _batfish.smtMultipathConsistency(node1Regex, ifaceRegex);
        }
    }

    public static class MultipathConsistencyQuestion extends Question {

        private static final String NODE1_REGEX_VAR = "node1Regex";

        private static final String IFACE_REGEX_VAR = "ifaceRegex";

        private static final String NODE2_REGEX_VAR = "node2Regex";

        private String _node1Regex;

        private String _ifaceRegex;

        private String _node2Regex;

        public MultipathConsistencyQuestion() {
            _node1Regex = ".*";
            _ifaceRegex = ".*";
            _node2Regex = ".*";
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
                        case NODE1_REGEX_VAR:
                            setNode1Regex(parameters.getString(paramKey));
                            break;
                        case IFACE_REGEX_VAR:
                            setIfaceRegex(parameters.getString(paramKey));
                            break;
                        case NODE2_REGEX_VAR:
                            setNode2Regex(parameters.getString(paramKey));
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

        @JsonProperty(NODE1_REGEX_VAR)
        public String getNode1Regex() {
            return _node1Regex;
        }

        @JsonProperty(IFACE_REGEX_VAR)
        public String getIfaceRegex() {
            return _ifaceRegex;
        }

        @JsonProperty(NODE2_REGEX_VAR)
        public String getNode2Regex() {
            return _node2Regex;
        }

        public void setNode1Regex(String _node1Regex) {
            this._node1Regex = _node1Regex;
        }

        public void setIfaceRegex(String _ifaceRegex) {
            this._ifaceRegex = _ifaceRegex;
        }

        public void setNode2Regex(String _node2Regex) {
            this._node2Regex = _node2Regex;
        }

        @Override
        public boolean getDataPlane() {
            return false;
        }

        @Override
        public String getName() {
            return "smt-multipath-consistency";
        }

        @Override
        public boolean getTraffic() {
            return false;
        }
    }


    @Override
    protected Answerer createAnswerer(Question question, IBatfish batfish) {
        return new MulipathConsistencyAnswerer(question, batfish);
    }

    @Override
    protected Question createQuestion() {
        return new MultipathConsistencyQuestion();
    }
}
