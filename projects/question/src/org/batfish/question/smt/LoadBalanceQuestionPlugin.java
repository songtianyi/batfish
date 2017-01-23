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


public class LoadBalanceQuestionPlugin extends QuestionPlugin {

    public static class LoadBalanceAnswerElement implements AnswerElement {
        @Override
        public String prettyPrint() throws JsonProcessingException {
            return "REACHABILITY";
            // ObjectMapper mapper = new BatfishObjectMapper();
            // return mapper.writeValueAsString(this);
        }
    }

    public static class LoadBalanceAnswerer extends Answerer {

        public LoadBalanceAnswerer(Question question, IBatfish batfish) {
            super(question, batfish);
        }

        @Override
        public AnswerElement answer() {
            LoadBalanceQuestion q = (LoadBalanceQuestion) _question;

            Pattern node1Regex;
            Pattern ifaceRegex;
            Pattern node2Regex;
            Pattern peerRegex;

            try {
                node1Regex = Pattern.compile(q.getNode1Regex());
                ifaceRegex = Pattern.compile(q.getIfaceRegex());
                node2Regex = Pattern.compile(q.getNode2Regex());
                peerRegex = Pattern.compile(q.getPeerRegex());
            }
            catch (PatternSyntaxException e) {
                throw new BatfishException(String.format(
                        "One of the supplied regexes (%s  OR  %s OR %s OR %s) is not a valid java regex.",
                        q.getNode1Regex(), q.getIfaceRegex(), q.getNode2Regex(), q.getPeerRegex()), e);
            }

            return _batfish.smtLoadBalance(node1Regex, ifaceRegex, node2Regex, peerRegex, q.getThreshold());
        }
    }

    public static class LoadBalanceQuestion extends Question {

        private static final String NODE1_REGEX_VAR = "node1Regex";

        private static final String IFACE_REGEX_VAR = "ifaceRegex";

        private static final String NODE2_REGEX_VAR = "node2Regex";

        private static final String PEER_REGEX_VAR = "peerRegex";

        private static final String THRESHOLD_VAR = "threshold";

        private int _threshold;

        private String _node1Regex;

        private String _ifaceRegex;

        private String _node2Regex;

        private String _peerRegex;

        public LoadBalanceQuestion() {
            _threshold = 0;
            _node1Regex = ".*";
            _ifaceRegex = ".*";
            _node2Regex = ".*";
            _peerRegex = ".*";
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
                        case THRESHOLD_VAR:
                            setThreshold(parameters.getInt(paramKey));
                            break;
                        case NODE1_REGEX_VAR:
                            setNode1Regex(parameters.getString(paramKey));
                            break;
                        case IFACE_REGEX_VAR:
                            setIfaceRegex(parameters.getString(paramKey));
                            break;
                        case NODE2_REGEX_VAR:
                            setNode2Regex(parameters.getString(paramKey));
                            break;
                        case PEER_REGEX_VAR:
                            setPeerRegex(parameters.getString(paramKey));
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

        @JsonProperty(THRESHOLD_VAR)
        public int getThreshold() {
            return _threshold;
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

        @JsonProperty(PEER_REGEX_VAR)
        public String getPeerRegex() {
            return _peerRegex;
        }

        public void setThreshold(int i) {
            this._threshold = i;
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

        public void setPeerRegex(String _peerRegex) {
            this._peerRegex = _peerRegex;
        }

        @Override
        public boolean getDataPlane() {
            return false;
        }

        @Override
        public String getName() {
            return "smt-load-balance";
        }

        @Override
        public boolean getTraffic() {
            return false;
        }
    }


    @Override
    protected Answerer createAnswerer(Question question, IBatfish batfish) {
        return new LoadBalanceAnswerer(question, batfish);
    }

    @Override
    protected Question createQuestion() {
        return new LoadBalanceQuestion();
    }
}
