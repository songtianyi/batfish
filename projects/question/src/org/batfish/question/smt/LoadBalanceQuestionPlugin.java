package org.batfish.question.smt;

import com.fasterxml.jackson.annotation.JsonProperty;
import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.questions.Question;
import org.batfish.question.QuestionPlugin;
import org.codehaus.jettison.json.JSONException;
import org.codehaus.jettison.json.JSONObject;

import java.util.Iterator;


public class LoadBalanceQuestionPlugin extends QuestionPlugin {

    public static class LoadBalanceAnswerer extends Answerer {

        public LoadBalanceAnswerer(Question question, IBatfish batfish) {
            super(question, batfish);
        }

        @Override
        public AnswerElement answer() {
            LoadBalanceQuestion q = (LoadBalanceQuestion) _question;

            return _batfish.smtLoadBalance(q.getHeaderSpace(),
                    q.getIngressNodeRegex(), q.getNotIngressNodeRegex(),
                    q.getFinalNodeRegex(), q.getNotFinalNodeRegex(),
                    q.getFinalIfaceRegex(), q.getNotFinalIfaceRegex(), q.getThreshold());
        }
    }

    public static class LoadBalanceQuestion extends HeaderLocationQuestion {

        private static final String THRESHOLD_VAR = "threshold";

        private int _threshold;

        public LoadBalanceQuestion() {
            _threshold = 0;
        }

        @Override
        public void setJsonParameters(JSONObject parameters) {
            super.setJsonParameters(parameters);

            Iterator<?> paramKeys = parameters.keys();

            while (paramKeys.hasNext()) {
                String paramKey = (String) paramKeys.next();
                if (isBaseKey(paramKey)) {
                    continue;
                }

                try {
                    switch (paramKey) {
                        case THRESHOLD_VAR:
                            setThreshold(parameters.getInt(paramKey));
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

        public void setThreshold(int i) {
            this._threshold = i;
        }

        @Override
        public String getName() {
            return "smt-load-balance";
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
