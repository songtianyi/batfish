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


public class BoundedLengthQuestionPlugin extends QuestionPlugin {

    public static class BoundedLengthAnswerer extends Answerer {

        public BoundedLengthAnswerer(Question question, IBatfish batfish) {
            super(question, batfish);
        }

        @Override
        public AnswerElement answer() {
            BoundedLengthQuestion q = (BoundedLengthQuestion) _question;

            return _batfish.smtBoundedLength(q.getHeaderSpace(),
                    q.getFailures(), q.getFullModel(),
                    q.getIngressNodeRegex(), q.getNotIngressNodeRegex(),
                    q.getFinalNodeRegex(), q.getNotFinalNodeRegex(),
                    q.getFinalIfaceRegex(), q.getNotFinalIfaceRegex(), q.getBound());
        }
    }

    public static class BoundedLengthQuestion extends HeaderLocationQuestion {

        private static final String LENGTH_VAR = "bound";

        private Integer _bound;

        public BoundedLengthQuestion() {
            _bound = null;
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
                        case LENGTH_VAR:
                            setBound(parameters.getInt(paramKey));
                            break;
                        default:
                            throw new BatfishException("Unknown key: " + paramKey);
                    }
                }
                catch (JSONException e) {
                    throw new BatfishException("JSONException in parameters", e);
                }
            }

        }

        @JsonProperty(LENGTH_VAR)
        public Integer getBound() {
            return _bound;
        }

        public void setBound(int i) {
            this._bound = i;
        }

        @Override
        public String getName() {
            return "smt-bounded-length";
        }
    }


    @Override
    protected Answerer createAnswerer(Question question, IBatfish batfish) {
        return new BoundedLengthAnswerer(question, batfish);
    }

    @Override
    protected Question createQuestion() {
        return new BoundedLengthQuestion();
    }
}
