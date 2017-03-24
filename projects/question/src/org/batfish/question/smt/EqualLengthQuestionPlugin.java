package org.batfish.question.smt;

import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.questions.Question;
import org.batfish.question.QuestionPlugin;
import org.codehaus.jettison.json.JSONObject;

import java.util.Iterator;


public class EqualLengthQuestionPlugin extends QuestionPlugin {

    public static class EqualLengthAnswerer extends Answerer {

        public EqualLengthAnswerer(Question question, IBatfish batfish) {
            super(question, batfish);
        }

        @Override
        public AnswerElement answer() {
            EqualLengthQuestion q = (EqualLengthQuestion) _question;

            return _batfish.smtEqualLength(q.getHeaderSpace(),
                    q.getFailures(), q.getFullModel(),
                    q.getIngressNodeRegex(), q.getNotIngressNodeRegex(),
                    q.getFinalNodeRegex(), q.getNotFinalNodeRegex(),
                    q.getFinalIfaceRegex(), q.getNotFinalIfaceRegex());
        }
    }

    public static class EqualLengthQuestion extends HeaderLocationQuestion {

        @Override
        public void setJsonParameters(JSONObject parameters) {
            super.setJsonParameters(parameters);
            Iterator<?> paramKeys = parameters.keys();
            while (paramKeys.hasNext()) {
                String paramKey = (String) paramKeys.next();
                if (isBaseKey(paramKey)) {
                    continue;
                }
                throw new BatfishException("Unknown key: " + paramKey);
            }
        }

        @Override
        public String getName() {
            return "smt-equal-length";
        }
    }


    @Override
    protected Answerer createAnswerer(Question question, IBatfish batfish) {
        return new EqualLengthAnswerer(question, batfish);
    }

    @Override
    protected Question createQuestion() {
        return new EqualLengthQuestion();
    }
}
