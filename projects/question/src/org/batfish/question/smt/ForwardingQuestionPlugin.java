package org.batfish.question.smt;

import org.batfish.common.Answerer;
import org.batfish.common.BatfishException;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.questions.Question;
import org.batfish.question.QuestionPlugin;
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
            return _batfish.smtForwarding(q.getHeaderSpace(), q.getFailures(), q.getFullModel(), q.getNoEnvironment());
        }
    }

    public static class ForwardingQuestion extends HeaderQuestion {

        @Override
        public boolean getDataPlane() {
            return false;
        }

        @Override
        public String getName() {
            return "smt-forwarding";
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
