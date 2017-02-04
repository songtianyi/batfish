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


public class RoutingLoopQuestionPlugin extends QuestionPlugin {

    public static class RoutingLoopAnswerer extends Answerer {

        public RoutingLoopAnswerer(Question question, IBatfish batfish) {
            super(question, batfish);
        }

        @Override
        public AnswerElement answer() {
            RoutingLoopQuestion q = (RoutingLoopQuestion) _question;
            return _batfish.smtRoutingLoop();
        }
    }

    public static class RoutingLoopQuestion extends Question {

        public RoutingLoopQuestion() {}

        @Override
        public boolean getDataPlane() {
            return false;
        }

        @Override
        public String getName() {
            return "smt-routing-loop";
        }

        @Override
        public boolean getTraffic() {
            return false;
        }
    }


    @Override
    protected Answerer createAnswerer(Question question, IBatfish batfish) {
        return new RoutingLoopAnswerer(question, batfish);
    }

    @Override
    protected Question createQuestion() {
        return new RoutingLoopQuestion();
    }
}
