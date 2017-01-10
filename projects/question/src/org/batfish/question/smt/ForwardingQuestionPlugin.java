package org.batfish.question.smt;

import com.fasterxml.jackson.core.JsonProcessingException;
import org.batfish.common.Answerer;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.datamodel.collections.EdgeSet;
import org.batfish.datamodel.collections.NodeInterfacePair;
import org.batfish.datamodel.questions.Question;
import org.batfish.datamodel.routing_policy.RoutingPolicy;
import org.batfish.datamodel.routing_policy.statement.If;
import org.batfish.datamodel.routing_policy.statement.Statement;
import org.batfish.question.QuestionPlugin;

import java.util.Map;
import java.util.Map.Entry;
import java.util.NavigableMap;
import java.util.Set;

/**
 * Created by ryanbeckett on 11/29/16.
 */
public class ForwardingQuestionPlugin extends QuestionPlugin {

    public static class ForwardingAnswerElement implements AnswerElement {
        @Override
        public String prettyPrint() throws JsonProcessingException {
            return "PRETTY PRINTING";
        }
    }

    public static class ForwardingAnswerer extends Answerer {

        public ForwardingAnswerer(Question question, IBatfish batfish) {
            super(question, batfish);
        }

        @Override
        public AnswerElement answer() {
            _batfish.encodeSMT();
            return new ForwardingAnswerElement();
        }
    }

    public static class ForwardingQuestion extends Question {

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
