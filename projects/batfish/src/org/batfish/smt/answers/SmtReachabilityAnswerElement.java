package org.batfish.smt.answers;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.smt.*;
import org.batfish.smt.utils.EncoderUtils;
import org.batfish.smt.utils.PatternUtils;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;


public class SmtReachabilityAnswerElement implements AnswerElement {

    private Map<GraphEdge, VerificationResult> _result;

    public SmtReachabilityAnswerElement(IBatfish batfish, Pattern n1, Pattern iface, Pattern n2) {
        Graph graph = new Graph(batfish);
        List<GraphEdge> destinationPorts = PatternUtils.findMatchingEdge(graph, n1, iface);
        List<String> sourceRouters = PatternUtils.findMatchingNodes(graph, n2);
        _result = new HashMap<>();

        for (GraphEdge ge : destinationPorts) {
            Prefix destination = ge.getStart().getPrefix();
            Encoder enc = new Encoder(Collections.singletonList(destination), graph);
            enc.computeEncoding();

            Map<String, BoolExpr> reachableVars = EncoderUtils.instrumentReachability(enc, ge);

            Context ctx = enc.getCtx();
            Solver solver = enc.getSolver();

            // Some router is unreachable (will be unsat)
            BoolExpr allReach = ctx.mkBool(false);
            for (String router : sourceRouters) {
                BoolExpr reach = reachableVars.get(router);
                allReach = ctx.mkOr(allReach, ctx.mkNot(reach));
            }
            solver.add(allReach);

            VerificationResult result = enc.verify();
            _result.put(ge, result);
        }
    }

    public Map<GraphEdge, VerificationResult> getResult() {
        return _result;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        return "REACHABILITY PRETTY PRINTING";
        // TODO: change this function to pretty print the answer
        // ObjectMapper mapper = new BatfishObjectMapper();
        // return mapper.writeValueAsString(this);
    }
}
