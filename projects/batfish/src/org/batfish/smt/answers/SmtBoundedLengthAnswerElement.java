package org.batfish.smt.answers;


import com.fasterxml.jackson.core.JsonProcessingException;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.smt.Encoder;
import org.batfish.smt.Graph;
import org.batfish.smt.GraphEdge;
import org.batfish.smt.VerificationResult;
import org.batfish.smt.utils.EncoderUtils;
import org.batfish.smt.utils.PatternUtils;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

public class SmtBoundedLengthAnswerElement implements AnswerElement {

    private Map<GraphEdge, VerificationResult> _result;

    public SmtBoundedLengthAnswerElement(IBatfish batfish, Pattern n1, Pattern iface, Pattern n2, int k) {
        Graph graph = new Graph(batfish);
        List<GraphEdge> destinationPorts = PatternUtils.findMatchingEdge(graph, n1, iface);
        List<String> sourceRouters = PatternUtils.findMatchingNodes(graph, n2);
        _result = new HashMap<>();

        for (GraphEdge ge : destinationPorts) {
            Prefix destination = ge.getStart().getPrefix();
            Encoder enc = new Encoder(Collections.singletonList(destination), graph);
            enc.computeEncoding();

            Map<String, ArithExpr> lenVars = EncoderUtils.instrumentPathLength(enc, ge);

            Context ctx = enc.getCtx();
            Solver solver = enc.getSolver();

            // All routers bounded by a particular length
            BoolExpr allBounded = ctx.mkBool(false);
            for (String router : sourceRouters) {
                ArithExpr len = lenVars.get(router);
                ArithExpr bound = ctx.mkInt(k);
                allBounded = ctx.mkOr(allBounded, ctx.mkGt(len, bound));
            }
            solver.add(allBounded);

            VerificationResult result = enc.verify();
            _result.put(ge, result);
        }
    }

    public Map<GraphEdge, VerificationResult> getResult() {
        return _result;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        return "BOUNDED PATH LENGTH PRETTY PRINT";
    }
}