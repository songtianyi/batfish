package org.batfish.smt.answers;


import com.fasterxml.jackson.core.JsonProcessingException;
import com.microsoft.z3.*;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.smt.Encoder;
import org.batfish.smt.Graph;
import org.batfish.smt.GraphEdge;
import org.batfish.smt.VerificationResult;
import org.batfish.smt.utils.EncoderUtils;
import org.batfish.smt.utils.PatternUtils;

import java.util.*;
import java.util.regex.Pattern;

public class SmtEqualLengthAnswerElement implements AnswerElement {

    private Map<GraphEdge, VerificationResult> _result;

    public SmtEqualLengthAnswerElement(IBatfish batfish, Pattern n1, Pattern iface, Pattern n2) {
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

            // All routers have the same length through transitivity
            List<Expr> lens = new ArrayList<>();
            for (String router : sourceRouters) {
                lens.add( lenVars.get(router) );
            }
            BoolExpr allEqual = EncoderUtils.allEqual(ctx, lens);

            solver.add( ctx.mkNot(allEqual) );

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