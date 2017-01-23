package org.batfish.smt.answers;


import com.fasterxml.jackson.core.JsonProcessingException;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Configuration;
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

public class SmtMultipathConsistencyAnswerElement implements AnswerElement {

    private Map<GraphEdge, VerificationResult> _result;

    public SmtMultipathConsistencyAnswerElement(IBatfish batfish, Pattern n1, Pattern iface) {
        Graph graph = new Graph(batfish);
        List<GraphEdge> destinationPorts = PatternUtils.findMatchingEdge(graph, n1, iface);
        _result = new HashMap<>();

        for (GraphEdge ge : destinationPorts) {
            Prefix destination = ge.getStart().getPrefix();
            Encoder enc = new Encoder(Collections.singletonList(destination), graph);
            enc.computeEncoding();

            Map<String, BoolExpr> reachableVars = EncoderUtils.instrumentReachability(enc, ge);

            Context ctx = enc.getCtx();
            Solver solver = enc.getSolver();

            // All neighbor forwarded to have the same length
            BoolExpr acc = ctx.mkBool(false);
            for (Map.Entry<String, Configuration> entry : graph.getConfigurations().entrySet()) {
                String router = entry.getKey();
                BoolExpr reach = reachableVars.get(router);
                BoolExpr bad = ctx.mkBool(false);
                for (GraphEdge edge : graph.getEdgeMap().get(router)) {
                    BoolExpr dataFwd = enc.getDataForwarding().get(router).get(edge);
                    BoolExpr ctrFwd = enc.getControlForwarding().get(router).get(edge);
                    bad = ctx.mkOr(bad, ctx.mkAnd(ctrFwd, ctx.mkNot(dataFwd)));
                }
                acc = ctx.mkOr(acc, ctx.mkAnd(reach, bad) );
            }
            solver.add( acc );
            VerificationResult result = enc.verify();
            result.debug();
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