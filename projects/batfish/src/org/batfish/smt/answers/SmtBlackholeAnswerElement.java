package org.batfish.smt.answers;


import com.fasterxml.jackson.core.JsonProcessingException;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.smt.*;

import java.util.*;

public class SmtBlackholeAnswerElement implements AnswerElement {

    private VerificationResult _result;

    public SmtBlackholeAnswerElement(IBatfish batfish) {
        Graph graph = new Graph(batfish);
        Prefix p = new Prefix("0.0.0.0/0");
        Encoder enc = new Encoder(Collections.singletonList(p), graph);
        enc.computeEncoding();

        Context ctx = enc.getCtx();
        Solver solver = enc.getSolver();

        // Collect routers that have no host/environment edge
        List<String> toCheck = new ArrayList<>();
        graph.getEdgeMap().forEach((router, edges) -> {
            boolean check = true;
            for (GraphEdge edge : edges) {
                if (edge.getEnd() == null) {
                    check = false;
                    break;
                }
            }
            if (check) {
                toCheck.add(router);
            }
        });

        // Ensure the router never receives traffic and then drops the traffic
        BoolExpr someBlackHole = ctx.mkBool(false);

        for (String router : toCheck) {
            Map<GraphEdge,BoolExpr> edges = enc.getDataForwarding().get(router);
            BoolExpr doesNotFwd = ctx.mkBool(true);
            for (Map.Entry<GraphEdge,BoolExpr> entry : edges.entrySet()) {
                BoolExpr dataFwd = entry.getValue();
                doesNotFwd = ctx.mkAnd(doesNotFwd, ctx.mkNot(dataFwd));
            }

            BoolExpr isFwdTo = ctx.mkBool(false);
            Set<String> neighbors = graph.getNeighbors().get(router);
            for (String n : neighbors) {
                for (Map.Entry<GraphEdge,BoolExpr> entry : enc.getDataForwarding().get(n).entrySet()) {
                    GraphEdge ge = entry.getKey();
                    BoolExpr fwd = entry.getValue();
                    if (router.equals(ge.getPeer())) {
                        isFwdTo = ctx.mkOr(isFwdTo, fwd);
                    }
                }
            }

            someBlackHole = ctx.mkOr(someBlackHole, ctx.mkAnd(isFwdTo, doesNotFwd));
        }

        solver.add(someBlackHole);

        _result = enc.verify();
        _result.debug();
    }

    public VerificationResult getResult() {
        return _result;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        return "BLACK HOLE PRETTY PRINT";
    }

}
