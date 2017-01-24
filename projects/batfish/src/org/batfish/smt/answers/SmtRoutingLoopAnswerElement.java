package org.batfish.smt.answers;


import com.fasterxml.jackson.core.JsonProcessingException;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import org.batfish.common.plugin.IBatfish;
import org.batfish.datamodel.Prefix;
import org.batfish.datamodel.StaticRoute;
import org.batfish.datamodel.answers.AnswerElement;
import org.batfish.smt.*;
import org.batfish.smt.utils.EncoderUtils;

import java.util.ArrayList;
import java.util.List;


public class SmtRoutingLoopAnswerElement implements AnswerElement {

    private VerificationResult _result;

    public SmtRoutingLoopAnswerElement(IBatfish batfish) {
        Graph graph = new Graph(batfish);

        // Collect all relevant destinations
        List<Prefix> prefixes = new ArrayList<>();
        graph.getStaticRoutes().forEach((router,ifaceMap)-> {
            ifaceMap.forEach((ifaceName, srs) -> {
                for (StaticRoute sr : srs) {
                    prefixes.add(sr.getNetwork());
                }
            });
        });

        // Collect all routers that use static routes as a
        // potential place node along a loop
        List<String> routers = new ArrayList<>();
        graph.getConfigurations().forEach((router,conf) -> {
            if (conf.getDefaultVrf().getStaticRoutes().size() > 0) {
                routers.add(router);
            }
        });

        Encoder enc = new Encoder(prefixes, graph);
        enc.computeEncoding();
        Context ctx = enc.getCtx();
        Solver solver = enc.getSolver();

        BoolExpr someLoop = ctx.mkBool(false);
        for (String router : routers) {
            BoolExpr hasLoop = EncoderUtils.instrumentLoop(enc, router);
            someLoop = ctx.mkOr(someLoop, hasLoop);
        }
        solver.add( someLoop );

        _result = enc.verify();
    }

    public VerificationResult getResult() {
        return _result;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        return "Routing Loop pretty print";
    }

}
