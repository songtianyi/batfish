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

public class SmtLoadBalanceAnswerElement implements AnswerElement {

    private Map<GraphEdge, VerificationResult> _result;

    public SmtLoadBalanceAnswerElement(IBatfish batfish, Pattern n1, Pattern iface, Pattern n2, Pattern peers, int k) {

        Graph graph = new Graph(batfish);
        int threshold = k;
        List<GraphEdge> destinationPorts = PatternUtils.findMatchingEdge(graph, n1, iface);
        List<String> sourceRouters = PatternUtils.findMatchingNodes(graph, n2);
        Map<String, List<String>> peerRouters = new HashMap<>();
        _result = new HashMap<>();

        List<String> pRouters = PatternUtils.findMatchingNodes(graph, peers);

        // TODO: refactor this out separately
        for (String router : sourceRouters) {
            List<String> list = new ArrayList<>();
            peerRouters.put(router, list);
            Set<String> neighbors =  graph.getNeighbors().get(router);
            for (String peer : pRouters) {
                if (neighbors.contains(peer)) {
                    list.add(peer);
                }
            }
        }

        for (GraphEdge ge : destinationPorts) {
            Prefix destination = ge.getStart().getPrefix();
            Encoder enc = new Encoder(Collections.singletonList(destination), graph);
            enc.computeEncoding();

            Map<String, ArithExpr> loadVars = EncoderUtils.instrumentLoad(enc, ge);

            Context ctx = enc.getCtx();
            Solver solver = enc.getSolver();

            // TODO: add threshold
            // All routers bounded by a particular length
            List<Expr> peerLoads = new ArrayList<>();
            peerRouters.forEach((router, allPeers) -> {
                // ArithExpr load = loadVars.get(router);
                for (String peer : allPeers) {
                    peerLoads.add( loadVars.get(peer) );
                }
            });
            BoolExpr evenLoads = EncoderUtils.allEqual(ctx, peerLoads);
            solver.add(ctx.mkNot(evenLoads));

            VerificationResult result = enc.verify();
            _result.put(ge, result);
        }
    }

    public Map<GraphEdge, VerificationResult> getResult() {
        return _result;
    }

    @Override
    public String prettyPrint() throws JsonProcessingException {
        return "LOAD BALANCE PRETTY PRINT";
    }
}