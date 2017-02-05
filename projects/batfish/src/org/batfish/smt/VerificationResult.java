package org.batfish.smt;


import com.fasterxml.jackson.annotation.JsonCreator;
import com.fasterxml.jackson.annotation.JsonProperty;

import java.util.Map;
import java.util.SortedMap;

public class VerificationResult {

    private static final String VERIFIED_VAR = "verified";

    private static final String MODEL_VAR = "model";

    // private static final String STATISTICS_VAR = "statistics";

    private boolean _verified;

    private SortedMap<String, String> _model;

    // private VerificationStats _statistics;

    @JsonCreator
    public VerificationResult(
            @JsonProperty(VERIFIED_VAR) boolean verified,
            @JsonProperty(MODEL_VAR) SortedMap<String, String> model) {
        _verified = verified;
        _model = model;
    }

    @JsonProperty(VERIFIED_VAR)
    public boolean getVerified() {
        return _verified;
    }

    @JsonProperty(MODEL_VAR)
    public Map<String,String> getModel() {
        return _model;
    }

    // @JsonProperty(STATISTICS_VAR)
    // public VerificationStats getStatistics() {
    //    return _statistics;
    //}

    /* public void debug() {
        System.out.println("Number of variables:   " + _statistics.getNumVariables());
        System.out.println("Number of constraints: " + _statistics.getNumConstraints());
        System.out.println("Number of nodes: " + _statistics.getNumNodes());
        System.out.println("Number of edges: " + _statistics.getNumEdges());
        System.out.println("Solving time: " + _statistics.getTime());

        //System.out.println("================= Variables ==================");
        //for (Expr e : _encoder.getAllVariables()) {
        //    System.out.println(e.toString());
        //}
        System.out.println("================= Constraints ==================");
        for (BoolExpr be : _encoder.getSolver().getAssertions()) {
           System.out.println(be.simplify());
        }
        if (_verified) {
            System.out.println("verified");
        } else {
            System.out.println("================= Model ================");
            _encoder.getDataForwarding().forEach((router, map) -> {
                map.forEach((edge, e) -> {
                    String expr = e.toString();
                    if (expr.contains("data-")) {
                        String result = _model.get(expr);
                        if (result.equals("true")) {
                            System.out.println(edge);
                        }
                    }
                });
            });
            System.out.println("");
             _model.forEach((var,val) -> {
                System.out.println(var + "=" + val);
            });
        }

        System.out.println("================= Unsat Core ================");
        for (BoolExpr be : _encoder.getSolver().getUnsatCore()) {
            BoolExpr constraint = _encoder.getTrackingVars().get(be.toString());
            System.out.println(constraint.simplify());
            System.out.println("");
        }
    } */

}
