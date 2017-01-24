package org.batfish.smt;


import com.microsoft.z3.*;

import java.util.Map;

public class VerificationResult {

    private Encoder _encoder;

    private boolean _verified;

    private Map<String, String> _model;

    private VerificationStats _statistics;

    public VerificationResult(Encoder enc, boolean verified, Map<String, String> model, VerificationStats stats) {
        _encoder = enc;
        _verified = verified;
        _model = model;
        _statistics = stats;
    }

    public boolean getVerified() {
        return _verified;
    }

    public Map<String,String> getModel() {
        return _model;
    }

    public VerificationStats getStatistics() {
        return _statistics;
    }

    public void debug() {
        System.out.println("Number of variables:   " + _statistics.getNumVariables());
        System.out.println("Number of constraints: " + _statistics.getNumConstraints());
        System.out.println("Number of nodes: " + _statistics.getNumNodes());
        System.out.println("Number of edges: " + _statistics.getNumEdges());
        System.out.println("Solving time: " + _statistics.getTime());

        //System.out.println("================= Variables ==================");
        //for (Expr e : _encoder.getAllVariables()) {
        //    System.out.println(e.toString());
        //}
        //System.out.println("================= Constraints ==================");
        //for (BoolExpr be : _encoder.getSolver().getAssertions()) {
        //   System.out.println(be.simplify());
        //}
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
    }

}
