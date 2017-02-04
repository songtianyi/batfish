package org.batfish.smt;


import org.batfish.datamodel.routing_policy.expr.BooleanExpr;
import org.batfish.datamodel.routing_policy.expr.Conjunction;
import org.batfish.datamodel.routing_policy.expr.Disjunction;
import org.batfish.datamodel.routing_policy.expr.Not;
import org.batfish.datamodel.routing_policy.statement.If;
import org.batfish.datamodel.routing_policy.statement.Statement;

import java.util.List;
import java.util.function.Consumer;

public class AstVisitor {

    private List<Statement> _statements;

    public AstVisitor(List<Statement> statements) {
        _statements = statements;
    }

    private void visit(BooleanExpr e, Consumer<BooleanExpr> fe) {
        fe.accept(e);
        if (e instanceof Conjunction) {
            Conjunction c = (Conjunction) e;
            for (BooleanExpr be : c.getConjuncts()) {
                visit(be, fe);
            }
        } else if (e instanceof Disjunction) {
            Disjunction d = (Disjunction) e;
            for (BooleanExpr be : d.getDisjuncts()) {
                visit(be, fe);
            }
        } else if (e instanceof Not) {
            Not n = (Not) e;
            visit(n.getExpr(), fe);
        }
    }

    private void visit(Statement s, Consumer<Statement> fs, Consumer<BooleanExpr> fe) {
        fs.accept(s);
        if (s instanceof If) {
            If i = (If) s;
            visit(i.getGuard(), fe);
            visit(i.getTrueStatements(), fs, fe);
            visit(i.getFalseStatements(), fs, fe);
        }
    }

    private void visit(List<Statement> ss, Consumer<Statement> fs, Consumer<BooleanExpr> fe) {
        for (Statement s : ss) {
            visit(s, fs, fe);
        }
    }

    public void visit(Consumer<Statement> fs, Consumer<BooleanExpr> fe) {
        visit(_statements, fs, fe);
    }

}
