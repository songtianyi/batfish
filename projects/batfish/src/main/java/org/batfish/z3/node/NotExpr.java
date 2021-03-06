package org.batfish.z3.node;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Z3Exception;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import org.batfish.z3.NodProgram;

public class NotExpr extends BooleanExpr implements ComplexExpr {

   private BooleanExpr _arg;
   private List<Expr> _subExpressions;

   public NotExpr() {
      init();
   }

   public NotExpr(BooleanExpr arg) {
      init();
      _arg = arg;
      refreshSubExpressions();
   }

   @Override
   public Set<String> getRelations() {
      return _arg.getRelations();
   }

   @Override
   public List<Expr> getSubExpressions() {
      return _subExpressions;
   }

   @Override
   public Set<String> getVariables() {
      return _arg.getVariables();
   }

   private void init() {
      _subExpressions = new ArrayList<>();
      _printer = new CollapsedComplexExprPrinter(this);
   }

   private void refreshSubExpressions() {
      _subExpressions.clear();
      _subExpressions.add(new IdExpr("not"));
      _subExpressions.add(_arg);
   }

   public void SetArgument(BooleanExpr arg) {
      _arg = arg;
      refreshSubExpressions();
   }

   @Override
   public BooleanExpr simplify() {
      BooleanExpr simplifiedArg = _arg.simplify();
      if (simplifiedArg == FalseExpr.INSTANCE) {
         return TrueExpr.INSTANCE;
      }
      else if (simplifiedArg == TrueExpr.INSTANCE) {
         return FalseExpr.INSTANCE;
      }
      else if (simplifiedArg != _arg) {
         return new NotExpr(simplifiedArg);
      }
      else {
         return this;
      }
   }

   @Override
   public BoolExpr toBoolExpr(NodProgram nodProgram) throws Z3Exception {
      Context ctx = nodProgram.getContext();
      BoolExpr arg = _arg.toBoolExpr(nodProgram);
      BoolExpr result = ctx.mkNot(arg);
      return result;
   }

}
