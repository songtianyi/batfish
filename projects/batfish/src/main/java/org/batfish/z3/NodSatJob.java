package org.batfish.z3;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Fixedpoint;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Params;
import com.microsoft.z3.Status;
import com.microsoft.z3.Z3Exception;
import java.util.LinkedHashMap;
import java.util.Map;
import org.batfish.common.BatfishException;
import org.batfish.config.Settings;
import org.batfish.job.BatfishJob;

public class NodSatJob<Key> extends BatfishJob<NodSatResult<Key>> {

   private final SatQuerySynthesizer<Key> _query;

   private final Synthesizer _synthesizer;

   public NodSatJob(
         Settings settings, Synthesizer synthesizer,
         SatQuerySynthesizer<Key> query) {
      super(settings);
      _synthesizer = synthesizer;
      _query = query;
   }

   @Override
   public NodSatResult<Key> call() throws Exception {
      Map<Key, Boolean> results = new LinkedHashMap<>();
      long startTime = System.currentTimeMillis();
      long elapsedTime;
      try (Context ctx = new Context()) {
         NodProgram baseProgram = _query.synthesizeBaseProgram(
               _synthesizer,
               ctx);
         NodProgram queryProgram = _query.getNodProgram(baseProgram);
         NodProgram program = baseProgram.append(queryProgram);
         Params p = ctx.mkParams();
         p.add("fixedpoint.engine", "datalog");
         p.add("fixedpoint.datalog.default_relation", "doc");
         // p.add("fixedpoint.print_answer", true);
         Fixedpoint fix = ctx.mkFixedpoint();
         fix.setParameters(p);
         for (FuncDecl relationDeclaration : program.getRelationDeclarations()
               .values()) {
            fix.registerRelation(relationDeclaration);
         }
         for (BoolExpr rule : program.getRules()) {
            fix.addRule(rule, null);
         }
         for (int queryNum = 0; queryNum < program.getQueries()
               .size(); queryNum++) {
            BoolExpr query = program.getQueries().get(queryNum);
            Key key = _query.getKeys().get(queryNum);
            Status status = fix.query(query);
            elapsedTime = System.currentTimeMillis() - startTime;
            switch (status) {
            case SATISFIABLE:
               results.put(key, true);
               break;
            case UNKNOWN:
               return new NodSatResult<>(elapsedTime, _logger.getHistory(),
                     new BatfishException("Query satisfiability unknown"));
            case UNSATISFIABLE:
               results.put(key, false);
               break;
            default:
               return new NodSatResult<>(elapsedTime, _logger.getHistory(),
                     new BatfishException("invalid status"));
            }
         }
         elapsedTime = System.currentTimeMillis() - startTime;
         return new NodSatResult<>(results, _logger.getHistory(), elapsedTime);
      }
      catch (Z3Exception e) {
         elapsedTime = System.currentTimeMillis() - startTime;
         return new NodSatResult<>(elapsedTime, _logger.getHistory(),
               new BatfishException(
                     "Error running NoD on concatenated data plane", e));
      }
   }
}
