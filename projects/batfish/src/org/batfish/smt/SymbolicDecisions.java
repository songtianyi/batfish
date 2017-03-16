package org.batfish.smt;


import com.microsoft.z3.BoolExpr;
import org.batfish.smt.utils.Table2;
import org.batfish.smt.utils.Table3;

import java.util.HashMap;
import java.util.Map;

public class SymbolicDecisions {

    private Table2<String, Protocol, SymbolicRecord> _bestNeighborPerProtocol;

    private Map<String, SymbolicRecord> _bestNeighbor;

    private Table3<String, Protocol, LogicalEdge, BoolExpr> _choiceVariables;

    private Table2<String, GraphEdge, BoolExpr> _controlForwarding;

    private Table2<String, GraphEdge, BoolExpr> _dataForwarding;

    public SymbolicDecisions() {
        _bestNeighbor = new HashMap<>();
        _bestNeighborPerProtocol = new Table2<>();
        _choiceVariables = new Table3<>();
        _controlForwarding = new Table2<>();
        _dataForwarding = new Table2<>();
    }

    public Table2<String, Protocol, SymbolicRecord> getBestNeighborPerProtocol() {
        return _bestNeighborPerProtocol;
    }

    public Map<String, SymbolicRecord> getBestNeighbor() {
        return _bestNeighbor;
    }

    public Table3<String, Protocol, LogicalEdge, BoolExpr> getChoiceVariables() {
        return _choiceVariables;
    }

    public Table2<String, GraphEdge, BoolExpr> getControlForwarding() {
        return _controlForwarding;
    }

    public Table2<String, GraphEdge, BoolExpr> getDataForwarding() {
        return _dataForwarding;
    }

    public SymbolicRecord getBestVars(Optimizations opts, String router, Protocol proto) {
        if (opts.getSliceHasSingleProtocol().contains(router)) {
            return _bestNeighbor.get(router);
        } else {
            return _bestNeighborPerProtocol.get(router, proto);
        }
    }

}
