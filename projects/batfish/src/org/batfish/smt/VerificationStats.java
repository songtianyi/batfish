package org.batfish.smt;


public class VerificationStats {

    private int _numNodes;

    private int _numEdges;

    private int _numVariables;

    private int _numConstraints;

    private long _time;

    public VerificationStats(int n, int e, int v, int c, long t) {
        _numNodes = n;
        _numEdges = e;
        _numVariables = v;
        _numConstraints = c;
        _time = t;
    }

    public int getNumNodes() {
        return _numNodes;
    }

    public int getNumEdges() {
        return _numEdges;
    }

    public int getNumVariables() {
        return _numVariables;
    }

    public int getNumConstraints() {
        return _numConstraints;
    }

    public long getTime() {
        return _time;
    }

}
