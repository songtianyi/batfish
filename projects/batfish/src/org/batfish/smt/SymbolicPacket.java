package org.batfish.smt;


import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;

public class SymbolicPacket {

    private Context _ctx;

    private ArithExpr _dstIp;

    private ArithExpr _srcIp;

    private ArithExpr _dstPort;

    private ArithExpr _srcPort;

    private ArithExpr _icmpCode;

    private ArithExpr _icmpType;

    private BoolExpr _tcpAck;

    private BoolExpr _tcpCwr;

    private BoolExpr _tcpEce;

    private BoolExpr _tcpFin;

    private BoolExpr _tcpPsh;

    private BoolExpr _tcpRst;

    private BoolExpr _tcpSyn;

    private BoolExpr _tcpUrg;

    private ArithExpr _ipProtocol;

    public SymbolicPacket(Context ctx, int id, String sliceName) {
        _ctx = ctx;
        _dstIp = ctx.mkIntConst(sliceName + "dst-ip" + id);
        _srcIp = ctx.mkIntConst(sliceName + "src-ip" + id);
        _dstPort = ctx.mkIntConst(sliceName + "dst-port" + id);
        _srcPort = ctx.mkIntConst(sliceName + "src-port" + id);
        _icmpCode = ctx.mkIntConst(sliceName + "icmp-code" + id);
        _icmpType = ctx.mkIntConst(sliceName + "icmp-type" + id);
        _tcpAck = ctx.mkBoolConst(sliceName + "tcp-ack" + id);
        _tcpCwr = ctx.mkBoolConst(sliceName + "tcp-cwr" + id);
        _tcpEce = ctx.mkBoolConst(sliceName + "tcp-ece" + id);
        _tcpFin = ctx.mkBoolConst(sliceName + "tcp-fin" + id);
        _tcpPsh = ctx.mkBoolConst(sliceName + "tcp-psh" + id);
        _tcpRst = ctx.mkBoolConst(sliceName + "tcp-rst" + id);
        _tcpSyn = ctx.mkBoolConst(sliceName + "tcp-syn" + id);
        _tcpUrg = ctx.mkBoolConst(sliceName + "tcp-urg" + id);
        _ipProtocol = ctx.mkIntConst(sliceName + "ip-protocol" + id);
    }

    public BoolExpr mkEqual(SymbolicPacket other) {
        return _ctx.mkAnd(
                    _ctx.mkEq(this.getDstIp(), other.getDstIp()),
                    _ctx.mkEq(this.getSrcIp(), other.getSrcIp()),
                    _ctx.mkEq(this.getDstPort(), other.getDstPort()),
                    _ctx.mkEq(this.getSrcPort(), other.getSrcPort()),
                    _ctx.mkEq(this.getIpProtocol(), other.getIpProtocol()),
                    _ctx.mkEq(this.getIcmpCode(), other.getIcmpCode()),
                    _ctx.mkEq(this.getIcmpType(), other.getIcmpType()),
                    _ctx.mkEq(this.getTcpAck(), other.getTcpAck()),
                    _ctx.mkEq(this.getTcpCwr(), other.getTcpCwr()),
                    _ctx.mkEq(this.getTcpEce(), other.getTcpEce()),
                    _ctx.mkEq(this.getTcpFin(), other.getTcpFin()),
                    _ctx.mkEq(this.getTcpSyn(), other.getTcpSyn()),
                    _ctx.mkEq(this.getTcpPsh(), other.getTcpPsh()),
                    _ctx.mkEq(this.getTcpRst(), other.getTcpRst()),
                    _ctx.mkEq(this.getTcpUrg(), other.getTcpUrg()));
    }

    public ArithExpr getDstIp() {
        return _dstIp;
    }

    public ArithExpr getSrcIp() {
        return _srcIp;
    }

    public ArithExpr getDstPort() {
        return _dstPort;
    }

    public ArithExpr getSrcPort() {
        return _srcPort;
    }

    public ArithExpr getIcmpCode() {
        return _icmpCode;
    }

    public ArithExpr getIcmpType() {
        return _icmpType;
    }

    public BoolExpr getTcpAck() {
        return _tcpAck;
    }

    public BoolExpr getTcpCwr() {
        return _tcpCwr;
    }

    public BoolExpr getTcpEce() {
        return _tcpEce;
    }

    public BoolExpr getTcpFin() {
        return _tcpFin;
    }

    public BoolExpr getTcpPsh() {
        return _tcpPsh;
    }

    public BoolExpr getTcpRst() {
        return _tcpRst;
    }

    public BoolExpr getTcpSyn() {
        return _tcpSyn;
    }

    public BoolExpr getTcpUrg() {
        return _tcpUrg;
    }

    public ArithExpr getIpProtocol() {
        return _ipProtocol;
    }

}
