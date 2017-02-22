package org.batfish.question.smt;


import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.batfish.common.BatfishException;
import org.batfish.datamodel.*;
import org.batfish.datamodel.questions.IQuestion;
import org.batfish.datamodel.questions.Question;
import org.codehaus.jettison.json.JSONException;
import org.codehaus.jettison.json.JSONObject;

import java.io.IOException;
import java.util.*;

public class HeaderQuestion extends Question implements IQuestion {

    private static final String DST_IPS_VAR = "dstIps";

    private static final String DST_PORTS_VAR = "dstPorts";

    private static final String FRAGMENT_OFFSETS_VAR = "fragmentOffsets";

    private static final String ICMP_CODES_VAR = "icmpCodes";

    private static final String ICMP_TYPES_VAR = "icmpTypes";

    private static final String IP_PROTOCOLS_VAR = "ipProtocols";

    private static final String NOT_DST_IPS_VAR = "notDstIps";

    private static final String NOT_DST_PORTS_VAR = "notDstPorts";

    private static final String NOT_FRAGMENT_OFFSETS_VAR = "notFragmentOffsets";

    private static final String NOT_ICMP_CODE_VAR = "notIcmpCodes";

    private static final String NOT_ICMP_TYPE_VAR = "notIcmpTypes";

    private static final String NOT_IP_PROTOCOLS_VAR = "notIpProtocols";

    private static final String NOT_SRC_IPS_VAR = "notSrcIps";

    private static final String NOT_SRC_PORTS_VAR = "notSrcPorts";

    private static final String SRC_IPS_VAR = "srcIps";

    private static final String SRC_OR_DST_IPS_VAR = "srcOrDstIps";

    private static final String SRC_OR_DST_PORTS_VAR = "srcOrDstPorts";

    private static final String SRC_PORTS_VAR = "srcPorts";

    private Set<ForwardingAction> _actions;

    private final HeaderSpace _headerSpace;

    public HeaderQuestion() {
        _actions = EnumSet.of(ForwardingAction.ACCEPT);
        _headerSpace = new HeaderSpace();
    }

    @Override
    public boolean getDataPlane() {
        return true;
    }

    @JsonProperty(DST_IPS_VAR)
    public Set<IpWildcard> getDstIps() {
        return _headerSpace.getDstIps();
    }

    @JsonProperty(DST_PORTS_VAR)
    public Set<SubRange> getDstPorts() {
        return _headerSpace.getDstPorts();
    }

    @JsonProperty(FRAGMENT_OFFSETS_VAR)
    public Set<SubRange> getFragmentOffsets() {
        return _headerSpace.getFragmentOffsets();
    }

    @JsonIgnore
    public HeaderSpace getHeaderSpace() {
        return _headerSpace;
    }

    @JsonProperty(ICMP_CODES_VAR)
    public Set<SubRange> getIcmpCodes() {
        return _headerSpace.getIcmpCodes();
    }

    @JsonProperty(ICMP_TYPES_VAR)
    public Set<SubRange> getIcmpTypes() {
        return _headerSpace.getIcmpTypes();
    }

    @JsonProperty(IP_PROTOCOLS_VAR)
    public Set<IpProtocol> getIpProtocols() {
        return _headerSpace.getIpProtocols();
    }

    @Override
    public String getName() {
        throw new BatfishException("Unimplemented getName");
    }

    @JsonProperty(NOT_DST_IPS_VAR)
    public Set<IpWildcard> getNotDstIps() {
        return _headerSpace.getNotDstIps();
    }

    @JsonProperty(NOT_DST_PORTS_VAR)
    public Set<SubRange> getNotDstPorts() {
        return _headerSpace.getNotDstPorts();
    }

    @JsonProperty(NOT_FRAGMENT_OFFSETS_VAR)
    private Set<SubRange> getNotFragmentOffsets() {
        return _headerSpace.getNotFragmentOffsets();
    }

    @JsonProperty(NOT_ICMP_CODE_VAR)
    public Set<SubRange> getNotIcmpCodes() {
        return _headerSpace.getNotIcmpCodes();
    }

    @JsonProperty(NOT_ICMP_TYPE_VAR)
    public Set<SubRange> getNotIcmpTypes() {
        return _headerSpace.getNotIcmpTypes();
    }

    @JsonProperty(NOT_IP_PROTOCOLS_VAR)
    public Set<IpProtocol> getNotIpProtocols() {
        return _headerSpace.getNotIpProtocols();
    }

    @JsonProperty(NOT_SRC_IPS_VAR)
    public Set<IpWildcard> getNotSrcIps() {
        return _headerSpace.getNotSrcIps();
    }

    @JsonProperty(NOT_SRC_PORTS_VAR)
    public Set<SubRange> getNotSrcPorts() {
        return _headerSpace.getNotSrcPorts();
    }

    @JsonProperty(SRC_IPS_VAR)
    public Set<IpWildcard> getSrcIps() {
        return _headerSpace.getSrcIps();
    }

    @JsonProperty(SRC_OR_DST_IPS_VAR)
    public Set<IpWildcard> getSrcOrDstIps() {
        return _headerSpace.getSrcOrDstIps();
    }

    @JsonProperty(SRC_OR_DST_PORTS_VAR)
    public Set<SubRange> getSrcOrDstPorts() {
        return _headerSpace.getSrcOrDstPorts();
    }

    @JsonProperty(SRC_PORTS_VAR)
    public Set<SubRange> getSrcPorts() {
        return _headerSpace.getSrcPorts();
    }

    @Override
    public boolean getTraffic() {
        return true;
    }

    @Override
    public String prettyPrint() {
        try {
            String retString = String.format("reachability %sactions=%s",
                    prettyPrintBase(), _actions.toString());
            if (getDstPorts() != null && getDstPorts().size() != 0) {
                retString += String.format(" | dstPorts=%s", getDstPorts());
            }
            if (getDstIps() != null && getDstIps().size() != 0) {
                retString += String.format(" | dstIps=%s", getDstIps());
            }
            if (getFragmentOffsets() != null
                    && getFragmentOffsets().size() != 0) {
                retString += String.format(" | fragmentOffsets=%s",
                        getFragmentOffsets());
            }
            if (getIcmpCodes() != null && getIcmpCodes().size() != 0) {
                retString += String.format(" | icmpCodes=%s", getIcmpCodes());
            }
            if (getIcmpTypes() != null && getIcmpTypes().size() != 0) {
                retString += String.format(" | icmpTypes=%s", getIcmpTypes());
            }
            if (getIpProtocols() != null && getIpProtocols().size() != 0) {
                retString += String.format(" | ipProtocols=%s",
                        getIpProtocols().toString());
            }
            if (getSrcOrDstPorts() != null && getSrcOrDstPorts().size() != 0) {
                retString += String.format(" | srcOrDstPorts=%s",
                        getSrcOrDstPorts());
            }
            if (getSrcOrDstIps() != null && getSrcOrDstIps().size() != 0) {
                retString += String.format(" | srcOrDstIps=%s",
                        getSrcOrDstIps());
            }
            if (getSrcIps() != null && getSrcIps().size() != 0) {
                retString += String.format(" | srcIps=%s", getSrcIps());
            }
            if (getSrcPorts() != null && getSrcPorts().size() != 0) {
                retString += String.format(" | srcPorts=%s", getSrcPorts());
            }
            if (getNotDstPorts() != null && getNotDstPorts().size() != 0) {
                retString += String.format(" | notDstPorts=%s",
                        getNotDstPorts());
            }
            if (getNotDstIps() != null && getNotDstIps().size() != 0) {
                retString += String.format(" | notDstIps=%s", getNotDstIps());
            }
            if (getNotFragmentOffsets() != null
                    && getNotFragmentOffsets().size() != 0) {
                retString += String.format(" | notFragmentOffsets=%s",
                        getNotFragmentOffsets());
            }
            if (getNotIcmpCodes() != null && getNotIcmpCodes().size() != 0) {
                retString += String.format(" | notIcmpCodes=%s",
                        getNotIcmpCodes());
            }
            if (getNotIcmpTypes() != null && getNotIcmpTypes().size() != 0) {
                retString += String.format(" | notIcmpTypes=%s",
                        getNotIcmpTypes());
            }
            if (getNotIpProtocols() != null
                    && getNotIpProtocols().size() != 0) {
                retString += String.format(" | notIpProtocols=%s",
                        getNotIpProtocols().toString());
            }
            if (getNotSrcIps() != null && getNotSrcIps().size() != 0) {
                retString += String.format(" | notSrcIps=%s", getNotSrcIps());
            }
            if (getNotSrcPorts() != null && getNotSrcPorts().size() != 0) {
                retString += String.format(" | notSrcPorts=%s",
                        getNotSrcPorts());
            }
            return retString;
        }
        catch (Exception e) {
            try {
                return "Pretty printing failed. Printing Json\n"
                        + toJsonString();
            }
            catch (JsonProcessingException e1) {
                throw new BatfishException(
                        "Both pretty and json printing failed\n");
            }
        }
    }

    @JsonProperty(DST_IPS_VAR)
    public void setDstIps(Set<IpWildcard> dstIps) {
        _headerSpace.setDstIps(new TreeSet<>(dstIps));
    }

    @JsonProperty(DST_PORTS_VAR)
    public void setDstPorts(Set<SubRange> dstPorts) {
        _headerSpace.setDstPorts(new TreeSet<>(dstPorts));
    }

    @JsonProperty(ICMP_CODES_VAR)
    public void setIcmpCodes(Set<SubRange> icmpCodes) {
        _headerSpace.setIcmpCodes(new TreeSet<>(icmpCodes));
    }

    @JsonProperty(ICMP_TYPES_VAR)
    public void setIcmpTypes(Set<SubRange> icmpTypes) {
        _headerSpace.setIcmpTypes(new TreeSet<>(icmpTypes));
    }

    @JsonProperty(IP_PROTOCOLS_VAR)
    public void setIpProtocols(Set<IpProtocol> ipProtocols) {
        _headerSpace.setIpProtocols(ipProtocols);
    }

    protected boolean isBaseKey(String paramKey) {
        if (super.isBaseParamKey(paramKey)) {
            return true;
        }

        switch (paramKey) {
            case DST_IPS_VAR:
                return true;
            case DST_PORTS_VAR:
                return true;
            case NOT_DST_IPS_VAR:
                return true;
            case NOT_DST_PORTS_VAR:
                return true;
            case SRC_IPS_VAR:
                return true;
            case NOT_SRC_IPS_VAR:
                return true;
            case SRC_PORTS_VAR:
                return true;
            case NOT_SRC_PORTS_VAR:
                return true;
            case ICMP_CODES_VAR:
                return true;
            case NOT_ICMP_CODE_VAR:
                return true;
            case ICMP_TYPES_VAR:
                return true;
            case NOT_ICMP_TYPE_VAR:
                return true;
            case IP_PROTOCOLS_VAR:
                return true;
            case NOT_IP_PROTOCOLS_VAR:
                return true;
            case FRAGMENT_OFFSETS_VAR:
                return true;
            case NOT_FRAGMENT_OFFSETS_VAR:
                return true;
            default:
                return false;
        }
    }

    @Override
    public void setJsonParameters(JSONObject parameters) {
        super.setJsonParameters(parameters);

        Iterator<?> paramKeys = parameters.keys();

        while (paramKeys.hasNext()) {
            String paramKey = (String) paramKeys.next();
            if (super.isBaseParamKey(paramKey)) {
                continue;
            }

            try {
                switch (paramKey) {
                    case DST_IPS_VAR:
                        setDstIps(new ObjectMapper().<Set<IpWildcard>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<IpWildcard>>() {
                                }));
                        break;
                    case DST_PORTS_VAR:
                        setDstPorts(new ObjectMapper().<Set<SubRange>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<SubRange>>() {
                                }));
                        break;
                    case ICMP_CODES_VAR:
                        setIcmpCodes(new ObjectMapper().<Set<SubRange>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<SubRange>>() {
                                }));
                        break;
                    case ICMP_TYPES_VAR:
                        setIcmpTypes(new ObjectMapper().<Set<SubRange>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<SubRange>>() {
                                }));
                        break;
                    case IP_PROTOCOLS_VAR:
                        setIpProtocols(new ObjectMapper().<Set<IpProtocol>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<IpProtocol>>() {
                                }));
                        break;
                    case SRC_IPS_VAR:
                        setSrcIps(new ObjectMapper().<Set<IpWildcard>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<IpWildcard>>() {
                                }));
                        break;
                    case SRC_OR_DST_IPS_VAR:
                        setSrcOrDstIps(new ObjectMapper().<Set<IpWildcard>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<IpWildcard>>() {
                                }));
                        break;
                    case SRC_OR_DST_PORTS_VAR:
                        setSrcOrDstPorts(new ObjectMapper().<Set<SubRange>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<SubRange>>() {
                                }));
                        break;
                    case SRC_PORTS_VAR:
                        setSrcPorts(new ObjectMapper().<Set<SubRange>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<SubRange>>() {
                                }));
                        break;
                    case NOT_DST_IPS_VAR:
                        setNotDstIps(new ObjectMapper().<Set<IpWildcard>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<IpWildcard>>() {
                                }));
                        break;
                    case NOT_DST_PORTS_VAR:
                        setNotDstPorts(new ObjectMapper().<Set<SubRange>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<SubRange>>() {
                                }));
                        break;
                    case NOT_ICMP_CODE_VAR:
                        setNotIcmpCodes(new ObjectMapper().<Set<SubRange>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<SubRange>>() {
                                }));

                        break;
                    case NOT_ICMP_TYPE_VAR:
                        setNotIcmpTypes(new ObjectMapper().<Set<SubRange>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<SubRange>>() {
                                }));
                        break;
                    case NOT_IP_PROTOCOLS_VAR:
                        setNotIpProtocols(
                                new ObjectMapper().<Set<IpProtocol>> readValue(
                                        parameters.getString(paramKey),
                                        new TypeReference<Set<IpProtocol>>() {
                                        }));
                        break;
                    case NOT_SRC_IPS_VAR:
                        setNotSrcIps(new ObjectMapper().<Set<IpWildcard>> readValue(
                                parameters.getString(paramKey),
                                new TypeReference<Set<IpWildcard>>() {
                                }));
                        break;
                    case NOT_SRC_PORTS_VAR:
                        setNotSrcPortRange(
                                new ObjectMapper().<Set<SubRange>> readValue(
                                        parameters.getString(paramKey),
                                        new TypeReference<Set<SubRange>>() {
                                        }));
                        break;
                    default:
                        break;
                }
            }
            catch (JSONException | IOException e) {
                throw new BatfishException("JSONException in parameters", e);
            }
        }
    }

    @JsonProperty(NOT_DST_IPS_VAR)
    public void setNotDstIps(Set<IpWildcard> notDstIps) {
        _headerSpace.setNotDstIps(new TreeSet<>(notDstIps));
    }

    @JsonProperty(NOT_DST_PORTS_VAR)
    public void setNotDstPorts(Set<SubRange> notDstPorts) {
        _headerSpace.setNotDstPorts(new TreeSet<>(notDstPorts));
    }

    @JsonProperty(NOT_ICMP_CODE_VAR)
    public void setNotIcmpCodes(Set<SubRange> notIcmpCodes) {
        _headerSpace.setNotIcmpCodes(new TreeSet<>(notIcmpCodes));
    }

    @JsonProperty(NOT_ICMP_TYPE_VAR)
    public void setNotIcmpTypes(Set<SubRange> notIcmpType) {
        _headerSpace.setNotIcmpTypes(new TreeSet<>(notIcmpType));
    }

    @JsonProperty(NOT_IP_PROTOCOLS_VAR)
    public void setNotIpProtocols(Set<IpProtocol> notIpProtocols) {
        _headerSpace.setNotIpProtocols(notIpProtocols);
    }

    @JsonProperty(NOT_SRC_IPS_VAR)
    public void setNotSrcIps(Set<IpWildcard> notSrcIps) {
        _headerSpace.setNotSrcIps(new TreeSet<>(notSrcIps));
    }

    @JsonProperty(NOT_SRC_PORTS_VAR)
    public void setNotSrcPortRange(Set<SubRange> notSrcPorts) {
        _headerSpace.setNotSrcPorts(new TreeSet<>(notSrcPorts));
    }

    @JsonProperty(SRC_IPS_VAR)
    public void setSrcIps(Set<IpWildcard> srcIps) {
        _headerSpace.setSrcIps(new TreeSet<>(srcIps));
    }

    @JsonProperty(SRC_OR_DST_IPS_VAR)
    public void setSrcOrDstIps(Set<IpWildcard> srcOrDstIps) {
        _headerSpace.setSrcOrDstIps(new TreeSet<>(srcOrDstIps));
    }

    @JsonProperty(SRC_OR_DST_PORTS_VAR)
    public void setSrcOrDstPorts(Set<SubRange> srcOrDstPorts) {
        _headerSpace.setSrcOrDstPorts(new TreeSet<>(srcOrDstPorts));
    }

    @JsonProperty(SRC_PORTS_VAR)
    public void setSrcPorts(Set<SubRange> srcPorts) {
        _headerSpace.setSrcPorts(new TreeSet<>(srcPorts));
    }

}
