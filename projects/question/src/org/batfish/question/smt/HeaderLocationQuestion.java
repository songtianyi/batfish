package org.batfish.question.smt;


import com.fasterxml.jackson.annotation.JsonProperty;
import org.batfish.common.BatfishException;
import org.codehaus.jettison.json.JSONException;
import org.codehaus.jettison.json.JSONObject;

import java.util.Iterator;

public class HeaderLocationQuestion extends HeaderQuestion {

    private static final String DEFAULT_FINAL_IFACE_REGEX = ".*";

    private static final String DEFAULT_FINAL_NODE_REGEX = ".*";

    private static final String DEFAULT_INGRESS_NODE_REGEX = ".*";

    private static final String DEFAULT_NOT_FINAL_NODE_REGEX = "";

    private static final String DEFAULT_NOT_FINAL_IFACE_REGEX = "";

    private static final String DEFAULT_NOT_INGRESS_NODE_REGEX = "";

    private static final String FINAL_NODE_REGEX_VAR = "finalNodeRegex";

    private static final String FINAL_IFACE_REGEX_VAR = "finalIfaceRegex";

    private static final String INGRESS_NODE_REGEX_VAR = "ingressNodeRegex";

    private static final String NOT_FINAL_NODE_REGEX_VAR = "notFinalNodeRegex";

    private static final String NOT_FINAL_IFACE_REGEX_VAR = "notFinalIfaceRegex";

    private static final String NOT_INGRESS_NODE_REGEX_VAR = "notIngressNodeRegex";


    private String _finalNodeRegex;

    private String _finalIfaceRegex;

    private String _ingressNodeRegex;

    private String _notFinalNodeRegex;

    private String _notFinalIfaceRegex;

    private String _notIngressNodeRegex;

    public HeaderLocationQuestion() {
        super();
        _finalNodeRegex = DEFAULT_FINAL_NODE_REGEX;
        _finalIfaceRegex = DEFAULT_FINAL_IFACE_REGEX;
        _ingressNodeRegex = DEFAULT_INGRESS_NODE_REGEX;
        _notFinalNodeRegex = DEFAULT_NOT_FINAL_NODE_REGEX;
        _notFinalIfaceRegex = DEFAULT_NOT_FINAL_IFACE_REGEX;
        _notIngressNodeRegex = DEFAULT_NOT_INGRESS_NODE_REGEX;
    }

    @Override
    protected boolean isBaseKey(String paramKey) {
        if (super.isBaseKey(paramKey)) {
            return true;
        }
        switch (paramKey) {
            case FINAL_NODE_REGEX_VAR:
                return true;
            case NOT_FINAL_NODE_REGEX_VAR:
                return true;
            case FINAL_IFACE_REGEX_VAR:
                return true;
            case NOT_FINAL_IFACE_REGEX_VAR:
                return true;
            case INGRESS_NODE_REGEX_VAR:
                return true;
            case NOT_INGRESS_NODE_REGEX_VAR:
                return true;
            default:
                return false;
        }
    }


    @JsonProperty(FINAL_NODE_REGEX_VAR)
    public String getFinalNodeRegex() {
        return _finalNodeRegex;
    }

    @JsonProperty(FINAL_IFACE_REGEX_VAR)
    public String getFinalIfaceRegex() {
        return _finalIfaceRegex;
    }

    @JsonProperty(INGRESS_NODE_REGEX_VAR)
    public String getIngressNodeRegex() {
        return _ingressNodeRegex;
    }

    @JsonProperty(NOT_FINAL_NODE_REGEX_VAR)
    public String getNotFinalNodeRegex() {
        return _notFinalNodeRegex;
    }

    @JsonProperty(NOT_FINAL_IFACE_REGEX_VAR)
    public String getNotFinalIfaceRegex() {
        return _notFinalIfaceRegex;
    }

    @JsonProperty(NOT_INGRESS_NODE_REGEX_VAR)
    public String getNotIngressNodeRegex() {
        return _notIngressNodeRegex;
    }

    @JsonProperty(FINAL_NODE_REGEX_VAR)
    public void setFinalNodeRegex(String regex) {
        _finalNodeRegex = regex;
    }

    @JsonProperty(FINAL_IFACE_REGEX_VAR)
    public void setFinalIfaceRegex(String regex) {
        _finalIfaceRegex = regex;
    }

    @JsonProperty(INGRESS_NODE_REGEX_VAR)
    public void setIngressNodeRegex(String regex) {
        _ingressNodeRegex = regex;
    }

    @JsonProperty(NOT_FINAL_NODE_REGEX_VAR)
    public void setNotFinalNodeRegex(String notFinalNodeRegex) {
        _notFinalNodeRegex = notFinalNodeRegex;
    }

    @JsonProperty(NOT_FINAL_IFACE_REGEX_VAR)
    public void setNotFinalIfaceRegex(String notFinalIfaceRegex) {
        _notFinalIfaceRegex = notFinalIfaceRegex;
    }

    @JsonProperty(NOT_INGRESS_NODE_REGEX_VAR)
    public void setNotIngressNodeRegex(String notIngressNodeRegex) {
        _notIngressNodeRegex = notIngressNodeRegex;
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
                    case FINAL_NODE_REGEX_VAR:
                        setFinalNodeRegex(parameters.getString(paramKey));
                        break;
                    case FINAL_IFACE_REGEX_VAR:
                        setFinalIfaceRegex(parameters.getString(paramKey));
                        break;
                    case INGRESS_NODE_REGEX_VAR:
                        setIngressNodeRegex(parameters.getString(paramKey));
                        break;
                    case NOT_FINAL_NODE_REGEX_VAR:
                        setNotFinalNodeRegex(parameters.getString(paramKey));
                        break;
                    case NOT_FINAL_IFACE_REGEX_VAR:
                        setNotFinalIfaceRegex(parameters.getString(paramKey));
                        break;
                    default:
                        break;
                }
            }
            catch (JSONException e) {
                throw new BatfishException("JSONException in parameters", e);
            }
        }
    }

}
