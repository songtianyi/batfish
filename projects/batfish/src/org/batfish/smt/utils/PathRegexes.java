package org.batfish.smt.utils;


import org.batfish.common.BatfishException;

import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

public class PathRegexes {

    private Pattern _dstRegex;

    private Pattern _notDstRegex;

    private Pattern _ifaceRegex;

    private Pattern _notIfaceRegex;

    private Pattern _srcRegex;

    private Pattern _notSrcRegex;

    public PathRegexes(String dst, String notDst, String iface, String notIface, String src, String notSrc) {
        try {
            _dstRegex = (dst == null ? null : Pattern.compile(dst));
            _notDstRegex = (notDst == null ? null : Pattern.compile(notDst));
            _ifaceRegex = (iface == null ? null : Pattern.compile(iface));
            _notIfaceRegex = (notIface == null ? null : Pattern.compile(notIface));
            _srcRegex = (src == null ? null : Pattern.compile(src));
            _notSrcRegex = (notSrc == null ? null : Pattern.compile(notSrc));
        } catch (PatternSyntaxException e) {
            throw new BatfishException(String.format("One of the supplied regexes  is not a " +
                    "valid java regex."), e);
        }
    }

    public Pattern getDstRegex() {
        return _dstRegex;
    }

    public Pattern getNotDstRegex() {
        return _notDstRegex;
    }

    public Pattern getIfaceRegex() {
        return _ifaceRegex;
    }

    public Pattern getNotIfaceRegex() {
        return _notIfaceRegex;
    }

    public Pattern getSrcRegex() {
        return _srcRegex;
    }

    public Pattern getNotSrcRegex() {
        return _notSrcRegex;
    }
}
