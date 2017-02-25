package org.batfish.smt;


import org.batfish.common.BatfishException;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public enum OspfType {
    O, OIA, E1, E2;

    public static final List<OspfType> values =
            Collections.unmodifiableList(Arrays.asList(O, OIA, E1, E2));

    @Override
    public String toString() {
        switch(this) {
            case O:
                return "O";
            case OIA:
                return "O IA";
            case E1:
                return "O E1";
            case E2:
                return "O E2";
        }
        throw new BatfishException("Invalid Ospf Type");
    }
}
