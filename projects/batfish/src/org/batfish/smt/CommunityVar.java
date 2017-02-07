package org.batfish.smt;


public class CommunityVar {

    private boolean _regex;

    private String _value;

    private Long _long;

    public CommunityVar(boolean regex, String value, Long l) {
        _regex = regex;
        _value = value;
        _long = l;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        CommunityVar that = (CommunityVar) o;

        if (_regex != that._regex)
            return false;
        if (_value != null ? !_value.equals(that._value) : that._value != null)
            return false;
        return _long != null ? _long.equals(that._long) : that._long == null;
    }

    @Override
    public int hashCode() {
        int result = (_regex ? 1 : 0);
        result = 31 * result + (_value != null ? _value.hashCode() : 0);
        result = 31 * result + (_long != null ? _long.hashCode() : 0);
        return result;
    }

    public boolean isRegex() {
        return _regex;
    }

    public String getValue() {
        return _value;
    }

    public Long asLong() {
        return _long;
    }
}
