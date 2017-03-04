package org.batfish.smt;


public class CommunityVar implements Comparable<CommunityVar> {

    public enum Type {
        EXACT, REGEX, OTHER
    }

    private Type _type;

    private String _value;

    private Long _long;

    public CommunityVar(Type type, String value, Long l) {
        _type = type;
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

        if (_type != that._type)
            return false;
        if (_value != null ? !_value.equals(that._value) : that._value != null)
            return false;
        return _long != null ? _long.equals(that._long) : that._long == null;
    }

    @Override
    public int hashCode() {
        int result = _type != null ? _type.hashCode() : 0;
        result = 31 * result + (_value != null ? _value.hashCode() : 0);
        result = 31 * result + (_long != null ? _long.hashCode() : 0);
        return result;
    }

    @Override
    public int compareTo(CommunityVar that) {
        if (this._type.compareTo(that._type) < 0) {
            return -1;
        } else if (this._type.compareTo(that._type) > 0) {
            return 1;
        }

        if (this._value.compareTo(that._value) < 0) {
            return -1;
        } else if (this._value.compareTo(that._value) > 0) {
            return 1;
        }

        if (this._long.compareTo(that._long) < 0) {
            return -1;
        } else if (this._long.compareTo(that._long) > 0) {
            return 1;
        }
        return 0;
    }

    public Type getType() {
        return _type;
    }

    public String getValue() {
        return _value;
    }

    public Long asLong() {
        return _long;
    }
}
