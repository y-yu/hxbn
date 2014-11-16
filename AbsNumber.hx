enum Number<T> {
	Num(i : Int) : Number<Int>;
	Str(s : String) : Number<String>;
}

abstract AbsNumber<X>(Number<X>) {
    inline function new(x) {
		this = x;
	}

    @:from public static inline function fromInt(x : Int) : AbsNumber<Int> {
        return new AbsNumber(Num(x));
	}

    @:from public static inline function fromString(x : String) : AbsNumber<String> {
        return new AbsNumber(Str(x));
	}

    @:from public static inline function fromNumber<T>(x : Number<T>) : AbsNumber<T> {
        return new AbsNumber(x);
	}

    @:to public inline function toX() : X {
        return switch(this) {
            case Num(i): i;
            case Str(s): s;
        }
	}
	
	@:to public inline function toNumber() : Number<X> {
        return this;
	}
}
