package modPow;
import modPow.ModPow;

class Barrett implements ModPow {
	private var r2 : BigInteger;
	private var q3 : BigInteger;
	private var mu : BigInteger;
	private var m  : BigInteger;

	// Barrett modular reduction
	public function new(m : BigInteger) {
		// setup Barrett
		this.r2 = BigInteger.nbi();
		this.q3 = BigInteger.nbi();
		BigInteger.ONE.dlShiftTo(2*m.t,this.r2);
		this.mu = this.r2.divide(m);
		this.m = m;
	}

	public function convert(x : BigInteger) : BigInteger {
		if(x.s < 0 || x.t > 2*this.m.t) return x.mod(this.m);
		else if(x.compareTo(this.m) < 0) return x;
		else { var r = BigInteger.nbi(); x.copyTo(r); this.reduce(r); return r; }
	}

	public function revert(x : BigInteger) : BigInteger { return x; }

	// x = x mod m (HAC 14.42)
	public function reduce(x : BigInteger) {
		x.drShiftTo(this.m.t-1,this.r2);
		if(x.t > this.m.t+1) { x.t = this.m.t+1; x.clamp(); }
		this.mu.multiplyUpperTo(this.r2,this.m.t+1,this.q3);
		this.m.multiplyLowerTo(this.q3,this.m.t+1,this.r2);
		while(x.compareTo(this.r2) < 0) x.dAddOffset(1,this.m.t+1);
		x.subTo(this.r2,x);
		while(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
	}

	// r = x^2 mod m; x != r
	public function sqrTo(x,r) { x.squareTo(r); this.reduce(r); }

	// r = x*y mod m; x,y != r
	public function mulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }
}
