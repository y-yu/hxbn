package lib.modPow;
import lib.modPow.ModPow;

class Classic implements ModPow {
	private var m : BigInteger;

	public function new(m : BigInteger) { this.m = m; }

	public function convert(x : BigInteger) : BigInteger {
		if(x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
		else return x;
	}
	public function revert(x : BigInteger) : BigInteger { return x; }
	public function reduce(x : BigInteger) { x.divRemTo(this.m,null,x); }
	public function mulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }
	public function sqrTo(x,r) { x.squareTo(r); this.reduce(r); }
}
