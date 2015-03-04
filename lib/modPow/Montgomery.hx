package lib.modPow;
import lib.modPow.ModPow;

class Montgomery implements ModPow {
	private var m   : BigInteger;
	private var mp  : Int;
	private var mpl : Int;
	private var mph : Int;
	private var um  : Int;
	private var mt2 : Int;

	public function new(m : BigInteger) {
		this.m = m;
		this.mp = m.invDigit();
		this.mpl = this.mp&0x7fff;
		this.mph = this.mp>>15;
		this.um = (1<<(BigInteger.DB-15))-1;
		this.mt2 = 2*m.t;
	}

	// xR mod m
	public function convert(x : BigInteger) {
		var r = BigInteger.nbi();
		x.abs().dlShiftTo(this.m.t,r);
		r.divRemTo(this.m,null,r);
		if(x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r,r);
		return r;
	}

	// x/R mod m
	public function revert(x : BigInteger) {
		var r = BigInteger.nbi();
		x.copyTo(r);
		this.reduce(r);
		return r;
	}

	// x = x/R mod m (HAC 14.32)
	public function reduce(x : BigInteger) {
		while(x.t <= this.mt2)	// pad x so am has enough room later
			x.n[x.t++] = 0;
		for(i in 0 ... (this.m.t - 1)) {
			// faster way of calculating u0 = x[i]*mp mod DV
			var j = x.n[i]&0x7fff;
			var u0 = (j*this.mpl+(((j*this.mph+(x.n[i]>>15)*this.mpl)&this.um)<<15))&BigInteger.DM;
			// use am to combine the multiply-shift-add into one call
			j = i+this.m.t;
			x.n[j] += this.m.am(0,u0,x,i,0,this.m.t);
			// propagate carry
			while(x.n[j] >= BigInteger.DV) { x.n[j] -= BigInteger.DV; x.n[++j]++; }
		}
		x.clamp();
		x.drShiftTo(this.m.t,x);
		if(x.compareTo(this.m) >= 0) x.subTo(this.m,x);
	}

	// r = "x^2/R mod m"; x != r
	public function sqrTo(x,r) { x.squareTo(r); this.reduce(r); }

	// r = "xy/R mod m"; x,y != r
	public function mulTo(x,y,r) { x.multiplyTo(y,r); this.reduce(r); }
}
