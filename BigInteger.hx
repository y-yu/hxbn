import lib.modPow.ModPow;
import lib.modPow.Classic;
import lib.modPow.Barrett;
import lib.modPow.Montgomery;

import lib.AbsNumber;
import lib.CharArray;

@:generic
class BigInteger {
	// Bits per digit
	public var t : Int;
	public var s : Int;
	public var n : Array<Int> = new Array();
	
	private static inline var dbits = 28;

	public static inline var DB = BigInteger.dbits;
	public static inline var DM = ((1<<BigInteger.dbits)-1);
	public static inline var DV = (1<<BigInteger.dbits);

	public static inline var BI_FP = 30;
	public static inline var FV = 1073741824; // 2^30 -- Math.pow(2,BigInteger.BI_FP);
	public static inline var F1 = BigInteger.BI_FP - BigInteger.dbits;
	public static inline var F2 = 2 * BigInteger.dbits - BigInteger.BI_FP;

	private static var lowprimes = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997];
	private static var lplim = (1<<26)/BigInteger.lowprimes[BigInteger.lowprimes.length-1];

	// return new, unset BigInteger
	public static function nbi()  : BigInteger { return new BigInteger(); }

	// return bigint initialized to value
	public static inline function nbv(i : Int) : BigInteger { var r = BigInteger.nbi(); r.fromInt(i); return r; }

	public static var ZERO = nbv(0);
	public static var ONE  = nbv(1);

	public static inline var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
	public static var BI_RC        = [null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,0,1,2,3,4,5,6,7,8,9,null,null,null,null,null,null,null,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,null,null,null,null,null,null,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35];

	public static function intAt(s : String, i : Int) : Int {
		var c = BI_RC[s.charCodeAt(i)];
		return (c==null)?-1:c;
	}

	public static inline function int2char(n : Int) : String { return BI_RM.charAt(n); }


	// am: Compute w_j += (x*this_i), propagate carries,
	// c is initial carry, returns final carry.
	// c < 3*dvalue, x < 2*dvalue, this_i < dvalue
	// We need to select the fastest one that works in this environment.
	//
	// Alternately, set max digit bits to 28 since some
	// browsers slow down when dealing with 32-bit numbers.
	public inline function am (i : Int, x : Int, w : BigInteger, j : Int, c : Int, n : Int) {
		var xl = x&0x3fff, xh = x>>14;
		while(--n >= 0) {
			var l = this.n[i]&0x3fff;
			var h = this.n[i++]>>14;
			var m = xh*l+h*xl;
			l = xl*l+((m&0x3fff)<<14)+w.n[j]+c;
			c = (l>>28)+(m>>14)+xh*h;
			w.n[j++] = l&0xfffffff;
		}
		return c;
	}

	// (public) return value as integer
	public function intValue() {
		if(this.s < 0) {
			if(this.t == 1) return this.n[0]-DV;
			else if(this.t == 0) return -1;
		}
		else if(this.t == 1) return this.n[0];
		else if(this.t == 0) return 0;
		// assumes 16 < DB < 32
		return ((this.n[1]&((1<<(32-DB))-1))<<DB)|this.n[0];
	}

	// (public) 0 if this == 0, 1 if this > 0
	public inline function signum() {
		if(this.s < 0) return -1;
		else if(this.t <= 0 || (this.t == 1 && this.n[0] <= 0)) return 0;
		else return 1;
	}

	// (public)
	public function clone() { var r = nbi(); this.copyTo(r); return r; }

	// (public) true iff nth bit is set
	public function testBit(n : Int) {
		var j = Math.floor(n/BigInteger.DB);
		trace(j, this.t);
		if(j >= this.t) return(this.s!=0);
		return(( this.n[j] & (1 << (n % BigInteger.DB)))!=0);
	}

	// (protected) clamp off excess high words
	public inline function clamp() {
		var c = this.s&BigInteger.DM;
		while(this.t > 0 && this.n[this.t-1] == c) --this.t;
	}

	// (protected) return x s.t. r^x < DV
	public function chunkSize(r : Int) : Int { return Math.floor(Math.log(2)*DB/Math.log(r)); }

	// (protected) convert to radix string
	public function toRadix(b : Int) : String {
		if(b == null) b = 10;
		if(this.signum() == 0 || b < 2 || b > 36) return "0";
		var cs = this.chunkSize(b);
		var a = Std.int(Math.pow(b,cs));
		var d = nbv(a), y = nbi(), z = nbi(), r = "";
		this.divRemTo(d,y,z);
		while(y.signum() > 0) {
			r = Std.string((a+z.intValue())).substr(1) + r;
			y.divRemTo(d,y,z);
		}
		return Std.string(z.intValue()) + r;
	}

	// (protected) r = this op a (bitwise)
	public inline function bitwiseTo(a : BigInteger, op : Int -> Int -> Int, r : BigInteger) {
		var i, f, m = Std.int(Math.min(a.t,this.t));
		for(i in 0 ... m) r.n[i] = op(this.n[i],a.n[i]);
		if(a.t < this.t) {
			f = a.s&BigInteger.DM;
			for(i in m ... this.t) r.n[i] = op(this.n[i],f);
			r.t = this.t;
		}
		else {
			f = this.s&BigInteger.DM;
			for(i in m ... a.t) r.n[i] = op(f,a.n[i]);
			r.t = a.t;
		}
		r.s = op(this.s,a.s);
		r.clamp();
	}

	// returns bit length of the integer x
	public static inline function nbits(x : Int) {
		var r = 1, t;
		if((t=x>>>16) != 0) { x = t; r += 16; }
		if((t=x>>8) != 0) { x = t; r += 8; }
		if((t=x>>4) != 0) { x = t; r += 4; }
		if((t=x>>2) != 0) { x = t; r += 2; }
		if((t=x>>1) != 0) { x = t; r += 1; }
		return r;
	}

	// return index of lowest 1-bit in x, x < 2^31
	public static inline function lbit(x : Int) {
		if(x == 0) return -1;
		var r = 0;
		if((x&0xffff) == 0) { x >>= 16; r += 16; }
		if((x&0xff) == 0) { x >>= 8; r += 8; }
		if((x&0xf) == 0) { x >>= 4; r += 4; }
		if((x&3) == 0) { x >>= 2; r += 2; }
		if((x&1) == 0) ++r;
		return r;
	}

	// (public) returns index of lowest 1-bit (or -1 if none)
	public function getLowestSetBit() {
		for (i in 0 ... this.t)
			if(this.n[i] != 0) return i*DB+lbit(this.n[i]);
		if(this.s < 0) return this.t*DB;
		return -1;
	}

	// (public) return the number of bits in "this"
	function bitLength() {
		if(this.t <= 0) return 0;
		return DB*(this.t-1)+nbits(this.n[this.t-1]^(this.s&DM));
	}

	// (protected) r = this << n*DB
	public function dlShiftTo(n : Int, r : BigInteger) {
		var i;
		for(i in -(this.t-1) ... 1) r.n[-i+n] = this.n[-i];
		for(i in -(n-1) ... 1) r.n[-i] = 0;
		r.t = this.t+n;
		r.s = this.s;
	}

	// (protected) r = this >> n*DB
	public function drShiftTo(n : Int, r : BigInteger) {
		for(i in n ... this.t) r.n[i-n] = this.n[i];
		r.t = Std.int(Math.max(this.t-n,0));
		r.s = this.s;
	}

	// (public) this & a
	public static inline function op_and(x,y) { return x&y; }
	public inline function and(a : BigInteger) { var r = BigInteger.nbi(); this.bitwiseTo(a,op_and,r); return r; }

	// (public) this | a
	public static inline function op_or(x,y) { return x|y; }
	public inline function or(a : BigInteger) { var r = BigInteger.nbi(); this.bitwiseTo(a,op_or,r); return r; }

	// (public) this ^ a
	public static inline function op_xor(x,y) { return x^y; }
	public inline function xor(a : BigInteger) { var r = BigInteger.nbi(); this.bitwiseTo(a,op_xor,r); return r; }

	// (public) this & ~a
	public static inline function op_andnot(x,y) { return x&~y; }
	public inline function andNot(a : BigInteger) { var r = BigInteger.nbi(); this.bitwiseTo(a,op_andnot,r); return r; }

	// (public) ~this
	public inline function not() {
		var r = nbi();
		for(i in 0 ... this.t) r.n[i] = BigInteger.DM &~ this.n[i];
		r.t = this.t;
		r.s = ~this.s;
		return r;
	}

	// (protected) r = this << n
	public inline function lShiftTo(n : Int,r : BigInteger) {
		var bs = n%BigInteger.DB;
		var cbs = BigInteger.DB-bs;
		var bm = (1<<cbs)-1;
		var ds = Math.floor(n/BigInteger.DB), c = (this.s<<bs)&BigInteger.DM, i;
		for(i in -(this.t-1) ... 1) {
			r.n[-i+ds+1] = (this.n[-i]>>cbs)|c;
			c = (this.n[-i]&bm)<<bs;
		}
		for(i in -(ds-1) ... 1) r.n[-i] = 0;
		r.n[ds] = c;
		r.t = this.t+ds+1;
		r.s = this.s;
		r.clamp();
	}

	// (protected) r = this >> n
	public function rShiftTo(n : Int, r : BigInteger) {
		r.s = this.s;
		var ds = Math.floor(n/BigInteger.DB);
		if(ds >= this.t) { r.t = 0; return; }
		var bs = n%BigInteger.DB;
		var cbs = BigInteger.DB-bs;
		var bm = (1<<bs)-1;
		r.n[0] = this.n[ds]>>bs;
		for(i in ds+1 ... this.t) {
			r.n[i-ds-1] |= (this.n[i]&bm)<<cbs;
			r.n[i-ds] = this.n[i]>>bs;
		}
		if(bs > 0) r.n[this.t-ds-1] |= (this.s&bm)<<cbs;
		r.t = this.t-ds;
		r.clamp();
	}

	// (public) this << n
	public inline function shiftLeft(n : Int) {
		var r = nbi();
		if(n < 0) this.rShiftTo(-n,r); else this.lShiftTo(n,r);
		return r;
	}

	// (public) this >> n
	public inline function shiftRight(n : Int) {
		var r = nbi();
		if(n < 0) this.lShiftTo(-n,r); else this.rShiftTo(n,r);
		return r;
	}

	// (protected) true iff this is even
	public inline function isEven() { return ((this.t>0)?(this.n[0]&1):this.s) == 0; }

	// (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
	public function exp(e : Int, z : ModPow) {
		if(e > 0xffffffff || e < 1) return BigInteger.ONE;
		var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e)-1;
		g.copyTo(r);
		while(--i >= 0) {
			z.sqrTo(r,r2);
			if((e&(1<<i)) > 0) z.mulTo(r2,g,r);
			else { var t = r; r = r2; r2 = t; }
		}
		return z.revert(r);
	}

	// (protected) this += n << w words, this >= 0
	public inline function dAddOffset(n : Int, w : Int) {
		if(n == 0) return;
		while(this.t <= w) this.n[this.t++] = 0;
		this.n[w] += n;
		while(this.n[w] >= BigInteger.DV) {
			this.n[w] -= BigInteger.DV;
			if(++w >= this.t) this.n[this.t++] = 0;
			++this.n[w];
		}
	}

	// (protected) copy this to r
	public inline function copyTo(r : BigInteger) {
		for(i in -(this.t-1) ... 1) r.n[-i] = this.n[-i];
		r.t = this.t;
		r.s = this.s;
	}

	// (protected) r = this + a
	function addTo(a : BigInteger, r : BigInteger) {
		var i = 0, c = 0, m = Math.min(a.t,this.t);
		while(i < m) {
			c += this.n[i]+a.n[i];
			r.n[i++] = c&BigInteger.DM;
			c >>= BigInteger.DB;
		}
		if(a.t < this.t) {
			c += a.s;
			while(i < this.t) {
				c += this.n[i];
				r.n[i++] = c&BigInteger.DM;
				c >>= BigInteger.DB;
			}
			c += this.s;
		}
		else {
			c += this.s;
			while(i < a.t) {
				c += a.n[i];
				r.n[i++] = c&BigInteger.DM;
				c >>= BigInteger.DB;
			}
			c += a.s;
		}
		r.s = (c<0)?-1:0;
		if(c > 0) r.n[i++] = c;
		else if(c < -1) r.n[i++] = BigInteger.DV+c;
		r.t = i;
		r.clamp();
	}

	// (protected) r = this - a
	public function subTo(a : BigInteger, r : BigInteger) {
		var i = 0, c = 0, m = Math.min(a.t,this.t);
		while(i < m) {
			c += this.n[i]-a.n[i];
			r.n[i++] = c&BigInteger.DM;
			c >>= BigInteger.DB;
		}
		if(a.t < this.t) {
			c -= a.s;
			while(i < this.t) {
				c += this.n[i];
				r.n[i++] = c&BigInteger.DM;
				c >>= BigInteger.DB;
			}
			c += this.s;
		}
		else {
			c += this.s;
			while(i < a.t) {
				c -= a.n[i];
				r.n[i++] = c&BigInteger.DM;
				c >>= BigInteger.DB;
			}
			c -= a.s;
		}
		r.s = (c<0)?-1:0;
		if(c < -1) r.n[i++] = BigInteger.DV+c;
		else if(c > 0) r.n[i++] = c;
		r.t = i;
		r.clamp();
	}

	// (protected) r = this * a, r != this,a (HAC 14.12)
	// "this" should be the larger one if appropriate.
	public function multiplyTo(a : BigInteger ,r : BigInteger) {
		var x = this.abs(), y = a.abs();
		var i = x.t;
		r.t = i+y.t;
		while(--i >= 0) r.n[i] = 0;
		for(i in 0 ... y.t) r.n[i+x.t] = x.am(0,y.n[i],r,i,0,x.t);
		r.s = 0;
		r.clamp();
		if(this.s != a.s) BigInteger.ZERO.subTo(r,r);
	}

	// (protected) this *= n, this >= 0, 1 < n < DV
	public function dMultiply(n) {
		this.n[this.t] = this.am(0,n-1,this,0,0,this.t);
		++this.t;
		this.clamp();
	}

	// (protected) r = this^2, r != this (HAC 14.16)
	public function squareTo(r : BigInteger) {
		var x = this.abs();
		var i = r.t = 2*x.t;
		while(--i >= 0) r.n[i] = 0;
		for(i in 0 ... x.t-1) {
			var c = x.am(i,x.n[i],r,2*i,0,1);
			if((r.n[i+x.t]+=x.am(i+1,2*x.n[i],r,2*i+1,c,x.t-i-1)) >= BigInteger.DV) {
				r.n[i+x.t] -= BigInteger.DV;
				r.n[i+x.t+1] = 1;
			}
		}
		if(r.t > 0) r.n[r.t-1] += x.am(i,x.n[i],r,2*i,0,1);
		r.s = 0;
		r.clamp();
	}

	// (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
	// r != q, this != m.  q or r may be null.
	public function divRemTo(m : BigInteger, q : BigInteger, r : BigInteger) {
		var pm = m.abs();
		if(pm.t <= 0) return;
		var pt = this.abs();
		if(pt.t < pm.t) {
			if(q != null) q.fromInt(0);
			if(r != null) this.copyTo(r);
			return;
		}
		if(r == null) r = nbi();
		var y = nbi(), ts = this.s, ms = m.s;
		var nsh = BigInteger.DB-BigInteger.nbits(pm.n[pm.t-1]);	// normalize modulus
		if(nsh > 0) {pm.lShiftTo(nsh,y); pt.lShiftTo(nsh,r); }
		else { pm.copyTo(y); pt.copyTo(r); }
		var ys = y.t;
		var y0 = y.n[ys-1];
		if(y0 == 0) return;
		var yt = y0*(1<<BigInteger.F1)+((ys>1)?y.n[ys-2]>>BigInteger.F2:0);
		var d1 = BigInteger.FV/yt, d2 = (1<<BigInteger.F1)/yt, e = 1<<BigInteger.F2;
		var i = r.t, j = i-ys, t = (q==null)?nbi():q;
		y.dlShiftTo(j,t);
		if(r.compareTo(t) >= 0) {
			r.n[r.t++] = 1;
			r.subTo(t,r);
		}
		BigInteger.ONE.dlShiftTo(ys,t);
		t.subTo(y,y);	// "negative" y so we can replace sub with am later
		while(y.t < ys) y.n[y.t++] = 0;
		while(--j >= 0) {
			// Estimate quotient digit
			var qd = (r.n[--i]==y0)?BigInteger.DM:Math.floor(r.n[i]*d1+(r.n[i-1]+e)*d2);
			if((r.n[i]+=y.am(0,qd,r,j,0,ys)) < qd) {	// Try it out
				y.dlShiftTo(j,t);
				r.subTo(t,r);
				while(r.n[i] < --qd) r.subTo(t,r);
			}
		}
		if(q != null) {
			r.drShiftTo(ys,q);
			if(ts != ms) BigInteger.ZERO.subTo(q,q);
		}
		r.t = ys;
		r.clamp();
		if(nsh > 0) r.rShiftTo(nsh,r);	// Denormalize remainder
		if(ts < 0) BigInteger.ZERO.subTo(r,r);
	}

	// (protected) return "-1/this % 2^DB"; useful for Mont. reduction
	// justification:
	//         xy == 1 (mod m)
	//         xy =  1+km
	//   xy(2-xy) = (1+km)(1-km)
	// x[y(2-xy)] = 1-k^2m^2
	// x[y(2-xy)] == 1 (mod m^2)
	// if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
	// should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
	// JS multiply "overflows" differently from C/C++, so care is needed here.
	public function invDigit() : Int {
		if(this.t < 1) return 0;
		var x = this.n[0];
		if((x&1) == 0) return 0;
		var y = x&3;		// y == 1/x mod 2^2
		y = (y*(2-(x&0xf)*y))&0xf;	// y == 1/x mod 2^4
		y = (y*(2-(x&0xff)*y))&0xff;	// y == 1/x mod 2^8
		y = (y*(2-(((x&0xffff)*y)&0xffff)))&0xffff;	// y == 1/x mod 2^16
		// last step - calculate inverse mod DV directly;
		// assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
		y = (y*(2-x*y%DV))%DV;		// y == 1/x mod 2^dbits
		// we really want the negative inverse, and -DV < y < DV
		return (y>0)?DV-y:-y;
	}

	// (public) this + a
	public inline function add(a) { var r = nbi(); this.addTo(a,r); return r; }

	// (public) this - a
	public inline function subtract(a) { var r = nbi(); this.subTo(a,r); return r; }

	// (public) this * a
	public inline function multiply(a) { var r = nbi(); this.multiplyTo(a,r); return r; }

	// (public) this^2
	public inline function square() { var r = nbi(); this.squareTo(r); return r; }

	// (public) this / a
	public inline function divide(a) { var r = nbi(); this.divRemTo(a,r,null); return r; }

	// (public) this % a
	public inline function remainder(a) { var r = nbi(); this.divRemTo(a,null,r); return r; }

	// (public) -this
	public inline function negate() { var r = nbi(); BigInteger.ZERO.subTo(this,r); return r; }

	// (public) |this|
	public inline function abs() { return (this.s<0)?this.negate():this; }

	// (public) return + if this > a, - if this < a, 0 if equal
	public function compareTo(a : BigInteger) {
		var r = this.s-a.s;
		if(r != 0) return r;
		var i = this.t;
		r = i-a.t;
		if(r != 0) return (this.s<0)?-r:r;
		while(--i >= 0) if((r=this.n[i]-a.n[i]) != 0) return r;
		return 0;
	}

	// (protected) r = lower n words of "this * a", a.t <= n
	// "this" should be the larger one if appropriate.
	public function multiplyLowerTo(a : BigInteger, n : Int, r : BigInteger) {
		var i = Std.int(Math.min(this.t+a.t,n));
		r.s = 0; // assumes a,this >= 0
		r.t = i;
		while(i > 0) r.n[--i] = 0;
		var j;
		var ii = i;
		for(i in ii ... (r.t-this.t)) r.n[i+this.t] = this.am(0,a.n[i],r,i,0,this.t);
		for(i in (r.t-this.t) ... Std.int(Math.min(a.t, n))) this.am(0,a.n[i],r,i,0,n-i);
		r.clamp();
	}

	// (protected) r = "this * a" without lower n words, n > 0
	// "this" should be the larger one if appropriate.
	public function multiplyUpperTo(a : BigInteger,n : Int, r : BigInteger) {
		--n;
		var i = r.t = this.t+a.t-n;
		r.s = 0; // assumes a,this >= 0
		while(--i >= 0) r.n[i] = 0;
		for(i in Std.int(Math.max(n-this.t,0)) ... a.t)
			r.n[this.t+i-n] = this.am(n-i,a.n[i],r,0,0,this.t+i-n);
		r.clamp();
		r.drShiftTo(1,r);
	}

	// (public) this mod a
	public function mod(a : BigInteger) {
		var r = nbi();
		this.abs().divRemTo(a,null,r);
		if(this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r,r);
		return r;
	}

	// (public) this^e % m, 0 <= e < 2^32
	public function modPowInt(e : Int, m : BigInteger) {
		var z : ModPow;
		if(e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
		return this.exp(e,z);
	}

	// (public) this^e % m (HAC 14.85)
	public function modPow(e : BigInteger, m : BigInteger) {
		var i = e.bitLength(), k, r = nbv(1);
		var z : ModPow;
		if(i <= 0) return r;
		else if(i < 18) k = 1;
		else if(i < 48) k = 3;
		else if(i < 144) k = 4;
		else if(i < 768) k = 5;
		else k = 6;
		if(i < 8)
			z = new Classic(m);
		else if(m.isEven())
			z = new Barrett(m);
		else
			z = new Montgomery(m);

		// precomputation
		var g = new Array(), n = 3, k1 = k-1, km = (1<<k)-1;
		g[1] = z.convert(this);
		if(k > 1) {
			var g2 = nbi();
			z.sqrTo(g[1],g2);
			while(n <= km) {
				g[n] = nbi();
				z.mulTo(g2,g[n-2],g[n]);
				n += 2;
			}
		}

		var j = e.t-1, w, is1 = true, r2 = nbi(), t;
		i = nbits(e.n[j])-1;
		while(j >= 0) {
			if(i >= k1) w = (e.n[j]>>(i-k1))&km;
			else {
				w = (e.n[j]&((1<<(i+1))-1))<<(k1-i);
				if(j > 0) w |= e.n[j-1]>>(DB+i-k1);
			}

			n = k;
			while((w&1) == 0) { w >>= 1; --n; }
			if((i -= n) < 0) { i += DB; --j; }
			if(is1) {	// ret == 1, don't bother squaring or multiplying it
				g[w].copyTo(r);
				is1 = false;
			}
			else {
				while(n > 1) { z.sqrTo(r,r2); z.sqrTo(r2,r); n -= 2; }
				if(n > 0) z.sqrTo(r,r2); else { t = r; r = r2; r2 = t; }
				z.mulTo(r2,g[w],r);
			}

			while(j >= 0 && (e.n[j]&(1<<i)) == 0) {
				z.sqrTo(r,r2); t = r; r = r2; r2 = t;
				if(--i < 0) { i = DB-1; --j; }
			}
		}
		return z.revert(r);
	}

	// (protected) this % n, n < 2^26
	public function modInt(n : Int) {
		if(n <= 0) return 0;
		var d = BigInteger.DV%n, r = (this.s<0)?n-1:0;
		if(this.t > 0)
			if(d == 0) r = this.n[0]%n;
			else for(i in -(this.t-1) ... 1) r = (d*r+this.n[-i])%n;
		return r;
	}

	// (protected) true if probably prime (HAC 4.24, Miller-Rabin)
	public function millerRabin(t : Int) {
		var n1 = this.subtract(BigInteger.ONE);
		var k = n1.getLowestSetBit();
		if(k <= 0) return false;
		var r = n1.shiftRight(k);
		t = (t+1)>>1;
		if(t > lowprimes.length) t = lowprimes.length;
		var a = nbi();
		for(i in 0 ... t) {
			//Pick bases at random, instead of starting at 2
			a.fromInt(lowprimes[Math.floor(Math.random()*lowprimes.length)]);
			var y = a.modPow(r,this);
			if(y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
				var j = 1;
				while(j++ < k && y.compareTo(n1) != 0) {
					y = y.modPowInt(2,this);
					if(y.compareTo(BigInteger.ONE) == 0) return false;
				}
				if(y.compareTo(n1) != 0) return false;
			}
		}
		return true;
	}

	// (public) test primality with certainty >= 1-.5^t
	public function isProbablePrime(t) {
		var i, x = this.abs();
		if(x.t == 1 && x.n[0] <= lowprimes[lowprimes.length-1]) {
			for(i in 0 ... lowprimes.length)
				if(x.n[0] == lowprimes[i]) return true;
			return false;
		}
		if(x.isEven()) return false;
		i = 1;
		while(i < lowprimes.length) {
			var m = lowprimes[i], j = i+1;
			while(j < lowprimes.length && m < lplim) m *= lowprimes[j++];
			m = x.modInt(m);
			while(i < j) if(m%lowprimes[i++] == 0) return false;
		}
		return x.millerRabin(t);
	}

	// (public) 1/this % m (HAC 14.61)
	public function modInverse(m : BigInteger) {
		var ac = m.isEven();
		if((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
		var u = m.clone();
		var v = this.clone();
		var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
		while(u.signum() != 0) {
			while(u.isEven()) {
				u.rShiftTo(1,u);
				if(ac) {
					if(!a.isEven() || !b.isEven()) { a.addTo(this,a); b.subTo(m,b); }
					a.rShiftTo(1,a);
				}
				else if(!b.isEven()) b.subTo(m,b);
				b.rShiftTo(1,b);
			}
			while(v.isEven()) {
				v.rShiftTo(1,v);
				if(ac) {
					if(!c.isEven() || !d.isEven()) { c.addTo(this,c); d.subTo(m,d); }
					c.rShiftTo(1,c);
				}
				else if(!d.isEven()) d.subTo(m,d);
				d.rShiftTo(1,d);
			}
			if(u.compareTo(v) >= 0) {
				u.subTo(v,u);
				if(ac) a.subTo(c,a);
				b.subTo(d,b);
			}
			else {
				v.subTo(u,v);
				if(ac) c.subTo(a,c);
				d.subTo(b,d);
			}
		}
		if(v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
		if(d.compareTo(m) >= 0) return d.subtract(m);
		if(d.signum() < 0) d.addTo(m,d); else return d;
		if(d.signum() < 0) return d.add(m); else return d;
	}

	public function new<T> (?a_ : Null<AbsNumber<T>>, ?b : Int = 10, ?c) {
		var a : Null<Number<T>> = a_;
		
		if (a != null) {
			switch (a) {
				case Num(a) :
					this.fromNumber(a, b, c);
				case Str(a) :
					this.fromString(a, b);
			}
		}
	}

	// (protected) alternate constructor
	private function fromNumber<T>(a : Int, b : Int, ?c = 10) {
		// new BigInteger(int,int,RNG)
		if(a < 2) this.fromInt(1);
		else {
			//this.fromNumber(a,c);
			if(!this.testBit(a-1))	// force MSB set
				this.bitwiseTo(BigInteger.ONE.shiftLeft(a-1),op_or,this);
			if(this.isEven()) this.dAddOffset(1,0); // force odd
			while(!this.isProbablePrime(b)) {
				this.dAddOffset(2,0);
				if(this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a-1),this);
			}
		}
	}

	// (protected) set from integer value x, -DV <= x < DV
	private function fromInt(x : Int) {
		this.t = 1;
		this.s = x < 0 ? -1 : 0;
		if(x > 0) this.n[0] = x;
		else if(x < -1) this.n[0] = x+DV;
		else this.t = 0;
	}

	// (protected) convert from radix string
	public function fromRadix(s : String, b : Int) {
		this.fromInt(0);
		if(b == null) b = 10;
		var cs = this.chunkSize(b);
		var d = Std.int(Math.pow(b,cs)), mi = false, j = 0, w = 0;
		for(i in 0 ... s.length) {
			var x = intAt(s,i);
			if(x < 0) {
				if(s.charAt(i) == "-" && this.signum() == 0) mi = true;
				continue;
			}
			w = b*w+x;
			if(++j >= cs) {
				this.dMultiply(d);
				this.dAddOffset(w,0);
				j = 0;
				w = 0;
			}
		}
		if(j > 0) {
			this.dMultiply(Std.int(Math.pow(b,j)));
			this.dAddOffset(w,0);
		}
		if(mi) BigInteger.ZERO.subTo(this,this);
	}

	private static function intOfString(c : Int) : Int {
		if ("0".charCodeAt(0) <= c || c <="9".charCodeAt(0))
			return c - "0".charCodeAt(0);
		else
			return 0;
	}

	private function fromString<T>(s_ : String, b_ : AbsNumber<T>) {
		var b : Number<T> = b_;
		var s : CharArray = s_;
		var k;
		
		switch (b) {
			case Num(b):
				if(b == 16) k = 4;
				else if(b == 8) k = 3;
				else if(b == 256) k = 8; // byte array
				else if(b == 2) k = 1;
				else if(b == 32) k = 5;
				else if(b == 4) k = 2;
				else { this.fromRadix(s,b); return; };
			case _:
				throw "Error!";
		}

		this.t = 0;
		this.s = 0;
		var i = (!s).length, mi = false, sh = 0;
		while(--i >= 0) {
			var x = (k==8) ? intOfString(s[i]) & 0xff : intAt(s, i);
			if(x < 0) {
				if((!s).charAt(i) == "-") mi = true;
				continue;
			}
			mi = false;
			if(sh == 0)
				this.n[this.t++] = x;
			else if(sh+k > DB) {
				this.n[this.t-1] |= (x&((1<<(DB-sh))-1))<<sh;
				this.n[this.t++] = (x>>(DB-sh));
			}
			else
				this.n[this.t-1] |= x<<sh;
			sh += k;
			if(sh >= DB) sh -= DB;
		}
		if(k == 8 && (intOfString(s[0])&0x80) != 0) {
			this.s = -1;
			if(sh > 0) this.n[this.t-1] |= ((1<<(DB-sh))-1)<<sh;
		}
		this.clamp();
		if(mi) BigInteger.ZERO.subTo(this,this);
	}

	// (public) return string representation in given radix
	public function toString(?b : Int = 10) : String {
		if(this.s < 0) return "-"+this.negate().toString(b);
		var k;
		if(b == 16) k = 4;
		else if(b == 8) k = 3;
		else if(b == 2) k = 1;
		else if(b == 32) k = 5;
		else if(b == 4) k = 2;
		else return this.toRadix(b);
		var km = (1<<k)-1, d, m = false, r = "", i = this.t;
		var p = DB-(i*DB)%k;
		if(i-- > 0) {
			if(p < DB && (d = this.n[i]>>p) > 0) { m = true; r = int2char(d); }
			while(i >= 0) {
				if(p < k) {
					d = (this.n[i]&((1<<p)-1))<<(k-p);
					d |= this.n[--i]>>(p+=DB-k);
				}
				else {
					d = (this.n[i]>>(p-=k))&km;
					if(p <= 0) { p += DB; --i; }
				}
				if(d > 0) m = true;
				if(m) r += int2char(d);
			}
		}
		return m?r:"0";
	}

	public static function main () {
		var x = new BigInteger("3", 10);
		var y = new BigInteger("11");
 
		trace(x.modInverse(y).toString());
	}
}
