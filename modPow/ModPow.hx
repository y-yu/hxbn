package modPow;
import BigInteger;

interface ModPow {
	public function convert(x : BigInteger) : BigInteger;
	public function revert(x : BigInteger) : BigInteger;
	public function reduce(x : BigInteger) : Void;
	public function mulTo(x : BigInteger, y : BigInteger, r : BigInteger) : Void;
	public function sqrTo(x : BigInteger, r : BigInteger) : Void;
}
