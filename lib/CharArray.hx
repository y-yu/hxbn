package lib;

abstract CharArray(String) {
    inline function new(x) {
        this = x;
    }
    
    public function get() { return this; }
    
    @:from public static inline function fromString(x : String) : CharArray {
        return new CharArray(x);
    }
    
    @:to public inline function toString() : String {
        return this;
    }
    
    @:arrayAccess public inline function arrayGetInt(i:Int) : Int {
        return this.charCodeAt(i);
    }
    
    // @:arrayAccess public inline function arraySetString(i:Int, v:String) : Void {
    //     this = this.substr(0, i) + v + this.substr(i + 1);
    // }

    @:arrayAccess public inline function arraySetInt(i:Int, v:Int) : Void {
        this = this.substr(0, i) + String.fromCharCode(v) + this.substr(i + 1);
    }

    // to access String's method
    @:op(!A) public inline function fieldAccess() : String {
        return this;
    }
    
}
