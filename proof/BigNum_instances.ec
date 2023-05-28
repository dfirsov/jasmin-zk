from Jasmin require import JBigNum.

require Array32 Array64 Array128 Array3.

abbrev nlimbs = 32.
abbrev dnlimbs = 64.

clone BigNum as W64xN with
 op nlimbs <- nlimbs,
 theory R.A <= Array32.Array32,
 theory R2.A <= Array64.Array64,
 theory Array3 <= Array3.Array3
proof*.
realize gt0_nlimbs by done.


clone BigNum as W64x2N with
 op nlimbs <- dnlimbs,
 theory R.A <= Array64.Array64,
 theory R2.A <= Array128.Array128,
 theory Array3 <= Array3.Array3
proof*.
realize gt0_nlimbs by done.
