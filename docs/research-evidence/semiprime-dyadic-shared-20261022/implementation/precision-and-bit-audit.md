# Precision, Laurent and bit-cost audit

The stable implementation has optional `precision=h`, a positive integer; default `None` retains the full norm/tangent. It does not change frozen repository files.

At rank p, both retained inputs have z-degree <=q=min(p,h−1). The known support includes the COMPLETE product through j=2q. Its normalized exponent interval has width at most 4+ceil(L/p), so the slot count is O((q+1)(1+L/p)), including h=1. Interpolate on this complete candidate, restore actual spatial parity, halve spatial exponents, THEN discard j>=h. The production code follows this order; the test suite includes a wrong-order countercontrol which changes even the low coefficients.

Summing the candidate sizes over dyadic p<m gives

 O(h log(2m)+L log(2h)+L),

with the evident m-sized improvement when h>m. Indeed, for p<h, q<=p and the L/p term contributes O(L) per stage; for p>=h, the tail sum hL/p is geometric. For h=1 the sum is O(log m+L), not zero. Thus fast polynomial kernels give soft O(h+L) scalar arithmetic. The geometric-product exponent bound remains <=10m², because q<=p and radix 2q+1 is no larger than the full-stage radix 2p+1.

Negative shifts are handled in the formal Laurent ring R[Y,Y^-1][X]/(X^m−Y), where X is a unit and the determinant norm is well-defined. Evaluations at scalar Y require Y to be a unit when a returned exponent is negative. The constructor never assigns Y=0. Restored Laurent exponents are metadata; interpolation always uses the nonnegative normalized support.

An arbitrary integer shift s is not unit-cost input. Floor(s/p), its parity, and restored output exponents use O(log(2+|s|)+log m) bits. The bit bound is therefore soft O((h+L)(log N+log(2+|s|)+log m)), suppressing the multiplication/gcd logarithms and rank-depth logarithm. In the native polynomially bounded exponent regime this is the claimed soft-linear-in-m bit budget. If |s| is unrestricted, its bit length must remain explicit; there is no bound independent of reading/outputting it.

All nontrivial inversions are scalar unit inversions or formal series inversions with a unit constant. Interpolation nodes are eta^E with E spans below 10m², so local order >16m² proves all pairwise differences units. Formal polynomial products reduce coefficients modulo N; no coefficient swell with symbolic degree is assumed away. Monic remainder/product-tree routines admit standard fast-kernel replacement over the composite coefficient ring. The current Python polynomial kernels are schoolbook and do NOT certify that asymptotic bound by timing.

Stable files: `sheared_norm.py`, `test_sheared_norm.py`, `README.md`. Replay from this directory with `python3 -m unittest -v test_sheared_norm.py`.
