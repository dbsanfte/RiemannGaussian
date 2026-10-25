# Cheap traces need a detector theorem

23 October 2026. Root clarification of the acquisition target, using the
already acquired ordinary-cofactor reindexing. No general arithmetic or
circuit lower bound is asserted.

For consecutive integer exponents T in [L,U], let Z_T=beta^(N-T), with
beta a known unit modulo N. The k-th power trace is

    S_k=beta^(k(N-L))*sum_(j=0)^(U-L) (beta^(-k))^j.

Every specified k of O(log N) bits is therefore evaluated in polynomial
logarithmic bit work, even when U-L is of order r^3. No division by
1-beta^(-k) is needed. The binary geometric-sum recursion

    G_(2n)(z)=(1+z^n)G_n(z),
    G_(2n+1)(z)=G_(2n)(z)+z^(2n), G_n=sum_(0<=j<n)z^j,

uses O(log n) ring operations and handles nonunit 1-z. The same applies
to a progression of exponents, and excluded multiples of r are removed
by subtracting another geometric sum. Actual signed interval endpoints
and negative powers are safe because beta is a known unit.

Consequently h specified traces of this normalized, product-equivalent
cofactor family are already acquired in soft O(h) work. In particular
h<=r fits the desired budget. If the supplied indices are k=1,...,h,
Newton's identities recover the corresponding length-h product prefix
in soft O(h) additional work: P,Q>16r^2 makes every denominator 1,...,h
a unit. The original unnormalized leaves need not have these same traces.

This supplies no full product value at z=1. The polynomial can have
degree Theta(r^3), and the acquired prefix is not its complete list of
coefficients. The inherited ordinary progression product query still has
the charged soft O(r^(3/2)) evaluator. A faster evaluator is not ruled
out; it simply does not follow from the cheap traces.

This is a concrete reason to require a proved detection link whenever a
new trace algorithm is proposed. Even improving the latest quadratic
family from soft O(rh) to soft O(r+h) for h=Theta(r) would not, on its own,
establish a collision detector. Such a trace improvement should be
pursued only alongside a reason those particular data retain a useful
collision. A compact representation, simultaneous moments, or a Newton
prefix is not the whole-family acquisition theorem requested by the user.

Inherited source: semiprime-curvature-acquisition-20261023, report
interval-reindexing.md. The new checkpoint's source pins preserve its
exact path and fingerprint.
