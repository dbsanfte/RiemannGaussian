
## Finite quadratic-class transport and Casoratian test, 2026-10-24

The full query still costs soft sqrt(JL), hence soft k^(3/2) at
J=O(k), L=O(k²). This pass proves two exact finite identities and pays
their auxiliary data, but does not acquire the coarse residue or improve
the whole-query exponent. The all-semiprime sixth-rate goal, unconditional
orientation and executable Lean bit-cost proof remain open. These are
tested algorithm candidates, not a generic obstruction to faster recurrence.

The actual inputs remain the prime-cube construction k=d r³, m=d r²,
H=k², d=2c0. Use INVERSE arguments z_h=Vhat_h^-1=C D^h E^(h²),
including the known common q shift and D's barpi^(-2m) factor. Then
P_L(z)=prod_(i<L)(1-q^i z) vanishes exactly at the original covered
equality Vhat_h=q^i. All original labels and signed carry-adjusted
indices remain attached. No D=q or E=q specialization is assumed.

The centered phase coefficient ell2 is an integer multiple of m²,
because H=m²r². Consequently theta=pi^(m²) and a=-ell2/m² are supplied,
with E=theta^a and E^(r²)=q^a globally. Here a is a known signed integer,
unit modulo r; this is not an acquired discrete logarithm.

For Z(C,D)=prod_(h<r) P_L(C D^h E^(h²)), shifting h by one proves
the division-free identity

    P_L(C) Z(CDE,DE²) = P_L(C D^r q^a) Z(C,D).

For M=J/r classes, both endpoint-value vectors are actually acquired by
zero-safe polynomial multipoint evaluation in soft sqrt(ML). Choose
b~sqrt(ML), build a degree-b baby product, evaluate its M L/b target
arguments, and retain the clipped tail. Thus the endpoint batch costs
soft k^(3/2)/sqrt(r) in the upper-bound regime. This is an auxiliary
batch improvement only: the class amplitude Z remains unpaid.

Indeed, writing A_h=P_L(z_h), the two products are A_0 U and A_r U,
where U=prod_(1<=h<r) A_h. An interior hit zeros both products; their
known endpoint ratio cancels the interior first variation as well.
After r² shifts, C becomes C D^(r²) q^(a r²), while D becomes
D q^(2a). The retained mixed factor in D^(r²) prevents claiming a
closed scalar orbit. Artificial h=r endpoints have no inherited native
unique-hit or saturated-leaf decoder. Endpoint nonunits are classified
lawfully, with unusable cases retaining the established bounded fallback.

A second test uses a finite specialization of Warnaar's determinant
(Lemma 5.2, Lemma 5.3 and Corollary 5.4 of
[Summation and transformation formulas for elliptic hypergeometric series](https://people.smp.uq.edu.au/OleWarnaar/pubs/Elliptic-HS.pdf)).
First set the elliptic nome to zero, then the auxiliary reciprocal-pair
parameter to zero; neither operation changes the native C,D,E. For a
class of n points set

    R_ij=(q^L z_i;q)_j/(z_i;q)_j, 0<=i,j<n,
    K_n=q^[2 binom(n,3)] prod_(t=0)^(n-2)(1-q^(L-t))^(n-1-t).

Its exact finite determinant is

    det R = K_n prod_(i<j)(z_j-z_i) / prod_i(z_i;q)_(n-1).

The report also derives the coefficient determinant directly, checking
the sign and q power without an infinite-product specialization.
For M_ij=P_L(q^j z_i), finite product cancellation gives

    M=diag(P_L(z_i)) R,
    det M=(det R) prod_i P_L(z_i).

Only SHORT head factors are inverted. The shifted own index exceeds r,
so extended unique-minus coverage makes every such head factor nonzero
at the good smaller nonsplit prime. Norm/coordinate classification
therefore gives a proper factor or actual units on that branch.

For an invertible normalizer, sort/deduplicate exact global points
WITHIN classes and rerun actual separation. A duplicate involving the
unique hit is impossible. Removing nonhit duplicates preserves the weak
coarse-label derivative ratio up to a nonzero LOCAL common multiplier;
it is not equality of the full-r products. Retained sizes can vary, so
the earlier uniform-size leading-coefficient assertion is not reused.

All short head polynomials, their derivative values, K_n, ordered class
Vandermondes and normalization derivatives cost soft k for the WHOLE
family: n<=r, total points<=k, and r²<=k. Recursive cross-products and
monic MPE avoid materializing n² matrices. Supplied-vector actions of
the short R matrices are also paid. None of this acquires the long
row amplitudes inside M. At an actual collision, a zero row of M still
contains precisely the missing collision information.

The zero-parameter initialization was tested as well. For
H(C)=prod_(h<r)(1-C D^h E^(h²)), the exact equation

    H(C) Z(qC,D)=H(q^L C) Z(C,D), Z(0,D)=1

provides genuine short coefficient data. But C=0 is a separate fixed
orbit, and the product degree is rL. No fast evaluation at the supplied
unit C follows; full coefficient execution also needs q-denominator
guards beyond 16H when its degree exceeds that screen. No analytic
continuation modulo N or infinite theta-tail deletion is used.

The next useful algorithm must retain the interior weak collision
signal while using this paid finite data, or acquire all small-class
remainders with shared preprocessing. A proposed bound such as
soft(sqrt L+sum_c n_c^omega) is only a target: the paired Cauchy/Krylov
contraction needed to initialize those remainders has not been supplied.
Additional correct residues, low-degree output lists or short germs
must not be treated as acquired merely because their consumers are cheap.

Exact reports, independent source reviews and preservation validation:
/tmp/semiprime-quadratic-class-query-20261024/. No numerical success
campaign, backend lemma batch or broad build was used for this pass.
All previous shared-document prefixes, 270 frozen evidence entries,
HEAD and concurrent RH work are preserved.
