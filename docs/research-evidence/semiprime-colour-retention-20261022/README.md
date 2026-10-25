# Retained quadratic colour and two shared long products

22 October 2026. This continuation follows the user's request to focus on
twists, colour and character cancellation. Its constructive result is a
reduction of **all native quadratic index masks to two common products**,
with every row translation and endpoint correction acquired in soft
O(m+J). The two remaining long products are not yet acquired in that bound.
The all-input sixth-rate goal and its full Lean bit-complexity proof remain
open. These are reviewed classical arguments and a reference implementation,
not new Lean theorems.

The earlier [twist palette](../semiprime-twist-palette-20261022/README.md)
pays unit corrections to the original query. This packet asks what
arithmetic information can survive cancellation, and constructs the
resulting common query explicitly. It does not count numerical successes
as coverage evidence.

## What the higher character actually retains

Use the retained prepared input N=P Q, odd prime row modulus m coprime to N,
nonzero tags j, and the original scalar gamma. The canonical row satisfies

    m² c_j - j m b_j + j² a_j = N,
    ell_j = m b_j - 2 a_j j,
    E_j = N + a_j + ell_j,        q = gamma^(m²).

At its own factor P=j+m h, the native index I obeys the INTEGER identity

    I P = a_j h² + b_j h + c_j.

The [higher-conductor derivation](reports/native-quadratic-colour.md) shows
that a conductor-m³ character cancels dependence on P's third digit but
retains exactly

    I = (a_j h² + b_j h + c_j)/j mod m.

The same colour can be carried by the proof-only source
gamma*zeta_(m³)^(-1); it does not need a new Gauss-derived scalar base or
its unproved order contract. The true h is still unknown. Eliminating it
gives the exact public mask

    Legendre(Delta_j + 4 a_j j I, m) in {0,1},
    Delta_j = b_j² - 4 a_j c_j.

This has exactly (m+1)/2 admissible residues. Completing the square gives

    kappa_j = -Delta_j/(4 a_j j) mod m,
    sign_j = Legendre(N j,m),
    I mod m in kappa_j + R_(sign_j),

where R_+ is zero together with the nonzero squares, and R_- is zero
together with the nonsquares. Thus the full row family needs two ordered
residue lists and J translation/sign pairs, not an m-by-J mask table.
The derivation and its source/recovery distinctions received an
[independent review](reviews/higher-conductor-review.md).

The review also constructs the two cyclotomic mask polynomials in soft
O(m), in a formal quadratic algebra g²=Legendre(-1,m)*m. Their power sums
are (1+sign*Legendre(k,m)*g)/2 for 1<=k< m, so fast truncated-series
exponentiation recovers their coefficients using only certified small
unit denominators. This does not identify the actual hidden colour or
replace the original scalar q by a root of unity.

## The paid common-product reduction

Write L=mK+t, 0<=t<m. Define just TWO common products in the ORIGINAL q:

    H_sign(X) = product_(r in R_sign, 0<=n<K) (X-q^(r+mn)).

For row j use y_j=gamma^E_j*q^(-kappa_j). Every translated mask reduces
to H_(sign_j)(y_j), with three prefix/suffix boundary corrections on the
two fixed residue lists. Their roots use only the three channels

    q^(r-m),     q^(r+mK),     q^(r+m(K-1)).

The [exact formulas](reports/two-common-products.md) retain the scaling
q^(kappa_j D_j), where D_j is the selected native index count. They handle
wraparound, the final partial block and K=0. Balanced product trees and
batched monic multipoint evaluation acquire ALL boundary requests in
soft O(m+J): each tree depth has total degree O(m) and O(J) requested
points. This is acquired arithmetic, not just a compact description.

Nonunit boundaries can be localized within the same budget. The
[independent cost and recovery audit](reviews/two-common-products-review.md)
discharges the nonzero exponent guard on the retained input:

    P,Q>16m²,  E_j>=N-3m²,  L<=4m²
    imply E_j>m²(L+m).

Consequently even a boundary leaf just beyond L supplies either a proper
factor or a nonzero O(log N)-bit annihilator for the original gamma.
The existing conditional annihilator decoder applies. The general formula
outside these retained promises still needs its stated ledger check.

**The remaining sufficient acquisition target** is evaluation of H_+
and H_- at their assigned O(J) points in soft O(m+J). Values alone suffice:
the [sufficiency addendum](reviews/two-products-sufficiency-addendum.md)
proves that J gcds select one collision-bearing row, after which the
inherited UNMASKED scalar interval product and descent cost soft O(sqrt L).
Every leaf has the already verified nonzero exponent ledger. No new
restriction-stable H oracle, coefficient array or H-localizer is needed.
Each common polynomial has degree K(m+1)/2, about L/2; its coefficients
have not been acquired cheaply.
They satisfy exactly

    H_+ H_- = product_(i<mK)(X-q^i)
                * product_(n<K)(X-q^(mn)),

and their ratio is the Legendre-signed q-product over nonzero residues.
The second factor above is cheap because K<=4m. The first is still the
long geometric query. A quadratic Gauss-period identity in zeta_m alone
does not evaluate either H at the original q.

For comparison, ordinary blocking still gives soft O(J+sqrt(JL)):
construct a block of B quotient-index steps, of degree O(mB), and
evaluate it at O(JK/B) shifted targets. Choosing B of order sqrt(JK/m)
gives the familiar dominant term. The new reduction pays translations
and exposes shared character structure; it does not yet reduce that term.

Further precision at the SAME prime does not repeatedly thin this mask.
The exact equation has discriminant

    D(I)=(b-mI)²-4a(c-jI).

Every lift of any nonzero-square class modulo m remains soluble at all
powers of m by Hensel lifting. There are (m-1)/2 such classes; only the
single zero-discriminant class can acquire additional restrictions. This
is a fact about this necessary residue predicate, not a general lower
bound for factoring or for character methods.

## Packed coefficients now have an executable acquisition path

The previous [packed Gauss quotient construction](reports/packed-gauss-quotient.md)
and its [independent audit](reviews/packed-gauss-independent-review.md)
are archived here with their original bytes. For a public auxiliary prime
ell and k dividing ell-1, it acquires C_E in (Z/N)[X]/(X^k-1), with
G_1^E=C_E G_E, including all exceptional character components. Its
mathematical native cost is soft O(ell+k) for polynomial-size E.

The new [coefficient controller](reports/packed-coefficient-observables.md)
folds C_N to EVERY divisor d of k and tests EVERY possible monomial
support in total soft O(k) work. Prefix/suffix gcds produce a proper factor
whenever one hidden reduction is a monomial and the other is not the same
monomial. Divisor-DAG folding charges all input and output arrays. This
is a sufficient condition with a paid detector, not universal coverage.
The reciprocal correlation collapses to the ordinary Fermat value
ell^(N-1), so a cheap initial Fermat gcd screens when this route can help.

[Reference code](implementation/packed_gauss.py) now constructs the actual
coefficient vector and runs that controller. It uses carry-safe byte
packing for convolution, GMP when available, and no supplied hidden field
or factors. Eight exact algebra/control test groups compare against an
independent small full cyclotomic carrier and synthetic support cases.
They are correctness tests, not semiprime-family coverage or scaling
benchmarks. See the [run instructions](implementation/README.md),
[independent implementation review](reviews/implementation-review.md) and
root replay in validation.json. Python/GMP runtime is not formally proved.

The same report specifies a second controller using C_N^k-1 and guarded
fast half-gcd. Its degree-imbalance condition is sufficient and its costs
are proved at the algorithm level; this controller is NOT implemented
here. The primary fast polynomial-gcd reference is
[van der Hoeven, version 1](https://arxiv.org/abs/2212.12389v1).
The missing selection theorem must guarantee an affordable auxiliary
whose coefficient behaviour separates the two hidden factors. A
compositeness witness alone does not imply that separation.

## Evidence and limits

reports/weighted-twist-outcome.md records the tested Fourier/jet route:
Fourier projection of the paid unit gauges does not acquire the original
collision product. No universal impossibility is inferred.

Reports and agent code are copied verbatim; archive-provenance.json maps
their original scratch locations to these portable artifacts. Historical
scratch cross-references inside reports resolve through that mapping.
Source papers are fingerprinted in source-pins.json rather than copied.
manifest.json freezes this packet; the older two twist packets are
unchanged. No Lean source, public endpoint, commit or push is part of
this research continuation.

The next mathematical target is simultaneous values of the pair H_+, H_-
with original scalar q. Recovery from those values is paid. The sixth-rate all-input acquisition
theorem, full bit/controller proof and Lean composition remain open.
