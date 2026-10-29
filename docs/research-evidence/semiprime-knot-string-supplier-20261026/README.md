# Residue acquisition and the string-theory proposal: executed tests

26 October 2026. The preceding hybrid audit was progress: it proved a
soft-k consumer for a coarse residue of a covered kernel collision and
identified the missing supplier. This continuation tests actual suppliers
and incorporates the user's new
[string-theory research proposal](../../semiprime-string-theory-research-proposal.md).
The proposal is preserved unchanged.

**There is no new whole-query exponent.** The constructive result is an
explicit Schur boundary matrix whose entries, determinant and inverse
action are all acquired in soft O(k). Its exact relation to the covered
query exposes a separate diagonal of long products that is still unpaid.
The residue algorithms tested here are fully initialized, but their
complete cost remains soft O(N^(1/4)). The retained earlier route is
soft O(k^(5/4)), with k of order N^(1/6); neither bound is presented as
a general factoring record. The all-semiprime sixth-exponent goal,
complete bit-complexity proof and eventual Lean verification remain open.

## 1. What was executed

| Candidate | Acquired result | Remaining gap |
|---|---|---|
| Base-three residue refinement | A complete supplier of a useful h mod k, with punctures and factor recovery handled | Initial branch tests cost soft N^(1/4); the final cheap channel does not pay for them |
| Factor-lift congruence palette | Exact affine formula for h mod (k/2); a legitimate AP image in nonunit-slope cases | In the common unit-slope case every residue survives; actual integer factor information is needed beyond these congruences |
| Auxiliary-root colour filter | Correct residue semantics under an explicit order-coprimality premise; extra phase hits have a lawful decoder even without that premise | It enforces a supplied residue but does not cheaply choose one; extension and long-product costs remain |
| Nekrasov cancellation on the covered kernel rectangle | Exact cleared boundary identity, with collision multiplicities and literal holes accounted for | The boundary retains a mixed difference of collision counts, not the covered bulk count |
| Finite Schur/vertex and qq-character specialization | Both actual alphabets are geometric; the finite recurrence and its boundary coefficients are acquired | Literal deflation, finite endpoints and the long amplitude remain |
| Unbalanced Schur and spectral-dual boundary | Explicit boundary matrix, cheap determinant and a paid inverse action | The cleared Schur matrix still includes the original long row products |

The string-theory packages were specialized to the independently covered
universal kernel rectangle. This is not a claim to have executed every
package on the original phased Young hyperbola D_k. The latter still
needs its colour-incidence and carry analysis before uncoloured corner
counts can support a complexity claim.

## 2. A genuinely initialized boundary operator

The kernel product is

    product_(|b|<=V,|h|<=W,h!=Cb)(1-q^(Cb-h)),
    C=ceil(N/(2k)), V=O(sqrt k), W=O(sqrt(N/k)+sqrt k).

In the prepared hard branch C>W. Pairing opposite exponents reduces
its nonunit predicate to a b=0 factorial A0 and a positive-b block Z.
The A0 branch still costs soft sqrt(W); it has not been silently removed
from the coverage theorem. Set

    r=V, s=2W+1, A=C-W-1,
    Z_i=product_(t=1)^s(1-q^(A+C*(r-i)+t)),
    Z=product_i Z_i.

A concrete partition lambda_i=A+(C-1)(r-i) turns the principal Schur
specialization into an r-by-r cleared Jacobi--Trudi matrix K with

    K=diag(Z_i)*U.

All entries of U are products of at most r-1 endpoint factors. There
are O(r^2)=O(k) acquired factors and entries. More strongly, formal
cancellation gives the division-free identity

    det U=q^eta
      *product_(d=1)^(r-1)(1-q^(C*d))^(r-d)
      *product_(t=1)^(r-1)(1-q^(s+t))^t.

Only O(r) short-labelled factors need a unit screen. Any nonunit in
that screen has the original lawful factor/annihilator recovery. On
the continuing branch U is invertible. Interpolation followed by a
triangular polynomial-basis solve applies U inverse to an acquired
vector in O(r^2) ring operations, hence soft O(k) bit work.

This removes an initially unnecessary full-prefix denominator screen.
The long Schur denominator may be nonunit; all identities stay cleared.
The result is an actual initialized operator, not merely a small
determinant description or a hypothetical inverse.

The limit is equally exact: det K=Z det U. Computing or inverting U
does not acquire K, its singularity bit, or the unknown Z_i. Their
collision information is in the removed diagonal. No inexpensive
boundary determinant has been substituted for the original query.

See [construction and inverse algorithm](schur-boundary-operator.md),
[independent review](review-schur-boundary.md), and the broader
[spectral-duality specialization](cyclic-reciprocity.md).

## 3. What the arithmetic residue test establishes

At the true colour write P=j+ku, Q=c+kv, c=Q mod k, a=kt+cb,
D_N=(N-jc)/k, and R=k/2=3^e. The exact collision index is

    h=Cb+((P-1)/2)*(t-bv).

Eliminating v modulo R using PQ=N gives

    h=alpha+gamma*u mod R,
    gamma=b*((j-1)/2)*c*j^(-1) mod R.

For j=2 mod 3 and b a 3-unit, gamma is a unit. Consequently the
necessary modular lift family supplies every h residue modulo R.
Completing those residue cosets exactly recombines the original long
clock. If gamma is nonunit, its image is a computable AP, but there
is no uniform witness-selection theorem forcing sufficient divisibility.

This concerns a particular congruence-only construction. It does NOT
say that the actual divisors of a fixed N realize every formal lift,
or that a stronger arithmetic selector is impossible. It identifies
the additional information that this proposed supplier would need.
[Proof and boundary-count test](arithmetic-selector.md),
[review](review-arithmetic-selector.md).

## 4. Finite cancellation retains a boundary equation, not its amplitude

Regularizing a leaf as 1-(1-epsilon)q^e makes its epsilon valuation
at a hidden prime equal to one precisely when that leaf collides.
The valuation of the full punctured product is therefore the actual
collision count. Nekrasov's rectangle cancellation takes a mixed
difference of these counts; interior contributions can cancel. A
symbolic valuation or gcd flag is not an acquired numerical count.

The finite qq-style identity also keeps an explicit boundary:

    F(q^-W*z)*D(qz)=F(q^(W+1)*z)*D(z),
    F(z)=product_(b=-V)^V(1-q^(Cb)*z).

Both boundary polynomials are acquired. The known literal factors in
D must be deflated before interpreting a zero. Finite screening sums
have endpoint and hole corrections. The infinite formal commutation
identities in the source papers do not supply those amplitudes or
weights over the composite arithmetic ring.

The residue refinement algorithm does obtain an actual useful class,
but its first coarse nonunit tests pay soft sqrt(VW)=soft N^(1/4).
Later tests become cheaper geometrically; that does not reduce the
initial cost. [Initialized algorithms and source checks](multisection.md),
[review](review-multisection.md).

## 5. What remains worth combining

The Schur boundary operator supplies genuinely paid data that can be
used in a future hybrid. Its exact diagonal factorization also prevents
counting that normalization as collision acquisition. A successful next
step must acquire a collision-sensitive statistic of K without its
long row products, or supply a stronger arithmetic restriction on
actual factor lifts. Neither operation is supplied here.

For the proposal's main native-boundary direction, a different finite
weighted-state construction could still retain the cancelled divisor.
It must acquire its weights, initial state and finite endpoint terms
and prove a decoder; the present rectangle calculation is not a
general obstruction to qq-characters or string-theory methods.

All terminating saturated branches retain the once-only
T_ext=soft O(N^(31/192)) cost. Verification consists of symbolic
derivations, primary-source checks and independent reviews, not Lean
or a numerical coverage campaign. The packet preserves 890 prior
protected files, both research-document prefixes and 23 concurrent
files, including the user's proposal. See [validation](review.json),
[source pins](sources.json), and [manifest](manifest.json).
