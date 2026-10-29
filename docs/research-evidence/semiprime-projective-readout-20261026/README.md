# Coefficient readouts: paid projective starts and paired arithmetic structure

26 October 2026. Continuation of the user's request for other expressions
for the factor-tag coefficients and useful connections to other domains.
This follows the [alternative-expression packet](../semiprime-coefficient-forms-20261026/README.md)
and the [uniform two-monic handoff](../semiprime-axis-supplier-20261026/hybrid-handoff.md).

**Two constructive results:** the projective recurrence now has cheaply
acquired adjacent starting ratios with a certified unit increment; and
the two-monic preparation can use a pure modulus K=2*3^e, making both
coefficient images single arithmetic progressions. These are acquisition
and structure improvements. The full query bound has not improved: the
best completed native weighted route remains soft K^(5/4), while the
simpler two-monic first-jet fallback costs soft K^(3/2). The all-semiprime
sixth-exponent factoring goal remains open.

## 1. What is being computed

The prepared hard branch has H=K², h=2H+1, J=phi(K)<=K, row roots y_j,
and labels w_j=[j]_n for n|K, n>2. For the soft-K single-residue HH
recovery choose n>=K^(1/3), with the fixed constants of that handoff.
The initialization proof itself only needs n>2. At one nonsplit prime R, one of two
families has exactly one row-clock equality y_j=q^i in 0<=i<h. Its
label is R mod n. No uniqueness is promised at the other prime.

For the product of marked leaves

    Z(delta,Y)=product_(j,i)(1-y_j*q^(-i)+delta*(1-Y*w_j)),

the first coefficients V=[delta]Z(delta,0), U=-[delta*Y]Z have V!=0
and U/V=R mod n at that good prime. The preceding packet also gives a
derivative-free row-cofactor replacement and two directional-resultant
outputs with the same ratio. Any such valid pair feeds the already paid
norm/gcd, small-label and restricted-HH recovery in soft K.

The full clock is long; the question is whether the required pair or ratio
can be acquired without computing all its long row products.

## 2. A proved short-prefix initialization algorithm

Acquire in soft J, without row-separation inverses,

    f(X)=product_j(1-y_j*X),
    v(X)=sum_j product_(l!=j)(1-y_l*X),
    u(X)=sum_j w_j*product_(l!=j)(1-y_l*X).

The original coefficients have the exact initialized recurrence

    (P_0,V_0,U_0)=(1,0,0),
    P_(i+1)=f_i*P_i,
    V_(i+1)=f_i*V_i+v_i*P_i,
    U_(i+1)=f_i*U_i+u_i*P_i,

where f_i=f(q^-i), and similarly for u_i,v_i. At the unique good hit,
this recurrence sets P to zero and fixes U/V to the correct tag.

**The new theorem:** evaluating the first 5J steps costs soft J and
either yields a legal factor-return branch, or, on the good family,
supplies an index s and c in {0,1,2} such that

    r_s=U_s/(V_s+c*U_s),
    r_(s+1)=U_(s+1)/(V_(s+1)+c*U_(s+1))

are defined by certified global units and their difference is also a
certified global unit. The selected chart is valid at the eventual good
hit, where its value is w/(1+c*w); the old recovery can undo this change.

The key arithmetic is that

    E(X)=v(X)*u(q^-1*X)-u(X)*v(q^-1*X)

cannot be the zero polynomial at the good field. Otherwise u/v is
q-invariant of degree below ord(q), hence constant. Its value at zero is
the complete unit-tag average n/2, whereas its value at the hit is a
unit residue modulo n. These cannot agree. Thus deg E<=2J-2 bounds
changes of direction in the normalized two-coordinate prefix. If every
adjacent determinant vanished, counting nonzero internal states and
zero-zero edges would give 5J<=5J-4, a contradiction.

Norm and coordinate gcd tests turn this existence proof into the stated
deterministic algorithm. A nonunit original leaf in the prefix has a
positive, O(log N)-bit scalar annihilator label; the existing extractor
is paid at most once on a terminating branch. Additive state zeros are
not sent to that extractor. The complete proof and cost are in
[initial-chart.md](initial-chart.md), independently checked in
[review-initial-chart.md](review-initial-chart.md).

Eliminating P gives an exact second-order nonlinear ratio relation. The
starting data are now paid; future chart and stepping pivots, and fast
advancement over the remaining interval, are still open. See
[projective-closure.md](projective-closure.md). This result corrects the
earlier assessment that the missing initial ratio was itself an unpaid
obstacle; it does not make nonlinear recurrence advancement automatic.

## 3. Pure modulus, paired twists and one arithmetic progression

Auditing the actual scalar and torus suppliers shows that conductor
divisibility was needed for the old character-coloured rows, not for
these two explicit monic families. One can choose K=2*3^e~N^(1/6),
discover D independently, retain the actual |D|<=K/2 guard and old
finite-exception convention, and rerun the entire preparation in soft K.
All changed-base order screens are executed; no old certificate is reused.
See [pure-modulus-preparation.md](pure-modulus-preparation.md).

For this K the unit-square image is 1 modulo 6. Consequently the values
a=[N/j²]_K in family A and b=[j²/N]_K in family B each form exactly

    {z: 1<=z<K, z=N mod 6},

with two tags per value. A dividing 3-power n near K^(1/3) is also
available for the restricted-HH consumer. Neither structure supplies the
unknown factor residue on its own.

The pairing j*=N/j maps family A to family B with exactly the same
stationary phase. Its roots differ by the explicit twist
barpi^((a-1)(N-1)). Pairing opposite tags gives quadratic factors
P_A=1-c_A*T*z+c_A²*z² and P_B=1-c_B*T*z+c_B²*z², with

    c_B*P_A-c_A*P_B=(c_B-c_A)*(1-c_A*c_B*z²).

The twist gate and exceptional a=1 rows are paid in soft K. The
remaining correction reindexes as a two-geometric-progression family
using the public step-6 coefficient list. Its starts are acquired,
but its current long readout still costs soft K^(3/2), and it has no
proved coverage promise as a replacement. Predicate-equivalent removal
of a unit factor does not silently preserve first-jet amplitudes. The
full identities and recovery checks are in [paired-monic.md](paired-monic.md).

## 4. What the other domain tests actually establish

New modular-composition and nearlinear power-series algorithms were
checked against their primary theorem statements. They accept supplied
polynomials; they do not initialize this implicit long q-product. The
first J+1 q-product coefficients are cheap, but the exact omitted tail is
a terminating basic-hypergeometric polynomial times a unit modulo the
row polynomial. Degree truncation supplies no reason that tail vanishes.
This gives a precise finite hypergeometric/rational-sequence contraction
target, not a fast evaluation of it. See [modular-algorithm.md](modular-algorithm.md).

The joint global rational telescoping certificate forces the complete
tag average n/2, rather than the tag selected by the finite interval.
That rules out this particular endpoint cancellation. The same average
calculation is constructive in the initialization proof above. A
conjugate-cross Wronskian has an exact six-coordinate closure, but at the
good hit its entire state vanishes and it loses the tag. Neither finding
is a general lower bound for compressed coefficient extraction.

The next substantive target is fast interval-sensitive advancement from
the now acquired projective starts, or a contraction exploiting the
paired arithmetic progression while retaining its correction. Another
formal closure without the long evaluation would not close the gap.

## Review and preservation

Three Sol 6.1 investigations and independent reviews are retained:
[projective/Wronskian review](review-projective.md),
[preparation/pairing review](review-pure-pairing.md), and
[initialization review](review-initial-chart.md). These are paper proofs,
not Lean certificates. The primary agent checked the stronger prefix
argument and the exact hypergeometric-tail scope.

Source pins and validation are in [sources.json](sources.json),
[review.json](review.json) and [manifest.json](manifest.json).
All 949 prior protected files, two document prefixes and 23 concurrent
files are preserved. No numerical campaign, factoring implementation,
Lean/public assets, commit or push is part of this packet.
