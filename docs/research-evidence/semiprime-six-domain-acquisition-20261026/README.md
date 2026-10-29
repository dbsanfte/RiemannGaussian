# Single symmetric residue and six acquisition routes

26 October 2026. Research result note from the side-conversation investigation.

**One symmetric additive pole coefficient suffices for the original weighted
row family, with recovery inside soft O(K).** The sharper hit-count bound is
`d <= 3^floor(e/2)`, and a fixed linear combination of the count and squared-tag
coefficients encodes both quantities. Six investigations identify different
barriers to obtaining that coefficient cheaply. None supplies a whole-family
soft-O(K) acquisition algorithm; the retained weighted query costs soft
O(K^(5/4)), with K of order N^(1/6).

These are paper derivations under the cited preparation and recovery contracts,
not compiled Lean theorems or a completed bit-complexity theorem for sixth-rate
factoring. The negative results apply to the constructions specified below.
They do not exhaust the six mathematical domains or establish a general
acquisition lower bound.

## 1 Prepared family and inherited contracts

Use the [original pure weighted bank](../semiprime-fused-readout-20261026/pure-weighted-common-tag.md)
and its [symmetric squared-tag consumer](../semiprime-primitive-pair-20261026/primitive-asymmetry.md).
The prepared hard branch has

    K = 2*3^e, e >= 3, H = K^2,
    N = P*Q <= K^6, P < Q, P,Q > 16H,
    J = phi(K) = K/3.

There is exactly one acquired Gauss row per unit colour j modulo K. The native
quadratic algebra is B = (Z/NZ)[tau]/(tau^2-Delta). At the nonsplit prime R,
either P or Q, its reduction is a field. The prepared units satisfy

    q = pi^H, rho = q^-1,
    ord_R(q) = ord_R(pi) > 256H^2.

The global differences 1-q^s are certified units for 1 <= s <= 16H. In each
public factor-size bin the acquired normalized roots are T_j, with leaves

    a_jt = 1-T_j*rho^t, 0 <= t < h,
    h = O(K^(3/2)) < 16H.

Each row has at most one hit at the good field. In a correct bin every hit has
exact integer provenance, and all hit colours satisfy

    j = R mod n, n = 3^ceil(e/2).

Coverage guarantees at least one such hit. This includes axes and nonprimitive
rows. Wrong bins need not have this tag property and remain separate attempts.

For canonical integer weights w_j, write

    Res(w) = [delta^-1] sum_(j,t) w_j/(delta+a_jt).

This is a componentwise Laurent coefficient. A zero leaf contributes w_j; a
nonzero leaf contributes zero. The notation does not provide an algorithm for
inverting a series with a nonunit constant term over B.

In particular, for u_j = [j^2]_n in {0,...,n-1}, the inherited target is

    V = Res(1), U2 = Res(u),
    (V,U2) mod R = (d,d*u), u = [R^2]_n.

Public Hensel lifting of a correct u gives exactly two unit roots modulo n.
The existing guarded restricted-HH consumer handles these and their
complementary factor residues in soft O(K). No square-root oracle modulo an
unknown prime is involved. All soft bounds here suppress polynomial factors
in log N; native ring elements and the scalar integers below have O(log N)
bits.

## 2 Sharper multiplicity and a single symmetric coefficient

### Paper proposition 1 The good hit count is at most D0

Put

    D0 = 3^floor(e/2), so n*D0 = K/2.

Then every correct bin of the original bank satisfies 1 <= d <= D0.

**Proof.** Fix the unit residue r = [R]_n. Among residues modulo K there are
K/n = 2D0 lifts of r. Since n is odd, exactly D0 lifts are odd; all lifts are
nonzero modulo 3. Thus exactly D0 are units modulo K. Every good hit has one
of these colours, each colour has one row, and each row has at most one hit.
Coverage supplies the lower bound. This counts multiplicity even if different
rows have the same root. QED.

The one-row-per-colour hypothesis is essential. The bound is not automatically
valid for a completed catalogue containing several rows of one colour.

### Paper proposition 2 One packed residue determines the count and square tag

Let L = K/2 = n*D0 and give each row the public weight

    w_j = L + u_j, u_j = [j^2]_n.

These weights are invariant under j -> -j and cost soft O(J) to construct.
The single acquisition target is

    C = Res(w) = L*V + U2.

At the good field it is the reduction of the positive integer

    c = d*L + d*u, 1 <= d <= D0, 0 < u < n.

Since d*u <= D0*(n-1) < L, the ordinary integer decoder is

    d = floor(c/L),
    u = (c-d*L)/d.

The size bound is

    0 < c < M := (D0+1)*L = O(K^(3/2)) < P,Q.

Thus the encoding is injective on the permitted count-tag pairs and has no
wraparound at the good prime. This proves the integer statement. Obtaining
that integer from an acquired algebra element requires the following step.

### Paper proposition 3 Modular recovery fits the target budget

Given an actual C in B satisfying the correct-bin promise above, a factor or
the integer c can be recovered in soft O(K^(3/4)) bit operations. The subsequent
tag recovery and inherited HH consumer cost soft O(K).

**Proof.** Write C = c0+c1*tau, using canonical coordinates modulo N. At the
nonsplit field C is the scalar c, so R divides c1. Compute gcd(c1,N). A proper
gcd factors N; on continuation the gcd is N and C is globally scalar. A gcd
of one rejects a wrong-bin attempt and cannot occur in the correct bin.

If 0 <= c0 < M, then c0 = c as integers: they are congruent modulo R and both
lie in an interval shorter than R. Otherwise search for a factor in the
integer differences c0-a for 0 <= a < M by a blocked polynomial product.
Set b = ceil(sqrt(M)) and construct

    F(X) = product_(v=0)^(b-1) (X-v) mod N.

Evaluate F at c0-b*s for s = 0,...,b-1. These are the products over b
consecutive blocks covering 0 <= a < b^2. Product trees and monic multipoint
evaluation cost soft O(b) ring operations and require no division by a
possibly nonunit difference. The padded interval is harmless: b^2 <= 4M <
16H < P,Q on the native e >= 3 range.

At least one block product has nontrivial gcd with N, because a = c occurs
in the range. A proper block gcd finishes. If a block gcd is N, inspect its
at most b individual differences. One gives a proper factor, or one has gcd
N. In the latter case c0 = a as canonical integers since 0 <= a < b^2 < N;
moreover a = c because both a and c are below R and congruent modulo R.
The search therefore returns a factor or the actual c, not merely a residue
modulo an unidentified prime.

There are O(b) gcd computations, including the inspection of one flagged
block. Since b = O(K^(3/4)) and all residues have O(log N) bits, the total
cost is soft O(K^(3/4)). This is the standard Strassen product/evaluation
mechanism; see the introduction and Section 2 of
[Bostan–Gaudry–Schost](https://mathexp.eu/bostan/publications/BoGaSc07.pdf).

Decode d and u by Proposition 2. Check the count range, divisibility and unit
square condition before invoking the existing two-root/HH consumer. Wrong-bin
attempts may produce invalid candidates or fail recovery; every reported
factor is checked, and failure continues to the next bin. The correct bin
cannot be lost. O(log N) separate bins preserve soft O(K) recovery. QED.

This proves a smaller sufficient output interface. It does not acquire C.
In particular, interpreting C as the valuation of a product with exponents
w_j is not a free algorithm for computing it.

## 3 Algebraic geometry and local residues

Global residues and quotient-algebra traces can eliminate an explicit sum
over solutions once a suitable denominator, quotient representation or normal
form is supplied. Relevant primary sources are
[Cattani–Dickenstein–Sturmfels, Computing Multidimensional Residues](https://arxiv.org/abs/alg-geom/9404011)
and [Arreche–Sitaula on discrete residues](https://arxiv.org/abs/2503.15636).
Their algorithms are not native composite-ring collision-selector oracles.

For the actual resolvent

    S(delta) = sum_(j,t) w_j/(delta+a_jt),

the sum of residues at ALL finite poles is h*sum_j w_j. This is already
known and independent of which leaves vanish. The information resides in
the selected pole at delta = 0, not in the global sum.

An alternative is common-root projection using

    F(X) = product_j (X-T_j),
    G_h(X) = product_(t<h) (1-rho^t*X).

The natural quotient/gcd construction needs access to G_h inside the row
quotient, for example G_h mod F. This is an unacquired long-clock operation.
Repeated row roots also matter: the degree of an ordinary gcd does not
automatically count original-row multiplicities. A multiplicity-aware
construction or the direct product of row evaluation algebras must preserve
them.

The discrete-residue alternative likewise does not supply a missing oracle.
The cited 2025 treatment concerns rational summability with a supplied
denominator and uses shift-dispersion information. Importing it here would
require a native finite multiplicative-orbit algorithm and its cost proof.

**Stopping point.** Global cancellation is explicit; the required local
projector and its acquisition cost are not. This is a gap in these proposed
algorithms, not an impossibility theorem for algebraic geometry.

## 4 Coding theory and sparse interpolation

Prony-type reconstruction recovers a sparse object from supplied measurements;
see [Peter–Plonka](https://na.math.uni-goettingen.de/pdf/Operator_Prony_revised2.pdf)
and [Kaltofen–Pernet](https://arxiv.org/abs/1403.3594). The selected hit measure
has one tag, but its defining measurements are already collision-filtered.

The unfiltered moments have a simpler public description:

    A_s(w) = sum_(j,t) w_j*(T_j*rho^t)^s
           = (sum_j w_j*T_j^s)*(1-rho^(s*h))/(1-rho^s),

for positive s with a certified denominator; A_0(w) = h*sum_j w_j. The short
q-difference screen supplies the denominators in the relevant initial range.
This formula does not make the underlying measure sparse.

### Paper proposition 4 The raw moment recurrence has at least h modes

Work at the good field and take w_j = 1. Let Omega be the set of distinct
values T_j*rho^t. A row contributes h distinct nonzero values, so
|Omega| >= h. For v in Omega its multiplicity m_v is at most J because each
row contributes at most once. Hence 1 <= m_v <= J < R, with no vanishing
multiplicity in the good characteristic. Consequently

    sum_(s>=0) A_s*z^s = sum_(v in Omega) m_v/(1-v*z)

has exactly |Omega| uncancelled simple poles. Any homogeneous
constant-coefficient recurrence for this infinite sequence has order at
least |Omega|, by its reduced rational denominator, or equivalently by
Vandermonde independence. QED.

The same conclusion holds for the packed positive weights of Section 2.
Here n <= K/6, w_j < L+n <= 2K/3, and the amplitude of any raw mode is a
positive integer at most J*max(w_j) < 2K^2/9 < R. Packing therefore does not
produce cancellations that make the raw Prony problem sparse.

A pointwise polynomial selector also needs degree at least h-1 to vanish
at the nonhit nodes of a colliding row while remaining nonzero at its hit.
This is only a degree bound for that selector form. It is not a lower bound
for nonlinear or aggregate readout algorithms.

**Stopping point and alternative.** Raw sparse interpolation retains at
least h modes. Changing the encoding after selection does work: Section 2
reduces two sufficient coefficients to one, but leaves selection unpaid.

## 5 Lattice counting and short generating functions

The original row data already give the compact Laurent generating function

    Phi(X,Y,Z) = sum_j w_j*X^a_j*Y^b_j*Z^ell_j
                * sum_(i=-M0)^M0 Z^(-H*i).

The clock factor is a geometric sum. The exact good-bin relation is

    a_j*R+b_j*S+ell_j-H*i = 0, S = N/R.

Thus the desired weighted hit count is formally

    [z^0] Phi(z^R,z^S,z).

The projection direction (R,S,1) contains the unknown factors.
[Barvinok–Woods](https://arxiv.org/abs/math/0211146) provide algorithms for
specified lattice constraints and linear maps in the relevant fixed-dimension
setting. Treating R and S as additional variables introduces RS = N, a
nonlinear constraint to which that polyhedral theorem does not apply.
Equality of formal exponent vectors also cannot be replaced silently by
equality after specializing into a finite field.

The hyperbola-hull alternative offers a different interface.
[Alcántara–Blanco–Criado–Santos](https://arxiv.org/abs/2501.19193) give fast
successor operations, but the complete integer hull has at least order
N^(1/3) vertices. At K of order N^(1/6), full materialization exceeds the
target budget. This does not bound a selective algorithm that avoids most
vertices. Adjacent-hull divisor selection has also been considered in the
repository's existing [investigation journal](../../semiprime-factorisation-investigation.md);
it is not a newly discovered representation here.

**Stopping point.** The first construction needs an unknown linear
projection; the second needs a cheaper selective search than complete hull
traversal. Neither supplies that operation.

## 6 Tensor networks and matchgates

For one row consider the binary-clock tensor

    f_A(b) = 1/(A-T*rho^index(b)), A = 1+delta.

Take a prefix of length h0 = 2^ell <= h < 2*h0. Work over the good field
with A an indeterminate. Splitting the ell bits into two balanced groups
gives index(b) = u+v and a flattening

    M_uv = 1/(A-r_u*s_v), r_u = T*rho^u, s_v = rho^v.

### Paper proposition 5 The balanced flattening has full possible rank

The r_u are distinct, as are the s_v, by the prepared order bound. Write
M_uv = r_u^-1/(A/r_u-s_v). The Cauchy determinant of any maximal square
submatrix is nonzero: its row and column Vandermonde factors are nonzero,
and its denominators are nonzero rational functions of A. Hence the rank
is 2^floor(ell/2) = Theta(sqrt(h)). QED.

This rules out a constant or polylogarithmic bond dimension for an exact
tensor-train representation of this full resolvent across the balanced cut.
Local invertible basis changes preserve that rank. It does not establish a
lower bound on residue extraction, and high flattening rank alone does not
exclude a matchgate or Pfaffian representation.

### Paper proposition 6 A fixed basis cannot give parity throughout the family

For distinct indices k the rational functions 1/(A-T*rho^k) are linearly
independent over the good coefficient field: taking the residue at any one
of their distinct poles kills every term except its own coefficient.
Every row of an invertible A-independent basis transformation therefore
produces a nonzero rational function. No such transformation can make half
the coordinates vanish identically, as required for an even or odd
matchgate signature. This applies even to an arbitrary fixed invertible
transformation, and therefore to a fixed product basis change. QED.

The necessary parity and matchgate identities are described in
[Cai–Gorenstein](https://theoryofcomputing.org/articles/v010a007/).
Further context is [Landsberg–Morton–Norine](https://arxiv.org/abs/0904.0471)
and [Bravyi](https://arxiv.org/abs/0801.2989). An A-dependent transformation,
a different encoding, or a tensor representing only the selected residue is
not excluded by Proposition 6.

**Stopping point.** Small-bond compression of the full resolvent and a fixed
matchgate basis fail for separate reasons. Exploiting Cauchy structure by the
existing block evaluator still costs soft O(b+Jh/b+J), minimized at the
retained soft O(J+sqrt(Jh)) bound. This is a cost of that algorithm, not a
lower bound for every use of Cauchy structure.

## 7 Constant and variable coefficient recurrences

Fast constant-coefficient recurrence algorithms, including
[Bostan–Mori](https://arxiv.org/abs/2008.08822), require a supplied recurrence
and initial data. The native row product instead has a variable coefficient:

    F_0 = 1,
    F_(n+1) = (1-T*rho^n)*F_n.

### Paper proposition 7 A nonhit prefix has no short constant recurrence

For a nonhit row at the good field, all F_n through n = h are nonzero.
Suppose a homogeneous constant-coefficient relation of order d satisfies

    sum_(k=0)^d c_k*F_(n+k) = 0

for all 0 <= n <= h-d, with 2d <= h. Divide by F_n and use n = 0,...,d.
Then the polynomial

    Q(X) = sum_(k=0)^d c_k*product_(t=0)^(k-1)(1-T*rho^t*X)

has the d+1 distinct roots rho^0,...,rho^d but degree at most d. Thus Q is
zero. The product polynomials have distinct degrees 0,...,d and nonzero
leading coefficients, so all c_k are zero. QED.

Every nontrivial recurrence of this specified kind therefore has d > h/2.
The statement concerns a recurrence valid on the whole finite prefix, not
one that starts after most of the data have already been acquired. Nonhit
rows exist in the good bank since d_hit <= D0 < J.

This excludes compiling these row products directly into small homogeneous
constant-coefficient recurrences. It does not exclude a new aggregate
recurrence or an improved algorithm with variable coefficients.
[Bostan–Yurkevich](https://arxiv.org/abs/2012.08656) supply square-root-index
algorithms for q-holonomic sequences; that result alone does not give the
required whole-family bound.

Divide-and-conquer identities such as

    G_(2s)(T) = G_s(T)*G_s(T*rho^s)

generate shifted evaluation alphabets. Their direct batched use returns to
the existing block cost unless an additional closure identity is supplied.
The full-period identity giving 1-T^h for an h-th-root-of-unity clock does
not apply: the actual order of rho is much larger than h.

**Stopping point.** The variable clock coefficient cannot simply be
removed by a short constant recurrence. A faster joint q-recurrence remains
an open algorithmic possibility.

## 8 Localization and the long denominator

The localization principle in
[Atiyah–Bott](https://www.math.stonybrook.edu/~mmovshev/MAT570Spring2008/BOOKS/atiyahbott_moment.pdf)
motivates a finite algebraic calculation that requires no geometric
specialization. Put

    lambda_i = rho^i,
    C_h(X) = product_(i<h)(X-lambda_i),
    P_h(A,T) = product_(i<h)(A-T*lambda_i).

The differences between distinct lambda_i are certified units. Lagrange
partial fractions give the exact identity

    sum_(i<h) 1/(C_h'(lambda_i)*(A-T*lambda_i))
      = T^(h-1)/P_h(A,T).

Indeed, start with 1/C_h(X) = sum_i 1/(C_h'(lambda_i)*(X-lambda_i)),
substitute X = A/T, and multiply by T^-1. The collapsed right side retains
the original long product. Removing the special weights gives instead

    sum_(i<h) 1/(A-T*lambda_i) = (partial_A P_h)/P_h.

At A = 1+delta a hitting row in the first identity contributes
1/C_h'(lambda_I), depending on its unknown hit position I. These individual
weights are nonzero, but their sum over several hit rows does not inherit
the positive integer count guarantee. Multiplying all good contributions
by a common tag or by the packed weight does not itself prevent cancellation.

**Relation to concurrent progress.** The repository's
[symmetric singleton-block construction](../semiprime-even-acquisition-20261026/README.md)
already removes this particular amplitude problem within blocks: it
partitions the original bank into O(sqrt K) symmetric blocks with at most
one good hit each and gives finite Lambert residue pairs. That is a
constructive alternative to demanding a noncancelling whole-bin weighted
sum. The cited packet still leaves simultaneous acquisition of those block
residues open. The whole-bin observation above must not be read as a
refutation of that block construction.

**Stopping point.** The finite localization identity retains P_h, and
plain aggregation changes the certified amplitudes. Singleton blocks repair
the latter issue, but no soft-O(K) supplier for their residues or the packed
whole-bin residue follows from this identity.

## 9 What can be combined and what remains open

| Route | Specific barrier | Scope of the conclusion |
| --- | --- | --- |
| Global residues and quotient traces | Selecting the local collision contribution requires additional acquired data | The tested global sum and quotient construction do not provide that data |
| Sparse interpolation | The raw moment sequence has at least h uncancelled modes | Applies to the raw measurements, not to all possible measurements |
| Lattice generating functions | The desired linear projection contains R and N/R | The cited polyhedral algorithms do not accept the unknown projection for free |
| Tensor networks and matchgates | Full Cauchy rank and failure of fixed-basis parity | Applies to the full resolvent representation and the specified basis class |
| Fast recurrences | A nonhit product prefix needs constant recurrence order greater than h/2 | Does not exclude variable-coefficient or joint algorithms |
| Localization | The long denominator survives; whole-bin amplitudes need control | Singleton blocks repair amplitude control but still require acquisition |

These are different structural barriers. A residue-only algorithm need not
construct the full moment sequence, tensor or long polynomial used in the
obstruction calculations. Conversely, a correct decoding theorem does not
make any of those structures cheap to acquire.

The explicit constructive combination is the common-tag theorem, the sharper
multiplicity bound, the packed symmetric coefficient and blocked modular
integer recovery. It asks for one output per bin:

    C_bin = [delta^-1] sum_(j,t)
            (K/2 + [j^2]_(3^ceil(e/2))) / (delta+1-T_j*rho^t).

An algorithm acquiring these actual coefficients from the original public
row data in total soft O(K), with valid composite-ring operations or verified
factor exits, would meet the missing acquisition target for this interface.
Every modified row catalogue must retain coverage, tag provenance and its
own multiplicity bound. No such acquisition algorithm, general lower bound,
or complete sixth-rate factoring theorem is established here.
