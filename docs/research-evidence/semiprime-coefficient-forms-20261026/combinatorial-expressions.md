# One-defect hybrid coefficients: cycle trees, a one-hot solve, and paid moments

26 October 2026. Primary combinatorial reading plus explicit finite
specialization to `hybrid-handoff.md` Sections1-4. No numerics, tests,
factoring code, Lean or repository edits.

**Positive initialized information:** the actual rank-two row/clock
weights supply O(J) ORDINARY Krylov moments and tag-weighted moments in
soft J, in addition to the older q-binomial moment alphabet. There is
also an exact amplitude-free one-hot linear solve for the desired tag.
The cycle-tree series reduction and low-rank solve have been executed
below. Their immediate scalar/readout implementations retain the old
geometric-product cost; the new moments have not yet initialized the
required one-hot solve. This is a concrete possible hybrid input, not
another claimed faster determinant or sampler.

## 1. Exact one-defect input

Use either good monic family of the reviewed uniform handoff. There
are J<=K acquired unit row roots y_j, tags w_j=[j]_n, and clocks
x_i=q^i, 0<=i<h=2H+1. The actual leaf is

    a_(j,i)=1-y_j/x_i.

At the unknown nonsplit field R exactly ONE leaf is zero. Let the
flattened edge index e=(j,i), tag w_e=w_j, D=J*h. Define

    P=product_e a_e,
    V=sum_e product_(f!=e) a_f,
    U=sum_e w_e*product_(f!=e) a_f.                  (1)

These are exactly the two coefficients requested in the handoff:
`V=[delta]product(a_e+delta)` and
`U=-[delta Y]product(a_e+delta(1-Yw_e))`.
At the good field P=0, V!=0 and U/V=w_hit. No promise of a unique
hit at the other prime is used. Every proposed probabilistic or matrix
interpretation below must preserve this one-prime projective contract.

## 2. Exact spanning-tree interpretation and series reduction

Make a cycle with D edges, conductance a_e on edge e. Its spanning
trees are obtained by omitting exactly one edge. Therefore its tree
polynomial is V, and U is its tree polynomial weighted by the tag of
the OMITTED edge. This directly proves the identity over any ring;
Kirchhoff's cofactor theorem supplies a Laplacian realization without
dividing by the number of vertices. At the unique zero the cycle is a
weighted path and its only nonzero spanning tree omits that zero edge.
Thus the normalized omitted-edge observable is exactly the wanted tag,
not a different positive-probability approximation.

Primary context: Chebotarev--Agaev, *Forest matrices around the
Laplacian matrix*, LAA356(2002),253-274,
[primary text](https://arxiv.org/html/math/0508178), Sections3-4 and
adjugate expansion in the introduction. Kenyon,
*Spanning forests and the vector bundle Laplacian*, Ann.Probab.39(2011),
[primary text](https://arxiv.org/html/1001.4028), Sections4-5,7,
provides the bundle/CRSF and determinantal-process versions. Their
probability/positivity language is not imported into Z/N; only the
finite polynomial identities or a separately certified inverse apply.

Execute the plausible series/Kron contraction by grouping h consecutive
edges of each row. Put

    P_j=product_i a_(j,i),
    V_j=sum_i product_(r!=i) a_(j,r).

A series reduction would use effective edge P_j/V_j and multiply the
remaining tree polynomial by product_j V_j. The EXACT cleared result is

    V=sum_j V_j*product_(l!=j)P_l,
    U=sum_j w_j*V_j*product_(l!=j)P_l.             (2)

At the hit row P_j=0,V_j!=0, but V_l for other rows need NOT be units:
it is an additive sum even when every original a_(l,i) is a unit.
Hence a graph reduction may not invert all V_l or apply a stochastic
normalization without certified pivots. Keeping the pair (P_j,V_j)
cleared is always legal.

With Q_h(Y)=product_(i<h)(1-Yq^(-i)), direct differentiation gives

    P_j=Q_h(y_j), V_j=h*Q_h(y_j)-y_j*Q'_h(y_j).    (3)

Thus the exact row series reduction has a very concrete initialized
input requirement: the long off-grid Pochhammer AND its derivative.
The old constant-first-jet monic engine computes them jointly at
soft(J+sqrt(Jh)); it does not initialize them from short graph endpoints.
The cycle model has therefore not yet supplied a cheaper readout.

## 3. The strongest amplitude-free regularization: a one-hot solve

Let D_a be the D-by-D diagonal matrix of a_e and define

    M=D_a+1*1^t.

The finite determinant-lemma identity is

    det M=P+V.                                    (4)

At the good unique-hit field, M is invertible because V!=0. More
strongly, the solution Mz=1 is EXACTLY the one-hot vector at the hit:
the zero-edge row forces sum_e z_e=1; every other row then gives
z_e=0; the remaining coordinate is one. Consequently

    w^t M^(-1)1=w_hit.                            (5)

This avoids the unknown common amplitude V in the OUTPUT. Its
factor-or-unit global matrix gate still has to be acquired; a good-
field unit determinant alone does not perform an inverse. An arbitrary
additive singular auxiliary matrix gets no beta-annihilator decoder.

The row/clock structure makes the operator particularly explicit.
Reshape z to a J-by-h matrix Z, let T=diag(q^(-i)), Y=diag(y_j),
and s=sum_(j,i)Z_ji. Then Mz=1 is exactly

    Z-Y*Z*T=(1-s)*1*1^t, s=sum Z_ji.              (6)

It is a rank-one-forced diagonal Stein/Sylvester equation plus its
normalization. At the unique hit the solution is rank one. This is
not the generic dense inverse problem, and (6) is a precise new
structured projective-readout target.

The immediate fast-Sylvester formula divides entrywise by
1-y_j q^(-i), including the desired zero. A polynomially cleared solve
or bordered regularization must instead retain the nullspace and
normalization. The older small Cauchy/Bezout solve had the analogous
unacquired clock remainder. No initialized solution algorithm for (6)
in soft(J+sqrt h) is supplied by citing low displacement rank.

## 4. Genuinely cheap ordinary Krylov moments from the two alphabets

Here is additional concrete data that the operator formulation supplies
at target cost. Fix L=2J and for ell up to L define

    c_ell=1^t D_a^ell 1=sum_(j,i)(1-y_j q^(-i))^ell,
    d_ell=w^t D_a^ell 1.

Let p_t=sum_j y_j^t, p_t^w=sum_j w_j y_j^t, and
s_t=sum_(i<h)q^(-it). Then the exact finite binomial formula is

    c_ell=sum_(t=0)^ell (-1)^t binom(ell,t)*p_t*s_t,
    d_ell=sum_(t=0)^ell (-1)^t binom(ell,t)*p_t^w*s_t. (7)

All of this alphabet can be ACQUIRED, not just described:

- p_t for t<=L comes from the acquired monic F(X)=product_j(X-y_j)
  by its reversed logarithmic derivative/formal series division in
  soft(J+L).
- Acquire G_w(X)=sum_j w_j product_(l!=j)(X-y_l) by the weighted
  product tree in soft J. Expanding G_w/F at infinity supplies
  p_t^w, t<=L, in soft(J+L), even if off-clock root multiplicities
  have not been separated. No Lagrange denominator is inverted.
- s_0=h and for t>=1,
  `s_t=(1-q^(-th))/(1-q^(-t))`. Only the DENOMINATOR uses a short
  guarded exponent t<=L; the long numerator is multiplied, never
  presumed a unit. Powers of the acquired q^(-h) initialize all
  numerators in soft L.
- The binomial transform (7) is one factorial convolution per
  sequence: convolve `(-1)^t p_t s_t/t!` with `1/t!`, then multiply
  coefficient ell by ell!. Integers through L are units because
  L=O(J)=O(K)<P,Q; include the finite-size guard if the chosen
  constant makes L>=P. Acquired factorial/inverse-factorial arrays
  cost soft L. With L=2J<=2K, both the factorial and q-exponent guards
  follow directly from the prepared >16H bounds. Thus both length-O(J)
  moment lists cost soft J.

For the regularized operator M, the formal generating series are
also initialized at this precision. Put

    C(z)=sum_ell c_ell z^ell=1^t(I-zD_a)^(-1)1,
    E(z)=sum_ell d_ell z^ell=w^t(I-zD_a)^(-1)1.

The formal rank-one resolvent identity gives

    1^t(I-zM)^(-1)1=C(z)/(1-zC(z)),
    w^t(I-zM)^(-1)1=E(z)/(1-zC(z)).                (8)

The denominator has constant term1, so its truncated inverse is lawful
without a collision test. This also supplies short ordinary Krylov
moments of M at soft J, not merely those of D_a.

What is NOT acquired is evaluation at the inverse/zero-eigenvalue
boundary needed in (5). The zero diagonal eigenvalue contributes the
constant term1 to C(z) as z tends formally to infinity, and contributes
w_hit to E(z); the other eigenvalues give vanishing terms there. The
small-z series (7)-(8) has not determined that infinity readout. A
short Hankel determinant of these moments is a subset/moment statistic,
not automatically the unique-zero projector. Even one fixed native
row has h distinct diagonal values under the clock guard, so treating
the diagonal sequence as a supplied J-state system is unjustified.
More precisely, for each full-grid diagonal eigenvalue a its trace
weight is its integer multiplicity, at most J: within a fixed row the
h values are distinct. Thus every nonzero multiplicity is between1
and J<R, so it is nonzero in the good field. There are at least h
distinct eigenvalues from any one row. Vandermonde diagonalization
therefore gives full moment/Hankel rank equal to the number of
DISTINCT full-grid eigenvalues, at least h. The exact scalar trace
sequence from index0 has minimal recurrence order at least h; the
zero eigenvalue has weight1 and is included in that statement. If an
eventual-recurrence convention discards the initial pulse from the
zero eigenvalue, the bound is at least h-1, still long. No trace-
cancellation loophole licenses an exact O(J)-order Krylov closure.
This is a check of this particular diagonal/short-Prony mechanism,
not a lower bound against an algorithm using the additional known
F and q.

This ordinary moment alphabet is distinct from the earlier acquired
q-binomial S_m moments in the joint knot packet. Both may be inputs to
a new core algorithm; neither is counted as already solving (6).

## 5. Exact clock-block reset and rational resolvent expressions

Grouping all J factors at one clock point x=q^i gives, up to its
known common unit x^(-J), the actual first-jet block

    [[F(x),0,0],
     [xF'(x),F(x),0],
     [xG_w(x),0,F(x)]].                            (9)

Applied to start (1,0,0), its three coordinates are P,V,U up to the
same acquired monomial unit after all clocks. Every coefficient of
F,F',G_w is supplied in soft J. This is a direct initialized map
from the new row-marker to the old three-state reset machinery,
without a hidden tag-interpolation assumption. Its degree is J;
old blocking therefore costs soft(J+sqrt(Jh)), unchanged.

On the generic unit branch the same projective output is

    U/V = [sum_i x_i G_w(x_i)/F(x_i)]
                  /[sum_i x_i F'(x_i)/F(x_i)].     (10)

At the desired hit those sums have poles; (1) or (9), not numerical
inversion of F(x_i), defines their lawful collision limit. Thus (10)
is a useful Cauchy/linear-response interpretation but is not by itself
an initialized finite-ring ratio algorithm.

There is a native-specific obstruction to the PARTICULAR proposal of
turning its denominator sum into one rational endpoint coboundary.
Over the good field, set f(X)=X F'(X)/F(X). Suppose a rational R(X)
satisfied f(X)=R(qX)-R(X). For the differential f(X)dX/X, its residue
at a root of F is that root's multiplicity. Summing these normalized
residues around any finite q-orbit must give zero for a coboundary,
because q-shift only permutes the orbit. But an orbit meeting F has
between1 and J roots counted with multiplicity, and J<R is below
the field characteristic. Its residue sum is NONZERO. Therefore no
such rational antiderivative exists for this actual f, even with the
native finite-order q. This uses actual unit roots and their positive
integer multiplicities, not a generic formal-q model.

It excludes ONLY that exact rational endpoint telescoping route.
It does not rule out the projective ratio by another identity, higher
operators, a singular solve using (7), or a new finite combinatorial
contraction. Finite sums remain rational if their full denominators
are acquired; that full acquisition is the step not made cheap here.

## 6. Why standard DPP/forest normalization does not finish the handoff

The cycle spanning-tree law and Kenyon/Chebotarev forest projectors
are legitimate ways to identify the desired observable. A DPP/Green
kernel requires its actual inverse/minor normalization, not only the
fact that an unknown-field normalized measure is concentrated at the
one missing edge. Positivity/probabilistic sampling guarantees do not
apply to R or the quadratic algebra. The cleared identities remain
valid, but their kernels must still be initialized singular-safely.

Likewise replacing the cycle by a complete bipartite graph merely
because the array a_ji has rank at most two changes its spanning-tree
sector: a tree there has J+h-1 edges, whereas the cycle tree has Jh-1.
No matching factor/correction identity is supplied by that graph change.
This rejects the direct rank-two-graph identification, not every planar
network or integrable representation.

## Outcome and concrete next target

The concrete possible new combination is: acquired (7)-(8), explicit
rank-one Stein normalization (6), and the existing HH weak-tag consumer.
It asks for only the scalar w^t M^(-1)1, or a projectively equivalent
pair, with verified factor-or-unit handling. An algorithm using those
ordinary moments to initialize the one-hot solve would be substantive
new acquisition progress. The cycle-tree/Kron implementation and old
reset implementation have been completed and still pay the old cost.
No target-rate projective readout or all-semiprime improvement has been
proved in this pass.
