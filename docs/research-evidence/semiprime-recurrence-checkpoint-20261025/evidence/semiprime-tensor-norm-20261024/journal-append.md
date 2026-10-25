
## Two-grid tensor norm: executed elimination and paid pivot normalization, 2026-10-24

The previous turn was progress through an exact compressed index-mask
constructor. This pass executes the proposed tensor elimination rather
than treating its small initial generators as a fast norm algorithm.
No whole-query exponent improves: the available covered query remains
soft O(m^(3/2)), and the deterministic all-semiprime sixth-rate goal and
full bit/Lean composition remain open.

For A_s(X)=prod_(a<s)(X-q^a), B_t(Y)=prod_(b<t)(Y-q^(s*b)), the desired
prefix is Norm_(R[Y]/B_t) Res_X(A_s,F(XY)). The three short inputs cost
soft(J+s+t); one operation in the rank-t coefficient algebra costs with
t. In the balanced test s=J=n, normalize the second polynomial by the
known unit Y^-n. Its coefficients are single Laurent monomials.
Subtracting the two monic polynomials gives C=A-B. With
c=c_(n-1), d=c_(n-2), h=c*b_(n-1)-d, the actual first fraction-free
Schur update is D=c²B-(cX+h)C. Its degree is at most n-2, and each
coefficient has at most six Laurent monomials. This entire first update
is acquired in soft n, including its shared factors; no n-by-t table
is needed at this step.

A positive uniform normalization follows from the geometric A. Put
Z=Y^-1 and let p_k(Z) be its signed principal subresultant coefficient
at degree n-k. Its formal constant is the Toeplitz minor
Delta_k=det(a_(n-k+i-j)), up to a known convention sign. Dual Jacobi-Trudi
and principal specialization identify
Delta_k=(-1)^k*s_(k^k)(1,q,...,q^(n-1)). Every hook/content factor has
exponent between 1 and 2n-1, so EVERY Delta_k is a certified unit.
All boundaries are acquired in soft n: with
Q_r=prod_(v=1)^r(1-q^v), T_r=prod_(u=0)^(r-1)Q_u,
the square Schur value is
q^(k²(k-1)/2)*T_(n+k)*T_(n-k)*T_k²/(T_n²*T_(2k)).
This uses short prefix products, not separate quadratic hook tables.

The principal minors have a proved public bound deg_Z p_k<=k².
Reversing with this bound gives Y^(k²)*p_k(Y^-1) with UNIT LEADING
coefficient, even when the highest Z coefficient vanishes. Universal
exact-division identities can therefore be implemented by monic-normalized
polynomial division over R[Y] BEFORE reduction modulo B_t. This removes
formal-origin genericity and illegal division at that stage. It does not
license inverse pivots in the endpoint algebra. Expanded formal precision
M costs soft(nM), and Z=Y^-1 is a unit there, so an omitted formal tail
cannot be discarded. Later additive Schur updates still require acquired
mixed coefficients; scalar norms of their summands do not supply them.

The geometric transport was tested separately. Its q-scaling connection
is an acquired Cauchy matrix; its first Schur update closes using only
certified unit differences. Nevertheless d_q=B_t(qY) mod B_t is a UNIT,
and scaling a reduced product loses the actual multiplication quotient
multiplied by d_q. The defect has a free rank-(t-1) image for this operator;
the degree-J weight has a compact rank-at-most-J commutator, not a proved
constant-rank norm algorithm. A guarded first inverse update is acquired
in soft(J+t), using RAW h(qY) for its Bezout quotient before reduction.
Replacing that raw scaling by scaling h mod B_t would lose another carry.
The q^s shift has a genuine single boundary coordinate, but its initial
slice norms are the original unpaid data. Completed coefficient-algebra
elimination/transport costs soft m², worse than existing scalar blocking.

The first linear pivot and second unit-leading quartic pivot also yield
a paid soft-m adaptive proper-factor test via fixed-degree geometric
norms. No coverage theorem is known for those auxiliary pivots. A saturated
pivot norm is not an original beta collision and uses the safe fallback,
not the original factor-sum decoder. Structured-linear-system algorithms
still charge explicit generators, coefficient-ring size and pivot promises;
the sparse resultant mixed degrees are st,sJ,tJ. The resulting quadratic
size bound concerns coefficient-linear determinant formulas only, not
all scalar algorithms.

Exact reports, primary sources and independent reviews are in
`/tmp/semiprime-tensor-norm-20261024`. The Schur/hook formulas are classical;
no absolute novelty claim is made. The constructive result is a fully paid
formal pivot normalization and first elimination, not the missing endpoint
acquisition. The remaining target is scalar contraction of the mixed pivot
data with restrictions and nonunit handling included. No numerical examples
or new backend lemmas were used. Prior prefixes, all 270 frozen entries,
and concurrent RH work are preserved by the continuation validator.
