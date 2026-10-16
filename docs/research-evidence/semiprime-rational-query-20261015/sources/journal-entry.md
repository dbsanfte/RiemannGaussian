## 2026-10-15 — Rational adjoint solvability equals the row zero test

The previous goal turn was progress: complete first-current row-hit
sparsity left m-o(m) unit row products on a retained actual family,
and a finite-Laurent adjoint reduction retained Omega(m) sectors. This
continuation investigates the remaining rational-pole escape and pays
two positive shared computations. Evidence is under
`docs/research-evidence/semiprime-rational-query-20261015`.

**Exact rational certificates are now classified, including poles.**
Over a field K containing gamma of order R with R invertible,
gcd(d,R)=1, q=gamma^d, 0<=L<R, u=gamma^(-U), put

    T(p)=(1-x^d)p(x/gamma)-u(q^L-x^d)p(x), A=U-dL.

For EVERY integer e, the exact rational equation T(p)=x^e has a
solution in K(x) IF AND ONLY IF P_L(u gamma^e;q)=0. This is a rational
solvability theorem, not an acquisition algorithm or a degree heuristic.

The explicit gauge h=x^A prod_(r=0)^(L-1)(1-q^(-r)x^d) gives
T(hy)=C(S-1)y, where S(y)=y(x/gamma) and
C=gamma^(-A)x^A prod_(r=0)^L(1-q^(-r)x^d). The cyclic trace is zero
on every S-1 image; conversely trace zero has the elementary solution
y=(1/R)sum_(t=0)^(R-1)t S^t(g).

Writing Q_L^-=prod_(s=1)^L(1-q^(-s)), the reciprocal of the product
in C has a periodic coefficient expansion. If n_e is the unique
integer in [0,R) with e-A+d n_e=0 mod R, its trace is EXACTLY

    Tr(x^e/C)=(gamma^A R/Q_L^-) P_L(u gamma^e;q)
                * x^(e-A+d n_e)/(1-x^(dR)).

Every factor outside P_L is a nonzero rational function. Thus the
obstruction coefficient is the missing row product itself. R, n_e
and the R-term formula are proof-side data, not a free order oracle,
zero test, or fast long-query evaluator.

The theorem extends to rational functions of independent formal
weights: T(p)=sum_j w_j x^e_j is solvable exactly when EVERY associated
row product vanishes. Numerical weight specializations may cancel,
so that latter iff is not assigned to a single numeric weighted sum.

For the actual hidden fields take d=m^2, U=N+3d, e_j=3d-delta_j.
The targets and original intervals are unchanged. The prior retained
family has m-o(m) unit rows in both fields, so its full formal weighted
source has NO rational endpoint-only certificate in either field,
even with boundary poles and rational dependence on the weights. A
legitimate composite rational certificate with a non-zero-divisor
denominator would reduce to both fields, so is excluded as well.

The rational cokernel is ONE-dimensional over K(x^R), not Omega(m)
independent rational sectors. Its formal-weight trace remainder carries
the unpaid row values. The exact K(x) identity requirement is essential:
pointwise finite-grid interpolation with omitted poles, identities only
modulo x^R-1, parameter-deformation finite parts, other operators and
methods retaining a remainder are outside this theorem. No general
scalar complexity lower bound is claimed.

**Two shared computations have positive nearlinear clocks.**
First, for the ONE common q-binomial coefficient stream c_k of P_L,
any nu supplied public indices in [0,L] can be acquired together in
soft O(sqrt L+nu), with comparable storage, when 1-q^a is a unit for
1<=a<=L. This holds on the qualified actual source. Full-N-dependent
indices and repeated indices are allowed. Degree-sqrt(L) shared blocks
give coarse prefixes, binary tail refinement uses monic multipoint
evaluation of one common short block at each level, and one certified
batch inverse supplies all selected denominator products. Powers,
index bits, polynomial arithmetic and the k=L endpoint are charged.
This is a direct composite-ring specialization of the several-index
q-holonomic method. It does not evaluate changing-target row sums,
find unknown local indices, or provide parameter jets/pole finite parts.

Second, the initial J formal weighted values F_n=sum_j w_jP_n(z_j)
and the inverse prefix transform cost soft O(J): acquire J geometric
moments, form Q_n=(q;q)_n and chirps, and use one q-binomial convolution
F_n/Q_n=(A*B)_n. Parameter inverses are weight-independent certified
units. At a distant n the required weights contain the unpaid P_n(z_j),
so cheap initialization is not a cheap long-horizon jump.

Fresh primary rational-denominator/summation papers, including 2025
discrete residues and 2026 polynomial reduction, were checked with their
characteristic/order/singularity hypotheses retained. The new trace
proof and positive algorithms are self-contained; no characteristic-
zero rational-solver clock is imported into the finite composite ring.
The main rational theorem passed two independent final reviews, and
the positive constructions were independently reviewed.

The general acquisition bound remains soft O(m^(3/2)). A weighted or
scalar evaluator retaining a nonzero remainder, or a different exact
collision-preserving identity, remains to be found at soft O(m), then
composed with the full routing/kernel/controller bit and memory proof
in Lean. No new Lean, examples, broad build, improved factorization
exponent, commit or push is claimed. The all-semiprime sixth-rate goal
remains active and unproved.


