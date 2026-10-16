# Full-input digit folding fails; a weighted-sum interface remains worth attacking

2026-10-15. This continuation proves an arithmetic obstruction to a concrete
full-N-dependent acquisition route. It also gives a sufficient matrix-free
interface for a positive evaluator. Neither result supplies the missing
soft O(m) long-query algorithm or a new Lean endpoint.

## New actual-family obstruction

The earlier sparse-catalog theorem required indices fixed as N varied at
fixed m,j. The following probe uses the complete input and is covered by a
new count.

Let m~M be an allowed auxiliary prime, E=N+delta with
-3m^2<=delta<=m^2, and let gamma be the actual projected public unit.
Choose a prescribed m-only integer fold modulus W_m=Theta(m^2), and put

    alpha=gamma^(m^2),
    i_delta(N,m)=floor(E/m^2) mod W_m,
    A_(delta,s)=gamma^E-alpha^(i_delta+s).

This includes folding modulo m^2, modulo the complete canonical search
length 2m^2+2, and modulo the native padded seed length. The actual
first-current targets E_j=N+delta_j satisfy the required offset bound.

On the SAME balanced prime-pair supply P,Q~M^3, allow the first
K(N)<=ceil(N^(1/6))^.020 candidate primes, with K_*=O(M^.020), and all
shifts |s|<=S<=M^.004. The number of inherited admissible input pairs
having ANY such probe nonunit in EITHER hidden field at ANY candidate is

    O(K_* V(S+1) M^5),  V=O(M^.969).

This is an input-exception count, not an algorithm running time. It is
O(M^5.993), or soft O(M^5.989) for polylogarithmic S. Uniting these
exceptions with the frozen soft O(M^5.994) deletions preserves
Omega(M^6/log^2 M) actual inputs. Every observed residual is a unit on
that family, while the complete original seed rectangle has its known
forced collision.

The theorem simultaneously grants EVERY offset delta in the entire band
and EVERY allowed shift. Thus delta and s may be selected using N,
previous observations or advice. The fold formula and one prescribed
m-only W_m family remain fixed. Arbitrary input-dependent fold moduli,
other index formulas, additions producing new residuals and the implicit
long product remain outside this result.

For actual m-1 targets and polylogarithmic S, these probes cost soft O(m)
per candidate modulus, including public integer divisions, powers and
gcds. The complete offset band, polynomial shift window and polynomial
prime menu are granted for coverage only. They have no claimed near-linear
acquisition clock. See [the full proof](reports/high-digit-folding-obstruction.md).

## Why full-N dependence is countable here

Set A_m=m^2 W_m=Theta(m^4). Exact Euclidean division gives

    E=A_m t+m^2 i_delta+r,  0<=r<m^2,
    E-m^2(i_delta+s)=A_m t+r-m^2s=:n.

The literal menu-selector envelope is

    (m-G_m)^6<N<=m^6,
    sum_m(G_m+1)=O(K_*M),  G_m=o(m).

It puts every possible t, including offsets crossing a digit boundary,
in one m-only interval of length O(mG_m+1). Moreover n=Theta(M^6)>0;
there is no zero-integer exception to the divisor argument.

A local zero requires the actual prime order R_P>P^.677 to divide n.
Each fixed positive n has O(1) prime divisors exceeding cM^2.031.
For each such R, P=1+vR with 1<=v<=V gives O(V) possible P values.
For fixed P,t, existence of ANY permitted offset forces

    A_m t-m^2<=P Q<A_m(t+1)+3m^2.

This interval contains O(m) integer Q values TOTAL. It already absorbs all
tags and all offset choices; multiplying by their number would be an
incorrect extra charge. Summing t,r,s and m gives

    O(V(S+1) sum_m(mG_m+1)m^3)
      =O(K_*V(S+1)M^5).

Prime divisors and hidden factors are enumerated only in this counting
proof. No factorization oracle or advised order is supplied to the
algorithm. Two independent reviews verified the final theorem, its
prescribed-modulus corollary and its historical source bytes.

## A sufficient positive interface through formal weights

Normalize each row to P_L(z_j)=product_(i<L)(1-z_j q^i), with known units
z_j,q. Suppose a division-free straight-line program of T gates computes
the FORMAL identity

    F(w_1,...,w_J)=sum_j w_j P_L(z_j)

over R[w_1,...,w_J], R=Z/N. Reverse differentiation at w=0 recovers every
P_L(z_j); multiplying the recovered values gives the ANY-preserving norm.
It requires at most 5T+J-1 ring operations and O(T+J) stored residues,
with no inversion of a collision residual. This remains valid with zero
divisors. Inversions of weight-independent known units can be acquired
and checked separately as constants.

Thus a soft O(J+sqrt L) formal weighted-sum program would suffice for
near-linear batch acquisition in the balanced regime. This is an
optional sufficient route; a norm-only evaluator could succeed without
it. The fast weighted-sum program has NOT been found. A black-box scalar
sum, a formula valid only after specializing the weights, or pointwise
equality over a finite ring does not satisfy the formal-program premise.
See [the proof and bit/memory accounting](reports/positive-adjoint-interface.md).

One genuinely cheap ingredient is available: J weighted geometric nodes
give their first K moments in soft O(J+K) ring operations, through a
rational-function product tree with constant-one denominators. The unpaid
step is pairing that moment stream with the implicit dense q-binomial
coefficient stream without writing L coefficients. See
[the transform interface](reports/transform-interface.md).

## Other investigated interfaces and their limits

A companion matrix C and coefficient-scaling matrix D have an exact
rank-one q-Weyl defect. The constant matrix (I-C)D reproduces the first
J q-products, but later steps need explicit quotient-boundary corrections.
A finite-horizon theorem excludes a generic constant linear-state closure
realizing all prefixes, already at J=1. It is NOT an actual-family or
arbitrary scalar lower bound; horizon-specific, nonlinear and numerical
methods remain open. See [the corrected identities](reports/q-weyl-boundary.md).

On the actual prime-order family, q=gamma^(m^2) and gamma generate the
same local subgroup. Every target z=gamma^(-E) satisfies z^R=1, so
product_(k<R)(1-zq^k)=0. A nowhere-zero cyclic primitive satisfying
W(qz)=c(1-z)W(z) would instead require c^R(1-z^R)=1. Thus this cyclic
endpoint representation is unavailable even if the hidden order and
extension roots were supplied. Singular regularization and noncyclic
methods remain outside the obstruction. The phase-division and reversal
identities are exact but retain the original interval length. See
[the reciprocity audit and primary checks](reports/cyclic-reciprocity-audit.md).

The convex-box investigation is saved as an exploratory scoped analysis;
it does not exclude arithmetic pruning or adaptive algorithms generally.
It is not a premise of the new digit-folding proof.

## Status and evidence

The complete uncentered seed rectangle's arithmetic coverage and global-
leaf recovery were already proved in `SemiprimeSeedSumAcquisition`.
Restriction-stable scalar queries would support logarithmic-call gcd
bisection. The general evaluator still costs soft O(m^(3/2)); achieving
soft O(m), then composing all routing, kernel, bit and memory bounds in
Lean, remains necessary for the full goal.

`manifest.json` pins the final reports, reviews, historical source inputs
and primary artifacts. The new arithmetic count and adjoint reduction
are classical, independently reviewed results. The earlier evidence
bundles remain frozen. No new Lean source, numerical factorization
corpus or broad build was added. The guaranteed all-semiprime one-sixth
factorization goal remains active and unproved.
