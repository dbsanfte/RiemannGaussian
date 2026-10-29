# Quantum dilogarithm / knot audit (2026-10-25)

Result: I found a genuinely finite, fixed-number-of-indices cluster identity (Kato–Mizuno–Terashima, below), but no paid algorithm improving soft(J+sqrt(Jh)) for an arbitrary acquired F. The finite identity is a potentially useful rewrite engine, not a complexity result. A direct quantum-torus realization on R[X]/F has a strong elementary obstruction.

## Primary literature

1. Kato, Mizuno, Terashima, *Quiver mutation sequences and q-binomial identities*, https://arxiv.org/html/1611.05969 (2016), Theorems 4.1, 4.2, Proposition 4.3, Example 5.2 and Remark 5.3. Theorems relate mutation partition functions to shifted quantum-dilogarithm ratios and establish invariance for frozen-isomorphic final quivers. Proposition 4.3 expands those ratios in q-binomial weights. Equation (5.9) is the finite Stanley identity displayed below. This is more directly relevant than an infinite pentagon alone.

2. Kucharski, Reineke, Stošić, Sułkowski, *Knots-quivers correspondence*, https://arxiv.org/pdf/1707.04017, Sections 3, 4.1, 4.4. Knot generating functions are matched to sums over quiver dimension vectors with q-Pochhammer denominators; DT product factorization gives integrality consequences. The finite manipulations in Section 4.4 rewrite colored invariants into quiver form. A fixed quiver does not imply bounded coefficient-extraction cost as color grows, and the source does not provide arbitrary-modulus remainder algorithms.

3. Bonahon, *Miraculous cancellations for quantum SL2*, https://arxiv.org/pdf/1708.07617, Theorem 1, pp. 1–2. For products of triangular quantum matrices, Chebyshev threading simplifies to entrywise nth powers when q² is a primitive nth root of unity. Its hypotheses are essential; this does not supply short cancellation at n~h when both local orders exceed 16k². The exact local-order convention must be translated before even proposing an application.

4. Faddeev–Kashaev, *Quantum Dilogarithm*, https://arxiv.org/abs/hep-th/9310070. Its finite-dimensional construction uses Fermat-curve data and a restricted star-triangle relation. It is a root-of-unity/cyclic construction, not a generic high-order finite q-Pochhammer evaluation algorithm.

5. Kashaev–Nakanishi, *Classical and Quantum Dilogarithm Identities*, https://www.imath.kiev.ua/~sigma/2011/102/ (arXiv:1104.4630). Gives tropical, universal and local forms from periodic quantum cluster mutations. These organize formal noncommutative identities; periodicity of a mutation sequence is not finite multiplicative order of the supplied scalar q and does not remove support costs.

6. Garoufalidis–Kashaev, *Quantum dilogarithms over local fields and invariants of 3-manifolds*, https://arxiv.org/abs/2306.01331 and author PDF https://people.mpim-bonn.mpg.de/stavros/publications/padic-quantum-dilogarithm.pdf. Local-field quantum dilogarithms yield face/edge state-integrals and distributional manifold invariants. Z/NZ is not a local field; neither integration nor distributional identities are finite ring arithmetic algorithms here.

## Exact finite candidate and paid audit (own analysis)

Write [n choose r]_q for Gaussian polynomials. KMT equation (5.9) is

    [c+a choose a]_q [d+b choose b]_q
      = sum_{t=0}^{min(a,b)} q^((a-t)(b-t))
          [c+d+t choose t]_q
          [c+a-b choose a-t]_q [d+b-a choose b-t]_q.

Take nonnegative integer parameters making the upper indices nonnegative. This is an exact polynomial identity and can be evaluated over R without division if Gaussian polynomials are constructed integrally. For coefficient formulas using factorial quotients, check every denominator 1-q^j: under the given order promise these are units for 0<j<16k² (gcd failure yields a factor). No square root of q is needed in the displayed version.

The sum has min(a,b)+1 terms. Fixed mutation width does not make that constant. In a length-h Pochhammer, coefficient support is h+1. Specializing c+a=h gives Gaussian coefficients of the target product, but it neither computes the weighted sum modulo F nor bounds the aggregate work by soft(J). If min(a,b)=Theta(h) this expands the same cost. Choosing one small index produces a short identity only for a special coefficient slice; no uniform map for all residues modulo arbitrary F was identified. This is the cleanest finite literature candidate to test, but I do not claim an algorithm from it.

## Quotient-module obstruction (own proof)

Status correction after coordination: this dilation obstruction duplicates prior work in the parent investigation. It is retained only as background, not a new finding or the main conclusion.

Let A be multiplication by X in S=R[X]/(F), with F monic degree J. The natural dilation B:f(X)->f(qX) descends to S iff F(X) divides F(qX). Because the degrees coincide and leading coefficients are units, this requires

    F(qX)=q^J F(X).

If F=sum f_i X^i, then (q^i-q^J)f_i=0 for i<J. For 1<=J-i<=J<16k² the order promise makes q^i-q^J a unit in R, forcing f_i=0. Thus only F=X^J admits this natural dilation. That exceptional quotient is nilpotent and fundamentally different from arbitrary F.

More generally, suppose an invertible J-by-J B satisfies B A B^-1=q A. Similarity forces characteristic polynomials F(T)=q^J F(T/q), again forcing F=T^J. If A is also invertible, determinants already force q^J=1, impossible under the promise. Consequently a quantum torus with both generators invertible cannot be represented in dimension J over R under these hypotheses. This is not an impossibility theorem for all compressed algorithms; it rules out a specific frequently implicit mapping.

Possible escape: use intertwiners between the different quotients F(X), F(qX), ..., or enlarge to a q-stable orbit of moduli. The orbit has no short exact return in the promised range, so its size and all boundary data must be charged. A finite nilpotent auxiliary variable of width L is legitimate, but truncating its series computes X-adic coefficients, not reduction modulo F: discarded X^n (n>=J) generally return nonzero residues. Recovering those contributions is exactly the missing operation.

## Weak factor locator

A formal identity does not preserve factor detection automatically after introducing inverses. Each inverse in R or S must be justified. Scalar nonunits give gcd witnesses; nonunits in S can encode polynomial-resultant obstructions rather than immediate nontrivial integer factors. Passing to DT exponents, logarithms or infinite series introduces denominators and coefficient recovery costs. No reviewed source proves that a short trace, determinant or selected state detects precisely the collision required by the original semiprime query.

## What remains open

A useful theorem would provide a bounded-state finite identity together with an explicit arbitrary-F remainder evaluation costing soft(J), including every endpoint Pochhammer and denominator check. None of the cited sources supplies this. KMT finite mutation sums deserve higher priority than analytic/cyclic dilogarithms for further exploration, but currently do not change the soft(k^1.25) baseline.

## Follow-up: relative Habiro / étale / Frobenius constructions

### Precisely relevant published constructions

Garoufalidis–Wheeler, *A lift of the colored Jones polynomial of a knot*, https://arxiv.org/pdf/2603.01619 (March 2026), Definition 1.1, Lemma 1.2, Theorem 1.3, Corollary 1.4. Their relative Habiro ring has coefficients in Z[t^±1,Delta_K(t)^-1], with p-Frobenius t->t^p and q fixed. Theorem 1.3 gives a knot-invariant lift specializing t=q^(n-1) to the colored Jones polynomial. Lemma 1.2 injects into the mixed cyclotomic completion with ideals (t^-1;q)_n; Corollary 1.4 recovers a finite-at-color cyclotomic expansion. The truncation comes from the exact zero in (q^(-n+1);q)_k at k>=n, rather than an arbitrary acquired polynomial F. This is constructive topology-to-series information, but no cost bound for recovering the cyclotomic coefficients is asserted.

Garoufalidis–Wheeler, *Explicit classes in Habiro cohomology*, https://arxiv.org/pdf/2505.19885, Theorem 1.18, Section 3.3: on its analytic subring the push-forward is f->[f omega], for a Frobenius-invariant differential form. The proof explicitly checks convergence; its target is a product of de Rham classes expanded at roots of unity. Thus the push-forward is not asserted to be a finite sum in a discrete coefficient ring. Proposition 1.14 does give an integral Gaussian-binomial multisum for symmetrized admissible series; it still sums over all nonnegative dimension vectors. Question 1.17 explicitly leaves open whether the general q-Borel transform descends to these Habiro rings/cohomology. This prevents assuming a universal quadratic-twist push-forward rule.

Garoufalidis–Scholze–Wheeler–Zagier, *The Habiro ring of a number field*, https://arxiv.org/html/2412.04241, Section 5: Propositions 5.1–5.4 give genuinely finite congruence coordinates. At filtration L the change-of-basis matrix M_L is square of dimension L(L-1)/2; its determinant D(L) is explicit. Membership is tested by the adjugate congruence M_L^*gamma=0 mod D(L), with Frobenius-twisted coordinates in the number-field case. Equations (325)–(328) construct composite-modulus Frobenius by prime-power factorization and CRT. These are useful exact arithmetic recipes, but they neither compress the coordinates to soft(L) nor provide a factorization-free construction. Their completed-ring Frobenius fixes q and the local root variable; it does not identify P_h(X;q) with a shorter product at q^p.

### A specific computational lemma to extract and test (own analysis)

The finite Habiro congruence recipes can safely be used modulo N at a filtration L below both unknown factors: all prime divisors of D(L) are <=L (see the determinant formula). Thus if L<min(p,r), gcd(D(L),N)=1 and M_L is invertible over R. One can reconstruct a finite Habiro polynomial from a *supplied full vector* of Taylor/cyclotomic coordinates by modular linear algebra, without knowing p or r. In this problem the local-order promise already implies p,r>16k², so L=O(h) satisfies this for large k. This is a valid factorization-free finite computational lemma, unlike using prime-power CRT Frobenius without factoring N.

Paid audit: the vector and matrix dimension is Theta(L²). Taking L~sqrt(J) makes the coordinate count O(J), but no theorem says that this filtration determines evaluation at the given high-order q. Taking L~h costs Theta(h²) coordinates. There is no claimed fast transform in these sources. Merely inverting D(L) is cheap and legitimate; obtaining and applying all needed coordinates is the unpaid part.

Here is an exact criterion that explains the missing specialization step. Let Q be a formal variable and q0 the supplied scalar in R. A map from the finite ordinary Habiro quotient R[Q]/((Q;Q)_L) to R sending Q->q0 exists iff (q0;q0)_L=0. In the promised range 1<=L<min(ord_p(q0),ord_r(q0)), every factor 1-q0^i is a unit, so the entire product is a unit: the proposed map cannot exist. This is specific to the finite-quotient evaluation interface, not a prohibition on evaluating a known finite polynomial. Even a very fast M_L transform would need extra information to bridge this interface.

For the *relative* completion, setting t^-1=X makes its level-h modulus exactly P_h(X). A map to S=R[X]/F exists precisely when P_h=0 in S, which is not the desired general case. One could instead push forward to a trace, residue, or norm, but a computational theorem must prove which finite jet controls that push-forward. The cohomological push-forward theorem gives no such finite-jet statement for arbitrary F.

### Constructive next target, not established

Seek a relative-Habiro **finite-jet remainder theorem**: given monic F of degree J and h, select O(J) explicit cyclotomic/relative coordinates, computable in soft(J), whose push-forward determines P_h mod F (or a collision-preserving scalar) with an O(J)-size integral reconstruction transform. The finite coordinate congruences suggest an algebraic language for stating this, and denominator invertibility is unusually favorable here. The current papers do not supply the selection theorem or reconstruction cost. Without it, neither Frobenius gluing nor étale push-forward improves the existing bound.
