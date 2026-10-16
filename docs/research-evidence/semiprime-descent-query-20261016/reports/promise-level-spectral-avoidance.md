# A forced hit does not force a spectral zero from the subgroup promises alone

2026-10-16. Exact promise-level construction, following the root's grid argument. This is NOT an actual quadratic-tag counterfamily. It does not settle the source-specific spectral route or prove a computation lower bound.

## Field statement

Let K be a field containing q of odd prime order R. Let J>=2, L>=J, J<R, T=floor((L+1)/J), and R>L+J+T. Put a=q^L. For a monic H(t)=sum_(k=0)^J h_k t^k, define

 phi_H(X)=sum_(k=0)^J h_k product_(s<k)(1-Xq^s)
                             product_(k<=s<J)(a-Xq^s).

Fix ANY z0=q^(-i), 0<=i<L. There exist J distinct nodes in the odd subgroup <q>, including z0, such that z0 is the ONLY root of F=P_L among them, while

    phi_H(0)!=0 and phi_H(q^(Jn))!=0 for every 0<=n<T,
    H(t)=product_j(t-z_j).                         (1)

Thus one forced collision, large odd order, distinct nodes and even the delta-unit branch do not alone imply a resonance in the complete-block spectral tests.

More strongly, the remaining J-1 nodes may be chosen from ANY supplied scalar grid S in K of size greater than L+J+T, provided z0 belongs to S. The grid version does not require S to be a subgroup, but choosing it inside the odd subgroup retains that promise.

## Nonzero spectral functionals under the prescribed root

For each tested X let P_k(X) be the product multiplying h_k. A linear functional sum h_k P_k vanishes identically on monic degree-J polynomials divisible by t-z0 if and only if

    (P_0,...,P_J)=lambda(1,z0,...,z0^J).            (2)

This follows by eliminating h_0 from H(z0)=0; all remaining h_1,...,h_(J-1) are free. Substituting H=(t-z0)product_(j=1)^(J-1)(t-z_j) does not turn a nonzero such affine coefficient functional into the zero polynomial in the remaining roots: elementary symmetric polynomials are algebraically independent, or simply have distinct leading monomials. No generic numerical specialization is inferred from this formal observation; the grid step below supplies the actual field choices.

At X=0, P_k=a^(J-k) is geometric with ratio a^(-1), different from z0 because i<L<R. Hence the delta functional is nonzero on the prescribed-root family.

At n=0, X=1 leaves only P_0 nonzero; its factors q^L-q^s, s<J, are nonzero. This vector is not geometric at a nonzero z0. At any other complete-block point v=Jn>0 with v+J-1<L, all P_k are nonzero. Their successive ratios are

    P_(k+1)/P_k=(1-Xq^k)/(a-Xq^k).

The first two ratios cannot agree: their cross-difference is X(q-1)(a-1), which is nonzero. J>=2 is used here. Finally, if v+J-1=L, only P_J survives and is nonzero; again (2) fails. These are all possibilities because complete-block endpoints lie at most L. Thus each factor in (1) is a nonzero polynomial in the remaining nodes.

## Explicit grid degree accounting

Multiply all T spectral polynomials, the delta polynomial, the J-1 factors F(z_j), and the distinctness factors

    product_j(z_j-z0) product_(j<k)(z_j-z_k).

The resulting polynomial is nonzero over K. Every spectral/delta factor is multiaffine in the roots, so the degree in each remaining root is at most T+1 from those factors. F avoidance contributes L, and distinctness contributes J-1. Hence each variable degree is at most L+J+T. A nonzero polynomial with each variable degree smaller than the size of a scalar grid cannot vanish on the entire Cartesian grid: prove this by induction using the univariate root bound. Therefore the product is nonzero at some S^(J-1), giving exactly (1), distinct nodes and no other hit.

For the canonical L=2m^2+2, J=Theta(m) and sufficiently large m, an interval of gamma exponents of length 4m^2+1 is already a sufficiently large field grid, because R>16m^2 makes those powers distinct. If such a grid contains the fixed hit, the same ONE-FIELD construction stays inside that exponent band. It still does not impose the literal quadratic/inverse-indexed tag map, and is not a semiprime-source counterfamily.

## Composite promise-level consequence and its limit

Take two actual qualified hidden fields with distinct odd prime subgroup orders satisfying the bound. In the P field use the fixed-hit construction above. In the Q field use the same nonvanishing-grid argument without a prescribed root and avoid F at all J nodes. Each spectral/delta functional is nonzero on unrestricted monic H; the same degree bound suffices. Combining the independently chosen nodes by CRT gives unit-difference nodes modulo N=PQ, exactly one P-only collision, and ALL tested spectral values units modulo N. Choose local q generators and their d-th roots gamma, d=m^2; since both orders are prime and exceed d, this gives q=gamma^d. Their distinct coprime odd orders make the CRT product subgroup cyclic, so all supplied nodes do lie in one common odd-order subgroup globally as well.

This construction proves that the abstract subgroup/order/unit-difference/forced-hit promises cannot force the proposed spectral factor test. The CRT choices need not be the same short integer gamma exponents in both fields and do not satisfy the literal delta_j(N,m) quadratic catalog. Consequently it must NOT be called an actual-source counterfamily. The exact question whether that additional catalog forces an interior spectral consequence remains open.

The determinant formula and paid uniqueness-check algorithm are pinned separately in spectral-check-status.md; no new computation clock, Lean theorem, or general hardness claim follows from this avoidance construction. No repository edits or numerical examples were used.
