# Exact packed residue from two fermionic mass insertions

26 October 2026. Focused paper-only source experiment. No repository edits, implementation, tests, numerical campaign or Lean.

**Positive identity:** the EXACT packed integer residue, with constant clock weights, is the residue of a two-insertion Gaussian determinant divided by a cheaply acquired UNIT normalizer. No q-binomial clock amplitude replaces the integer count. The mass insertion annihilates the unwanted double-pole term. Its direct initialized completion still costs the old K^(5/4) bound; a faster computation of this selected correlator is not supplied.

## 1. Exact target, not the earlier arbitrary-amplitude substitute

Use the original one-row-per-colour bank and actual normalized leaves

    a_e=1-T_j*rho^t, e=(j,t), 0<=t<h,
    w_e=L+[j²]_n, L=K/2, n=3^ceil(e/2).

The target of the [six-domain report §§1–2,6,8](../semiprime-six-domain-acquisition-20261026/README.md) is

    C=Res_(delta=0) S_w(delta),
    S_w=sum_e w_e/(a_e+delta), S_0=sum_e 1/(a_e+delta).

Here Res means the coefficient of delta^{-1}, componentwise in the actual quadratic algebra B. The row clock guard ensures at most one zero per row in every component, but MANY rows can hit. At the good field C is the positive packed integer dL+du, with 1<=d<=3^floor(e/2), and the existing bounded-integer recovery then costs soft K. This specific integer amplitude must be retained. The q-binomial source c_t of the earlier Lambert experiment does NOT compute C unless its changing amplitudes are actually normalized.

## 2. A two-insertion Ward identity preserving C exactly

Index the full leaf list by e and define the diagonal mass matrix

    D_delta=diag(a_e+delta).

Let U have two columns (1,a), and let V have two columns (w,a). The 2-by-2 source covariance is

    Q(delta)=V^t D_delta^{-1} U
      =[[S_w, W_0-delta*S_w],
        [D_0-delta*S_0, A_1-delta*D_0+delta²*S_0]],

where the entirely known totals are

    D_0=#leaves, W_0=sum_e w_e, A_1=sum_e a_e.

All entries follow from polynomial division by a+delta. Its determinant is EXACTLY

    det Q=A_1*S_w-D_0*W_0+delta*W_0*S_0.          (1)

Consequently

    Res(det Q)=A_1*C.                            (2)

The last term is regular because S_0 has at most a simple pole. Thus ALL possible double poles cancel, even with many hits and repeated rows. This is not a positivity argument, an approximation or a claim that high-rank resolvents are low rank. The source a vanishes at every hit and supplies a polynomial Ward cancellation.

Primary finite framework: Caracciolo–Sokal–Sportiello, [Algebraic/combinatorial proofs of Cayley-type identities](https://arxiv.org/pdf/1105.6270), Appendix A.5, Proposition A.14 and Theorem A.16, gives fermionic Gaussian/Wick determinant formulas. Here (1) proves the required specialization directly over the native ring; formal Laurent inverses are componentwise, not numerical inversions of nonunit masses. No complex Gaussian integral, continuous positivity or factorial inverse is imported.

The source depends on the ACTUAL masses a_e, so this experiment is not excluded by a theorem only about an A-independent fixed parity basis for the entire resolvent. Conversely that observation is not a speedup: the specified two-insertion coefficient must still be acquired.

## 3. The normalizer A_1 is genuinely cheap and can be made a unit

It is the FIRST unfiltered geometric moment:

    A_1=Jh-(sum_j T_j)*(sum_(t<h)rho^t),
    sum_t rho^t=(1-rho^h)/(1-rho).

All roots, weights and one short denominator are supplied, so A_1, W_0 and D_0 cost soft K to acquire, with O(log N)-bit exponentiation. This is not the unknown clock cofactor G_h'(T_j).

Norm/coordinate classification of A_1 returns a proper factor, an actual unit, or an actual global zero. A saturated norm alone is not called a global zero. If A_1 is a unit, use (2). If it is globally zero, remove ONE separately screened unit leaf a_e0 from the source list. This leaves C unchanged as an ACTUAL algebra element because the removed resolvent is regular at zero in every component. It changes A_1 to -a_e0, now a unit. Update D_0,W_0 by their known one-leaf amounts and apply exactly (1)–(2) to the remaining list.

The unit-leaf gate is paid: choose a fixed acquired boundary leaf. A proper norm/coordinate gcd factors. A saturated point equality is an ACTUAL global pi^A*barpi^B=1 with a nonzero short integer label pair, and is handled by the complete two-coordinate consumer of the frozen even-acquisition packet, at most once on a terminating branch. Nonaxis bN dominance and the original axis labels exclude (A,B)=(0,0); no arbitrary additive zero of A_1 is assigned that decoder. Otherwise the selected leaf is certified a unit. Only one such leaf is needed, so the gate fits soft K. Removing this unit may break the presentation's sign symmetry, but the selected residue C itself is exactly unchanged; it is not a new unproved coverage family.

This gives a valid direct target

    C=A_1^{-1} Res(det Q),                       (3)

with every normalization paid. It does not evaluate Res(det Q).

## 4. Rank-two determinant experiment and its initialized cost

To express the two insertions without any inverse notation, define

    P(delta)=det D_delta,
    N(delta)=[s*t] det(D_delta+U*diag(s,t)*V^t).

The finite rank-two determinant identity gives the CLEARED equality

    N(delta)=P(delta)*det Q(delta).              (4)

This polynomial relation is lawful on singular components. At a good bin with d hits, P has order d and det Q has residue A_1*C!=0 after the unit normalization. Hence N has order d-1. Their leading-coefficient ratio gives A_1*C. This route would need the appropriate leading data; the rank-two source does not automatically supply them or turn unknown depth d into fixed precision. The denominator matrix still has Jh modes.

The guaranteed singleton partition permits a fixed-depth implementation of (4). In one block define P0=P(0), P1=[delta]P and N0=N(0). After the mandatory P0 zero gate, a correct hitting block has

    N0/(A_1*P1)=w_hit,

where A_1 may be normalized as in §3 inside that block. Empty blocks must be skipped by their P0 gate. Taking a globally summed numerator and denominator is NOT equivalent to summing these ratios: cofactor amplitudes differ between blocks.

A completely initialized implementation acquires G_j=G_h(T_j) and the first physical regulator derivative

    gamma_j=h*G_h(T_j)-T_j*G_h'(T_j).

Constant-rank jets of the existing shared engine pay all these values jointly at soft(K+sqrt(Kh)). Three-coordinate products of (G_j,gamma_j,w_j*gamma_j) give each block's P0,P1 and its marked first derivative B1. Equation (1) gives N0=A_1*B1-D_0*W_0*P0. This acquires the selected two-insertion scalar without constructing Q, its full resolvent or the Jh-dimensional matrix. If a screened unit leaf was removed for normalization, divide its row polynomial jet by the known unit-start factor a_e0+delta; this is legal constant-depth arithmetic. The cost remains soft K^(5/4). For C ITSELF there is a still simpler value-only baseline: classify every acquired G_j by norm and coordinates, factor or obtain global zero/unit row flags, and sum w_j times those flags. The all-component one-clock-hit-per-row guard makes this exact even in wrong bins with multiple hitting rows. It needs no G_h' and no singleton partition. The Ward implementation is not claimed cheaper than that already available flag algorithm.

Thus this explicit source experiment has a paid normalizer and a valid finite rank-two/determinant realization, but no improved initialization of its selected residue. Applying Sherman–Morrison on unclassified D_delta, treating a Jh-mode insertion as constant-cost because its update rank is two, or discarding the first nonzero coefficient of P would leave the same operation unpaid.

## 5. Summing singleton ratios and exact-C scope

In this section ONLY, use the SQUARED-TAG weight u_j=[j²]_n, not the packed weight w_j=L+u_j, and define (d0_b,d1_b,dw_b) by multiplying (G_j,1,u_j). Thus dw_b is explicitly the u_j-weighted row-value derivative. If all these value-only block triples are actually acquired, a correct bin admits a factor-or-exact-C computation with no long clock normalization. Classify each d0 by norm and coordinates. A unit block contributes zero residue. On a global-zero block a proper norm gcd of d1 factors, and a unit d1 gives the exact row-hit tag dw/d1. Its contribution is L+dw/d1.

In a correct bin, a nonempty block has unit d1 at the good field. If another component had multiple zeros, d1's norm would expose a proper factor. If another component had a different empty/nonempty pattern, the d0 gate would expose a proper factor. Thus on a no-factor correct-bin continuation every component has the same 0/1 multiplicity per block, and

    C=sum_(globally hitting blocks)(L+dw_b/d1_b) (5)

is the ACTUAL global residue, not merely a correct good-field value. Its split-side tag values may differ; (5) still computes the actual algebra element, after which the packed scalar-coordinate/integer-recovery gate applies.

This is stronger than selecting one useful block, but it is conditional on acquiring ALL triples. Wrong bins can have multiplicities unsupported by constant-depth triples; such a proposed recovery algorithm may decline that bin, rather than claim to have computed its exact C. A uniform exact-C supplier for arbitrary bins would have to handle those multiplicities too, or provide a factor; the correct-bin factorization contract permits bounded wrong-bin failure. These interfaces must not be silently identified.

The all-row value engine and triple products complete (5) at the retained K^(5/4) bound. None of the ratios is free before those block triples are acquired.

## Outcome

Two-source mass insertion supplies an exact finite alternative for the specified PACKED C with a cheap unit normalizer, and cancels double poles without a full resolvent output. Its explicit rank-two determinant and singleton implementations still use the old long query. The q-binomial source cannot replace constant clock weights when claiming this integer C; it supplies a different arbitrary-amplitude block target. A method evaluating just (3) or the selected block data in total soft K remains the missing algorithm. No six-barrier general impossibility claim or sixth-rate improvement is made.
