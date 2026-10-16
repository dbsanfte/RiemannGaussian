# Paid block transforms and a polynomial gcd whose roots are exactly collisions

Recorded 2026-10-16; investigation began on 2026-10-15. Three user-authorized gpt-6.1-sol agents investigated in parallel, with root synthesis and independent final-byte reviews. These are new classical algorithms and proofs. No new Lean theorem, implemented factoring benchmark, or improved overall factoring exponent is claimed.

The main positive result is a nearlinear arithmetic operator on an implicit matrix with Theta(m^2) entries. It extends the earlier selected-coefficient primitive to arbitrary weighted blocks, a full binomial remainder, and an entire channel vector at any one supplied point. A second exact theorem identifies the common polynomial gcd of the channels with the collision set. Acquiring that gcd or the simultaneous diagonal remains open.

## What is now paid

Let F(t)=P_L(t;q)=sum c_k t^k over Z/N, with every 1-q^r, 1<=r<=L, a unit. Let B be a width, and let nu public row starts satisfy 0<=a_j and a_j+B-1<=L.

| Operation | Proven cost in ring operations, including setup |
|---|---|
| C*v and C^T*w, C_(j,s)=c_(a_j+s), arbitrary formal weights and repeated starts | soft O(B+nu+sqrt L) |
| Full F mod(t^B-X), at ONE arbitrary scalar X, including zero/nonunits | soft O(B+L/B+sqrt L) |
| All dyadic Cartier numerator values (N_r(X))_(r<B), at ONE arbitrary X, including collision points | soft O(J+B+L/B+sqrt L) |
| Both actions of an implicit matrix S with diag S=(F(z_j))_j | soft O(J+B+L/B+sqrt L) |

At B,nu,J=Theta(m), L=Theta(m^2), these bounds are soft O(m), with soft O(m) residue storage. The bit bounds include the usual log N factor and the displayed logarithmic powering/setup costs. The unit promise is verified on the retained actual long-query family. This is not a theorem that every semiprime input reaches that promise for free.

[The block-transform proof](reports/block-transform.md) constructs a common rational Newton basis, converts a weighted sum by a polynomial product tree, evaluates it, and transposes its formal linear circuit. It then computes the full binomial remainder. The mask is reduced fraction-free through a telescoping norm-complement recursion; no inverse of D_B(X), roots of unity or extension ring is needed, even at singular X. Two independent reviews passed: [A](reviews/block-transform-review-a.md), [B](reviews/block-transform-review-b.md).

[The mixed-matrix proof](reports/fast-mixed-matrix-interface.md) gives S=V_y C V_z^T plus a paid rank-one ragged correction, with y_j=z_j^B. Its diagonal is exactly F(z_j), and its actions are paid by the block and Vandermonde operators. An ordinary polylog-rank commutator generator would then suffice for nearlinear diagonal extraction; its rank and acquisition are still unproved. The available q-displacement changes the targets and is a different contract.

## The collision information is explicit, but its gcd is not acquired

After distinct-node deduplication on the actual odd-subgroup branch, define

    D(t)=prod_j(1-t/z_j),
    E_B(t)=D_B(t^B)/D(t),
    F(t)E_B(t)=sum_(r=0)^(B-1)t^r N_r(t^B).

For dyadic B>=2, in either hidden field,

    monic gcd_r N_r(Y)=prod_(j:F(z_j)=0)(Y-z_j^B).

[The locator proof](reports/common-channel-collision-locator.md) proves exactness and squarefreeness by complete dyadic fibers. The mask supplies the nontrivial phases; F supplies the remaining phase exactly at a collision. On the retained family this common factor has o(m) degree. [Review A](reviews/common-channel-locator-review-a.md) and [review B](reviews/common-channel-locator-review-b.md) checked the final proof bytes.

The new point-vector oracle does not supply that polynomial gcd or its coefficients. The [gcd literature audit](notes/channel-gcd-primary-check.md) found no applicable nearlinear conversion; output degree alone does not meet the sparse-input or black-box interpolation costs, and hidden-field gcd is not a free operation over Z/N. A simultaneous diagonal contraction, cheap structured common-gcd acquisition, or another sufficient additive observable remains necessary.

## Supporting investigations and limits

- [One-channel gcd interface](reports/one-channel-query-interface.md): ONE degree<2J coarse polynomial, or its remainder mod D_B, suffices for the restricted gcd query. Postprocessing needs no derivative or collision-value inverse. Acquiring its coefficient list is still missing.
- [Decimation](reports/decimation.md): exact mask and unit row transport; every mask phase is present and Fourier branches have disjoint active poles. These exclude specified pruning shortcuts, not direct one-channel convolution.
- [Mixed contraction and binomial coverage](reports/mixed-contraction-classification.md): target shifts and alignment are explicit; an exact binomial root-cover needs at least J moduli. This is not a lower bound on simultaneous evaluation or other additive algorithms.
- [Inverse-reflection pairs](reports/low-phase-pairing.md): higher input digits cancel in pair product phases, but leave (m-3)/2 distinct centers. No asymptotic speedup follows from grouping alone.
- [q-integration](reports/q-integration.md): the proposed rational primitive has nonzero cyclic trace; universal residual reduction and formal jets remain possible and unpaid.

The saved exploratory [Trummer source note](notes/mixed-diagonal-primary-note.md) preceded the exact S factorization. Its then-unpaid diagonal identification is resolved by the mixed-matrix proof here; compatible generators remain missing. The [independent block derivation](sources/independent-block-operator.md) supports the main operator proof with a slightly stronger denominator premise; the consolidated proof handles ragged blocks with only exponents through L. These backgrounds are not extra whole-query theorems.

## Evidence and unresolved goal

[manifest.json](manifest.json) pins reports, reviews, primary artifacts, journal entry and the seven frozen predecessor bundles. [source-map.json](source-map.json) resolves original temporary paths and adjacent-file references to durable repository artifacts, including reused primary gzip payloads. The new constructive proofs are self-contained relative to the earlier paid selected-coefficient and formal-transposition primitives. Primary literature is saved or resolved under the source map; investigator inspection and independent hash/mathematical review are distinguished.

The generic whole-query bound remains soft O(m^(3/2)). This packet proves useful new nearlinear subroutines and an exact collision locator, without claiming the whole-family soft O(m) acquisition advance. No new example corpus, Lean changes, broad build, commit or push is included. The guaranteed all-semiprime sixth-rate theorem and its full bit/memory/routing/controller proof in Lean remain active and unproved.
