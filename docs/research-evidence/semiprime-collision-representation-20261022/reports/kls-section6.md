# KLS v2 §6: source-retaining block mechanisms and arithmetic transfer limits

Source: Zhao Song and Xinzhi Zhang, *An O(1) Bound for the KLS Constant*, arXiv:2610.01447v2, dated October 2, 2026; version stamp October 4. Local user-supplied PDF SHA256 fad3f750a121cd99f09213ea237fc71b66e97ad1699ecca1d07f74c2fd69d771. Primary identifier https://arxiv.org/abs/2610.01447v2. Page numbers below are printed paper pages. This is a reading of §6's mechanisms and dependencies, not validation of the claimed full KLS proof.

## What §6 actually proves, under its hypotheses

Proposition 6.1 (p32, proof pp60–63) states that for every centered regular log-concave probability measure with Cov<=I and potential Hessian>=aI, a>0,

 CP <= Gamma_r² ell_r(a^-1)²,    Gamma_r²<=C(r+1)^(1/3),

where ell_r iterates x↦log(e+x). Regular means a smooth potential with some positive finite lower AND upper Hessian bounds (definition p14); constants of these bounds need not be uniform. The analytic setting is a real Hilbert space L²(mu), with a positive self-adjoint elliptic generator H=−Delta+gradW·grad, centered inverse powers, positive Dirichlet form, covariance normalization, and Bochner identity. These hypotheses are not supplied by a finite residue ring or a high-order cyclic orbit.

The coefficient estimates concern Appell polynomial tensors normalized by c_d=sqrt(K_d)/d!, uniformly over a fixed dimension range. They are bounds on variances/energies, not algorithms evaluating the coefficients or tensors.

## Four mechanisms worth transferring precisely

1. **Compensate an initial projection loss before restarting.** The restricted radius R=R_res satisfies R<=CP<=R+1 (Lemma6.4 p35). Its extremizer yields a low-energy centered gradient (Lemma6.5 p36). A skew-loss inequality charges skew mass to normalization gain (Lemma6.6 p36), and a three-slot frame prevents an unobserved tensor component from escaping (Lemma6.7 p37). Proposition6.8 pp37–38 constructs a restart with energy excess O(R^-2) and the first three losses O(lambda²). This is a rigorous model for retaining a source through a change of representation: discarded components are paid by an explicit nonnegative defect, rather than silently assumed absent.

2. **One joint frame across all dyadic degrees.** Theorem6.15 pp44–46: for every finite-dimensional real orthogonal representation of S_(2d), d dyadic,

 ||T||² <= 10^4 [d||P_dT||² + sum_(k<d,dyadic) k² ||(I−S_k)P_kT||²].

P_k and S_k are specified commuting permutation averages (p41). The proof uses multiplicity-free subset harmonics, half-block branching, and a scalar Schur-complement induction, not cancellation of arbitrary signs. Applied to a compatible derivative hierarchy, every coherent term is a projection of ONE tensor (identity96 p46). This prevents paying an independent full norm at every scale. Lemmas6.16–6.17 pp46–47 give cumulative loss <= startup + horizon*terminal contribution + an error-kernel constant times cumulative energy defect. A finite convolution's l² norm is bounded through its l¹ norm, so old defects are charged once through a kernel, not once for every later generation.

3. **Average a block by a direct sum, preserving mass.** Lemma6.21 pp50–51 bounds the mesoscopic block norm: R−C/R <= ||T^b||^(2/b)<=R for b<=floor(R)+2, with T=P_+gradH^-1. Proposition6.22 pp52–54 chooses b=floor(R), z=||T^b||^(2/b), a top right singular vector f, and w_j=z^(-j/2)T^j f. Crucially the startup family is Z=directsum_(j=0)^(b−1) w_j, NOT sum_j w_j. Orthogonality gives ||Z||²=sum||w_j||²; no accidental signed cancellation can remove the source. Bounds on the orbit's linear moments give first SEVEN losses S7=O(z^-3), initial energy excess D0=O(z^-3), and ||T^ell||<=C_blk z^(ell/2), C_blk<=2. That last constant is paid once over an entire defect propagation, not at each step. This is the strongest structural analogy to retaining all native row branches while controlling a global energy.

4. **Keep one static radius and summable iteration losses.** Lemma6.24 p55 builds Z(mu) controlling EVERY degree c_d<=Z^((d−1)/2), with CP<=Z+2 and Z<=max(H0,CP). The additive two is charged once after the depth induction. Lemmas6.25–6.26 pp56–57 use the accumulated metric M_t=Cov_t+(s/tau) integral_0^t Cov_u du, preserving correlation with past covariances instead of replacing noncommuting matrices by unrelated bounds. Proposition6.27 pp57–59 transfers an r-log radius bound to coefficients with factor (1+r^-2)^(d−1); the product of these depth losses converges. Finally the startup O(z^-3), depth mass budget p~1/(r+1), and z^-1=O((r+1)^(-1/3)) match. The iterated-log contraction absorbs polynomial scale changes. This explains the cube-root depth cost; it is not a square-root running-time bound.

## Concrete arithmetic research direction and sufficient missing hypotheses

The direct-sum/block architecture suggests retaining native collision witnesses as a nonnegative finite family rather than summing character values whose cancellation can erase a hit. To turn this into a theorem for the collision query, one must construct an EXPLICIT finite operator T and projections with all of the following:

- a source-to-detection implication for the exact original scalar collision, including same-leaf conjugate pairing;
- a conserved or controlled positive mass and an exact telescoping defect budget, in a specified ordered field or real lift;
- compatible projections of a common object (analogue of identity96), not unrelated per-scale masks;
- a uniform block propagation bound whose constant is paid once;
- acquisition of the required block norms, defect sums, or scalar contractions in soft O(m) BIT operations, including any operator applications and localization.

These conditions are substantive. A character matrix over Z/N has no ordered positive cone or real Hilbert norm supplied by the ring. Picking least residues and taking Euclidean norms is not compatible with multiplication modulo N. A whole native match is not preserved by arbitrary real averaging. A direct sum DOES preserve witnesses, but explicitly writing all row/seed entries still costs JL; the paper supplies no implicit geometric representation that removes this cost. Its singular-vector/extremizer choices are existence arguments and cannot be imported as free numerical or finite-ring algorithms.

There is one limited immediately useful design rule: any proposed multi-level cancellation controller should first retain branches orthogonally/directly, then prove that a shared projection/defect identity compresses the resulting positive energies. This avoids confusing cancellation of a character sum with acquisition of a collision. It does not itself evaluate those energies. An approximation route would additionally require certified absolute error below an integer-separation threshold and a way to compute the approximation cheaply; §6 gives neither for the native arithmetic matrix.

## Bottom line for the present query

No direct application of Proposition6.1, its tensor frame, or its averaged block startup yields a factoring observable. The meaningful connection is a proof architecture: compensated restart, simultaneous dyadic frame, direct-sum block startup, shared static radius, and summable transfer losses. The strongest actionable target is an exact source-retaining arithmetic energy recurrence with a cheaply acquired contraction; constructing that operator/contraction is still required. This report neither validates the full KLS claim nor dismisses that transfer as impossible.
