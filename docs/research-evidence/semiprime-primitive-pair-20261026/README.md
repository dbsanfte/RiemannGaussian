# Symmetric factor tags, paired products and polar lattice coefficients

26 October 2026. Continuation of the [whole-bin residue and finite chirp investigation](../semiprime-fused-readout-20261026/README.md). Three investigations and three independent paper reviews are retained.

**We can ask a symmetric identity for less information than previously required.** A readout invariant under colour reversal still suffices for the full weighted family. On primitive rows, even a readout invariant under both reversal and coefficient exchange suffices. Both recovery algorithms are proved within soft K, where K is of order N^(1/6). Their coefficients have not been acquired at that cost. The existing weighted query remains soft K^(5/4), and the guaranteed sixth-exponent factoring theorem remains open.

## 1. Symmetry does not have to lose the useful factor information

The preceding packet proves that every good-bin hit has the same colour modulo n*=3^ceil(e/2), for K=2*3^e. Replace its canonical colour weight by the canonical integer

    w2_j=[j²]_(n*).

An acquired additive pole pair would then equal (d,d*u), with u=[R²]_(n*) and 1<=d<R at the nonsplit prime R. Public Hensel lifting gives precisely the two roots +/-R modulo n*. The existing guarded validator and restricted-HH recovery handle this constant menu in soft K. This works for nonprimitive rows and axes too. It does not require an odd derivative that distinguishes j from -j.

There is a second useful option for primitive nonaxis rows. Put m=3^e and compute the canonical integer

    kappa_j=[(j+N/j)²]_m=[N(a+b)²*(ab)^-1]_m.

This is unchanged under j->-j and j->N/j, corresponding to phase reversal and coefficient exchange. At a good primitive hit it is [(P+Q)²]_m. Its candidate factor colours solve

    j^4+(2N-kappa)j²+N²=0 mod m.

Even with ramification this congruence has at most 4*3^floor(e/2)=O(sqrt K) unit roots. A public 3-adic tree acquires them in worst-case soft sqrt K; their odd lifts modulo K fit the soft-K restricted-HH budget. Neither nonsingularity nor a square-root oracle modulo an unknown prime is assumed.

The second option is primitive-only. A primitive subbank can miss the guaranteed witness, and coefficient exchange does not license adding rows outside the correct weighted window. Also the reduction modulo m must occur BEFORE embedding the weight in the native algebra: the unreduced rational expression containing N would vanish at the hidden prime. These qualifications are part of the theorem.

See [primitive-asymmetry.md](primitive-asymmetry.md) and its [review](review-primitive-asymmetry.md).

## 2. Execute an Askey–Wilson connection, keeping its collision factor

The actual primitive pair has normalized roots c*x and c/x, with rho=q^-1 and clock h=O(K^(3/2)). Its product is

    (c*x;rho)_h*(c/x;rho)_h.

This is an exact Askey–Wilson basis element. The finite connection identity in [Ismail–Stanton, equation (2.4)](https://www-users.cse.umn.edu/~stant001/PAPERS/AndrewsFormFinal.pdf) can be specialized at the acquired parameter d=rho^-r/x. Terms above r vanish, so r<=K gives a short sum with certified short q-factorial divisions.

But every surviving term contains the common factor

    L_r=(c*x*rho^r;rho)_(h-r)*(c/x;rho)_(h-r).

The residual short sum evaluates exactly the two removed boundary products. Their whole-bank cost is soft K; L_r still has a long clock. Removing it at a zero would erase the desired pole. Thus this specific identity pays for the boundaries but does not acquire the bulk. This is a scoped calculation, not a lower bound on symmetric algorithms.

The constructive change is the target: a symmetric paired pole count, marked by w2 or the primitive kappa, is enough. A future identity need not recover orientation, a full matrix, separated roots or a leading Hasse degree.

## 3. Two other representations identify different sufficient inputs

**Axis orders.** At the nonsplit prime, the supplied scalar and norm-one orders are coprime and exceed the preparation threshold. Their joint Frobenius query has a strong integer decoder, but their numerical orders remain unknown. A weaker extra input would suffice: any acquired nontrivial divisor d of either local order. Roughness forces d>K, and the smaller factor then lies in one of four classes {+1,-1,+N,-N} modulo d. Four explicitly bounded integer AP products recover it in soft K. This requires neither a full order nor identification of the nonsplit side. Acquisition of such a divisor remains open. The complete axis-colour query, with its phase carries and endpoints restored, still costs soft sqrt(B) on a factor-size bin B using the scalar GP engine.

See [axis-two-orders.md](axis-two-orders.md) and its [review](review-axis-two-orders.md).

**Polar lattice coefficients.** Absorbing the physical clock into l=ell-Hi gives discriminant D=4abN-l². Every exact native hit satisfies

    D=-(aR-bN/R)²=-H*u², u nonzero.

The standard Igusa seed gives zero weight to these indices, deleting all native witnesses. A meromorphic Appell summand does have the right negative-square algebraic support; its finite K-filter is (1+T^K)/(1-T^K). Laurent-chamber membership is a separate issue, so this is not a claim about all coefficients of one analytic expansion. The actual finite denominator test becomes 1-(pi*barpi^s)^K with guaranteed winding s=-R. The complementary target gives s=-N/R. These are exactly the axis Frobenius controllers again, with no cheaper acquisition supplied. The alternative winding for an actual primitive shortest pair is integral only in the monic exception; it cannot freely choose the smaller factor.

See [lattice-product.md](lattice-product.md) and its [review](review-lattice.md), including the primary-source checks for Igusa, Borcherds and Appell formulas.

## Next calculation

Target the even additive pole pair directly on the acquired primitive paired bank, while retaining the full-family nonprimitive and axis coverage. The successful operation must eliminate the long bulk, or supply a different sufficient arithmetic statistic such as a one-prime order divisor. Finite endpoint identities and correct polar support now have precise consumers; neither by itself meets the whole-family soft-K acquisition bound.

[Source contracts](sources.json), [review and preservation record](review.json) and [manifest](manifest.json) record the scope. All 1000 prior protected files, both document prefixes and 23 concurrent files are preserved. This packet contains paper proofs and audits, not new factoring code, a numerical campaign or Lean formalization. No commit or push was performed.
