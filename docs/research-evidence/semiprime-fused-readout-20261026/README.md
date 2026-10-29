# Whole-bin common-tag readout and finite quadratic-phase contraction

26 October 2026. Continuation of the [acquired coefficient-transform investigation](../semiprime-direct-contraction-20261026/README.md). Five paper investigations, independent cross-reviews and a primary-agent audit are retained.

**The strongest result is a simpler uniform acquisition problem:** on the pure modulus K=2*3^e, the short weighted family needs only TWO additive simple-pole coefficients per factor-size bin. All its good-bin hits, including axes and nonprimitive rows, have one common factor tag modulo 3^ceil(e/2). Multiple hits, repeated roots, content-sector palettes and unknown Hasse depth are no longer obstacles to specifying that readout.

There is also an executed finite contraction: completing fixed coefficient pairs and decomposing their quadratic phases turns each branch into O(log g) geometric-progression strings. All completion, starts and endpoint guards are paid. **Its whole-family cost is still soft K^(5/4), not soft K.** The sixth-exponent factoring goal and full target bit-complexity proof remain open. No formal reformulation below is counted as the missing acquisition algorithm.

## 1. Combine the short clock with one common tag

The original signed-weight construction already enumerates all unit tags j and uses roots pi^ell_j*barpi^(a+bN). Its weighted lattice and Frobenius proofs do not use chi_D(j). The independently audited pure-K preparation can therefore supply this bank as well as the earlier two-monic bank. Bases and order screens are actually rebuilt at the chosen K.

In a correct bin for the unknown nonsplit factor R, the acquired weighted Gauss rows give a clock of length h=O(K^(3/2)). Every hit has exact integer provenance. For a nonaxis row of content g=gcd(a,K)=gcd(b,K), the valuation argument gives R=j modulo K/g. The Gauss bound gives g²<=|ab|<=K/sqrt(3). Consequently

    n*=3^ceil(e/2) divides EVERY K/g.

Axes give the full tag modulo K. Thus every good-bin hit has the SAME w_j=[j]_(n*)=r=[R]_(n*), and n* is of order sqrt K.

With shifted roots T_j and leaves a_jt=1-T_j q^-t, define

    V=[delta^0] delta sum_(j,t) 1/(a_jt+delta),
    U=[delta^0] delta sum_(j,t) w_j/(a_jt+delta).

At the good field these are exactly (d,d*r), where 1<=d<=J<R. Every pole is simple even with many hit rows. Repeated rows are counted directly; no derivative inverse or separated-root interpolation is required. The existing guarded ratio and restricted-HH consumer then recover a factor in soft K from a correct pair. Bins remain separate because wrong-bin aliases lack that provenance.

The full retained-bound factorer is also verified: acquire all row products with the old division-free engine, classify each by norm/coordinate gcds as a proper factor or a global zero/unit, and sum its 0/1 flags and tagged flags. This computes the ACTUAL pair above and completes factoring at soft K^(5/4), including setup and recovery. It needs no saturated-leaf clock localization or beta-annihilator decoder.

See [pure-weighted-common-tag.md](pure-weighted-common-tag.md) and its [review](review-pure-weighted.md). The more general conductor-aware sector version and its first-pole proof are in [direct-residue.md](direct-residue.md), with [review](review-residue.md). The pure common-tag result is stronger when its preparation is used.

## 2. Quadratic phase blocks really can be contracted

For a fixed nonaxis coefficient pair (a,b) of content g, the valid colour lifts have an exact quadratic phase modulo H=K². The even-content case needs a parity correction. After reducing it, the effective phase modulus is m=3^v3(g), and the acquired roots take the form

    y_t=y_0*qhat^(quadratic(t) mod m)*q^(carry_t),
    qhat=pi^(H/m), qhat^m=q.

The finite carries are explicitly retained. Completing each DISTINCT acquired pair to all its valid unit colours is affordable: there are O((K/g²)log K) possible signed nonzero pairs at content g, each with O(g) lifts, and sum_(g|2*3^e)1/g is bounded. The complete enlarged bank therefore still costs soft K to acquire. Added rows preserve the weighted bound and good-bin tag proof.

After paid endpoint factor-or-unit gates, carry removal preserves the collision predicate and additive residues. It does not assert equality of the raw scalar products. Completing the square then partitions the full phase multiset into O(log g) arithmetic progressions, with explicit positive multiplicities. For a progression of length L and base r satisfying r^L=q,

    product_(v<L,i<h)(1-z*r^v*q^-i)
       =product_(u=-L(h-1))^(L-1)(1-z*r^u).

The bijection u=v-Li makes this one GP string of length Lh. This is a finite exponent identity at the actual native bases, not a root-of-unity Gauss-sum substitution. The collapsed lengths remain inside the guarded order range. Branch tags and multiplicities are retained.

Batching the resulting strings gives soft(K+sqrt(Kh)) again. The nontrivial-content terms decrease geometrically with g; the g=1 part retains the old scale, and the separately handled axes can also retain it. This identifies the dominant part of THIS execution, not a lower bound on primitive rows or another contraction method.

See [quadratic-lifts.md](quadratic-lifts.md) and its [review](review-quadratic.md).

## 3. A higher quotient digit cancels in the ternary hierarchy

The earlier complete monic hierarchy also has a useful cancellation. With parent modulus n=K/g, write P=j+n u and I0(u)=F(u)/(j+n u), where F is the acquired quadratic from stationarity. For the child coefficient d matching u modulo g, the exact finite difference shows

    I0(u+g t)+d(u+g t)=I0(u)+du mod g².

Hence matched child phases need only g classes per parent, not g². Their whole table costs soft K. The stronger prerequisite suggested by separately aligning every phase is withdrawn. The congruence is automatic for each correctly matched child and therefore does not identify the unknown class. Its remaining integral clock position still requires a query.

The actual parent-window implementation is also costed: for a public smaller-factor bin [L,2L] and parent modulus n, its cost is soft(n+sqrt(N/(nL)+L)). The sqrt L contribution survives this particular descent. This is a cost of the executed engine, not a lower bound on the hierarchy.

See [hierarchical-contraction.md](hierarchical-contraction.md) and its [review](review-hierarchy.md).

## 4. The coefficient transform has an explicit Cauchy basis

The acquired triangular displacement operator now has an explicit Toeplitz eigenbasis. Both basis changes cost soft B, and the transformed coefficient matrix has Cauchy entries with certified unit denominators. This applies to arbitrary native clock length h=BM+r, with all r+1 tails and both factorial-offset tables paid.

Two actual trace algorithms were executed: a dual Sylvester solve and a linked-displacement generator contraction. Both retain the true matched moment right-hand side and cost soft(J(B+M)) in the supplied execution. A finite kernel cancellation also works, but after restoring its tails it gives the original q-difference relation on a shifted root alphabet. None yet computes the selected scalar at target cost.

See [structured-trace.md](structured-trace.md) and its [review](review-trace.md). These are exact native-ring calculations; numerical low-rank approximation and generic field inversion are not imported from the literature.

## Next acquisition target

The short pure weighted bank is now the cleanest direct-residue target: acquire its one common-tag pair per bin in total soft K. The completed quadratic blocks give an explicitly initialized alternative bank of GP strings. The nonaxis execution concentrates its remaining cost in primitive-content rows; the axes still require their own acquisition route. The next algorithm should exploit that primitive paired structure, improve the axis query, or compute the additive residue directly; it need not rediscover sector recovery, separate repeated roots, or determine a leading Hasse degree.

Paper reviews, source contracts and preservation hashes are recorded in [review.json](review.json), [sources.json](sources.json) and [manifest.json](manifest.json). All 986 prior protected files, both document prefixes and 23 concurrent files are preserved. No factoring implementation, numerical campaign, Lean/public assets, commit or push was performed.
