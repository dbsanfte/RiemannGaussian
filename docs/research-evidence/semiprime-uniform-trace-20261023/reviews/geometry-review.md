# Independent review of the all-input AP multiplier geometry

23 October 2026. Reviewed `/tmp/semiprime-trace-acquisition-20261023/unbalanced-geometry.md` against the derivation in `docs/semiprime-sparse-residue-gauss-audit.json` and the inherited uniform setup/annihilator interface. Source inspection and independent algebra only; no new examples campaign, repository edits, implementation integration, or Lean claim.

**Verdict: PASS as a paper-level whole-input geometry and fixed-k additive-source extension. It does not acquire the multiplicative detector or prove the sixth-rate factorizer. No mathematical repair is required in the reviewed version.**

The inherited nearest-lift inequality before its old modulus simplification is exactly

    d^2+X^2b^2+X^4a^2 <= (2N/H+H^2/2)X^2.

It does not require the old `HX<=2sqrt(N)` condition. With H=r^2, N<=r^6, and the stated public windows X=32r*2^j, it gives the asserted `(5/2)H^2X^2` bound and `|a|<r/20`. Every surviving smaller factor lies in a public window; its covered h is nonnegative and less than X. Since P>=rX/2, Cauchy–Schwarz gives `|sigma|<=sqrt(30)r<6r`. These constants and the direction `N<=H^3` check. Retaining a=0 is essential; one cannot reuse the old a!=0 conclusion at these parameters.

The two coefficient branches are sound. C=0 would imply H|a, hence a=u=0, contradicting the nonzero quotient vector. If a=0, **exact shortestness** against the lattice vector (N,0) forces u=±N, so C=±H and b is a unit modulo r and H. This is what makes the linear branch valid; a merely approximate short-vector promise would not justify that argument unchanged. The primitive-linear-divisibility paragraph also checks: C=0 is exactly the saturated polynomial-multiple obstruction, and the constructed rows exclude it.

The public K=0 screen works in both branches. For nonzero a, a is an r-adic unit, and the uniquely least valuation in `a(c-s)^2+Hb(c-s)+H^2(d-sigma)` forces H|(c-s). For a=0, the certified unit b gives the same conclusion. In the canonical AP range only s=c=1 can remain, with sigma=d. Thus there is at most one candidate leaf per window, with labeled multiplicities retained if descriptors repeat. This is **individual leaf deletion**, not the old whole-row deletion: no inherited alias-prefix certificate is needed, because the true own leaf is independently nonzero and cannot be removed.

The true exponent identity is correct:

    K=(P-1)(CQ-ac^2).

It is nonzero for a=0 because C!=0. For nonzero a, equality CQ=ac^2 would make prime Q divide ac^2, impossible with 0<|a|<r and 1<=c<r<Q. All exponents have logarithmic bit length. A surviving saturated leaf therefore supplies a legal nonzero short annihilator of its own rho_v, whose odd local orders exceed 16r^2; the inherited unconditional unbalanced decoder applies without assuming that it is the true row.

The root normalization is legally closed. E0 includes r and every nonzero |a|; raising by E0^ceil(log2N) removes their prime divisors from surviving local orders. A collapse is handled by the inherited factorable-small-leaf descent, **not** by handing the long raising exponent to the short-annihilator decoder. The NoHit branch gives rho_v^a=beta0 and preserves equal large local orders. Outside powers are charged. This is inherited source preparation rather than new query acquisition.

The fixed-k formula retains the necessary row-dependent seed clock:

    A_(v,k)=sum_sigma rho_v^(-kH^2sigma),
    w_(v,k)=rho_v^(kC_vN) A_(v,k).

Consequently one common quadratic polynomial with coefficients beta0^(kc^2), plus one linear polynomial for a=0 rows, suffices for monic multipoint evaluation across all windows. Division-free seed sums, signed endpoints, repeated points, native-tag masks, and public-zero subtraction are all included. The row count is O(r logN), absorbed only by the stated soft notation. The acquired bound is one-k soft O(r), or h traces soft O(rh), with logarithmic bit factors; no simultaneous-index or full-product contraction follows.

Required qualifications are already explicit in the report: exact Gauss/nearest-lift arithmetic is inherited but the guarded old implementation cannot be called unchanged; the scale includes N<=r^6 and r=Theta(N^(1/6)); square/even/auxiliary-divisor branches are supplied by the paid setup; coefficient roots and global saturation are inherited; and all actual signed lifts and row seed clocks remain in the source. The remaining main task is the restriction-safe multiplicative/nonunit detector for this full family, not its coverage, coefficient nontriviality, short-seed geometry, or fixed-k additive trace.
