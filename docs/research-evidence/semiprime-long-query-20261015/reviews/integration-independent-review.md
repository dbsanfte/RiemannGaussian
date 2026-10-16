# Independent integration review — 2026-10-15

Reviewed file: `/home/dbsanfte/riemann/formal/docs/research-evidence/semiprime-long-query-20261015/README.md`

SHA-256: `245935f8b0adf89af5cf79b888f41c725ef0c0df16c86ee6f1450dae8339fef1`

Verdict: **PASS for the stated algebraic and algorithmic scope**, conditional on the explicitly inherited hard-family order and source-identity inputs. No report or repository file was modified during this review.

## Checked claims

* Resultant orientation is correct: S=Res(G_L,H)=(-1)^(JL)Res(H,G_L). The text correctly conditions sufficiency of a small remainder on paying subsequent factor-aware resultant cost.
* Doubling identity, universal scaling-endomorphism criterion, and the normalized moving-carrier polynomial are correct, including the q^(h^2) and q^(-hJ) factors.
* The actual-family obstruction is sound: over either hidden field, unit constant coefficient and scaling invariance imply q^(sJ)=1. Prime order R_p and 0<J<R_p force R_p|s. Thus every nonzero |s|<R_p is excluded. The stated exponent gap 2.031 versus 2 absorbs fixed constants and soft factors for J and the O(m^2) shifts. This review does not independently re-prove the inherited existence of those prime-order families.
* No unjustified minimum-degree claim is inferred from global distinctness modulo composite N. The caveat correctly permits alternative moving-carrier algorithms.
* Unit-X truncation obstruction and its norm version are correct. Rational endpoint valuation obstruction is correctly limited to the asserted rational form.
* Spiroid theorem formula and composite-ring hypothesis agree with the saved author PDF; historical attribution to KU is corrected. D^(5/sqrt(log D)) is superpolylogarithmic, so the text correctly separates almost-linear from strict softly linear. Determinism matches the presented construction.
* The proposed target soft O((J+sqrt L) polylog N), in the balanced J~m,L~m^2 regime, avoids accidentally demanding a polylogarithmic scalar q-factorial algorithm at J=1. This corrects the unnecessarily stronger all-parameter J*polylog L formulation.
* Compact q-difference identity is correct, and the finite-order nonuniqueness caveat is necessary and present.
* Public-period branch preserves exact prefixes and needs no inversion of candidate residuals.

## Scope limits and small wording point

The LCM paragraph relies on its linked independently reviewed proof and source identities. Its stated primitive-progression bit-size implication is consistent with the classical progression LCM inequality; this review did not reconstruct those source identities from the original arithmetic source. The formal addition/subtraction-chain bound concerns an exact unreduced exponent and is correctly disclaimed for independent order reductions.

For the normalized product T(1), the original unnormalized collision scalar can differ by a known unit/sign phase. The current wording says “rectangular normalized collection,” which makes this acceptable for the gcd acquisition objective; retaining an explicit unit phase would be needed if claiming literal equality to the earlier unnormalized S. This is not a blocking correction.

No universal scalar lower bound, exhaustive literature theorem, new factor-recovery theorem, or Lean result is asserted. The final open-status statements agree with the demonstrated scope.
