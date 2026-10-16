# Independent exact review A: mixed index/geometric scalar and matrix obstruction

2026-10-16. PASS for the exact theorem, proof and scope below. This review is independent of the mixed report's author; the reviewer authored its separate pure-geometric matrix predecessor. No original file was modified and no build was run.

Targets: mixed-index-clock-obstruction.md12194 bytes/SHA256 `55da629133046fc1cf162e8f130ce141b8516213dac9b77de3e4871a52fa7073`; mixed-source-pins.json1033 bytes/SHA256 `89fa96ac4b560483b98101ccfa000691974c433c3815d19d8a04692c67383dd4`. All four declared prerequisite paths independently match their raw lengths and hashes, including pure matrix10313/810253fc..., arbitrary scalar10847/586a884f..., uniform screen7000/22d22246..., and latest all-input setup13939/4c4efaba....

## Confluent independence and finite characteristic

The Hasse-jet evaluation map on polynomials of degree<v(D_k+1) is invertible because the powers of the distinct linear factors are pairwise coprime. Its transpose, factorial/lambda scaling and the triangular falling-factorial conversion give exactly the sample matrix n^j lambda_i^n. The needed nonzero factorials have j<=D_k. Thus characteristic0 or>D_k is sufficient even when the total number of samples exceeds the characteristic. Repeated numerical frequencies must be grouped first, as the report does. The conclusion is zero COEFFICIENT POLYNOMIAL for every group, not merely sampled numerical zeros.

## Regular start, effective order and nominal range

A nonvacuous polynomial-in-index/geometric function has at most D_h+1 grouped frequencies and degree<=D_k in the index. If its first M0=(D_k+1)(D_h+1) samples vanished, confluent independence would force an identically zero trajectory. Hence a regular leading value exists at j<=M0-1. Substitution P_t(Z+j,h^j X) preserves both degree bounds. Dropping identically-zero coefficient FUNCTIONS does not extend the original k<=L-r interval; the explicit nominal-r sample condition pays for the full M0-1 shift loss. An effective order-zero relation contradicts P0(j,h^j)A_j!=0 directly. Vacuous formal polynomials are therefore not mistakenly used as nonzero recurrences.

## Cleared ratios, alias coarsening and poles

The shifted ratio has the correct g chirp exponent, numerator factors and scalar q^j shifts. Every sampled denominator exponent is<=L. There are at most(r+1)^2(D_h+1) frequencies, each with index-polynomial coefficients of degree<=D_k; the displayed sample condition suffices for grouped polynomial identities.

A nonzero alias must have nonzero h-coordinate. Eliminating h between two aliases creates a g/q relation with exponent magnitudes<=2rD_h<=m. The certified box forces both determinants zero, proving collinearity. Coarsening G=x^c,Q=y^c,H=x^(-a)y^(-b) preserves vanishing group coefficient POLYNOMIALS in Z even if more groups merge. Actual g,q constants remain constants in the rational multipliers. This distinction is made explicitly.

If a!=0 the leading P polynomial remains nonzero in K(Z)[x,x^-1] at the highest-shift pole y^c=q^(-j-t_*); its numerator factors are nonzero by ord(q)>L+r. Lower terms are regular. Inseparability changes pole multiplicity without cancelling it. If a=0, distinct x powers isolate the leading term; b!=0 gives a nonzero substituted polynomial, while b=0 uses its selected nonzero value at Z=0. No-alias and D_h=0 cases also force the contradiction directly. The proof thus covers ordinary polynomial-index recurrences in the specified range.

## Mixed matrix scalarization and finite-orbit repair

The cleared rows have bidegrees(s delta_k,s delta_h), since shifting Z+i and h^i X does not increase degrees. Rank-minor scalarization has bidegrees at most(s²delta_k,s²delta_h). Singular matrices and rankzero are included. For a long/infinite h-orbit, a nonzero formal coefficient yields distinct h-frequencies and is nonvacuous by the established confluent independence.

For a short orbit T<=D_h, specializing CLEARED rows at each orbit point produces a polynomial-in-Z row kernel with degree<=D_k via minors, or a constant dependency in rankzero. Interpolating these kernel vectors in X gives degree<T and preserves degree in Z. At least one coefficient polynomial remains nonzero, and the T distinct h-frequencies with characteristic>D_k imply a nonvacuous trajectory. This is a proof-side existence construction, not free order finding or a computed interpolation oracle. Cleared rows exist even at zeros of B outside the actual sample window; division is used only at legal starts. Thus no full-orbit denominator promise or extra state transition has been assumed.

## Actual application and limits

The latest paid all-semiprime setup plus the old square-alias screen supplies the relation box and both q-order margins without balance, prime orders or extra source deletion. The sample conditions imply D_k<L, while P,Q>16m²>L, so the characteristic condition is automatic. The conclusion is factor-or-representation-obstruction on both hidden fields, not a guarantee that the screen factors every input. Fixed/polylogarithmic scalar or matrix parameters eventually satisfy the stated inequalities.

Standard Hermite interpolation, falling factorials, minors and finite-node interpolation are credited. The claimed new composition retains the ordinary index clock and repairs finite-orbit nonvacuity; it does not subsume the known TWO-geometric-clock ratio. No full-query evaluator, arbitrary operation/circuit lower bound, improved query clock, native theorem or Lean bit proof is asserted. Selected values/jump algorithms, other streams, high-degree sparse entries, multivariate geometric clocks and nonlinear/norm/factor-only methods remain outside. No correction requested.

Final wording corrections verified: after transposition the scaled jet index labels a column; g^k and q^k are retained commensurate powers, with no false independence claim. Neither correction alters the proof.
