# Signed current growth and the complete energy Abel expression

This slice implements the signed-current fallback in the research memo
`RiemannGaussian_reduced_product_or_signed_current_steer.md`. The preceding
[Gamma audit](eta-gamma-radical-bulk.md) proved that its full completion
boundary tends to twice the nonzero source. The present slice proves the
divergence side of the new signed contradiction target. It does not prove
an independent upper estimate, exclude a new zero, or prove RH.

## Actual carrier and signed growth

For an actual `rho : NontrivialZetaZero`, retain

\[
J_\rho(N)=\operatorname{pairedEtaTopPrefixFiniteEnergyLeadingFlux}(\rho,N),
\quad w_N=2N+1,
\quad W_\rho(K)=\sum_{N<K}w_NJ_\rho(N).
\]

Write `P_rho(N)` for the existing principal endpoint, `e=|2*Re(rho)-1|`,
and `s=-1` for `Re(rho)<=1/2`, `s=1` otherwise. Off the critical line,
the already proved zero-strip bounds give `0<e<1`.

In [EtaLeadingFluxSignedPartialSum.lean](../RiemannGaussian/EtaLeadingFluxSignedPartialSum.lean):

- `pairedEtaCurrentPrincipalEndpoint_side_eq_abs_eventually` proves
  `s*P_rho(N)=|P_rho(N)|` eventually. The actual multiplicity selects the
  positive dominant coefficient; no simple-zero assumption is added.
- `pairedEtaLeadingFluxSignedPartialSum_principal_error_le` bounds
  `|W_rho(K)-sum_(N<K) w_N*P_rho(N)|` by the finite total
  `E_rho=sum'_N w_N*|J_rho(N)-P_rho(N)|` for every cutoff.
- `pairedEtaLeadingFluxSignedPartialSum_lower_with_offset` proves, for
  some finite initial cutoff `N0` and every `K`,
  `c_rho*(K+1)^e-B_rho(N0) <= s*W_rho(K)`.
- `pairedEtaLeadingFluxSignedPartialSum_power_lower_eventually` absorbs
  the offset to obtain `c_rho/2*(K+1)^e <= s*W_rho(K)` eventually.
- `pairedEtaLeadingFluxSignedPartialSum_tendsto_side_infinity_of_re_ne_half`
  and its right/left corollaries prove the corresponding signed divergence.

The explicit positive coefficient is the existing

\[
c_\rho=\frac{\operatorname{pairedEtaCurrentPrincipalGrowthFloor}(\rho)}e
=\frac{A_{\rm dom}}{5e}\,5^{e-1}>0.
\]

The full lower-bound allowance is

\[
B_\rho(N_0)=E_\rho+
\sum_N w_N\bigl(|P_\rho(N)|-sP_\rho(N)\bigr)+c_\rho+
\sum_{N<N_0}\operatorname{pairedEtaCurrentPrincipalGrowthFloor}(\rho)(N+1)^{e-1}.
\]

The principal deficit is nonnegative and eventually zero, so this infinite
sum is proved summable under the stated off-critical hypothesis. The
finite initial segment is paid explicitly; it is never assumed to have
the eventual principal sign.

## What cancellation across cutoffs can do

The same module defines the actual nonnegative deficit

\[
D_\rho(N)=w_N\bigl(|J_\rho(N)|-sJ_\rho(N)\bigr).
\]

`summable_pairedEtaLeadingFluxCancellationDeficit` proves its summability
off the line. The pointwise comparison retains the finite principal
deficit and costs at most twice the already summable principal error.
`pairedEtaLeadingFluxSignedPartialSum_cancellationDeficit_tendsto` proves

\[
\sum_{N<K}w_N|J_\rho(N)|-sW_\rho(K)\longrightarrow\sum_N D_\rho(N)<\infty.
\]

This does not assert that the actual current is eventually pointwise of
one sign; occasional opposite-sign errors are allowed. It does show that
cancellation across cutoff indices cannot remove its displacement power.
Any successful estimate must use information inside the actual arithmetic
current beyond cancellation across those indices.

`pairedEtaLeadingFluxSignedPartialSum_bounded_iff_re_eq_half` gives the
memo's bounded-signed criterion. On this actual carrier it is equivalent
to the existing critical-line criterion. Its weaker form does not by
itself make its unknown arithmetic direction easier.

## Exact signed summation by parts

Let `E_N` be the existing signed finite energy difference, `I_N` its
signed increment-energy difference, and `R_N` the existing remainder flux.
The upstream exact conservation law is

\[
E_N-E_{N+1}=I_N+J_\rho(N)+R_N.
\]

[EtaLeadingFluxSignedAbel.lean](../RiemannGaussian/EtaLeadingFluxSignedAbel.lean)
retains the correction `C_N=I_N+R_N` and the entire Abel expression

\[
\mathcal A_\rho(K)=E_0+2\sum_{N<K}E_{N+1}-(2K+1)E_K.
\]

- `pairedEtaLeadingFluxSignedPartialSum_add_correction_eq_abel` proves
  `W_rho(K)+sum_(N<K) w_N*C_N = A_rho(K)` for every `K`, including zero.
- `summable_oddEndpoint_mul_abs_pairedEtaLeadingFluxAbelCorrection` pays
  both corrections throughout the critical strip.
- `pairedEtaLeadingFluxSignedPartialSum_abel_error_le` bounds the
  difference by `F_rho=sum'_N w_N*|C_N|`.
- `pairedEtaLeadingFluxEnergyAbelSum_sub_current_tendsto` retains the
  signed correction limit `sum'_N w_N*C_N`.
- `pairedEtaLeadingFluxEnergyAbelSum_lower_with_offset` proves the same
  signed power lower bound with allowance `B_rho(N0)+F_rho`.
- `pairedEtaLeadingFluxEnergyAbelSum_tendsto_side_infinity_of_re_ne_half`
  proves that the complete Abel expression diverges in the same direction.

The terminal weighted energy has not been omitted. The existing
unweighted fact `E_K -> 0` does not justify dropping `(2K+1)*E_K`.
The theorem about divergence concerns the full signed Abel expression;
this slice does not separately claim a new asymptotic for that boundary.

## Remaining arithmetic target

For a hypothetical actual zero right of `1/2`, an independent uniform
upper bound for `W_rho(K)` would contradict the proved divergence. A
sub-power upper bound, or any proved eventual upper coefficient below
`c_rho/2` at power `e`, would already suffice. Uniformity in `rho` and
absolute summability are unnecessary for this contradiction.

The current identities do not supply that upper bound. The direct signed
sum and the complete Abel expression now have the same checked lower
obstruction, and the total cancellation across cutoffs is finite. A next
arithmetic attempt should retain the full two-colour quadratic in the
actual finite moments, or their exact full inverse regions from
`EtaCurrentFullInverseEnergy.lean`, including all mixed terms. It needs a
new comparison between the reflected complete energies; another
telescoping identity or a norm on each inverse summand does not give one.

## Verification

Both modules pass direct warning-as-error elaboration. The focused build
passes 4,212 jobs and the full build passes 9,732 jobs. All 14 verbose root
linters and whole-project lint pass. Fifteen terminal theorem axiom audits
use only `propext`, `Classical.choice`, and `Quot.sound`; the compiled
inventory/soundness generator and source placeholder scans also pass.
The root imports include both modules. Staged freshness, whitespace, and
the tracked pre-commit gate are required at commit time; exact-commit
GitHub Actions success is required before the next slice.
