# Exact dominant eta-energy asymptotic

[EtaCurrentDominantEnergyAsymptotic.lean](../RiemannGaussian/EtaCurrentDominantEnergyAsymptotic.lean)
identifies the surviving power with the literal Euler endpoint of the
reflected eta tail. This is a diagnostic for the current family. It
proves no zero exclusion, independent upper saving, or RH theorem.

## Exact coefficient and actual carriers

Let `rho` be an actual nontrivial zero with `sigma=Re(rho)>1/2`,
`z=rho#=1-conj(rho)`, `tau=Re(z)=1-sigma`, and
`e=pairedEtaCurrentHorizontalDisplacement rho=2*sigma-1>0`.
Write `chi_z=pairedEtaXiCompletionFactor z.1` and
`C_z=pairedEtaCurrentZeroEnergyCoefficient z`. The coefficient retains
the repository's actual analytic multiplicity; no simple-zero assumption
is made.

For the unchanged channel and current definitions,

\[
E_z(N)=\Re(C_z)|F_z(N)|^2,\qquad
F_z(N)=\operatorname{pairedEtaFiniteCompletedMoment}(z,N+2,0),
\]

\[
P_z(K)=\sum_{N<K}E_z(N),\qquad
S_\rho(K)=P_{\rho^\#}(K)-P_\rho(K),
\]

\[
W_\rho(K)=\sum_{N<K}(2N+1)J_\rho(N),
\]

Lean proves

\[
\frac{P_{\rho^\#}(K)}{K^e}\longrightarrow A_\rho,
\qquad
\frac{S_\rho(K)}{K^e}\longrightarrow A_\rho,
\qquad
\frac{W_\rho(K)}{K^e}\longrightarrow 4A_\rho,
\]

where the literal coefficient is

\[
\boxed{A_\rho=
\frac{\Re(C_{\rho^\#})|\chi_{\rho^\#}|^2
                 2^{-2(1-\sigma)}}{4e}>0.}
\]

The zero parameter is fixed in these limits. Uniformity as it approaches
the critical line or as its height changes is not claimed.

## Proof chain

1. `pairedEtaCurrentEulerMoment_zero` simplifies the existing complex
   order-zero Euler term to `-(chi_z/2)*exp(-z*L_N)`. It retains the
   completion phase and uses the nonzero actual zero coordinate.
   `norm_pairedEtaCurrentEulerMoment_zero_sq` then evaluates its squared
   norm exactly at `L_N=log(2*N+5)`.
2. `summable_abs_pairedEtaCurrentChannelEnergy_sub_euler` proves absolute
   summability of the actual energy minus
   `Re(C_z)*(norm(chi_z)^2/4)*(2*N+5)^(-2*Re(z))` throughout the open
   strip. It reuses the established Euler pair error with its extra
   `1/(N+1)` factor. The signed partial discrepancy converges to its own
   series in `pairedEtaCurrentChannelEnergyPartialSum_sub_euler_tendsto`.
3. `tendsto_scaled_odd_shifted_rpow_sum` uses a decreasing-function
   integral comparison. The sum-minus-integral error lies between zero
   and the first summand; its normalized contribution vanishes. This
   gives the exact power-sum coefficient `2^(-2*tau)/(1-2*tau)`.
4. `pairedEtaCurrentPartnerEnergy_natCutoff_scaled_tendsto` transfers
   that coefficient to the actual reflected channel. Positivity is a
   separate theorem, `pairedEtaCurrentDominantEnergyCoefficient_pos`,
   using the proved nonvanishing completion and positivity in both
   multiplicity branches.
5. `pairedEtaNormalizedReflectedEnergyPartialSum_natCutoff_scaled_tendsto_of_half_lt_re`
   removes the original channel only after its summability is proved.
   `pairedEtaLeadingFluxSignedPartialSum_natCutoff_scaled_tendsto_of_half_lt_re`
   uses both existing convergent signed transport corrections to obtain
   the exact factor four for the original current.

The first normalization uses `(K+1)^e`, whose base is always positive.
A separate limiting-ratio argument proves all three literal `K^e`
statements, restricting the division identity to positive cutoffs when
needed. No singular finite endpoint is used as an analytic identity.

## Consequence for the research path

`pairedEtaLeadingFluxSignedPartialSum_scaled_not_tendsto_zero` proves
that a right-half zero prevents `W(K)/K^e` from tending to zero.
More sharply, `pairedEtaLeadingFluxSignedPartialSum_gt_subdominant_eventually`
proves that every constant `a<4*A_rho` satisfies
`a*K^e<W(K)` at every sufficiently large cutoff.

The power was already present in the elementary tail endpoint before any
Möbius matrix, gcd split, fibre cut, or completion rearrangement. Exact
rearrangements preserve this coefficient. Separate bounds on pieces must
be reconciled with the full positive leading term and every mixed term.

This is the stopping test requested in the quick dominant-energy steer:
further decomposition of this family is suspended unless an independent
arithmetic or spectral theorem forces a contradictory bound on this exact
coefficient or current. Such a theorem would be real progress towards RH;
the present asymptotic does not provide it. Subtracting the Euler term
already leaves a summable error for every actual zero in the open strip,
so decay of that subtracted object alone does not distinguish critical
zeros from hypothetical off-line zeros.

The next research task is to select an independent global arithmetic or
spectral inequality and check its literal hypotheses and source before
building another representation. The existing Gaussian/Weil and Suzuki
detectors remain available, but their open positivity or vanishing
premises must not be assumed. No independent identity annihilating this
coefficient has been established in this slice.

Validation is local while commits are held: the focused Lean build and
root import, declaration lint for this module, and terminal-theorem axiom
audit. No commit, push, or new CI verification is part of this slice.
