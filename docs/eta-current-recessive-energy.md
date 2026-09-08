# Quantitative removal of the recessive eta-energy channel

The module [EtaCurrentRecessiveEnergy.lean](../RiemannGaussian/EtaCurrentRecessiveEnergy.lean)
bounds one entire channel in the actual normalized current. The other
channel's independent upper bound remains open. This is an auxiliary
estimate, with no new zero exclusion or RH claim.

## Actual quantities and assumptions

Let `rho` be an actual `NontrivialZetaZero`, with `sigma=Re(rho)>1/2`,
and write `rho#=1-conj(rho)`. Use the existing completed moment,
multiplicity-selected coefficient, and moment constant:

\[
F_\rho(N)=\operatorname{pairedEtaFiniteCompletedMoment}(\rho,N+2,0),
\quad C_\rho=\operatorname{pairedEtaCurrentZeroEnergyCoefficient}(\rho),
\quad Q_\rho=\operatorname{pairedEtaCurrentMomentConstant}(\rho).
\]

The new definitions are precisely

\[
E_\rho(N)=\Re(C_\rho)|F_\rho(N)|^2,
\qquad P_\rho(K)=\sum_{N<K}E_\rho(N).
\]

The coefficient is positive in both actual multiplicity branches. The
old normalized current is unchanged:

\[
S_\rho(K)=P_{\rho^\#}(K)-P_\rho(K).
\]

`pairedEtaNormalizedReflectedEnergyPartialSum_eq_channels` checks this
identity. No inverse-product or physical-prefix diagonal has been removed.

## Independent upper bound for the original colour

`norm_pairedEtaFiniteCompletedMoment_sq_le_rpow` retains the squared
horizontal decay for every order below the actual multiplicity:

\[
|F_{\rho,k}(N)|^2\le Q_\rho^2(N+1)^{-2\sigma}.
\]

The genuine zero equation and existing complete-tail estimate supply
this bound. Since `2*sigma>1`, these sequences and `E_rho` are summable.
For every `K>=1` and every band length `L>=0`,

\[
0\le\sum_{n<L}E_\rho(K+n)
\le A_\rho K^{1-2\sigma},
\qquad
A_\rho=\frac{\Re(C_\rho)Q_\rho^2}{2\sigma-1}.
\]

The proof compares the decreasing power sum with its integral over
`[K,K+L]`. It retains the positive lower endpoint, so the negative
exponent and denominator cause no singularity. Passing to the limit
after proving summability gives the same bound for the entire tail:

\[
R_\rho(K)=\sum_{n\ge0}E_\rho(K+n)\le A_\rho K^{1-2\sigma}.
\]

Compiled entry points are `sum_pairedEtaCurrentChannelEnergy_band_le`
and `tsum_pairedEtaCurrentChannelEnergy_tail_le`. The exponent is
`-e_rho` on this side of the critical line. The constant depends on the
zero and grows as `sigma` approaches `1/2`; no uniformity in the zero
is asserted. The bound is not applied to `rho#`, whose real part is
strictly less than one half.

## Signed transport with all offsets retained

Set `T_rho=sum_N E_rho(N)`. Its finiteness is proved, and
`tsum_pairedEtaCurrentChannelEnergy_le` also proves

\[
0\le T_\rho\le E_\rho(0)+A_\rho.
\]

`pairedEtaNormalizedReflectedEnergyPartialSum_sub_reflected_eq_tail`
and `_bounds` retain the exact identity and its signed estimate:

\[
S_\rho(K)=P_{\rho^\#}(K)-T_\rho+R_\rho(K),
\qquad 0\le R_\rho(K)\le A_\rho K^{-e_\rho}.
\]

For every late finite band the exact discrepancy is

\[
P_{\rho^\#}(K+L)-P_{\rho^\#}(K)
-[S_\rho(K+L)-S_\rho(K)]
=\sum_{n<L}E_\rho(K+n).
\]

`pairedEtaNormalizedReflectedEnergy_band_sub_bounds` bounds this
nonnegative discrepancy by the same `A_rho*K^(-e_rho)`, independently
of `L`. The signed difference `S_rho(K)-P_rho#(K)` converges to `-T_rho`.

Finally, let `B_rho` denote the sum of the two previously proved
transport budgets, for the full inverse replacement and the odd-weight
normalization. The original weighted leading current satisfies

\[
\left|W_\rho(K)-4[P_{\rho^\#}(K)-T_\rho]\right|
\le B_\rho+4A_\rho K^{-e_\rho}.
\]

This is `pairedEtaLeadingFluxSignedPartialSum_reflected_error_le`.
The finite early-cutoff total and both complete error series are included.

## Consequence for the local-gap strategy

This slice was motivated by auditing the source term left after the
sparse divisibility cut. The original colour has only a finite total
available to offset the reflected positive energy. The known positive
power lower bound therefore remains a bound that an independent estimate
for the reflected energy would have to contradict.

The product-one carrier already contains the full physical prefix.
The existing complete-fibre identity and diagonal-zero odd heat kernel
mean an off-diagonal Hilbert estimate alone does not control this source
contribution. A useful Hilbert or commutator route must retain a checked
comparison with the actual scalar current, including its diagonal.
Local-gap specializations and a source-saving commutator estimate have
not been proved in this slice. No claim rules out all uses of that machinery.

The new bound removes one quantitative uncertainty in the signed
comparison. It supplies no relative saving for `P_rho#` or `S_rho`, and
the active contradiction goal remains open. The dashboard milestone
remains the existing normalized-current lower bound.
