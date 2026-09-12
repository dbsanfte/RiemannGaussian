# The source retained when the heat recurrence is iterated

The decay of one upper-order correction does not permit its removal from
a growing sum of recurrences. Lean now proves that the complete correction
band retains a fixed negative source under the hypothetical right-half
zero. This identifies an information loss that a reconstruction argument
must avoid. It supplies no independent prime lower bound or additional
zero exclusion.

## One common width and the complete band

Fix the actual cutoff `D>=1`, finite prime sieve `S`, selected zero `rho`,
normalized divisor polynomial `q`, multiplicity `m`, and `c>0`. Put

\[
u=3/2-\operatorname{Re}\rho,\qquad
B_N=\frac{cu^2}{(N+1)(N+2)},\qquad
P_k(B)=u^{k+1}A_k[q](B,s_\rho).
\]

The [three-order recurrence](../RiemannGaussian/ZetaPrimeHeatRecurrence.lean)
at order `N+j` has upper-order coefficient

\[
w_{N,j}=\frac{2c(N+j+2)}{(N+1)(N+2)}.
\]

Define the **complete actual correction band**

\[
W_N=\sum_{j=0}^{N-1}w_{N,j}P_{N+j+2}(B_N).
\]

Every term uses `B_N`. It is not evaluated at its own order's quadratic
width. The definitions `quadraticBandWeight` and `clearedPrimeHeatBand`
retain these precise indices.

In [GaussianPoleHeatBand.lean](../RiemannGaussian/GaussianPoleHeatBand.lean),
`sum_quadraticBandWeight` and `tendsto_sum_quadraticBandWeight` prove

\[
\sum_{j=0}^{N-1}w_{N,j}=\frac{3cN}{N+2}\longrightarrow3c.
\]

For `N>=1`, this total lies between `c` and `3c`. The earlier
[single-neighbour bound](../RiemannGaussian/ZetaPrimeHeatNeighbourBound.lean)
therefore cannot pay for the accumulated band by simply dropping its
vanishing contribution before summation.

## Uniform residual control across the growing band

The theorem `eventually_norm_clearedPrimeRemainderHeat_band_le` in
[ZetaPrimeHeatBand.lean](../RiemannGaussian/ZetaPrimeHeatBand.lean) proves,
for every `epsilon>0`, eventually and simultaneously for all
`N<=k<=2N+2`,

\[
|E_k(B_N)|\le\varepsilon.
\]

The actual central bound is at most `C*theta^N`, with `0<theta<1`.
The whole outer bound is at most `A*G^(2N+2)*T(B_N)`, with `G=4u>1`.
The already proved Gaussian tail absorbs this larger exponential as
well. This establishes uniformity over a growing set of orders, beyond
the earlier theorem for each fixed offset.

Define `E_band,N` by replacing `P` with `E` in the complete weighted band.
The exact weight budget gives `|E_band,N|<=3c*epsilon` eventually, so
`tendsto_clearedPrimeRemainderHeatBand` proves

\[
E_{\mathrm{band},N}\longrightarrow0.
\]

## The accumulated source stays negative

The original positive gamma average satisfies
`attenuation(k,u,B)>=exp(-B*(k+1)*(k+2)/u^2)`.
For every `j<N`, the complete upper order `k=N+j+2` has

\[
B_N\frac{(k+1)(k+2)}{u^2}\le4c.
\]

The theorem `weighted_attenuation_band_lower` therefore proves

\[
\sum_{j=0}^{N-1}w_{N,j}\operatorname{attenuation}(N+j+2,u,B_N)
\ge c e^{-4c},\qquad N\ge1.
\]

The exact actual-prime source identity passes through the finite sum:

\[
W_N=-m\sum_{j=0}^{N-1}w_{N,j}\operatorname{attenuation}(N+j+2,u,B_N)
+E_{\mathrm{band},N}.
\]

Consequently `eventually_clearedPrimeHeatBand_re_le_negative` proves

\[
\operatorname{Re}W_N\le-\frac{mc e^{-4c}}2
\quad\text{eventually}.
\]

This is a fixed strictly negative bound for every fixed `c>0`. Both the
complex residual and the original multiplicity have been included.

## Exact reconstruction retains the band and both boundaries

The theorem `clearedPrimeHeat_extraFactor_band` sums the actual recurrence
without changing widths:

\[
\begin{aligned}
\sum_{j=0}^{N-1}u^{N+j+1}
A_{N+j+1}[(X-\rho)q](B_N,s_\rho)
={}&P_{2N}(B_N)-P_N(B_N)+W_N.
\end{aligned}
\]

Thus the complete accumulated correction is part of the signed
reconstruction. Its omission would erase a nonvanishing source under the
same hypothesis used by the contradiction argument. The extra factor on
the left also removes the selected pole, so decay of that altered heat
alone does not bound the original heat.

The next arithmetic estimate must retain this full identity, or control
the original signed prime heat directly. The recurrence and Gaussian
bounds do not supply that estimate. These statements concern fixed
cutoff, sieve, zero and positive relative width; they do not assert a
uniform theorem for arbitrary moving parameters. RH remains open and the
proved zero-free region is unchanged. No historical novelty claim is made.
