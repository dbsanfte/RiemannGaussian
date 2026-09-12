# Signed curvature and the actual Fermi zero budget

This slice removes the inverse-Gaussian-width factor from the full outside
zero allowance. The resulting bound is `K / sqrt(H)`, uniformly over every
admissible width, interior line and evaluation ordinate. It also bounds the
actual constant-frequency prime/pole residual independently of width.
These are analytic estimates in the literal zeta theorem chain. The signed
prime lower bound and RH remain open; no larger zero-free region is claimed.

## The identity before the absolute value

Write

\[
q_a(v)=\frac1{1+e^{-av}},\qquad
f_{a,B,x}(v)=e^{-Bv^2-xv}q_a(v),
\]

and retain the logarithmic slope and curvature

\[
s(v)=-2Bv-x+a(1-q_a(v)),\qquad
k(v)=2B+a q_a'(v),\qquad
q_a'(v)=a q_a(v)(1-q_a(v)).
\]

For `a > 0`, the logistic derivative has exact full mass one. Lean proves
the original signed derivative identities

\[
f'=sf,\qquad f''=s^2f-kf,\qquad
\int_{\mathbb R}s^2f=\int_{\mathbb R}kf.
\]

Integrability of every term and the full integration by parts are proved.
The last equality is the unnormalized Fisher-information identity for this
actual amplitude; no historical novelty is claimed for that identity.
Only after the equality do we use

\[
\int_{\mathbb R}|f''|\le 2\int_{\mathbb R}kf.
\]

On the closed strip `0 <= x <= a`, `f <= exp(-B*v^2) <= 1`, giving

\[
\int |f''|\le 4B\sqrt{\pi/B}+2a.
\]

On the enlarged strip `-delta <= x <= a+delta`, provided
`delta >= 0` and `delta^2 <= B`, the existing Gaussian domination gives
`f <= exp(1/2)*exp(-B*v^2/2) <= exp(1/2)`. Consequently

\[
\int |f''|
\le e^{1/2}\left(4B\sqrt{\pi/(B/2)}+2a\right)
\le C_F:=e^{1/2}(8\sqrt\pi+2)
\]

for `0 < a <= 1` and `0 < B <= 1`. In particular there is no inverse-width
factor. Two exact integrations by parts transfer this bound to the complex
analytic reflected transform. The physical same-phase reflection inherits
its real-part bound through the proved conjugation identity; the two
complex carriers are not equated.

Proofs: [GaussianFermiFisherBound.lean](../RiemannGaussian/GaussianFermiFisherBound.lean),
especially `integral_score_eq_curvature`, and
[GaussianFermiFisherTail.lean](../RiemannGaussian/GaussianFermiFisherTail.lean),
especially `integral_score_eq_curvature_enlarged` and
`im_sq_mul_norm_pair_le_enlarged`.

## Every actual outside zero

Let `c(B,sigma,t,rho)` be the original real reflected contribution, including
the analytic multiplicity and the factor of one half correcting for the
double occurrence of partners. Put

\[
D(H)=\sum_{|\Im\rho|>H}\frac{m_\rho}{1+(\Im\rho)^2},
\qquad E_F(H)=4C_F D(H).
\]

The actual divisor is summable. For all

\[
H\ge1,\quad 0<B\le1,\quad \tfrac12<\sigma\le1,
\quad (1-\sigma)^2\le B,\quad 2|t|\le H,
\]

the complete signed outside sum satisfies

\[
\left|\sum_{|\Im\rho|>H}c(B,\sigma,t,\rho)\right|
\le E_F(H)\le\frac K{\sqrt H}
\]

for one proved `K > 0` independent of all these parameters. No zero-free
location premise is used for these outside zeros. The constant `K` is
existential; it has not been numerically evaluated. This removes the
logarithmic factor in the earlier uniform allowance
`K_old*log(H+2)/sqrt(H)`. It does not assert that the actual signed sum has
that exact asymptotic order.

The terminal theorems are `abs_tsum_outside_le_uniform`,
`exists_uniform_outside_sqrt_bound` and `eventually_all_outside_lt` in
[GaussianFermiFisherTail.lean](../RiemannGaussian/GaussianFermiFisherTail.lean).
The qualitative limit now uses only divisor summability, without a
quantitative decay rate for the common zero-free margin.

For any common band margin `0 <= m <= 1/4`, put `sigma=1-m` and require
`m^2 <= B=b+c <= 1`, `b,c > 0`. If that margin encloses every actual zero
through height `H`, the selected-zero budget becomes

\[
\sum_{j\in J}w_j\sum_{\rho\in S}c(B,1-m,\omega_jt,\rho)
+\sum_{j\in J}w_j P(1-2m,B,\omega_jt)
\le \sum_{j\in J}w_j A_j
+\left(\sum_{j\in J}w_j\right)E_F(H),
\]

where `w_j >= 0`, `S` is any finite actual zero set in the band,
`2*abs(omega_j*t) <= H`, `P` is the literal Fermi prime-power sum, and

\[
A_j=\operatorname{polePair}(B,1-m,\omega_jt)-\frac{\log\pi}{4}
+\operatorname{digammaAverage}(1-2m,b,c,\omega_jt).
\]

The signed prime sum remains present. There is no nonnegative-cosine-test
assumption. `fermi_selected_zero_phase_budget_with_uniform_tail` discharges
the band-location premises with the proved global Fermi margin, for every
admissible finite family. The existing global margin keeps its original
definition; the later eventual zero-free theorem is not silently substituted
for an all-height bound.

## Constant-frequency prime/pole cancellation

The closed-strip bound and the genuine lower bound on zero ordinates give
the finite constant

\[
K_0=(4\sqrt\pi+2)\sum_\rho\frac{m_\rho}{1+(\Im\rho)^2}.
\]

At evaluation frequency zero, the inside divisor costs at most `K_0`,
and the outside divisor costs at most `E_F(H)`. The exact formula therefore
proves, under the same band and scale conditions,

\[
|A_0-P(1-2m,B,0)|\le K_0+E_F(H).
\]

The actual global margin discharges the band conditions. For every positive
tolerance, one height works for all admissible positive Gaussian splits,
making this residual smaller than `K_0 + tolerance`.

If `j0` belongs to the phase family and `omega(j0)=0`, the richer selected
budget is

\[
\begin{aligned}
&\sum_{j\in J}w_j\sum_{\rho\in S}c(B,1-m,\omega_jt,\rho)
+\sum_{j\in J\setminus\{j_0\}}w_j P(1-2m,B,\omega_jt)\\
&\quad\le\sum_{j\in J\setminus\{j_0\}}w_j A_j
+w_{j_0}K_0
+\left(\sum_{j\in J}w_j+w_{j_0}\right)E_F(H).
\end{aligned}
\]

Thus the full constant-mode pole and gamma term can be replaced by a
bounded residual while retaining all selected zero channels. If the
constant-frequency zero channel is also dropped, the signed phase budget
can already be applied directly to the reduced family. The new residual
estimate does not by itself establish a stronger resonant source bound.

Proofs: `abs_fermi_constant_prime_residual_le`,
`fermi_selected_budget_without_constant_pole` and
`eventually_constant_prime_residual_lt` in
[GaussianFermiConstantMode.lean](../RiemannGaussian/GaussianFermiConstantMode.lean).

## Remaining obstruction

Nonnegativity of the full cosine test does not imply nonnegativity after
its constant term is removed. The remaining prime combination therefore
cannot be dropped from this improved budget. The full complex moment filter
and its factorial orders likewise have no new positivity theorem here.

The original RH route still requires an independent cofinal bound
`Re(P_N) >= -1 + epsilon` with a fixed `epsilon > 0` for the original
normalized prime response. Its hypothetical zero limit remains negative
analytic multiplicity. The improved outside allowance and the bounded
constant-frequency residual do not supply that arithmetic estimate.

The latest proved eventual edge width remains `9/(50*log(abs(t)))`, with
an existential, unevaluated height threshold. These new modules make no
claim to improve that region or to prove RH.
