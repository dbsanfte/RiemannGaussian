# Corrected Suzuki divisor certificates

The September 9 reorientation steer proposes a finite divisor certificate
for the exact Suzuki mass–moment potential. The interface is now checked in
[SuzukiLegendreDivisorDual.lean](../RiemannGaussian/SuzukiLegendreDivisorDual.lean).
The required uniform arithmetic floor is still open. This is a conditional
route to RH, with no new zero exclusion or claim of novel mathematical priority.

## The sign correction

At the physical endpoint `N = count + 2`, write

\[
M_N=\sum_{d\le N}\frac{\Lambda(d)}{\sqrt d},\qquad
P_N=\sum_{d\le N}\frac{\Lambda(d)\log d}{\sqrt d},\qquad m_N=M_N-c>0.
\]

Here `c` and `C` are the existing exact Archimedean slope and intercept.
The potential and its trial form are

\[
B_N=P_N-2m_N(\log(m_N/2)-1)+C,
\qquad F_N(r)=C+4e^{r/2}+cr+P_N-rM_N.
\]

The steer correctly identifies a minimum but reverses the subsequent
pointwise inequality. **The valid inequality is `B_N <= F_N(r)`.**
An arbitrary trial value cannot certify a lower bound for that minimum.
The error is already visible for `m=2, r=2`: the proposed inequality
`Phi(m) <= r*m-4*exp(r/2)` would say `-4 <= 4-4e`, which is false.

Lean proves the exact replacement. With

\[
r_N^*=2\log(m_N/2),\qquad u=(r-r_N^*)/2,
\]

\[
F_N(r_N^*)=B_N,\qquad
F_N(r)-B_N=2m_N(e^u-1-u)\ge0.
\]

The checked theorems are `suzukiLegendreTrial_massCenter`,
`suzukiLegendreTrial_sub_potential_eq`, and
`suzukiMassLegendrePotential_le_trial`. Positivity of the actual corrected
mass is discharged from the existing Suzuki theorem chain. No abstract
convex-analysis assumption or numerical minimizer is used.

## Exact positive divisor transport

For any real weights, with no sign restriction on the weights themselves,

\[
K_w(d;N)=\sum_{\substack{1\le m\le N\\d\mid m}}w(m),\qquad
\sum_{m\le N}w(m)\log m=\sum_{d\le N}\Lambda(d)K_w(d;N).
\]

`sum_weight_mul_log_eq_vonMangoldt_divisorDual` proves this directly from
Mathlib's von Mangoldt divisor identity. The implementation uses the
divisibility filter, avoiding a quotient reindexing obligation at zero.

Put `f_r(d)=(log d-r)/sqrt d` and
`L_N(r)=sum Lambda(d)*f_r(d)`. Lean retains the full slack identity:

\[
L_N(r)-\sum_{m\le N}w(m)\log m
=\sum_{d\le N}\Lambda(d)(f_r(d)-K_w(d;N)).
\]

Consequently `K_w <= f_r` on **every** integer `1,...,N` gives a lower
bound on the linear form. These are
`suzukiLegendreLinearForm_sub_dual_eq` and
`suzukiLegendreLinearForm_ge_dual`. There is no zero hypothesis and no
separate estimate of mass and moment.

At `r=r_N^*`, the same minorant gives

\[
C+4e^{r_N^*/2}+cr_N^*+\sum_{m\le N}w(m)\log m\le B_N.
\]

This is `suzukiMassLegendrePotential_ge_of_divisorDual`.
At any other center, `suzukiMassLegendrePotential_ge_of_divisorDual_with_cost`
subtracts the **exact** cost `2*m_N*(exp(u)-1-u)` from the certificate.
The potential minus this corrected certificate is precisely the weighted
kernel slack above; moving the center does not excuse a missing cost.

## Connection to the actual RH criterion

`riemannHypothesis_of_suzukiMassLegendrePotential_eventually_bounded_below`
transfers any eventual finite lower floor for `B_N` to the existing
Suzuki canonical-gap criterion. The already proved comparison error is
bounded by its value at the initial cutoff; a finite exceptional prefix
is absorbed into the constant.

The capstone `riemannHypothesis_of_suzukiDivisorDual_eventual_floor` uses
an actual family `w_count`. Its two open hypotheses are eventual kernel
feasibility at `r_N^*` and a common finite lower floor for its certificate.
The conclusion is literal Mathlib `RiemannHypothesis`. **Neither hypothesis
is asserted as proved.** Alternatively, a certificate valid uniformly in
`r` could be evaluated at the exact center.

The formulation removes a zero-dependent oscillatory sum from this
interface. It does not show that the new arithmetic obligation is easier
than RH. The exact center still depends on the actual finite prime mass.

## Numerical search and its limits

[probe_suzuki_divisor_dual.py](../scripts/probe_suzuki_divisor_dual.py)
uses floating-point linear programming and checks all `N` divisor
constraints for every sampled endpoint. It reports the kernel slack,
the exact-center correction, and the residual in the finite slack identity.
A small positive-basis correction handles solver tolerance; this is still
floating-point exploration, not a rigorous certificate.

The screen includes uniform interval weights, dyadic interval weights,
and weights `(a_j+b_j*log(m/N))/sqrt(m)` on dyadic or quotient intervals.
Coefficients are optimized anew at each endpoint. The smoother family is
much more accurate than constant interval weights, but its sampled loss
still increases. With 16 subdivisions per dyadic shell:

| N | Actual potential, approximate | Constant-weight certificate | Smooth-weight certificate | Smooth weighted slack |
| ---: | ---: | ---: | ---: | ---: |
| 512 | 0.031816 | -0.602490 | 0.029636 | 0.002181 |
| 8,192 | 0.042489 | -5.077921 | 0.022374 | 0.020114 |
| 32,768 | 0.060458 | -11.826849 | 0.004783 | 0.055675 |
| 65,536 | 0.033514 | not run | -0.051749 | 0.085263 |
| 131,072 | 0.055309 | not run | -0.078626 | 0.133935 |

The largest displayed residual in the finite slack identity is below
`7e-10`; this checks numerical consistency, not exact arithmetic.
At `N=8192`, using `r=log N` and subtracting its approximate cost
`0.000114816` improves the smooth certificate to about `0.023602`.
Thus optimizing within a restricted weight family need not favor the
exact mass center, but the full cost must accompany that choice.

An unrestricted descending finite solve makes every kernel constraint an
equality. At `N=512` it reproduces the potential within `2e-14`. This is
only a diagnostic: the divisor matrix is triangular with unit diagonal,
so unrestricted exact weights recover the original arithmetic problem.
They supply no independent all-cutoff bound. No Möbius inversion is used
in the Lean interface.

Reproduce the main and larger screens in an environment with numpy,
scipy, and mpmath:

```bash
python scripts/probe_suzuki_divisor_dual.py --cutoffs 128 512 2048 8192 32768 --output /tmp/suzuki-dual.json
python scripts/probe_suzuki_divisor_dual.py --cutoffs 65536 131072 --models dyadic:16:log_affine --output /tmp/suzuki-dual-large.json
python scripts/probe_suzuki_divisor_dual.py --cutoffs 8192 --models dyadic:16:log_affine --center endpoint
```

The next useful result would be an explicit family with a proved feasible
kernel and a lower certificate bound uniform in the endpoint. More fixed
coarse-bin searches are paused. The observed drift does not prove that
every smoother or growing family fails, but none tested establishes that
uniform bound. Further numerical success must be measured by total
weighted slack and a provable formula for the certificate, not sampled
positivity or equality recovery.

## Small secondary pole-cancellation screen

The existing positive-composite response has a positive triple pole at
one and coefficient `-m^2` at a right-half zero. A finite nonzero combination
of its signed derivative moments cannot remove the pole at one: the
largest derivative order contributes its own strictly highest pole order.
For a finite Gram combination of imaginary shifts, the coefficient of
the pole at one is the sum, over equal-frequency groups, of the squared
norm of each group's combined coefficient. It vanishes only when those
groups cancel and the corresponding test is identically zero.

These are symbolic feasibility observations for these specific classes,
not new Lean theorems and not a no-go result for every positive transform.
They do not justify expanding that secondary branch in this slice.

## Validation

All ten public theorems pass direct warnings-as-errors, focused and full
builds, whole-project declaration lint, and a root-import verbose lint and
explicit axiom audit. Their only axioms are `propext`, `Classical.choice`,
and `Quot.sound`. No new RH milestone or arithmetic floor is claimed.
