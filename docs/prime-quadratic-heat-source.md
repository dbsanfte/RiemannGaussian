# The selected prime source at quadratic Gaussian widths

The complete actual residual heat now tends to zero at every fixed positive
quadratic relative width. Lean combines uniform central geometric decay with
a global Euler-line bound and a quantitative Gaussian tail estimate. Thus the
full corrected prime arithmetic heat retains its negative selected source
on this explicit schedule. The independent signed arithmetic lower bound
remains open. Cutoffs and prime exclusions are fixed throughout this slice.

## Exact pole average, with the complex phase retained

Let `u > 0` be the real distance from the Euler center to the selected zero,
and let `M_B = sqrt(4*pi*B)` for `B > 0`. The normalized pole factor is

\[
A_N(u,B)=\frac{u^{N+1}}{M_B}
 \int_{\mathbb R}e^{-y^2/(4B)}(u-iy)^{-N-1}\,dy.
\]

In [GaussianSimplePoleHeat.lean](../RiemannGaussian/GaussianSimplePoleHeat.lean),
`integral_laplace` proves the factorial Laplace formula with complex damping.
`integrable_poleMoment` and `poleHeat_eq_attenuation` pay for the full
product-integral interchange and identify

\[
A_N(u,B)=\int_0^\infty
 \underbrace{\frac{u^{N+1}t^N}{N!}e^{-ut}}_{g_{N,u}(t)}
 e^{-Bt^2}\,dt.
\]

Thus the full complex average is real and positive. Individual complex pole
values need not be positive. The phase cancellation is retained until the
exact infinite integral is evaluated.

Lean evaluates both moments

\[
\int_0^\infty g_{N,u}(t)\,dt=1,\qquad
\int_0^\infty t^2g_{N,u}(t)\,dt=
 V_N(u):=\frac{(N+1)(N+2)}{u^2}.
\]

Integrating the exponential tangent, and then centering that tangent at the
exact second moment, proves

\[
e^{-B V_N(u)}\le A_N(u,B)\le1,\qquad
|A_N(u,B)-1|\le B V_N(u).
\]

The terminal theorems are `poleHeat_re_bounds` and
`norm_poleHeat_sub_one_le`. They apply to every order and every positive
width. The gamma integral and the centered exponential tangent are standard
mathematics; no historical novelty claim is made.

## A mathematically defined family of useful widths

For every relative width `c > 0`, set

\[
B_N(c,u)=\frac{c u^2}{(N+1)(N+2)}.
\]

Its complete loss parameter is exactly `c` at every order. The theorems
`poleHeat_quadraticWidth_bounds` and
`norm_poleHeat_quadraticWidth_sub_one_le` prove

\[
e^{-c}\le A_N(u,B_N(c,u))\le1,\qquad
|A_N(u,B_N(c,u))-1|\le c.
\]

A fixed `c` therefore retains a nonzero fraction of the source without an
unevaluated diagonal choice. For any positive sequence `c_N -> 0`,
`tendsto_poleHeat_quadraticWidth` proves that the complete unit pole source
is recovered while the order grows. These are all-family analytic bounds;
no numerical coefficient search is involved.

## The actual full arithmetic response

[ZetaPrimeClearedHeatSource.lean](../RiemannGaussian/ZetaPrimeClearedHeatSource.lean)
uses the actual divisor polynomial `q`, normalized to `q(rho)=1`, and the
fixed-support ordinary-prime continuation `F_(D,S)` constructed in
[ZetaPrimeClearedSource.lean](../RiemannGaussian/ZetaPrimeClearedSource.lean).
For a hypothetical right-half zero, put

\[
s_\rho=3/2+i\operatorname{Im}\rho,\qquad
u=3/2-\operatorname{Re}\rho,\qquad m=m_\rho.
\]

The actual residual is

\[
R_{D,S,\rho}(z)=q(z)F_{D,S}(z)+\frac{m}{z-\rho}.
\]

Its Gaussian moment is genuinely integrable on the original Euler line.
Writing `M_N` for the signed factorial derivative, define

\[
E_N(B)=\frac{u^{N+1}}{M_B}\int_{\mathbb R}e^{-y^2/(4B)}
 M_N(R_{D,S,\rho})(s_\rho-iy)\,dy.
\]

`normalizedClearedPrimeHeat_eq_source_add_remainder` proves the exact
identity for the entire corrected arithmetic heat,

\[
\mathcal P_N(B)=-m A_N(u,B)+E_N(B).
\]

Here `mathcal P_N` is the genuine complete prime series with every downward
Leibniz order and every Hermite correction from
[ZetaPrimeClearedHeat.lean](../RiemannGaussian/ZetaPrimeClearedHeat.lean).
The identity does not replace that arithmetic series by its pole model.
At the quadratic width, `normalizedClearedPrimeHeat_re_le` gives

\[
\operatorname{Re}\mathcal P_N(B_N(c,u))
 \le -m e^{-c}+\operatorname{Re}E_N(B_N(c,u)).
\]

## Uniform control near the central frequency

The original compact clearing radius is `R_0=5/4-Re(rho)/2`, with
`u<R_0`. Set

\[
r_0=\frac{u+R_0}{2},\qquad \delta=\frac{R_0-u}{4}.
\]

Then `delta>0`, `u<r_0`, and `delta+r_0<R_0`. The theorem
`exists_clearedPrimeRemainder_analyticRepresentative` constructs an analytic
representative of the actual residual on the whole closed clearing disc,
including every removed pole, and proves equality of the original Euler
germs.

Cauchy's estimate on all the nested discs yields
`exists_clearedPrimeRemainder_central_bound`:

\[
\exists C>0\ \forall N\ \forall |y|\le\delta,\qquad
\left|u^{N+1}M_N(R_{D,S,\rho})(s_\rho-iy)\right|
 \le C\left(\frac{u}{r_0}\right)^N,
\qquad \frac{u}{r_0}<1.
\]

The same neighborhood, radius and constant work for every order. The bound
is independent of the Gaussian width. This supplies the uniform input for
the central portion of the residual heat integral.

## Global control and the complete residual limit

[ZetaPrimeClearedHeatGrowth.lean](../RiemannGaussian/ZetaPrimeClearedHeatGrowth.lean)
first bounds the actual prime continuation uniformly on `Re z >= 5/4`,
using absolute Euler convergence. On quarter-discs about every point
`s_rho-i*y`, the clearing polynomial has a common polynomial envelope, and
the selected denominator stays at least `1/4` from zero. Cauchy's estimate
then gives `exists_clearedPrimeRemainder_global_bound`:

\[
\exists A>0\ \forall N,y,\qquad
\left|u^{N+1}M_N(R_{D,S,\rho})(s_\rho-iy)\right|
 \le A(4u)^N(1+y^2)^d,\qquad d=\deg q.
\]

The constant and degree are independent of the order and frequency.
The general theorem `norm_average_le` in
[GaussianCentralTailBound.lean](../RiemannGaussian/GaussianCentralTailBound.lean)
combines a central bound with any such polynomial global envelope. Put

\[
J_d=\int_{\mathbb R}(1+y^2)^d e^{-y^2/8}\,dy,\qquad
T_{\delta,d}(B)=\frac{J_d}{M_B}e^{-\delta^2/(8B)}.
\]

The envelope is proved integrable. For `0<B<=1`,
`exists_normalizedClearedPrimeRemainderHeat_bound` in
[ZetaPrimeClearedHeatDecay.lean](../RiemannGaussian/ZetaPrimeClearedHeatDecay.lean)
proves for the original complete residual

\[
|E_N(B)|\le C\left(\frac{u}{r_0}\right)^N
             +A(4u)^N T_{\delta,d}(B).
\]

At `B=B_N(c,u)`, the general quantitative tail theorem gives

\[
T_{\delta,d}(B_N)\le
 \frac{J_d}{M_{cu^2}}(N+2)
 \exp\!\left[-\frac{\delta^2}{8cu^2}(N+1)^2\right].
\]

This includes the complete Gaussian mass factor. Its Gaussian decay in the
order absorbs every fixed exponential rate, as proved by
`tendsto_pow_mul_tailAllowance_quadraticWidth`. The quadratic widths tend
to zero, so the restriction `B<=1` holds eventually. Consequently
`tendsto_normalizedClearedPrimeRemainderHeat_quadraticWidth` proves

\[
E_N(B_N(c,u))\longrightarrow0 \quad\text{for every fixed }c>0.
\]

The theorem `eventually_normalizedClearedPrimeHeat_re_le` therefore gives,
for every `epsilon>0`, eventually

\[
\operatorname{Re}\mathcal P_N(B_N(c,u))\le -m e^{-c}+\epsilon.
\]

In particular `eventually_normalizedClearedPrimeHeat_re_le_negative`
proves the upper bound `-m*exp(-c)/2` eventually. These are bounds on the
complete actual prime heat, retaining all Leibniz and Hermite corrections.
The subsequent [exact polynomial operator](prime-cleared-heat-operator.md)
combines those corrections inside each original prime summand and exposes
their derivative and adjacent-order coupling, without changing this source.
The constants can depend on the fixed cutoff, sieve, selected zero and
relative width; no uniformity for moving cutoffs or arbitrary varying
relative widths is asserted.

## What remains

An independent signed arithmetic bound for the corrected prime expression
is required for a contradiction. A cofinal lower bound exceeding
`-m*exp(-c)` by a fixed positive amount would conflict with the proved source.
Proving the existence and stability of a negative source under a hypothetical
zero does not exclude that zero. The original cofinal lower bound with a
fixed gap above `-1` and RH remain open. No new zero-free region is claimed.
