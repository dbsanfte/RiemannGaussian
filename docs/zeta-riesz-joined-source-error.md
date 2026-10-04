# Whole joined source-error payment

This local slice proves a quantitative error bound for the **existing
retained signed main**. It does not improve the independent floor constant.
The head remains `49db91eb2f5ea148c82b00bae9f241a836c272fe`; nothing is
committed, pushed, root-registered or added to ordinary CI.

For an exposed right-half zero, put

\[
u=\tfrac32-\Re\rho,\qquad m=\operatorname{mult}(\rho),\qquad
a_k=u^{k+1}\operatorname{ordinaryPrimeLogMoment}_k
  (\tfrac32+i\Im\rho).
\]

The new checked result is

\[
\sum_{k\ge0}|a_k+m|<\infty.
\]

Write this sum as \(D_\rho\). The proof isolates the selected mode using
the existing exact canonical moment identity. Competing direct modes,
reflected error channels, the zeta pole and the analytic Cauchy residual
have absolutely summable geometric majorants. Proper prime powers have
their independently proved `10001/15000` majorant. Orders zero and one
are retained. Every analytic multiplicity remains; simplicity is unused.

For the unchanged joined four-slot functional \(H_N\), the existing
whole-quadratic difference inequality now gives the explicit bound

\[
\left|H_N(a)-H_N(-m)\right|
\le \frac{22(m+D_\rho)D_\rho}{N},\qquad N\ge65536.
\]

The proof needs no separately assumed array bound: \(|a_k|\le m+D_\rho\)
follows from the same summable mass. The exact trace, central, successor
and logged-prefix indices stay joined. No low-order exceptional mass,
count-dependent positive allowance or independent main norm is introduced.

The existing whole-support bridge then proves for the literal carrier

\[
\begin{aligned}
\left|\operatorname{prefixPairDefect}_N-H_N(-m)\right|
&\le \operatorname{wholeCompletionBudget}_N
 +\operatorname{squareBudget}_N\\
&\quad+\frac{22(m+D_\rho)D_\rho}{N}.
\end{aligned}
\]

This is also a two-sided bound on the real difference. Both previous
geometric budgets are spent once. Proper powers are already included in
\(D_\rho\), so the separate proper-power insertion price must not be
added again. No complete-leg limit is transported through a hard share
projection: the already-proved whole symmetric completion licenses the
specific existing factorial quadratic.

## What remains

The source-error term tends to zero at the explicit inverse-order rate.
The selected evaluation does **not** tend to zero. Its previously proved
limit is \(m^2(1-c_{\rm ret}(u))\). For a simple source at the radius
ceiling, this is about `0.07987179703494418`, above the unchanged
independent upper target `399/5000 = 0.0798`.

Consequently this slice pays an actual conditional whole-sum error but
provides **no independent saving of the selected residue**, no certified
entry order and no new zero exclusion. \(D_\rho\) depends on the unknown
zero and its spectral gaps; its numerical size is not certified.
The remaining arithmetic task is still the independent signed bound on
the selected residue at heights outside existing zero-free coverage.
The higher-multiplicity ceiling also remains open.

## Focused checks and regression

- Lean: [`ZetaRieszJoinedSourceError.lean`](../RiemannGaussian/ZetaRieszJoinedSourceError.lean).
- Optional strict namespace/axiom check:
  [`CheckRieszJoinedSourceError.lean`](../scripts/CheckRieszJoinedSourceError.lean).
- Optional algebra probe:
  [`probe_riesz_joined_source_error.py`](../scripts/probe_riesz_joined_source_error.py).

The probe checks 20 **synthetic finite-error** arrays at 100 digits. Eight
small-order cases reassemble all four original factorial slots before
checking the signed difference. Swapped trace incidences and orders zero
and one remain; the low/low quadratic vanishes only by its exact total
index in these finite-support regressions. Positive and negative errors
give opposite signed inverse-order corrections, so the probe supplies no
universal correction sign. At larger orders it uses the existing stated
moving-length floor-error bound and labels that approximation explicitly.
It samples **zero primes and zero zeta values**, and assigns no numerical
value to the actual \(D_\rho\).

The strict leaf check and namespace/standard-axiom audit are local and
optional. Previous proof/probe snapshots and concurrent semiprime work
remain intact. See [`riesz-joined-source-error-audit.json`](riesz-joined-source-error-audit.json)
for the exact source and artifact pins.
