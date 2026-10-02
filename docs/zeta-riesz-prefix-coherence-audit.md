# Many bins and the actual prefix energy

The whole-carrier `-79/1000` floor remains **open**. This is a negative
audit of automatic diagonal/orthogonality estimates, together with an
exact constant-projection test. No new population is paid at source scale.

Proof: [ZetaRieszPrefixCoherenceAudit.lean](../RiemannGaussian/ZetaRieszPrefixCoherenceAudit.lean).
Validation: [proof audit](riesz-prefix-coherence-audit.json).

## A coherent channel on actual integers

Use the existing signed prefix, with the actual phases and funding inside
the weights:

\[
\Phi(k)=\sum_{n\in S} w(n)\sum_{\substack{d\mid n\\d\le k}}\mu(d).
\]

Every label has sharp prefix one at cutoff one. On a rough support with
`Q < minFac(n)` for every selected label, this persists through `1 <= k <= Q`:

\[
\Phi(k)=M,\qquad M=\sum_{n\in S}w(n).
\]

`phaseEnergy_coherent_lower` proves, on the SAME existing active profile,

\[
E\ \ge\ M^2\sum_{\substack{k\text{ active}\\k\le Q}}\frac1k.
\]

No prime incidence, count, bin, owner, radial mask or physical support is
completed. `funded_correlation_one` keeps the original rejoined funding
coefficients inside this moment, including overlapping paid/supply labels.
This does **not** assert a common roughness threshold for the entire unpaid
support; the cutoff-one identity needs no such assumption.

If cutoff one is active, a diagonal estimate `E <= C sum w(n)^2` valid
for **every** real weight on a nonempty support must have `C >= card(S)`.
`diagonal_coefficient_lower` proves this on the actual integer prefix, not
on synthetic bin columns. Many-bin occupancy therefore cannot justify a
small universal diagonal coefficient. This does not say that the specific
carrier weights are coherent or rule out their arithmetic cancellation.

For the existing one-sided cost, `negativeCost_one_lower` says that when
the complete first increment is adverse,

\[
C^-\ge-M\bigl(f(1)-f(2)\bigr).
\]

This is a necessary constraint for that **sufficient cost criterion**, not
a lower bound on the actual floor deficit and not an impossibility result
for other signed floor arguments.

## The common channel can be projected out exactly

The audit also checks a possible bypass. If `f(1)=f(X+1)`, then

\[
\sum_{k\text{ active}}(\Phi(k)-c)\,\Delta f(k)
=\sum_{k\text{ active}}\Phi(k)\,\Delta f(k)
\]

for every constant `c`. `constant_projection_pairing` proves this by exact
telescoping. Thus coherence does not preclude every projected energy method.
All original low divisor channels are retained in this identity.

The optional [actual-integer probe](../scripts/probe_riesz_prefix_coherence.py)
chooses equal profile endpoints, then optimally subtracts the constant
component for the full energy. Across nine cases at orders `4,5,6` and
heights `54,65,100`, the centered/full cost ratio is
`0.997574..0.999998`: at most about **0.243%** reduction. The one-sided cost
ratio ranges from `0.970172` to `1.027739`; this projection can make the
one-sided price worse. It gives no observed geometric rate.

These are generic finite regressions using test length `11N/8`, exact
small-order allocation zero, original integer divisor signs and phases.
They do **not** use the rounded moving length, actual unpaid count-56+
support or funding witness. They do not certify a floor or an asymptotic
obstruction to projection on the actual unpaid support. The probe is
outside ordinary CI.

## Literature applicability

[Liu's weighted multiplicative-sum theorem](https://arxiv.org/html/2210.01671v3#S2)
assumes a multiplicative squarefree coefficient with prime value
`g(p)=k/p+O(p^(-1-theta))`, and gives logarithmic asymptotics with constants
depending on the fixed smoothing order. It does not directly estimate
the current moving-order, hard-masked, phase-weighted joint carrier. A
fixed-order logarithmic asymptotic is not the fixed power saving needed
here. This is an applicability audit, not a claim that the paper's methods
cannot be adapted.

The remaining arithmetic question is cancellation in the **actual joined
signed weights and cutoff correlations**, after the exact funding ledger
has been assembled. Occupancy is not a bound on weighted mass distribution
or off-diagonal covariance. No new floor, ceiling or zero exclusion follows.
