# Probe of the unpaid prime / joined-semiprime period coupling

Local numerical research, 2026-10-03. **No new arithmetic floor or ceiling
is proved in this pass.** The existing independent higher-count and endpoint
payments remain unchanged.

The target is still the net signed complete-period scalar from
`ZetaRieszLowCountSignedBoundary`:

\[
B_j=\operatorname{Re}\bigl(P_{1,j}+P_{2,j}
               +H_j^{\rm original}-H_j^{\rm unallocated}\bigr)
       \le 399/5000+o(1)
\]

cofinally. The original head and the full unallocated correction are joined
on their actual product labels before examining the pair population. All
prime phases, both radial windows, older physical masks and finite factorial
allocation weights remain in the numerical arithmetic cases.

## A repeated cross-count pattern

The optional probe tests 52 heights (54 through 154 in steps of two, plus
65) at each toy order. On each complete period it evaluates the signed
ordinary-prime total and the signed **joined** semiprime total. Their median
correlations are:

| Toy order | Median period correlation | After smooth-density subtraction |
|---|---:|---:|
| 6 | -0.95075 | -0.95075 |
| 7 | -0.99142 | -0.99142 |
| 8 | -0.98561 | -0.98561 |
| 9, held out | -0.99049 | not evaluated |

The smooth comparison retains the two Riesz hinges and the moving ideal
length, correction/head conditions, binomial allocation and full phase at
each quadrature node. It is only a diagnostic against `dx/log(x)`, **not**
a prime-density transport estimate. Nine 16-versus-24-node rechecks differ
by at most approximately `6.82e-16`; these are floating comparisons, not
certified errors.

This supports investigating a coupled arithmetic mechanism across the two
counts. It does not establish an exact sign rule. At order 8 and height 142,
both complete aggregate contributions are positive:

\[
P_1\approx3.98\cdot10^{-6},\quad
P_2+H^{\rm original}-H^{\rm unallocated}
       \approx3.42\cdot10^{-6}.
\]

## Keep cancellation across periods too

The separate stress scan reaches height 51200. At that height the period
correlation is about -0.430, -0.644 and -0.784 at orders 6, 7 and 8.
At order 8 the net whole-period real sum is about `-3.77e-5`, although the
sum of positive **joined** period contributions is about `5.32e-4`.
Thus a bound on every period, or on positive period totals alone, can lose
useful cancellation. The target is the signed aggregate.

The report's cross-count credit is the finite identity

\[
\sum_k(P_{1,k})_++\sum_k(P_{2,k}^{\rm joined})_+
       -\sum_k(P_{1,k}+P_{2,k}^{\rm joined})_+\ge0.
\]

Its cross-period credit similarly compares positive joined periods with the
positive part of their **net** sum. These diagnostics are not new native
payments, and must not be applied to the proved-divergent positive atom price.
Their percentages do not measure progress toward the cofinal floor.

## Why correlation alone is insufficient

Even perfect opposition permits a nonzero mean. The canonical source-side
calibration at `u=10001/20000` gives

\[
c_{\rm ret}\approx0.920128202965056,
\qquad1-c_{\rm ret}\approx0.079871797034944>0.0798.
\]

The gap is approximately `7.18e-5`. A schematic unit prime channel and a
pair channel `-c_ret` oppose perfectly and still miss the required bound.
This is a calculation from the existing source, not an independent
arithmetic estimate or a numerical certificate.

The Selberg identity already formalized in `SuzukiLogarithmicConvolution`
is a plausible structural comparison. Its classical PNT use joins the
prime and prime-pair measures before estimating; see
[Tao's Banach-algebra proof](https://terrytao.wordpress.com/2014/10/25/a-banach-algebra-proof-of-the-prime-number-theorem/).
The estimate stated there does not by itself provide the required fixed
source-scale saving for these literal moving cutoff/allocation weights.
The existing `SuzukiConvolutionSource` also explicitly warns that vanishing
of the simple-zero quadratic source does not exclude that zero. No new
Selberg-to-masked-carrier theorem is claimed here.

## Reproducibility and scope

`scripts/probe_riesz_low_count_period_coupling.py --low-count-only` enumerates
only ordinary primes and distinct prime products, using their exact
one-/two-prime hinge formulas. It avoids recomputing already-paid higher
counts. All 27 comparisons with the frozen full-divisor probe pass; the
held-out order nine is an additional uncertified toy computation.

All orders use the ideal length `-2N log(u)` and older physical/factorial
schedule. They are **not** native dyadic evaluations. No eventual theorem is
applied at these toy orders. The independent sign-bias diagnostic replaces
the phase and is expressly separate from the actual fixed-height character.
It supplies no arithmetic floor.

The final three reports contain 244 evaluations, representing 235 distinct
order/height cases. Repeated frozen regressions are not independent
certificates. Source and report pins are in
`riesz-low-count-period-coupling-audit.json`.

The next mathematical result must bound this **whole signed** prime/pair
profile cofinally. Strong numerical correlation, a fitted slope, a generic
PNT/Abel error, or a new positive period price does not supply that result.
No Lean source, root registration, public frontier, README/explorer, CI,
commit or push is changed by this numerical pass. The floor, multiplicity
ceiling, restricted zero exclusion and RH remain open.
