# Joined low-count boundary: a single funded endpoint error

Local Lean work, 2026-10-03. The independent native floor remains open.

The preceding all-count payment leaves the literal scalar

\[
B_j=P_{1,j}^{\mathrm{central}}+P_{2,j}^{\mathrm{central}}
       +H_j^{\mathrm{original}}-H_j^{\mathrm{unallocated}}.
\]

Here each completed prime/semiprime term means its source-normalized real
part. The original head keeps its original owner interval, rough sieve,
factorial allocation and wider radial window. The unallocated correction
keeps every owner through the actual moving length and has no rough sieve
or factorial allocation. They are distinct arithmetic terms.

`ZetaRieszLowCountSignedBoundary` joins all four terms on their actual
integer-product labels **before** any norm. It proves:

* `headLabels_subset_correction`: every original head label also occurs
  in the full unallocated correction. This inclusion holds at every order.
* `head_le_correction`: on that label, the original head is exactly a
  nonnegative suballocation of the full correction.
* `completed_sub_correction_eq`: for a correction incidence `n=p*q`,
  with `p` the unique larger prime, the two Riesz hinges and the correction
  combine to the coefficient `-log(n)*log(q)/L`. The full product phase is
  preserved. No cofactor completion or prime-density replacement is made.
* `joinedCoefficient_bounds`: the **whole** remaining signed coefficient
  satisfies `-log(n) <= coefficient.re <= 0`. This includes ordinary
  primes, all distinct semiprimes, physical-prime failures, both original
  radial windows, the exact head allocation/sieve, and the extended-owner
  unallocated correction.

The resulting `joinedCoefficient_majorant` is used only for endpoint
errors. The complete interior sum is never norm-priced.

## Concrete payment in the same native ledger

The checked theorem `lowCountBoundary_sub_periods_bound` gives

\[
|B_j-B_j^{\mathrm{complete\ periods}}|
\le C_{\mathrm{edge}}\,r^{N_j},\qquad 0<r<1.
\]

**One** geometric budget covers all partial-period and outer-window terms
after the four components have been joined. The constant is the existing
existential `periodEdgeConstant`; this pass does not claim an evaluated
eventual threshold. Every complete-period phase remains literal.

`eventually_native_signed_period_bound` spends that payment alongside the
preceding all-count native budget:

\[
|\operatorname{Re}(u^{N_j+1}\,\mathrm{coreResponse}_j)
       +B_j^{\mathrm{complete\ periods}}|
\le \mathrm{nativeLowCountBudget}_j+C_{\mathrm{edge}}r^{N_j}\longrightarrow0.
\]

No old head-price credit or old four-component period budget is spent
again. This is an alternative ledger with one newly funded joined endpoint
error. It is a concrete geometric boundary saving, **not** a numerical
bound for the retained complete-period main.

The remaining sufficient arithmetic theorem is exactly a cofinal signed
aggregate upper bound

\[
B_j^{\mathrm{complete\ periods}}\le 399/5000+o(1).
\]

There are no remaining raw count-three-or-higher rows in this boundary.
The unresolved quantity is the first phase harmonic of the joined
ordinary-prime/distinct-prime-pair profile. Its coefficient sign alone
does not give the required upper bound: phases with negative cosine make
a positive contribution. Do not replace the signed aggregate by its
positive atom price; the balanced-semiprime price divergence is preserved.

## Optional numerical regression

`scripts/probe_riesz_low_count_signed_boundary.py` is outside builds and
CI. It retains the frozen **toy** orders 6/7/8, ideal length, older physical
schedule, exact finite factorial allocation and all complex phases. It
does not apply native eventual theorems at those orders.

All 27 frozen complex regressions pass. The entire joined coefficient
divided by `log(n)` lies in `[-1,0]` in each of the nine cases. At toy
`N=8`, the sum of positive **net whole-period** real contributions is
approximately `1.27e-6`, `2.36e-6`, and `2.93e-6` for heights 54, 65, and
100. The corresponding adverse-arc atom prices are approximately 0.0139,
0.0115, and 0.0175. These figures motivate retaining each signed period
and the signed aggregate; they do not certify any asymptotic floor or
native-order bound. The theorem's target is the net aggregate, not the
sum of positive period costs.

## Focused validation

Strict leaf elaboration and the targeted leaf build are followed by a
frozen compiled ordinary-root plus explicit-leaf audit. All namespace
linters and all-declaration transitive standard-axiom checks apply,
including private/generated helpers. Source, artifact and evidence pins
are recorded in `riesz-low-count-signed-boundary-audit.json`.

Work remains local and uncommitted. No root registration, public frontier,
README/explorer, wider gate, numerical certificate, zero exclusion or RH
claim is introduced.
