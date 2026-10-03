# Joint signed payment of rough rows and their prime-pair head

Local work after `194a361762f404a8f4473298b25d96fbae0bb56e`.
The whole floor **−399/5000**, ceiling **42/25**, restricted contradiction
and RH remain open. Public endpoints are unchanged.

The checked module is
[ZetaRieszRoughPrimePairCancellation](../RiemannGaussian/ZetaRieszRoughPrimePairCancellation.lean).
The new arithmetic theorem bounds a **joint signed expression** on actual
native labels. It does not assert that the rough packet or its prime head
is small separately.

## Literal population and retained masks

Use the original dyadic orders, physical prime set, Riesz length and
factorial allocation. Select squarefree composite labels `n=p*a` with

- an original intermediate owner satisfying `51N/50 <= log p <= 5N/4`;
- the exact core window `39N/20 < log(p*a) <= 203N/100`;
- no cofactor prime at or below `N^3`;
- the actual native prime-count ceiling.

The complete core geometry proves `a<p`, so the owner is uniquely the
largest prime. `rows_injective` proves there is no repeated product label.
`eventually_labels_subset_native` proves every original native mask,
including the absence of internal cancelling/dominant pieces. The full
original `residualCoefficient`, phase and `boundedShare` allocation remain.

`labels_disjoint_smallTags` proves this population is disjoint from the
previously paid least-small-prime rows. Both populations can therefore be
removed from the same native cutoff ledger without spending a label twice.
Other owner geometries and partial cofactor windows are still retained.

## What has actually been bounded

Let `P_j` denote the source-normalized **real** rough packet with the full
original allocation. Let `H_N = nativeHead u y N`. For fixed `|y|>=54` and
`1/2<u<=10001/20000`, the independent arithmetic result is

\[
\boxed{|P_j+H_{N_j}|\le E_j\ \text{eventually},\qquad E_j\longrightarrow0.}
\]

These are `eventually_packet_joint_bound`, `budget_tendsto` and
`tendsto_packet_add_nativeHead`. Their hypotheses contain no selected zero,
exposure, rightmost-zero condition, or unproved cancellation estimate.
Complex norm decay is not asserted.

The ordinary-prime correction is exact. `eventually_nativeHead_eq_prime_pairs`
identifies it as

\[
H_N=u^{N+1}\sum_{p\in\mathrm{owners}_N}
 \frac{L_N-\log p}{L_Np}
 \sum_{\substack{M_p<q\le X_p\\q\ \mathrm{prime}}}
 \frac{\mathrm{ownerAmplitude}(N,\log p,q)}q
 \cos\!\bigl(y(\log p+\log q)\bigr),
\]

where `M_p=floor(exp(39N/20-log p))` and
`X_p=floor(exp(203N/100-log p))`.
Every prime cofactor in this window already exceeds `N^3` eventually;
the rough sieve on the prime head is therefore exactly one.
This is the smooth singleton-owner extension at ordinary-prime cofactors,
not the unrelated joined marked weight that vanishes on two-prime labels.
That older two-prime cancellation cannot be used to erase this head.

## How the saving is obtained

The dyadic comparison retains **row + head − density main** together.
At most `N` capped dyadic windows cover the full cofactor interval. Their
density scalar and prime head are joined before the signed phase estimate
is applied. The exact cutoff scalar is

\[
A_{N,p}=\sum_{D=1}^{R_N}
 \bigl((L_N-\log p-\log D)_+
       -(L_N-\log p-\log(D+1))_+\bigr)
 \mathrm{roughDensityPrefix}(\mathrm{smallPrimes}_N,D),
\quad R_N=\lfloor e^{N/2}\rfloor.
\]

Only after the full integer-lattice phase sum has its saving is this
scalar bounded by `(L_N-log p)*(1+log R_N)`. Divisor signs are never
discarded before that phase payment. Owners aggregate by `sum 1/p`,
rather than their exponentially large cardinality.

The complete-row joint price is explicitly

\[
B_N=8uC(6+|y|)(N+1)^3e^{-3N/500}
     +8(N+1)^2\,\mathrm{ownerSamplingBudget}(u,y,N).
\]

Here `C` is the previously proved counting constant. The second term
uses the checked full-window phase bound, with geometric factors
`exp(-N/200000)` and `exp(-N/4)`. Thus `jointBudget_tendsto` is a theorem,
not an extrapolation from sampled orders. All initial thresholds are
existential; no numerical starting native order is certified.

The literal native count deletion costs exactly the previous
`allowance j` once on the rough population, justified by injective owner
incidences. The restricted nonowner transfer costs the existing
`nonownerBudget N_j` once. Hence

\[
E_j=B_{N_j}+\mathrm{allowance}(j)+\mathrm{nonownerBudget}(N_j)
\longrightarrow0.
\]

The small-tag payment retains its own independently proved budget. These
are signed totals, not claims that their absolute cutoff variations are
small.

## The whole floor now uses the joint payment

`paidIncrement` uses the same native cutoff profile and logarithmic null
coefficients. Its signed sum is exactly `P_j`. Subtract the old small-tag
increment and this rough increment **before** complete-period clipping.

`eventually_step_sub_paid` proves that the remaining main is exactly on
the native squarefree labels minus both disjoint populations. The whole
free tangent correction remains joined. This alternative still uses
zero imaginary tilt because the payment is a real signed estimate.

Writing `D_j` for the resulting joined `restCost`, the checked inequality
for the original carrier is

\[
\boxed{
 \operatorname{Re}(u^{N_j+1}\mathrm{joinedPhysical}_j)
 \ge -D_j-H_{N_j}-E_j^{\mathrm{small}}-E_j
       -\mathrm{nativeError}_j\quad\text{eventually}.
}
\]

The head is retained as **one signed scalar**. There is no termwise
absolute prime allowance, split by count, or double spending of the
old tangent or nonowner credits.

The new `price` takes the minimum of the previously valid small-tag price
and `D_j+H_{N_j}+E_j^{small}+E_j`. `price_le_previous` proves no regression.
It does not certify a positive fraction of the global deficit: deletion
can change a particular clipped period cost in either direction.

## What remains open

The remaining numerical premise is still

\[
\mathrm{price}_j\le399/5000\quad\text{cofinally}.
\]

`false_of_cofinal_price` is a **conditional** simple-exposed-zero endpoint.
The independent signed bound on `D_j+H_{N_j}` is not proved. In particular,
the ordinary-prime head must not be dropped, norm-paid using the old
two-prime marked weight, or declared source-small by this joint theorem.

The next target is the correlation of this literal prime-pair head with
the remaining signed cutoff periods and owner/window exteriors. The many
composite prime counts in the selected complete-owner slab no longer
need separate positive allowances, but the whole floor is not closed.

## Scoped verification

See [the focused audit](riesz-rough-prime-pair-cancellation-audit.json).
It records strict source checking, the targeted leaf build, all namespace
linters and standard-only transitive axioms for every compiled declaration,
including private/generated helpers. The audit imports the frozen compiled
ordinary root plus the explicit leaf. No root-source rebuild, wider gate,
public README/explorer change, commit or push is part of this slice.
