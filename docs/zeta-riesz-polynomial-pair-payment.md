# Polynomial-small pair payment: supporting work, not the balanced-pair milestone

Local Lean slice, 2026-10-03. The independent `399/5000 = 0.0798`
upper bound on the surviving signed balanced-pair aggregate remains open.
This slice does **not** lower that target or its source gap.

The checked leaf is
[ZetaRieszPolynomialPairPayment.lean](../RiemannGaussian/ZetaRieszPolynomialPairPayment.lean).
It was validated locally in the slice and is now registered in the ordinary
root and public explorer by the combined checkpoint.

## Actual estimate

On the SAME `completePeriodLabels (joinedLabels u N) N y` support,
select distinct prime pairs whose uniquely smaller prime satisfies
`q <= N^16`. `literalSmall` sums the **original** `selbergDefect` on those
labels with the original phase, factorial kernel, owner/allocation/sieve
and moving-length masks.

`tendsto_literalSmall` proves its source-normalized complex norm tends to
zero under exposure in `1/2 < u <= 10001/20000`. Simplicity is not needed
for this particular payment. This is a conditional arithmetic payment,
not an independent floor estimate.

## Why this completion is legitimate

Only the large prime is completed. On every genuine interior selected
pair, `log q <= N/10` eventually and `log p > L_N`. The original head and
unallocated correction are therefore absent **by their exact masks**.
The literal coefficient is exactly

\[
-\frac{\log(pq)\log q}{L_N}
+\frac{2\log p\log q}{\log(pq)}.
\]

The two complete rows retain their product phase and all factorial
orders. Existing complete prime-product bounds control them by the
arithmetic mass

\[
M_N=\sum_{q\le N^{16},\ q\text{ prime}}
 \log q(1+\log q)q^{-\beta}
\]

divided by `L_N` or by `N`. No lower-order allocations are discarded.
With real-power slack `1/128`,

\[
M_N\le D_\beta N^{16(1-\beta+1/128)},\qquad
16(1-\beta+1/128)\le\frac{629}{5000}<\frac15.
\]

Thus these completed budgets decay faster than `N^(-4/5)`; their
constants and eventual thresholds are not evaluated. The actual damped
floor length is retained and its existing linear lower bound is used.

`exists_literalSmall_completion_bound` separately proves that the
complete rows differ from the **literal selected sum** by at most
`C_edge * rate^N`, with `rate < 1`. On the strict interior the coefficients
agree exactly. Duplicated/repeated-prime incidences, missing radial labels
and partial-period edges are kept and paid by the previously checked
uniform exterior theorem. This does not infer a hard-share limit from
separate complete-leg phases or complete a composite cofactor.

`eventually_native_largePairRest_floor` spends the new payment once in the
original whole-floor inequality. The remaining aggregate stays signed.

## Explicit limitation and next required milestone

`balancedProducts_disjoint_literalSmall` proves that every old troublesome
balanced box remains completely outside the new paid population. The
preceding absolute-price divergence remains relevant. No norm allowance
for the balanced sum is introduced.

Under a simple exposed zero, the remaining signed aggregate still carries
the OLD source. At the radius ceiling its value is approximately
`0.07987179703494418`, exceeding `0.0798` by approximately
`0.00007179703494418`. These decimals calibrate the already-proved source;
they are not an actual-prime experiment or an independent bound.

Accordingly this payment **does not meet** the user's balanced-pair pass
criterion. The next decisive result must be an independent signed
`399/5000 + o(1)` upper bound, or a proved saving on the balanced aggregate
that demonstrably advances it. Another source equivalence, positive
majorant improvement or polynomial-prefix deletion is insufficient.

All previous payments/no-gos are retained. There is no cofinal floor,
multiple-zero ceiling, zero exclusion or RH claim. Validation is focused:
strict leaf, targeted build, frozen compiled ordinary-root plus explicit
leaf import, fourteen namespace linters and all-declaration standard-axiom
audit. No commits, pushes, subagents or public/root registration changes.
