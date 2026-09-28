# Complementary divisor subsets reduce higher-count signed costs

[ZetaRieszComplementWindow](../RiemannGaussian/ZetaRieszComplementWindow.lean)
proves a general signed coefficient improvement for higher even prime
counts on the original Riesz core. It uses the reflected cutoff and the
existing exact divisor window. No carrier, phase, factorial order,
allocation factor or prime support is replaced, and no prime supply is spent.

The new [terminal comparison](../RiemannGaussian/ZetaRieszComplementWindow.lean)
`eventually_core_subset_higher_even_bounds` holds for every subset of the
original core, uniformly in height and count ceiling, on
`1/2<u<=10001/20000`. It can be applied to the exact signed rest of the
existing head payments. All other counts and every favorable selected
observation remain in the same sum. Both whole-sum cofinal targets in the
[multiplicity-aware endgame](zeta-riesz-joint-floor.md) remain open.

## Information retained from the reflected cutoff

Delete the two smallest prime logarithms `a<=b`, and write `w_i>=b` for
the remaining `k` logarithms. The exact two-prime cancellation leaves a
strict divisor window

\[
v-b<\sum_{i\in S}w_i<v.
\]

The original core eventually satisfies `2*log n<=3L`. Reflection gives
`3v<=a+b+sum w_i` throughout the two-prime integral.
If both `S` and its complement met the window, their upper bounds would
give `sum w_i<2v`, hence `v<a+b<=2b`. But any `S` with at least two
coordinates has weight at least `2b`, contradicting its upper endpoint.
Thus complementary middle-rank subsets cannot both occur.

For even `k>=4`, complementing a middle-rank family pairs all
`C=choose(k,k/2)` possibilities. At most `C/2` survive. Let `B` be the
largest binomial layer of the same parity **outside** the middle rank.
The existing LYM inequality then gives the sharper parity capacity

\[
\boxed{\quad \#\{\text{surviving subsets of middle-rank parity}\}
\le \frac{C+B}{2}.\quad}
\]

For clarity, if `m` central subsets survive, the LYM budget gives
`total<=B+(1-B/C)*m`. Substitute `m<=C/2`. The other parity keeps its
previous capacity. `shortWindowCapacity_le_parity` proves that neither
cost increases. This is a finite combinatorial inequality, not an
approximation of prime density.

The exact divisor encoding and two-smallest-prime integral transfer both
signed capacities to `VaughanLogAverage.riesz`. At even total prime count,
reflection preserves its sign. Multiplication by `-log n/L` then gives
bounds for the literal `SquarefreeVaughanLogSource.coefficient`.

## Checked quantitative instances

The units in this table are `(log n/L)*log(minFac n)`:

| Total prime count | Previous parity interval | New interval |
| --- | --- | --- |
| 8 | [-15, 20] | **[-15, 13]** |
| 10 | [-70, 56] | **[-49, 56]** |
| 12 | [-210, 252] | **[-210, 186]** |

The eight-prime upper coefficient cost falls by 35%. Its improvement
belongs to the lower carrier bound on negative cosines and to the upper
carrier bound on positive cosines. The ten-prime improvement has the
opposite orientation. The original signed cosine is retained.

`coefficient_eight_bounds` and the three `shortWindowCapacity_*` theorems
check these constants in Lean. The generic proof applies beyond these
three instances. The stronger existing six-prime interval `[-3,4]` is
preserved: the new core comparison selects only even counts at least eight.

`allowance_le_signed` retains the actual least prime before comparing
with the earlier mean-prime allowance. `costs_le_previous` proves that
both phase-sensitive charges are no larger than before. The terminal
sum theorem retains favorable observations term by term and leaves every
other count exactly in the same real observation. There is no absolute
value of the whole remaining carrier and no new free credit.

## Optional quantitative probe and its limits

Run `python3 scripts/probe_riesz_complement_window.py` for the deterministic
[exact-rational weight probe](riesz-complement-window-probe.json). It
computes the full signed subset hinge at several reflected cutoff shares,
including all subset signs. The inputs are positive integer **models of
logarithms**, not literal prime labels or an arithmetic certificate.

The probe attains the unchanged lower endpoint `-15` at eight coordinates
with weights `[19,491,568,611,614,668,706,729]` and length share `2/3`.
Thus the geometric refinement should not be described as shrinking both
sides at every count. Its sampled opposite extreme is much smaller than
the proved upper 13; further integral geometry could improve the bound,
but the samples do not establish a uniform estimate or prime realization.

These estimates strengthen the arithmetic charges in the existing rest.
They do not establish its cofinal `-79/1000` floor or `3/2` ceiling, and do
not prove a new zero exclusion. The growing supply and its signed opposing
rest must still be controlled together.
