# Whole signed pair completion: an independent geometric boundary payment

The remaining period and radial masks of `prefixPairDefect` now have a
proved global completion payment. This is a bound for their difference,
not a bound for the retained signed main. The independent cofinal target
remains `Re prefixPairDefect <=399/5000+o(1)`; the floor and multiple-zero
ceiling remain open.

The leaf module is
[`ZetaRieszPairWholeCompletion.lean`](../RiemannGaussian/ZetaRieszPairWholeCompletion.lean).
For `1/2<=u<=10001/20000`, `54<=abs(y)` and `N>=65536`, it proves that a
single finite constant `C>=0`, independent of `u,y,N` and the exhaustive
prime prefix, satisfies

```math
\left\|\mathrm{finitePrefixPairDefect}_{N,P}
      -\mathrm{prefixPairDefect}_N\right\|
\le C\,e^{-N/1{,}000{,}000}
```

for every sufficiently large finite prime-prefix cutoff `P`, at each
fixed `N`. The theorem does not give a numerical value or small-order
smallness for `C`. This geometric cost tends to zero cofinally.

`finitePrefixPairDefect` sums the same symmetric factorial coefficient,
minus the same signed Selberg coefficient, over every distinct-prime pair
in that finite prefix. No square is inserted into the literal carrier.
The complete convolution identity accounts for its single whole square
diagonal explicitly.

## Why this completion is paid

Every genuine distinct-prime product in the strict interior
`1.971N+1<log(n)<=2.029N-1` already belongs to the original joined support
and to a complete phase period. `missing_pairs_interior_empty` proves this
exactly. The current symmetric prefix has no remaining hard prime-share
projection. Consequently every newly added pair is in the total-log
exterior or displaced edges, to which the existing tilt payment applies.
This does not license completing a bare cofactor or projecting separately
completed prime legs through any unrelated hard-share mask.

Writing `T=log(n)=x+z`, `f_x=F_(N+1,floor(13N/32))(x/T)` and similarly
`f_z`, the exact coefficient split is

```math
Q_N(x,z)-\mathrm{Selberg}(n)
=A_N(n)+\frac{T}{L_N}B_N(n),
```

where

```math
A_N=T(1-f_x-f_z)-\mathrm{Selberg}(n),\qquad
B_N=-T+x f_z+z f_x.
```

`prefix_atom_split` uses `T K_N=(N+1)K_(N+1)` before applying an edge
estimate. On every genuine pair, including arbitrarily distant exterior
pairs, `norm_prefixIntercept_le` gives `||A_N||<=2*divisorLogMajorant(n)`
and `norm_prefixSlope_le` gives `||B_N||<=divisorLogMajorant(n)`.
`exists_filter_edge_bound` extends the prior payment to any fixed
polynomial; its specialization to `X` pays `K_(N+1)` on the same order-N
total-log exterior. The moving factor `(N+1)/L_N` is at most one on the
proved order range.

The original radial endpoint correction is retained explicitly. It is
divisor-majorized and vanishes on the strict interior because every
interior pair is a central semiprime label. Its entire contribution uses
one further edge payment. No interior norm is charged.

The two tilt exponents at the radius ceiling are approximately
`-5.960289e-6` and `-3.921816e-6`; the checked rational rate is the weaker
`-1e-6`. Numerical diagnostics replay these values independently, but
Lean proves the inequalities used in the estimate.

## Exact connection to the existing floor

`finitePrefixPairDefect_eq_joined` applies the previously proved complete
factorial convolution with both central sums, the logged prefix, the whole
prime-square diagonal and the signed Selberg subtraction kept together.
The masks are removed only through the new geometric difference estimate.
There is no inference from separate prime-leg limits on a masked sum.

`eventually_native_whole_pair_floor` and
`exists_native_whole_pair_payment_simple` spend the old Selberg budget,
the old owner-mask budget and the new completion budget exactly once in
the original native-order floor ledger. They retain the complete signed
pair expression as an **unproved** main inequality. A bound for that
expression sufficient to reach `399/5000+o(1)` is still required; exposure
and source evaluation do not provide an independent arithmetic bound.

The earlier independently paid low logged orders on the physical population
remain valid. They are not silently deleted from this completed main or
paid again. A proof using that deletion must retain its exact physical
support and its complementary signed population.

## Local validation

The focused warning-as-error leaf build and namespace lint passed. The
compiled audit checked all 51 proof declarations, including private and
compiler-generated helpers, against the three permitted standard axioms.
There are 17 public theorems. No root registration, wider gate, commit or
push is included in this local slice.

The optional
[`probe_riesz_pair_whole_completion.py`](../scripts/probe_riesz_pair_whole_completion.py)
checks 469 exact rational coefficient cases and 36 finite genuine-prime
regressions with full complex phases. Its generic positive-length finite
regressions use `7*(N+1)/5`, not the literal moving cutoff; the literal
cutoff is retained in Lean. All sampled orders are below 65536 and the
finite prime universe is not the exhaustive literal population.
[`check_riesz_pair_whole_completion.py`](../scripts/check_riesz_pair_whole_completion.py)
independently replays binomial recurrences, separate prime phases and
decimal tilt exponents. These regressions receive no signed-floor credit.

See [`riesz-pair-whole-completion-audit.json`](riesz-pair-whole-completion-audit.json)
for scoped source and validation pins. This is a global geometric boundary
saving; no independent `399/5000` inequality, zero exclusion or RH proof is
claimed.
