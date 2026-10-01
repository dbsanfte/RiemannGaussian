# A joint growing-count signed prime-period bound

[ZetaRieszSymmetricPeriodPayment](../RiemannGaussian/ZetaRieszSymmetricPeriodPayment.lean)
removes an exact factorial overcount from the existing signed prime-period
estimate, then sums counts and radial periods with one quantitative cost.
The result concerns **complete literal prime fibres** and a **relative
positive-supply budget**. The signed hinge-crossing and owner-mask boundary,
the whole `-79/1000` floor, and the contradiction remain open.

For an arbitrary selected squarefree cofactor population `D` of count `k`
and nonnegative prime weights `f`, the checked bound is

```math
k!\sum_{a\in D}\prod_{p\mid a}f(p)
\le\left(\sum_{p\in P}f(p)\right)^k.
```

The proof maps each actual cofactor and each permutation of its prime
factors injectively into the original ordered-prime cover. No labels or
phases are averaged. Applying the bound to the original least-prime and
reciprocal masses divides the old complete-period population cost by `k!`.
The signed prime fibre has already been summed before these masses are used
to pay its variation; neither hinge, factorial weight, nor owner allocation
changes.

`sum_symmetricCost_le_six_factorial` gives an exact aggregate comparison
for every moving count set with cofactor count at least six (total label
count at least seven): the entire new complete-period allowance is at most
the old one divided by `6! = 720`. This is a saving on that population's
comparison cost, not a fraction of the whole signed floor deficit.
This division applies to the old ordered-tuple cover. Existing exact
Euler-product count-mass bounds already count labels once and must not be
divided by `k!` again.

`signed_population_floor` and `joined_counts_floor` retain the original
response, complex observation through its cosine, allocation and selected
cofactor support. Their cofactor selector still requires the original
`0.398 v < log a <= 0.985 v` cap and prime owner gap. Every prime in the
selected **complete** fibre must be in the original allocation set.
There is no assertion that filling a literal owner or cutoff hole is free.

The new uniform estimates are

```math
\frac{\mathrm{logMassConstant}(k)}{k!}\le144^k,\qquad
\frac{\mathrm{variationConstant}(k)}{k!}\le576^k,
```

and

```math
\mathrm{symmetricCost}(k)
\le2{,}000{,}000\,2048^k,\qquad
\sum_{k\in I}\mathrm{symmetricCost}(k)
\le2{,}000{,}000\,4096^K\quad(I\subseteq\{1,\ldots,K\}).
```

Thus when `4096^(4K) <= v`, the joined cost is at most
`2,000,000 v^(-1/4)` times **one same radial supply unit**. The deterministic
choice

```math
K_N=\left\lfloor\frac{\lfloor\log_{4096}(N+1)\rfloor}{4}\right\rfloor
```

tends to infinity and satisfies the condition whenever `N+2 <= v`.
`growing_counts_floor` is a signed inequality uniform over the selected
counts, with no separate eventual threshold at each count.
`radial_periods_floor` sums all selected radial periods before pricing them.
`eventually_radial_periods_supply_floor` pays this entire population with
an arbitrarily small fraction of any **already checked** positive supply
that pays the same radial units. The supply comparison is explicit in that
theorem; it is not a hidden bilinear or cancellation hypothesis.

The range grows slowly and the displayed constants are deliberately crude.
For moderate orders the older fixed-count `3..55` theorem is stronger.
The new theorem establishes growing-count uniformity for the displayed
complete-period geometry, not a practical finite-order certificate.
The unaligned periods, narrow hinge interval, cofactor-dependent prime holes
and counts beyond `K_N` still need their signed aggregate estimate. The
bound is relative to radial supply: multiplying its cost by a divergent
source envelope would **not** give source-o(1). Do not charge the old
fixed-count supply and this overlapping population twice.

The optional [probe](../scripts/probe_riesz_symmetric_period.py) checks the
finite symmetry inequality with rational weights and evaluates the actual
old/new comparison constants in logarithmic arithmetic. For cofactor count
seven the allowance denominator is exactly `7! = 5040`; this is not a
1/5040 fraction of the whole signed floor deficit. It also evaluates the
exact integer count schedule, records that no effective start is certified,
and never treats underflow as cancellation. The script is outside ordinary
builds and CI. Focused validation is recorded in
[the audit](riesz-symmetric-period-audit.json).
