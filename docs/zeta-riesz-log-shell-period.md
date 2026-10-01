# Comparable logarithms remove the count-dependent period cost

This local slice consolidates two previously separate arithmetic savings:
signed cancellation on a complete prime period, and the short-window price
of its close-owner boundary. Both now have a finite cost summed over every
selected prime count on a comparable-log population. The numerical
`-79/1000` floor, ceiling and restricted contradiction remain **open**.

The Lean source is
[ZetaRieszLogShellPeriodFloor.lean](../RiemannGaussian/ZetaRieszLogShellPeriodFloor.lean).
The focused validation record is
[riesz-log-shell-audit.json](riesz-log-shell-audit.json).

## The common mechanism

The old affine-zero blocks, adjacent hinge savings and higher-rank formula
are finite differences of the same two hinges. All divisor incidences of
one label have the same phase, factorial weight and allocation. They must
be joined before pricing the coefficient. When only the unit and the
single-prime subset layers are active, the coefficient is

\[
S-(k-1)P-k(S-L)
=(k-1)\left(\log e+\frac{kL}{k-1}-T\right).
\]

Thus the cancellation centre depends on total logarithm, base and rank,
not on the detailed cofactor prime geometry. `single_layer_radial_eq`
proves this identity exactly.

There is also previously unused support information. A based block
containing the canonical least pair, with lower offset nonnegative and
each retained prime logarithm at least `(P+D)/2`, forces **every** cofactor
prime logarithm into `[P/2,P]`, including primes in the base. This is proved
both generically and for the current `HigherRankData` on original core
labels. No extra cancellation hypothesis is introduced.

## The quantitative saving

For any literal finite prime set with `H <= log p <= 4H`, `H >= 1`, the
existing Chebyshev bound gives

\[
\sum_p\frac1p\le M=5\log4.
\]

For any selected squarefree cofactor population of count `k` supported in
that shell,

\[
\sum_a\frac1a\le\frac{M^k}{k!}.
\]

The shell height and the count may move. The old unrestricted fractional
moment constants grew with the count; retaining the lower logarithmic
endpoint removes that growth. The true factorial symmetry therefore wins
against the exponential coefficient/variation cost after the signed prime
period has been summed.

`all_counts_floor` gives one complete-period cost
`C_period * v^(-1/2)` relative to `amplitude N v / v`, where
`C_period = 1207600 * exp(4M)`. There is no additional count ceiling.
All original phase, factorial, Riesz hinges and allocation remain inside
the prime sum. The existing cofactor cap and membership of the **whole**
prime fibre in the original allocation set are still explicit hypotheses.
In particular this theorem does not cover tiny-owner fibres beyond that
cap merely by removing a count bound from its statement.

## Extending a boundary payment to all counts

The earlier `OwnerTieFloor` bound stopped at total count 55. For any
squarefree original label with nearly tied largest primes `p,q` and
`|log n-v| <= 1/16`, removing those two primes puts both into the same
literal short logarithmic window. If all prime logarithms are in the
shell, its actual reciprocal mass is at most `2/H`. Counting the pair
jointly supplies `4/H^2`.

The remaining squarefree cofactor is still counted with `M^k/k!`, and
the label geometry gives `v <= 8H(k+2)`. Summing **every** count therefore
gives the actual norm bound

\[
\sum_{n\in D}\left|\mathrm{residualCoefficient}(n)K_N(s_0,n)\right|
\le\frac{C_{\rm boundary}}{v}\frac{\mathrm{amplitude}(N,v)}v,
\qquad C_{\rm boundary}=24576e^{4M}.
\]

`all_count_close_owner_norm_bound` retains arbitrary original submasks,
allocation and height, without a count ceiling. Only this identified
boundary is priced by norm; the main prime period keeps its signed phase.
The short interval is deduced from the two largest primes and the radial
cell, not supplied by an unproved short-interval counting assumption.

`signed_period_with_boundary_floor` joins both estimates into an actual
one-sided arithmetic bound. `radial_periods_with_boundary_floor` sums all
selected counts and radial periods with one cost at most
`(C_period+C_boundary) * (N+1)^(-1/2)` times the same radial units.

## Scope and next obstruction

These are **relative radial/supply costs**, not source-normalized decay.
Do not multiply the vanishing relative rate by the divergent `(2u)^N`
whole-core envelope. A whole-ledger payment still requires a disjoint
literal cover and a comparison with the already retained positive supply,
with every older credit spent once.

The prime-period theorem retains the original cofactor cap, owner gap,
phase-grid orientation and complete-fibre membership. The boundary theorem
retains the comparable-log condition, `H >= 10000`, close-owner geometry
and short radial cell. Other owner holes, hinge-selector boundaries,
wider prime-log spreads and tiny-owner prime periods are not paid here.
The point of consolidation is a count-independent price on an identified
population, not a claim that this population exhausts the floor.

The explicit constants are very coarse. No effective starting order,
fraction of the global deficit or numerical floor is certified.

The optional `scripts/probe_riesz_log_shell.py` checks actual finite prime
reciprocal masses, exact rational factorial symmetry and the new versus
old comparison constants. It does not evaluate the retained carrier,
infer its masks from a continuum model, or certify source cancellation.
It remains outside ordinary builds and CI.
