# Higher-rank cancellation inside the retained hinge

This local slice strengthens the independent **sector** floor in the current
`polynomialCentralRemaining` ledger. The whole numerical floor, ceiling,
restricted contradiction and new zero exclusion remain open. The published
README and explorer endpoints are unchanged.

## The common mechanism

Every divisor incidence in a based block belongs to the same physical label
`n=p*a`. Changing the unsigned divisor changes the Möbius sign, but leaves
the full phase, factorial weight and owner allocation unchanged. The two
hinges must be joined before this common observation is applied.

Let `R=a/e`, `k=omega(R)`, `S=log R`, `P=log p`, and `D=S-L`. Suppose

\[
0\le D\le\log\minFac(R),\qquad
\frac{P+D}{2}\le\log q\le P\quad(q\mid R\text{ prime}).
\]

The lower cutoff sees only the unit divisor. The upper cutoff sees the
unit and all single primes; every divisor containing at least two primes
has a zero hinge. The **complete original** divisor block therefore equals

\[
w(n)\mu(R)\,[S-(k-1)P-kD].
\]

This is an exact evaluation, for every finite rank and every original
complex phase. No prime completion, density approximation or zero hypothesis
is used. `weighted_linear_orbit_eq` applies the existing arithmetic linear
Riesz identity to the joined original incidences.

`subset_single_layer_difference` proves the underlying principle for any
finite family of positive real increments, independently of primality:

\[
\sum_{U\subseteq Q}(-1)^{|U|}
\left[(P+D-\sum_{i\in U}x_i)_+-(D-\sum_{i\in U}x_i)_+\right]
=\sum_{i\in Q}x_i-(|Q|-1)P-|Q|D.
\]

Its hypotheses are `0<=P`, `0<=D`, and
`D<=x_i`, `(P+D)/2<=x_i<=P`. This shows that the controlling property is
which **subset layers the cutoff admits**, rather than a particular total
prime count.

## A concrete signed saving

Write `Q0=leastPairBlock(a)` and use the original canonical first block
`orbitDivisors a Q0 e`. The first block and all other ranks have opposite
amplitudes

\[
X=\log Q_0-P-2D,\qquad
Y=(k-2)(P+D)-(S-\log Q_0).
\]

Their exact complex responses are `w*mu(R)*X` and `-w*mu(R)*Y`. The latter
joins **all** remaining incidences, rather than only one adjacent prime.
If `3X<=5Y` and `3Y<=5X`, both amplitudes are nonnegative and

\[
|X-Y|\le\tfrac14(X+Y).
\]

`higher_rank_quarter_floor` proves the corresponding real floor with at
most one quarter of the separate first-block/other-ranks real allowance,
for every common complex phase. This is a **75% sector allowance saving**;
it is not a fraction of the whole floor deficit or an estimate of the
selected population's total mass.

The exact cancellation centre is

\[
D_*=\frac{S-(k-1)P}{k},\qquad
S-(k-1)P-kD=-k(D-D_*).
\]

`rank_quarter_of_band` gives one rank-dependent geometry test covering
all counts:

\[
\frac{5S-2\log Q_0-(5k-7)P}{5k-4}\le D\le
\frac{3S+2\log Q_0-(3k-1)P}{3k+4}.
\]

For equal increments, the centre is `P/k` and the endpoints become
`3P/(5k-4)` and `5P/(3k+4)`. This explains the numerical low-offset
cancellations and how their location changes with rank.

Away from this balance region, `norm_linear_orbit_le` still replaces the
exponential unsigned divisor cover by the joined linear bound

\[
\left\|\sum_{db\in\operatorname{orbit}}\mathrm{originalAtom}(db)\right\|
\le\|w(n)\|\,(k-1)P.
\]

The norm is taken **after** evaluating all original ranks. It is not a
source-scale population payment. The bound is sharp in the abstract
increment model: `reinforcing_endpoint_response` evaluates the admissible
equal-increment endpoint `D=P` as `-(k-1)P`. Thus this principle does not
justify a uniform zero cost or remove the need to retain the signed prime
moments.

## Compatibility with the current ledger

The maximal based orbit is exactly the original divisor antidiagonal
filtered by `e|d`. Because `e` is coprime to the canonical pair, this filter
includes either a whole old canonical orbit or none. Both old affine-zero
populations therefore still have zero response inside this filter.

`retained_based_sum_eq_full` proves that intersecting the based block with
the **current retained antidiagonal** leaves its response unchanged. No
old zero credit is spent again. `retained_higher_rank_floor` and
`global_retained_higher_rank_floor` leave every other label and incidence
signed, retaining count, radial, owner, physical and phase masks.

`eventually_remaining_higher_rank_floor` is a direct comparison for the
same `polynomialCentralRemaining` after the existing allocation and reduced
count payments. It subtracts the same old credits and the same two geometric
errors once. `HigherRankData` contains only finite prime-log geometry and
the explicit amplitude-balance tests, with no cancellation estimate assumed.
Select one base per physical label in this endpoint; different maximal based
blocks can overlap, so their savings cannot simply be added.

The retained prime row is one signed moment expression on the literal
prime set:

\[
\mu(R)\,[(S-kD)M_0-(k-1)M_{\log}].
\]

No clipped prime hole is filled, no cofactor is completed, and no separate
prime-count allowance replaces this expression. Bounds for its aggregate
cost and the complementary signed population remain open.

## Validation and optional regressions

The optional script `scripts/probe_riesz_higher_rank_hinge.py` checks nine
exact rational subset-cube regressions and seven actual-prime labels at
`N=640,1536`. Those labels retain the original core window, distinct rough
primes, physical masks, failed owner gap, allocation and phase. The
seven-/ten-prime examples have joined/separate allowance ratios about
`0.077..0.147`; their quarter balance tests pass. The fourteen-/twenty-prime
examples have ratios about `0.613..0.923`, and correctly fail that test.

The small literal samples are **not** below the new reduced-count threshold;
the crop theorem is eventual and is not a finite certificate at those
orders. Their source weights underflow in floating arithmetic; logged
underflow is not evidence of cancellation or a population bound. The
unscaled finite coefficients are compared directly to the exact formula.
The script is optional and outside builds/CI.

See [the Lean source](../RiemannGaussian/ZetaRieszHigherRankHingeFloor.lean)
and [the focused audit](riesz-higher-rank-hinge-audit.json). All 22 public
proofs are checked with warning-as-error compilation/build, ordinary root
plus explicit module namespace lint and transitive axiom inspection. Only
`propext`, `Classical.choice` and `Quot.sound` are permitted. No wider
publication gates, commit, push or claim of a numerical whole floor is made.
