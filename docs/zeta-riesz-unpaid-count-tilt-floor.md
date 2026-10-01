# Dense intermediate populations in the actual unpaid floor

The whole `-79/1000` floor remains open. This slice obtains a global
signed prime-period bound for a substantially lower growing-count band,
including its literal near-owner crossings. It also checks which older
dense examples were already paid. No new zero exclusion is claimed.

The follow-up [whole dense-count cover](zeta-riesz-dense-count-cover-floor.md)
now closes the original-fibre cover and whole-floor placement left open
by this component: the entire band leaves the unpaid remainder, with
`1/256` of the SAME supply retained. The numerical floor still remains
open.

## First remove the already-spent population

The old tail starts at the exact integer threshold

```
countThreshold(N) = 8 * Nat.clog 2 (N+1).
```

`paid_count_threshold_le` proves this is at most `16 log(N+1)` for
`N>=7`; its asymptotic coefficient is `8/log 2`, about `11.54`.
`whole_tail_subset_spent` and `unpaid_count_lt` refer to the ORIGINAL
spent-label union of the published compensated floor.

The previously investigated small-top condition forces
`omega(a)>=32 log(N+1)`. `small_top_mem_paid_tail` now proves that the
whole squarefree label containing this cofactor is already in the old
spent tail. Its `O(log N/N^12)` signed bound remains valid, including the
new nonempty-crossing variant, but it does not remove new labels from
the currently unpaid floor. Never spend a reserve for it again.

## Enumeration after this audit

Put `x=N+1`. Intermediate cofactor primes retain the existing test
`B<log p<J/W`, with `B=W=32 log x`. The old sparse-factor payment covers
at most `floor(log x/4)` such factors. The all-pattern payment covers at
most `floor(log x/16)` occupied dyadic log bins, without a factor-count
ceiling. Apply those proven tests before the following cases.

| Remaining dense population | Signed mechanism | Proven scope / remaining obligation |
| --- | --- | --- |
| `5 log x + 2 <= omega(n) < countThreshold(N)`, regardless of occupied bins, prime-log spread or crossing parity | Sum the original owner-prime period, keep the hard count cutoff, then sum the factorial population price | Global selected-period-plus-crossing price is `O(log^2 N/sqrt N)`. The follow-up `DenseCountCoverFloor` proves whole original fibre coverage and removes this band from the final floor, spending at most `1/256` of the SAME literal supply |
| Lower growing counts with many intermediate factors and many occupied bins, but separated background divisor-log crossings | Exact two-prime finite differences leave at most one tent at either hinge | Count-free per-label floor is proved; total weighted population cost remains open |
| Lower growing counts with many bins and overlapping active crossings of both parities | Same-label opposite-rank transport keeps both hinges, the original phase and exact log distances | Total matching distance, injective coverage and unmatched parity cost remain open |
| Lower growing counts with many bins and overlapping crossings of just one parity | Local parity matching can fail completely; complete owner-prime periods still apply | The new high-count price covers this when its total count is large enough. The lower-count global payment remains open |

Here “lower growing counts” means counts below `5 log x+2`; fixed low
counts and their existing heads remain in their original ledger.
These tests are a priority classification. A label is not charged once
for its count band and again for its bin pattern or a parity match.
Inactive hinges are exactly zero. Near-owner crossings are boundary
labels, not an additional disjoint parity class; the new estimate below
pays both missed sign selections once.

## Common cancellation principle and new bound

The arithmetic feature shared by these populations is unique prime
ownership. Freeze the squarefree cofactor and sum its largest prime
through a complete phase period BEFORE bounding the result. The proved
literal row floor has price

```
481 * 2^k/(H*a) * amplitude(N,v)/v,
k = omega(a).
```

The original Riesz hinges, phase, factorial weight and changing owner
allocation stay coupled. No assumed bilinear estimate enters.

The squarefree cofactor population contributes `M^k/k!`, with the actual
finite reciprocal-prime mass `M >= sum_{p in Q} 1/p`. Thus the price
after signed cancellation is `sum_k (2M)^k/k!`. This is where the lower
count restriction supplies information lost by the unrestricted budget.
`count_price_log_tail_le` proves

```
sum_{k in I, k>=5 log x} (2M)^k/k!
  <= exp(5M - 5 log x * log(5/2)).
```

The marker is exactly `5/2`. Lean certifies `log(5/2)>=9/10`.
The existing finite-prime mass estimate gives

```
M <= C_head + log x,
C_head = smallPrimeHeadMass + log 16 + 1/5000,
```

so the whole count price is at most `exp(5 C_head)*sqrt(x)`.
For an actually unpaid squarefree label, its old upper count bound and
`log n >= v/2` imply

```
v <= 128 H log x                 if every prime log <= 4H.
```

`unpaid_owner_scale` proves this directly from the original spent union.
The owner scale is therefore at least of order `N/log N` in the core.
This converts the square-root count price into a vanishing relative
period cost. There is no occupied-bin or opposite-parity requirement.

## Actual crossings and all radial periods

`clipped_count_lower_norm_bound` retains the exact count shift:
removing the two tied largest primes leaves `k=omega(n)-2`. This is why
the uniform whole-label band starts at `5 log x+2`.
The literal boundary includes squarefreeness, the original radial cell,
canonical owner, tied second prime, finite cofactor prime universe and
the full original allocation. Both missed sign selections use ONE norm
of that boundary atom. The signed main is not replaced by a norm.

`count_lower_with_boundary_floor` joins main and crossings at price

```
2017 * exp(5M - 5 log x*log(5/2))/H * amplitude(N,v)/v,
2017 = 481 + 1536.
```

`global_lower_count_floor` sums all selected counts, owner scales and
radial periods with ONE price

```
unpaidCountSupplyPrice(N)
 = 258176 * exp(5 C_head) * log x/sqrt x
   * (1 + log(4x)/log 2),
258176 = 2017 * 128.
```

`tendsto_unpaidCountSupplyPrice` proves convergence to zero. Its
conservative rate is `O(log^2 N/sqrt N)`. The true supply unit is

```
amplitude(N,v)/v = exp(-v/2) * v^N/N!.
```

This is a relative signed population payment, not a source-normalized
norm bound; those positive units can still grow after source scaling.
The fixed arithmetic head is exact, finite and unevaluated. No effective
starting order is asserted.

## Literal label and reserve checks

`middle_count_not_spent` proves EVERY count from eight up to the old
threshold avoids ALL old heads, supply and tails, with no roughness
premise. `owner_fibre_count` and
`literal_owner_population_subset_unpaid` specialize this to the actual
complete owner-prime fibres without the old fixed-count cofactor-share
cap. `retained_literal_count_floor` reindexes the signed bound onto
literal integer labels, counting each exactly once across count ranks
and marked incidences.

`eventually_count_cost_paid_by_same_supply` uses the SAME quantitative
four-prime supply selection as the published floor. The global new cost
is eventually at most `1/256` of that literal supply, leaving another
`1/256` of its previous `1/128` reserve. No separate choice of phase
window is made. The earlier geometric/nonowner payments remain intact.

This component's selected-row theorem needed a whole original cover.
The follow-up `ZetaRieszDenseCountCoverFloor` now proves that cover and
the exact final signed-ledger placement, retaining every old credit.
Its `remaining_count_cases` theorem gives the actual new unpaid counts:
`3,4,6,7`, or `8 <= omega(n) < 5 log x+2`. This lowers the whole-floor
unpaid count ceiling; it does not establish the `-79/1000` floor or a
zero exclusion.

The optional `scripts/probe_riesz_unpaid_count_tilt.py` compares the
ENTIRE infinite post-cancellation count budget with the exact tilt and
its rational bound. It scans the lower-count price obstruction without
replacing the carrier by prime density. Numerical rows factor out the
unevaluated head and certify neither physical prime fibres nor a whole
floor. It remains outside ordinary builds and CI.

Focused Lean checks and all public transitive axioms are recorded in
[riesz-unpaid-count-tilt-floor-audit.json](riesz-unpaid-count-tilt-floor-audit.json).
