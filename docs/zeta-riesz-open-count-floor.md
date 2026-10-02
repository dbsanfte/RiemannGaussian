# Native partner funding across the count and bin boundaries

The independent `-79/1000-o(1)` floor is **open**. This slice removes an
actual support/funding obstruction to cross-count parity matching: the
existing credited count/bin populations can be rejoined with their full
signed coefficients, while keeping the original supply debit once.
Every literal inner-hinge partner in the resulting support has funding
coefficient exactly one, including count four.

The eleven public proofs are in
[`ZetaRieszOpenCountFloor.lean`](../RiemannGaussian/ZetaRieszOpenCountFloor.lean).
Their focused checks are recorded in
[`riesz-open-count-floor-audit.json`](riesz-open-count-floor-audit.json).
No native matching capacity or independent bound for the unmatched
signed contribution is asserted.

## Keep the original populations joined

Let `S` be the actual `coreBand`, `B=wholeTail S N 0`, `T=radialTail S N 0`,
and `P` the existing fixed-count, dense-count and few-bin credit sets.
The original unpaid set is `H=S\(P union B)`. Lean proves `P subset S\B`
and the exact complex identity

```
sum_{n in (S\B) union T} f(n)
 = sum_{n in H} f(n) + sum_{n in P} f(n) + sum_{n in T} f(n).
```

The published floor has `max(Re(sum P),0)` and `max(Re(sum T),0)`.
Each is at least the corresponding signed sum. Thus the checked native
floor also holds for one signed sum over the joined original support.
The previously paid owner crop is then applied to that whole support.
For

```
R = ((S\wholeTail S N 0) union radialTail S N 0)\sector u N K,
d_N = tailCost c N + epsilon + growingDebit kappa N,
Y = the SAME original radialSupply N h w,
```

`eventually_joined_floor_open_counts` proves, along the original dyadic
orders and with the original supply witness,

```
u^(N+1) * [Re(sum_{n in R} f(n)) - d_N*Re(sum_{n in Y} f(n))] - err_j
 <= Re(u^(N+1)*joinedPhysical u y N K),
err_j -> 0,
1/2<u<=10001/20000, y>=54.
```

The canonical owner, literal physical/core masks, original allocation,
full complex phase, core count cutoff and whole-tail boundary remain.
The former count-55/56, dense-count and occupied-bin classifications no
longer divide this main support. A matching may cross them without using
a previously credited label twice.

Keeping a negative credited sum can lower this expression relative to
its positive part. This is an alternative joined ledger, not a new free
credit or a proved numerical improvement to the whole floor. Any gain
must come from actual signed cancellation in the joined sum. The previous
ledger remains available.

## Exact funding geometry, including count four

The same complex sum has coefficient

```
q(n) = 1_R(n) - d_N*1_Y(n).
```

`joinedFunding_sum` retains the overlap exactly as `1-d_N` on `R intersect Y`.
Supply labels have count four, so `q=1` on every included label with at
least five primes. More strongly, the literal prime-log geometry proves

```
every prime dividing a funding label:  log p <= 3*N/5;
every marked prime on an InnerHinge core label: log p >= 18*N/25.
```

The first bound comes from the actual four-prime tuple boxes. The second
uses `L>=11N/8`, the actual core upper window `log n<=203N/100`, and the
exact hinge inequalities. They are incompatible for `N>=1000`.

Consequently no literal inner-hinge label is a supply label. The original
funding coefficient is **one even for an admissible count-four partner**.
This is proved on the native support; it is not a funding equality assumed
from a finite probe or from the old `4+abs(epsilon)` envelope.

## Price any qualifying matching directly in the whole floor

`floor_after_matching` uses the prior fixed-owner estimate with `B=1`.
For any disjoint actual matching inside `R`, with opposite Möbius signs,
unchanged canonical owner, the exact common inner-hinge geometry and
total-log gaps at most `exp(-N/1000)`, it proves

```
u^(N+1) * [Re(sum_{R\matchedVertices} f) - d_N*Re(sum_Y f)]
 - err_j - matchingBudget(N,y)
 <= Re(u^(N+1)*joinedPhysical),

matchingBudget(N,y)
 = [168*radiusCeiling*(1+abs(y)) + 2*radiusCeiling*M(1+1/262144)]
     *(N+1)^3*exp(-N/1250)
   + ownerPaymentError(N),
matchingBudget(N,y) -> 0.
```

The existing nonowner error is used once in this pair removal. The
unchanged unmatched sum and supply debit stay signed. No pair funding
equality, share ordering, negative-first orientation or count/bin-sector
cost is postulated. All earlier primality, coprimality, squarefreeness,
window and actual-gap obligations remain explicit. Existence and
capacity of the matching remain arithmetic obligations.

## Complete-cell numerical audit

The optional `scripts/probe_riesz_open_count_capacity.py` includes **every**
squarefree composite integer cofactor in each tested cell, rather than
constructing a selected favorable partner pool. It factors these integers,
retains every observed prime count, the exact rounded moving length, both
Möbius signs, the full product phase and full original allocation.
Partner labels are spent once.

For the first order-96 cell, the complete count histogram is

| Total prime count | Labels |
| ---: | ---: |
| 4 | 685 |
| 5 | 861 |
| 6 | 517 |
| 7 | 175 |
| 8 | 39 |
| 9 | 1 |

Its cofactor parity imbalance is `+204`. At height 54, 1,037 adverse
labels pair with favorable opposite-parity labels, leaving no adverse
label unmatched; 583 pairs use a count-four label. At height 65 the phase
reverses: there are 1,241 adverse labels and only 1,037 favorable labels,
leaving 204 adverse labels unmatched. At order 128, analogous tested
deficits are 133, 101 and 252. A smaller order-64 cell already has a
deficit of two at each tested height.

Thus removing count/funding boundaries can materially increase finite
capacity, but automatic cellwise coverage is not supported by the
complete-cell experiment. The sign of the remaining imbalance changes
with the actual phase. It must be kept in the aggregate across radial
periods rather than norm-priced or declared favorable.

These finite orders do not meet the native eventual length lower bound,
do not belong to the unpaid count-56-and-up many-bin population and do
not instantiate its dyadic support or funding witness. The supply
disjointness and native joined floor are Lean proofs; these numerical
coverage figures are diagnostics only. Floating values and large-prime
tests are not interval or Lean certificates. No cofinal floor or zero
exclusion follows from the probe.

## Next actual estimate

Construct sufficient native distinct partners in the enlarged literal
support and control the **signed** residual parity imbalance across the
owner/cofactor/radial periods, with the same supply debit. Pair cost and
native inner-hinge funding equality are now proved. Neither many-bin
occupancy nor the finite positive-phase capacity establishes that remaining
global signed estimate.
