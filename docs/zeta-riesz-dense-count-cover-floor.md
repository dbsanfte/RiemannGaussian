# Whole dense-count band removed from the unpaid floor

`ZetaRieszDenseCountCoverFloor.eventually_joined_floor_without_dense_band`
removes the **entire original squarefree count band**

```text
5 log(N+1) + 2 <= omega(n) < 8 * Nat.clog 2 (N+1),   omega(n) >= 8
```

from the authoritative `joinedPhysical` floor. It covers every prime-log
spread, occupied-bin pattern and crossing parity in that band. The same
literal four-prime supply pays the cost, with **1/256 of that supply still
retained**. The originally proved five-prime payment and other credits
remain in the ledger.

This is an independent signed arithmetic payment on actual original
labels. The numerical `-79/1000` whole floor, `3/2` ceiling and restricted
zero exclusion remain open. No source-normalized norm decay is asserted
for this dense population. All results in this note are local and
unpublished.

## The actual cover and cancellation

Fix `1/2 < u <= 10001/20000` and `y >= 54`, and write `x=N+1`.
The physical labels retain the original core, squarefreeness, prime-count
cutoff, phase, factorial kernel, moving Riesz length and full allocation.

Freeze the cofactor `a=n/largestPrime(n)`, then run its canonical largest
prime through an entire phase period. The finite cofactor sets are images
of ORIGINAL labels, rather than a completed cofactor series. The original
prime-count mask is inherited from those seeds. Each extended fibre is
proved to remain in `coreBand` and in the same dense band.

Two staggered phase grids cover the two arithmetic sign selections. Near
an ownership change, the canonical second-largest prime determines the
boundary scale. The proof retains the count shift `omega(n)-2` in that
boundary. Disjointness in both radial periods and dyadic owner scales
prevents duplicated incidences. The unused opposite-sign boundary on
each grid is empty; the two missed selections spend one boundary price.

The joined signed main-plus-crossing price is

```text
2017 * exp(5 M - 5 log(x) log(5/2)) / H * amplitude(N,v)/v,
2017 = 481 + 1536.
```

Here `M` bounds the ACTUAL finite reciprocal-prime mass. The checked bound
`M <= C_head + log x`, with exact finite `C_head`, gives a count price at
most `exp(5 C_head) sqrt x`. The old unpaid count ceiling forces
`v <= 128 H log x`. Consequently ALL counts, owner scales and radial
periods have one relative-supply price

```text
price(N) = unpaidCountSupplyPrice(N)
         = 258176 * exp(5 C_head) * log(x)/sqrt(x)
           * (1 + log(4x)/log 2),
price(N) -> 0,
amplitude(N,v)/v = exp(-v/2) * v^N/N!.
```

No signed bilinear estimate or prime-density approximation is assumed.
The fixed arithmetic head is finite and unevaluated, so there is no
effective starting-order claim.

## Every unmatched literal boundary is paid

`dense_label_grid_cover` covers every interior label with owner share at
most `601/1000` and owner log above `20000`, by either a complete owner
fibre or the canonical second-owner clip. The actual interior is

```text
244 N/125 < log n <= 2029 N/1000.
```

`dense_grid_unmatched_geometry` proves that anything unmatched fails one
of those three conditions. The old upper count ceiling and the original
core lower length force the largest-prime log above `20000` eventually;
the small-owner exception is therefore impossible. The remaining radial
and large-owner failures have the previously proved geometric payments.
`exists_dense_unmatched_bound` applies those payments to ANY subset of
the actual unmatched labels. The global nonowner-allocation payment then
restores the full original allocation.

`exists_dense_band_floor` gives the complete signed population floor:

```text
Re[u^(N+1) sum_{n in denseBand} literalAtom(n)]
  >= -u^(N+1) price(N) * (units(grid_1) + units(grid_2))
     -4 * mass(1+1/262144) * exp(-N/1000000)
     -2 * C * r^N -3 * ownerPaymentError(N),
0 <= r < 1,   ownerPaymentError(N) -> 0.
```

The positive units need not decay at source scale. They are funded by
the same quantitative supply witness used in the original whole-floor
proof. Its previous `1/128` reserve spends at most `1/256` here, leaving
`1/256`. No new choice of supply weights is used.

## Exact remaining counts

Let `E` be the original unpaid set after the old spent union, `E5` its
five-prime part, and `D=denseBand`. The new unpaid set is

```text
E_remaining = (E \ E5) \ D.
```

`remaining_count_cases` proves that EVERY squarefree label in this actual
set has exactly one of the following counts:

```text
omega(n) = 3, 4, 6, or 7;
or 8 <= omega(n) < 5 log(N+1) + 2.
```

The source-geometric error in the new whole-floor theorem tends to zero.
Its right side is still the original `joinedPhysical`; its lower bound
keeps the signed lower-count remainder, joined-prefix/pair savings, all
six original nonnegative head credits and the retained supply reserve.
It does not infer that the remaining expression is at least `-79/1000`.

## Follow-up: lower-count few-bin class also paid

[The new few-bin whole-floor theorem](zeta-riesz-few-bin-cover-floor.md)
now closes the original fibre-cover and disjoint-funding obligations for
the stronger test counting ALL large-log cofactor bins. It removes that
class from this remainder and retains1/512 of the SAME supply. Its
`remaining_configuration_cases` proves the additional many-bin condition
on every remaining growing-count label. The older intermediate-gap test
is not claimed fully covered.

## Follow-up: fixed-count payments merged without overlap

[The joined-population theorem](zeta-riesz-joined-population-floor.md)
now preserves the stronger existing fixed-count payment through55.
The two new payments begin at56, avoiding all overlap. Its SAME supply
retains257/512. Its exact final remaining labels are count four, or
56<=omega(n)<5log(N+1)+2 with MORE than floor(log(N+1)/16) cofactor bins.
The component enumeration above remains correct for its earlier ledger;
it is not the current combined enumeration. The numerical floor remains open.

## Remaining obstacles, cancellation and order of attack

Apply these tests in order to avoid charging a label twice. Exact-zero
responses, old spent heads/tails, the five-prime class and the new dense
band are removed first. Nonowner allocation, radial exteriors and the
paid physical/share errors keep their existing geometric bounds.

| Remaining population or obligation | Signed cancellation already proved | What must still be bounded |
| --- | --- | --- |
| Fixed counts `3,4,6,7` outside the old paid selections | Exact two-hinge, reflected-prime and signed-period identities apply; old heads retain their original credits | A whole-population payment compatible with those spent selections. Count four contains the supply funding the other payments, so that credit cannot be spent twice |
| Lower growing counts with at most `floor(log x/16)` occupied cofactor bins above the exact head | **Follow-up paid:** `FewBinCoverFloor` proves the original fibre cover, all-pattern signed payment, real boundary payment and same-supply placement | Removed from the actual remainder; the stronger all-cofactor-bin selection is distinguished from the older intermediate-gap test |
| Lower growing counts with many bins but separated background divisor-log windows | `SeparatedParityFloor` joins both two-prime tents: at most one tent pays either hinge, giving the count-free floor `-2 |Re w| min(log r,log s)` | The total ORIGINAL weighted population price, or a signed prime-period payment for that price |
| Many-bin overlapping crossings with both active parities | `CrossCountTransport` pairs opposite ranks with the original phase and both hinges; common backgrounds preserve the relation | Injective global coverage, the summed log-distance cost, and the unmatched parity layers |
| Many-bin overlapping crossings with only one active parity | Universal within-label opposite-parity matching is formally impossible; complete owner-prime period cancellation remains available | Cancellation across original labels/prime periods or across cofactor/count layers, retaining the signed aggregate before estimating it |
| Final numerical margin | The new whole-floor theorem retains every old credit and an explicit `o(1)` error | Prove the real lower-count aggregate plus credits is at least `-79/1000-o(1)`, then invoke the existing contradiction criterion |

Few-bin and separated configurations are different tests. A few-bin
cluster can have only one active parity and still receive the proved
all-pattern price. Once that test has been applied, the last two rows
describe overlapping configurations that fail it. Near-owner clips are
already part of the relevant signed-period payment; they are not a new
independent parity population.

The main common mechanism is to sum an owner-prime phase period with the
two hinges and the allocation retained, THEN price the cofactor
population. For separated windows, exact support replaces an exponential
divisor multiplicity by a single-tent cost. Neither mechanism currently
pays every lower-count overlapping population.

## Why the new count saving does not close the central gap

The optional numerical scan examines the already-cancelled positive
factorial price, with the unknown arithmetic head factored out. Its
optimized power at count `c log x` is

```text
c * (1 - log(c/2)) - 1.
```

At `c=5` this is about `-0.58145`, explaining the successful upper-band
payment. At `c=2` it is `+1`; this is the central peak of the unrestricted
count-price model. Retuning the positive count marker therefore does not
pay the remaining bulk. The scan is not a theorem about the size or sign
of the actual carrier. It identifies where additional SIGNED cofactor,
count or prime-period cancellation is needed.

`scripts/probe_riesz_dense_count_cover.py` also checks unique owner versus
second-owner clipping, both staggered periods, exact dyadic endpoints
and squarefree factorial symmetry on actual finite prime labels. These
small examples do not certify the large-prime/core hypotheses and run
outside ordinary builds and CI.

Focused warning-as-error Lean checks, ordinary-root-plus-explicit-module
namespace lint, all public transitive axioms and source hashes are in
[riesz-dense-count-cover-floor-audit.json](riesz-dense-count-cover-floor-audit.json).
