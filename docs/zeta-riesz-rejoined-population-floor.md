# Rejoin the funding population before pricing the remaining floor

The independent numerical floor `-79/1000-o(1)` remains **open**. The
current request to close estimates1–5 has not been completed. Recent local
work proves an additional whole signed floor with count four rejoined,
a sharper signed bound for the original separated-crossing packet, and
an unconditional comparison for the literal masked carrier. It does not
prove a restricted contradiction or a new zero exclusion.

The latest [whole-core owner payment](zeta-riesz-core-owner-payment.md)
is now spent on this same ledger. It crops primes with share at least
`751/1250`, with an actual source-normalized geometric error, preserving
the funding witness and every debit. The remainder additionally has
**every prime share below 60.08%**. All five final estimates below remain
open; no numerical fraction of their combined deficit has been certified.

## Count four is part of the complete fixed-count band

The earlier [joined-population ledger](zeta-riesz-joined-population-floor.md)
left count four explicit alongside a positive supply credit. An existing
alternative is important here: `SharpSupplyFloor`, `WholeFixedCountFloor`
and `RejoinedSupplyFloor` already include ALL counts3..55, with the
four-prime funding population included exactly once. The remaining charge
is a relative debit, not an absolute source-scale allowance.

`ZetaRieszRejoinedPopulationFloor.eventually_joined_floor_rejoined_populations`
now combines that alternative with BOTH of the new, disjoint count56+
payments. It uses the SAME supply witness and keeps their exact prices,
instead of rounding them to fixed budget fractions. Let

```
S = coreBand(u,N,K),
D = S.filter(3 <= omega <= 55),
Ds = dense56Band(u,N,K),
Bs = bin56Band(u,N,K),
Paid = D union Ds union Bs,
H = S \ (Paid union wholeTail(S,N,0)),
f(n) = residualCoefficient(A,L,N,n) * zetaPrimeLogKernel(N,s0,n),
Y = Re(sum over the original four-prime supply of f),
g_N = (unpaidCountSupplyPrice(N) + intermediateSupplyPrice(N))/(128*kappa).
```

For every FIXED `epsilon>0`, the compiled result gives, eventually on the
original cofinal sequence,

```
Re(u^(N+1) * joinedPhysical)
  >= u^(N+1) * [Re(sum_H f) + max(Re(sum_Paid f),0)
                  + max(Re(sum_radialTail f),0)
                  - (tailCost(c,N) + epsilon + g_N) * Y]
     - err,
err -> 0.
```

All original phase, factorial, owner/allocation, physical, radial and
count conditions remain. Nonsquarefree atoms and all previous exact-zero
deletions retain their established treatment. The actual fixed-band
sum includes its heads and funding supply; no head or supply label is
credited twice. The earlier ledger with separately retained positive
credits remains available too. The two inequalities are not claimed to
dominate one another for every arithmetic configuration.

`remaining_effective_geometry` proves that every nonzero original atom
in THIS `H` is squarefree and satisfies

```
56 <= omega(n) < 5 log(N+1)+2,
card(cofactorBins(N,n/largestPrime(n))) > floor(log(N+1)/16).
```

There is no separate count-four label population in this `H`. That does
**not** close estimate1 at source scale: the funding charge is still
present in the combined inequality.

## The relative debit cannot be paid independently

The new `growingDebit` is nonnegative and tends to zero. The total price
`tailCost(c,N)+g_N` tends to zero RELATIVELY. Constants and the starting
order in the fixed-count theorem can depend on the fixed `epsilon`.
An `N`-dependent epsilon cannot be substituted without a uniform theorem.

The already compiled `ZetaRieszGlobalDebitAudit` is decisive:
`eventually_supply_tailDebit_gt` and `actual_combinedDebit_unbounded`
prove that the actual source-normalized tail debit exceeds every fixed
budget. This is about the charge, **not** divergence of the signed carrier.
The signed remainder and the supply/tail have to compensate jointly.

Its explicit actual-supply lower bound, at fixed height `y`, contains

```
[128*u*exp(1)/(3*(floor(2*y)+1))] * (2*u)^N/(N+1)^5.
```

For `u=10001/20000`, `y=54`, the optional probe evaluates this lower
bound to about `10^-20.93` at `N=100000`, but `10^13.15` at `N=1000000`.
Finite small numerical debit values therefore cannot establish the
cofinal floor. The bound is a proved debit formula; the probe does not
evaluate the original signed carrier.

## A sharper separated-crossing inequality for the literal packet

Put `a=n/largestPrime(n)`, `R=leastPairBlock(a)`, `B=a/R`, and let `w`
be the original `phaseWeight`. If all distinct divisor logs of `B` are
separated by at least `log R`, they must fit inside `[0,log B]`. There
are exactly `2^omega(B)` such divisors. The new compiled packing result
gives

```
(2^omega(B)-1) * log R <= log B.
```

After joining both original hinges and every background Möbius rank,

```
Re(retained original divisor response)
  >= -abs(Re w) * log B/(2^omega(B)-1).
```

This is an additional bound: the earlier
`-2 abs(Re w) min(log r,log s)` bound remains available and can be
stronger in other geometries. The packing bound is not claimed to be
uniformly better at every order.

`canonical_background_count` proves exactly
`omega(n)=omega(B)+3`. Thus every remaining count56+ label has at least
53 background primes. Its packing coefficient is at most `10^-15`
times its weighted background log. That tiny coefficient is **not** an
absolute source-scale population bound or a fraction of the floor gap.

`ZetaRieszSeparatedPackingFloor.source_scaled_current_separated_floor`
connects this directly to the ORIGINAL residual-coefficient sum over any
selected separated subset `S0` of the literal core:

```
Re(u^(N+1) * sum_{n in S0} f(n))
  >= -u^(N+1) * sum_{n in S0} abs(Re w(n)) * log B(n)/10^15
     - ownerPaymentError(N).
```

The SINGLE existing nonowner payment is included and tends to zero
geometrically. No completed profile, generic prime-density approximation,
separate prime-leg limit or unproved arithmetic estimate is used. The
total actual weighted logarithmic mass still needs a sufficient bound.

## Packing cannot be paid by the common positive period envelope

The additional compiled exponent audit in
`ZetaRieszSeparatedPackingFloor` prevents a misleading use of the small
packing coefficient. If a moving background rank satisfies

```
1 <= rank(N) <= 5 log(N+1)+2,
```

then `logarithmic_count_pow_le` and
`packing_factor_lower_of_logarithmic_count` prove

```
2^rank(N) <= 4 (N+1)^4,
1/(2^rank(N)-1) >= 1/[4 (N+1)^4].
```

`canonical_packing_factor_lower` derives this from the ORIGINAL count56+
core label and its exact background count. This is a bound for the price
factor. It is not a lower bound for the actual weighted separated mass.

For every fixed `u>1/2`, `y>=54`, and such a moving rank,
`logarithmic_packing_periodDebit_tendsto` proves

```
u^(N+1) * periodUnits(N,y)/(2^rank(N)-1) -> +infinity.
```

Consequently replacing the actual separated population by the common
positive period envelope does not close estimate2, even if the packing
rank grows and its coefficient becomes much smaller than `10^-15`.
The total signed population needs its own bound; this audit does not
refute the desired whole floor or assert divergence of that population.

The optional probe now also gives packing the strongest count allowed by
the remaining range: `rank < 5 log(N+1)-1`. At `u=10001/20000`, the proved
period-envelope lower-bound formula is about `10^-18.73` at `N=100000`
(rank56), but `10^15.74` at `N=1000000` (rank68). These evaluations are
diagnostics of that positive envelope, not evaluations of the carrier.

The existing smooth-owner comparison was also checked for applicability.
It pays an error on complete cofactor shells with owner larger than the
whole cofactor. Its theorem expressly retains a signed main and does not
remove the current count/bin/physical masks. It cannot be substituted for
the literal remaining set without paying those differences. Removing the
factorial rectangle also does not remove the squarefree zero-extension
variation obstruction; the generic absolute-variation route remains closed.

## Status of estimates1–5 after this pass

### Earlier joint cancellation applicability check

The preceding applicability inspection did not prove a new signed estimate. In
`ZetaRieszSignedConvolution`, `higher_count_quadratic_cancellation` removes
the complete Selberg quadratic for every squarefree cofactor with at least
three prime factors. It leaves the ORIGINAL clipped cutoff response,
multiplied by the original correlated `phaseWeight`; it does not make that
response zero. `prime_pair_boundary` also retains the negative ordinary-prime
boundary explicitly. Neither identity bounds the joined masked population.

The complete-shell theorem `ZetaRieszSmoothOwnerDiscrepancy.normalized_joint_owner_error`
does not pay the differences between those complete shells and the current
masked cofactor population. Its signed model remains a main term, rather
than a paid error. Consequently it cannot close the funding debit or the
unmatched parity layers by substitution.

The literature supplies a framework for parity-sensitive cancellation, but
no automatic estimate for this carrier. Friedlander and Iwaniec,
[Asymptotic sieve for primes](https://arxiv.org/pdf/math/9811186),
section1, hypotheses(B), (B1)–(B3), require an additional signed bilinear
estimate for the particular sequence being sieved. Theorem1 assumes it;
the congruence remainder hypothesis(R) alone does not discharge it. The
current carrier is complex and has correlated moving masks, so applying
that theorem would additionally require a justified reduction to its
nonnegative-sequence setting and verification of its stated hypotheses.
This check is NOT a proof that our particular signed estimate is impossible.

For comparison, the existing physical-cell fallback needs a one-sided
length saving1/10000: `ZetaRieszPhysicalCellFloor.restricted_saving_ratio`
checks `10001/10002 < 1`, while
`eventually_joinedPhysical_floor_of_cells` still openly assumes the literal
signed cell estimate. The logarithmic-envelope and fixed-height VMVT
audits remain applicable. A new assumption of bilinear cancellation, a
generic logarithmic error bound, or an unrelated sieve application must
not be recorded as closing any of estimates1–5.

### Subsequent estimate for the masked carrier

`ZetaRieszLongCutoffError.literal_joined_carrier_estimate` now derives an
unconditional comparison for any selected subset of the actual core,
with all owners/counts and both hinges joined. The longer cutoff uses
the explicit power error `C X^(63/64)` under `D^4 <= X^3`; the exact
core geometry discharges that range for the translated hinge. Centering
against the squarefree reference measure removes squarefree holes from
the variation cost without removing the squarefree mask from the carrier.

The stronger follow-up `literal_whole_carrier_estimate` puts repeated-owner
holes inside the same measure too. Its error is `6 C exp(-N/128)` times
the displayed hinge-weighted variation of the **raw** owner columns.
An exact density ratio `(p+1)/p` retains a common density across owners.
Finite prime exclusions can also be absorbed, with a weighted product
cost and an eventual geometric prefactor; this does not pay the deleted
population. No extra roughness condition is imposed on the whole core.
Every other original mask remains in those columns. That remaining
variation and the joined signed main are still unbounded at source scale.
Thus this is a new comparison estimate for the masked carrier, not a
numerical floor or a closure of any of estimates1–5. See
[the exact inequality and limitations](zeta-riesz-long-cutoff-error.md)
and [its focused audit](riesz-long-cutoff-error-audit.json).

| Estimate | Checked progress | Still required |
| --- | --- | --- |
|1. Count four with funding/head credits | The whole fixed band3..55 and both growing payments are in one checked inequality, with one exact relative debit | Independent joint compensation for the source-scaled debit; relative decay alone is insufficient |
|2. Separated crossings | Divisor packing strengthens the signed price and applies to the original residual packet; a new exponent audit rules out paying it by the common positive period envelope | Bound its total actual weighted population cost at source scale |
|3. Overlapping opposite-parity crossings | The earlier exact transport identities and signed unmatched remainder remain | A global construction with a proved summed weighted distance and coverage cost |
|4. Unmatched one-parity layers | All-count/multiscale models test whether many bins force parity mixing; they do not | Cross-label or complete prime-period signed cancellation for the actual weighted aggregate |
|5. Final floor | All proved errors and literal masks are retained; multiplicity/source endpoints remain checked | Prove the aggregate independent `-79/1000-o(1)` bound, then invoke the contradiction criterion |

The optional `probe_riesz_rejoined_estimates.py` produces many-bin models
with59 factors,12 occupied bins and only one active background parity.
The count/bin inequalities of the remaining population hold in these
continuous models, and their signed-to-unsigned response ratio is exactly
one. Both favorable and unfavorable real common-phase directions occur.
The parity conclusion has a strict log-window margin and does not require
exact equality of the perturbed divisor logs.

These are **not actual prime labels**. They use the continuous leading
moving length and do not estimate the source-scaled factorial/allocation
weight or sum any actual prime population. They do not refute a whole
floor; they rule out treating many occupied bins as numerical evidence
for automatic local opposite-parity cancellation. The existing actual
single-parity no-go remains in force. The script is outside ordinary CI.

Focused warning-as-error Lean/build/root-import checks, all namespace
linters and every public transitive axiom check are recorded in
[riesz-rejoined-population-floor-audit.json](riesz-rejoined-population-floor-audit.json)
and [riesz-separated-packing-floor-audit.json](riesz-separated-packing-floor-audit.json).
No commits, pushes, wider CI or public endpoint changes were made.
