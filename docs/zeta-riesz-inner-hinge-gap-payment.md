# A geometric price for joined literal hinge pairs

The independent `-79/1000-o(1)` floor remains **open**. This slice proves
the total joined mismatch cost for any disjoint matching with explicit
literal support, equal original funding and sufficiently small total-log
gaps. It does not construct a matching covering the unpaid many-bin
population or bound its original signed unmatched/supply contribution.

The thirteen public proofs are in
[`ZetaRieszInnerHingeGapPayment.lean`](../RiemannGaussian/ZetaRieszInnerHingeGapPayment.lean).
The focused source and standard-axiom audit is
[`riesz-inner-hinge-gap-payment-audit.json`](riesz-inner-hinge-gap-payment-audit.json).

## The signed cancellation is independent of prime count

On the existing exact `InnerHinge L p q b` geometry, put

```
T = log(p*q*b),       c = L + log q.
```

`unallocated_inner_atom` identifies the original full coefficient/kernel:

```
coefficient(L,p*q*b) * K_N(3/2+i*y,p*q*b)
 = mu(b) * (T-c)/L * T^(N+1)/N! * exp(-(3/2+i*y)*T).
```

For any two literal labels on this same inner hinge, with the same `q`
and opposite cofactor Möbius signs, their sum is a difference of this
smooth total-log function. Both complex phases remain present when the
subtraction is performed. There is no divisor-count allowance or separate
positive allowance for either count. `opposite_inner_pair_gap` proves,
for `L>=1`, a unit-size log gap and `log n'<=3(N+1)`,

```
norm(rawAtom(n) + rawAtom(n'))
 <= 21*(1+abs(y))*(N+1)*radialCap(N)/n * abs(log n-log n'),
radialCap(N) = (N+1)*2^(N+1).
```

This covers the old owner replacement `p -> p'*r` and also replacements
inside the cofactor. `cofactor_split_parity` proves the exact opposite
sign when one genuine prime is replaced by two coprime genuine primes.
It does not require that the inserted prime be smaller than the current
least prime. Cofactors already containing `2` therefore have an additional
candidate mechanism. Genuine primality, squarefreeness, both inner-hinge
conditions and the actual log gap remain required.

## Total source cost, with no count or bin multiplier

Let `E` be any disjoint matching, with vertices in `1..Q` and
`log Q<=3(N+1)`. Its **original** complex funding coefficients must obey
`norm(w(n))<=B` and `w(n)=w(n')` on every edge. For every actual pair require

```
abs(log n-log n') <= exp(-N/1000).
```

`global_literal_gap_cost` sums the joined pair differences first. Pair
disjointness reduces the reciprocal label price to one harmonic sum.
Throughout the unchanged radius `0<=u<=10001/20000`, it proves

```
u^(N+1) * sum_E norm(w(n)*rawAtom(n) + w(n')*rawAtom(n'))
 <= 168*radiusCeiling*B*(1+abs(y))*(N+1)^3 * exp(-N/1250).
```

`small_gap_source_rate` checks that the gap exponent beats `(2u)^N`;
`tendsto_gap_price` proves the resulting price tends to zero for fixed
`B,y`. This is a concrete geometric total-cost estimate for every matching
satisfying the stated arithmetic conditions, **not** an unconditional
estimate of the whole unpaid population.

`replacement_interval_log_gap` shows that an actual replacement interval
`p <= p'*r <= p*(1+eta)` supplies log gap at most `eta`. It is not a theorem
that the interval contains a prime or enough partners.

There is an exact feasibility restriction. `integer_log_gap_lower` proves
for distinct positive integers

```
abs(log a-log b) >= 1/max(a,b).
```

`small_gap_forces_large_local_factor` therefore proves that the required
gap forces `log(max(a,b))>=N/1000`. For an owner replacement these local
integers are `p,p'*r`; for a single cofactor-prime split they are
`v,r*r'`. This condition is not derived for every remaining owner or
cofactor prime. Many occupied bins alone do not prove that a one-factor
replacement has a linearly large logarithmic span. Pairing a larger block
can still be considered within `opposite_inner_pair_gap`, but its actual
arithmetic capacity and masks must be proved.

## The original floor ledger remains signed

`matching_original_floor_of_small_gaps` connects the total cost directly
to `OwnerPairFloor.matching_original_floor`. It retains the original
residual allocation on every unmatched label. Under the original owner
eligibility, ordered cofactor-share and negative-first conditions, it gives

```
sourceReal(original sum)
 >= sourceReal(original signed unmatched sum)
    - geometric joined-gap price
    - geometric lower-allocation-tail price
    - B * existing global nonowner price.
```

The previous allocation price is `O(exp(-N/50))`. The existing nonowner
payment is used once, not once per edge. Equal funding is explicit:
bin occupancy does not establish it, and a parity partner can cross an
original credit/debit population boundary. The original funding envelope
`B=4+abs(epsilon)` is eventually available with the **same fixed** epsilon;
it supplies a bound on coefficients, not equality of partner coefficients.

No many-bin assumption appears in the analytic price. Such a hypothesis
could help construct the arithmetic matching, but does not prove phase
orthogonality, partner capacity, mask stability or signed unmatched control.
The new result does not prove a new paid whole population, the floor,
the ceiling, a zero exclusion or RH.

## Optional finite capacity checks

[`probe_riesz_inner_gap_payment.py`](../scripts/probe_riesz_inner_gap_payment.py)
is outside ordinary CI. It uses actual integer labels, the rounded native
moving length, original factorial allocation, full phase and distinct
matching vertices. Its small-count tests are not the native unpaid
count56+ population, dyadic schedule or original funding witness.

In frozen-cofactor owner cells, combining insertion primes supplies enough
partners in the tested negative-first cells: `57` labels versus `64`
candidates at order32, and `28` versus `38` at order64. No single insertion
prime has sufficient capacity there. This tests a capacity issue which a
pointwise partner-existence argument would miss.

The cofactor-splitting checks retain the common primes `2,3,5,7,11` and
hold the largest and second-largest primes fixed. Although total partner
cardinality exceeds the original cardinality, monotone matching leaves
unmatched labels: `106/111` at order128 and `24/27` at order256. Thus total
cardinality alone does not pay the ordered matching boundary. These are
finite floating diagnostics, not asymptotic coverage or a floor saving.

Primality tests above `2^64` are probable-prime tests; no floating output
or finite primality check is trusted by the Lean proofs. The probe keeps
original signed unmatched quantities and distinguishes a finite capacity
observation from the missing global weighted matching/transport estimate.

The next arithmetic obligation is to construct enough **originally funded**
supported opposite-parity pairs, account for collisions across cofactors
and count boundaries, and bound the original signed unmatched/supply term.
The quantitative log-gap target and its total price are now explicit.
