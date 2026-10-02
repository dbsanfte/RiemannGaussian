# Fixed-owner cancellation without a share-ordering boundary

The independent `-79/1000-o(1)` floor is **open**. This slice removes the
ordered-share and negative-first restrictions from the price of an
admissible matching whose actual largest prime stays fixed. It does not
construct partners for the native unpaid many-bin population or bound its
original signed unmatched contribution.

The seven public proofs are in
[`ZetaRieszFixedOwnerPairFloor.lean`](../RiemannGaussian/ZetaRieszFixedOwnerPairFloor.lean).
Their focused source, namespace and transitive-axiom checks are recorded in
[`riesz-fixed-owner-pair-floor-audit.json`](riesz-fixed-owner-pair-floor-audit.json).
All earlier moving-owner, geometric pair-cost and negative audits remain
available.

## Pay the allocation difference after joining the phases

For `N>=32`, the exact original owner weight satisfies

```
A_N(x) = 1 - sum_{N/5+2 <= k <= 13*N/32} mass(N+1,k,x),
abs(A_N(x)-A_N(x')) <= 2*(N+1)*abs(x-x'),   0<=x,x'<=1.
```

This follows from the endpoint derivatives of its two exact binomial
cumulative sums. All factorial orders and both share endpoints remain.
With a fixed largest-prime logarithm `a` and total logarithms `T,U>=1`,
the owner cofactor shares are `1-a/T` and `1-a/U`; their difference is
at most `abs(T-U)`. Consequently, for arbitrary complex atoms `F,G`,

```
norm(A_N(1-a/T)*F + A_N(1-a/U)*G)
 <= norm(F+G) + 2*(N+1)*abs(T-U)*norm(G).
```

Both original complex phases are joined in `F+G` before its norm is
taken. The second term prices only the allocation difference. No share
ordering, negative-first orientation or `3/8` share restriction is needed
when the owner is unchanged. The earlier moving-owner floor theorem
keeps its original hypotheses.

## One geometric cost for the entire matching

Use the literal `InnerHinge` geometry and opposite cofactor Möbius signs
from `ZetaRieszInnerHingeGapPayment`. For a disjoint matching `E`, assume:

- every endpoint retains the literal window, squarefreeness, prime count
  at least three, and actual canonical owner in the original prime set;
- both endpoints have the same actual largest prime and original funding
  coefficient `w`, with `norm(w)<=B`;
- the same second-prime hinge and the original coprimality conditions hold;
- every actual total-log gap is at most `exp(-N/1000)`;
- matched labels lie in `[1,Q]` with `log Q<=3*(N+1)`.

Then `global_fixed_owner_cost` proves

```
u^(N+1) * sum_{e in E} norm(originalOwnerAtom(e.1)+originalOwnerAtom(e.2))
 <= [168*radiusCeiling*B*(1+abs(y))
     + 2*radiusCeiling*B*M(1+1/262144)]
       * (N+1)^3 * exp(-N/1250),
0<=u<=radiusCeiling=10001/20000.
```

Here `M` is the existing finite `zetaMoebiusLogMajorantMass`. Its norm
majorant is used only **after** the exponentially small actual gap is
included. The checked inequality

```
u^(N+1)*exp(-N/1000)*(131071/262144)^(-N)
 <= radiusCeiling*exp(-N/1250)
```

is the strict source-scale saving. This is not another polynomial
improvement to the growing positive carrier envelope.

`matching_original_signed_error` removes the matching from the **original
full signed carrier**, with the displayed geometric price plus the
existing global nonowner-allocation cost used once. The unmatched sum
keeps every original funding coefficient, allocation, mask and phase.
The estimate controls both real directions. It is conditional on actual
matching geometry and funding, not on a hypothetical bilinear estimate.

## Optional finite capacity regression

Run the optional probe with the repository Python environment:

```bash
../.venv/bin/python scripts/probe_riesz_fixed_owner_pairs.py
```

It holds the actual largest and second-largest primes fixed, retains the
rounded moving Riesz length, evaluates original full allocations and
complex phases, and deduplicates partners by their integer labels.

| Order | Families pooled | Parents | Partner incidences | Distinct partners | Unordered pairs |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 128 | 1 | 111 | 137 | 137 | 111 |
| 256 | 1 | 27 | 46 | 46 | 27 |
| 128 | 10 | 300 | 424 | 376 | 300 |
| 256 | 10 | 93 | 121 | 109 | 93 |

The single-family cases improve the old ordered coverage of `106/111`
and `24/27`. At height 54, `110/111` and `26/27` pairs have decreasing
owner cofactor shares, which the new estimate permits. The pooled cases
have 48 and 12 duplicate partner incidences; no such incidence is spent
twice. All sampled pointwise geometric prices pass.

These are finite low-count diagnostics with test funding `w=1`. They
do not evaluate the native count-56-and-up many-bin population, certify
the original dyadic support or its funding equality, or supply a
cofinal coverage theorem. Prime tests above `2^64` and floating values
are exploratory, not Lean or interval certificates. Their tiny sampled
norms are not a numerical value for the whole floor.

## The remaining arithmetic target

The cost of every qualifying fixed-owner pair is now paid at a rate
that beats source growth. What remains is to construct enough distinct,
same-funded opposite-parity partners with the literal hinge geometry,
control count/radial/funding boundaries, and bound the original signed
unmatched and supply contributions. Total partner cardinality in a
finite cell, or occupancy of many logarithmic bins, proves none of
these global obligations by itself.
