# Capacity and the global cost of centered insertion families

The independent native `nativeCost <= 399/5000` floor remains **open**.
This slice proves a global geometric transport price for genuinely centered
families. It also checks the complete finite product-weight insertion sum:
joining all counts leaves a positive residual, rather than supplying free
coverage. No native population has been paid by assuming these families exist.

The 15 public proofs are in
[`ZetaRieszInsertionCapacity.lean`](../RiemannGaussian/ZetaRieszInsertionCapacity.lean)
and
[`ZetaRieszCenteredInsertionPayment.lean`](../RiemannGaussian/ZetaRieszCenteredInsertionPayment.lean).
The focused validation and numerical source snapshots are recorded in
[`riesz-insertion-capacity-audit.json`](riesz-insertion-capacity-audit.json).

## A global transport estimate, with the actual kernel

Write the existing unallocated factorial amplitude and full phase as

```text
f_N(T) = exp(-T/2) T^(N+1)/(L N!) * exp(-(1+i*y)T).
```

For every original label `n` in a finite set `D`, retain all candidate
coefficients `c(n,i)>=0`, actual total logs `t(n,i)` and the exact first moment

```text
sum_i c(n,i)*(t(n,i)-log n) = 0.
```

`centered_amplitude_cost` differentiates this SAME amplitude twice. It gives
the squared-gap bound, with no frozen phase, asymptotic factorial mask or
derivative of a hard support condition. `global_centered_cost` then sums over
distinct original labels using one reciprocal-label harmonic bound. Assuming
`D subset [1,Q]`, `log Q <= 3(N+1)`, `L>=1`, `log n>=1`,
`sum_i c(n,i)<=3(N+1)` and literal gaps at most `exp(-N/5000)`, it proves

```text
u^(N+1) sum_n norm(sum_i c(n,i)*(f_N(log n)-f_N(t(n,i))))
 <= 72*U*(2+abs(y))^2*(N+1)^3*exp(-N/4000),
0 <= u <= U = 10001/20000.
```

The right side tends to zero at every fixed height. This relaxes the previous
first-order gap requirement `exp(-N/1000)` to `exp(-N/5000)` **when the first
moment really is zero**. It is a geometric rate, not another polynomial
improvement to `(2u)^N`. Candidate count and prime-count class do not appear
in the constant.

`global_centered_floor` gives the corresponding one-sided signed inequality
when `tau(n)=sum_i c(n,i)`, with an arbitrary unit complex multiplier retaining
the cofactor parity. This is a theorem for qualifying finite families. Actual
prime inventory, clipped coefficient coverage, partner column capacity,
original allocation and native support/funding still need their ledger
proofs before that inequality can be spent on `joinedPhysical`.

The existing `ZetaRieszOpenCountFloor` already proves native inner-hinge funding
is one and the owner log is at least `18N/25`. Those are reused facts, not new
capacity or supply credits. The unmatched signed sum and original supply debit
remain present. No original label or partner may be spent twice.

## Join every insertion count before auditing capacity

For the exact finite Riesz kernel `H_U(d)`, define

```text
B_Q(d) = sum_{U subset Q} (-1)^|U| (prod_{p in U} a_p) H_U(d).
```

`response_eq_average` proves exactly

```text
B_Q(d)
 = sum_{V subset Q} (prod_{p in V} a_p)
     (prod_{p in Q\V} (1-a_p)) (d-sum_{p in V} x_p)_+.
```

When `0<=a_p<=1`, this is a positive Bernoulli-weighted hinge average. Every
count, subset sign and empty channel remains. The checked consequences are

```text
0 <= B_Q(d) <= d_+                         (x_p>=0),
B_Q(d) >= (d-sum_p a_p*x_p)_+,
B_Q(d) >= d_+ * prod_p (1-a_p).
```

Thus every finite such family with `d>0` and `a_p<1` leaves a strictly positive
residual. A large mean inventory alone does not remove it. The arithmetic
bridge is exact: when the old squarefree base has every prime log at least
`d`, `arithmetic_response_eq` identifies the same sum with the actual finite
Riesz responses of `b*prod(U)`. Reciprocal weights `a_p=1/p` give the explicit
positive lower bound in `arithmetic_response_lower`.

This is an arithmetic **coefficient** inequality. It does not assert that the
native prime-owner inventory, allocation, masks or phase are independent
product weights. It does not refute native signed cancellation. It rules out
declaring the complete product-weight model annihilated just because several
opposite-sign counts cancel strongly.

## Unpaid-only capacity probe

The optional
[`probe_riesz_insertion_capacity.py`](../scripts/probe_riesz_insertion_capacity.py)
rejects paid geometry before coefficient work. At native index 1024 the final
scan has 27 complete model families and 18 paid skips. Original whole counts
are `56,65,301`; complete insertion families end at counts up to `365`. Their
old cofactors occupy `51..70` bins, beyond the paid ceiling 45. All selected
subset counts are inside the detector's unpaid band. This remains a sampled
rough model subset, not a proof of a complete native cover.

Pools of `8,32,64` virtual prime coordinates use **specified** reciprocal-prime
product weights. Integer probability numerators retain every one of `2^64`
subsets in the largest pool. States beyond the positive hinge have exactly
zero response; no unresolved count tail or probability renormalization is
discarded. Floor/ceiling log rounding gives exact rational brackets for these
finite-input coefficient models. Nine small cases also compare an independent
nested signed-subset sum against the Bernoulli formula.

At the finer grid the residual is about `0.167..0.466` of the original hinge.
The complete eight-coordinate signed absolute allowances are about
`1.76..3.41` times that hinge. The small cases also perform maximally generous
fractional matching, allowing EVERY opposite-sign edge. Exact node capacities
are respected and the positive unmatched mass equals the joined response.
This is a model capacity obstruction, not a native matching theorem.

The full phase at heights `54,65,100` is retained. Total log is exactly equal
in these constructed virtual-owner geometries; actual distinct integer labels
would require the proved small-gap transport instead. In 36 of 81 tested
phase cases the original phase is adverse, and the model residual keeps it.
Allocation enclosures at the extrema remain recorded; the fully allocated
family is not numerically evaluated or silently replaced by allocation one.
The exact rational arithmetic is Python evidence, not a Lean certificate of
the implementation or of actual prime support.

Reproduce from `formal/`:

```sh
../.venv/bin/python scripts/probe_riesz_insertion_capacity.py \
  --output .lake/riesz-insertion-capacity/unpaid-final.json
```

The concrete next obligation is native **capacity with the signed unmatched
parity remainder retained**. The new global theorem pays centered transport
if that capacity exists. It supplies no independent bound for the residual.
Keep these probes outside ordinary builds/CI; continue locally with the
published README, root/explorer endpoints and unrelated staged work preserved.
