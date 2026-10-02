# Join clipped insertions before pricing the floor

The native `nativeCost <= 399/5000` floor remains **open**. This local slice
proves an exact coefficient identity and a joined finite-family floor. It
also proves a quadratic transport saving when an actual family's weighted
total-log gap is zero. It does not establish native prime matching, funding,
population coverage or a source-scale numerical budget.

The eleven public proofs are in
[`ZetaRieszClippedInsertionFloor.lean`](../RiemannGaussian/ZetaRieszClippedInsertionFloor.lean).
The focused source/axiom/probe record is
[`riesz-clipped-insertion-floor-audit.json`](riesz-clipped-insertion-floor-audit.json).

## Short inserted primes still contribute

On the existing literal inner hinge, write `n=p*q*b` and
`tau=log(p*b)-L`, with `0<=tau<=log(minFac b)`. The original atom is exactly

```text
mu(b) * tau * phaseWeight(A,L,N,y,q*b,p).
```

Replace the owner prime by genuine distinct primes `p',r`. Retain both
actual saturation inequalities and put `tau'=log(p'*r*b)-L`. If
`0<=tau'<=log(minFac b)`, the inserted atom is exactly

```text
-mu(b) * min(tau',log r) * phaseWeight(A,L,N,y,q*r*b,p').
```

The upper cutoff uses the **old** base head. There is no requirement
`tau'<=log r`. The new result therefore retains insertions below the active
hinge which the older inserted `InnerHinge` theorem could not use.
Allocation and phase stay inside the actual finite atoms. Original support,
coprimality, funding and all masks are still required when applying this
identity to a native population.

## One cost for the whole family

Let `c_i=beta_i*min(tau_i,log r_i)`, with the actual fractional funding
`beta_i`, original complex amplitude `F` and inserted amplitudes `G_i`.
For `Re F<=0`, `joined_insertions_floor` proves

```text
Re(tau*F - sum_i c_i*G_i)
 >= -max(tau-sum_i c_i,0)*norm(F)
    -norm(sum_i c_i*(F-G_i)).
```

Coverage is priced only after adding the clipped coefficients. Transport
is priced only after adding the **complex** differences. The theorem does
not bound the two remaining quantities or assert that candidates exist.
`literal_insertions_floor` applies this inequality directly to the genuine
original residual atoms, with no completion.

`joined_owner_insertions_floor` reuses the existing one-sided owner-weight
increase. If every inserted unweighted phase has the favorable real sign
and its cofactor share increases, the same joined transport price works
with the original owner allocations. Only

```text
2*exp(-N/25) * sum_i c_i*norm(G_i)
```

is added. The rate is the already proved globally payable owner lower
tail, not a new credit. Spending it globally still requires actual
fractional capacity and original funding; it must not be charged or
credited once per overlapping candidate family.

## Why two-sided candidates can save another power of the gap

For the same smooth complex amplitude `f` at actual total logs `T,t_i`,
suppose the coefficient-weighted first gap is **proved** zero:

```text
sum_i c_i*(t_i-T) = 0.
```

If `c_i>=0`, `abs(t_i-T)<=rho` and the second derivative of `f` has norm
at most `M` on `[T-rho,T+rho]`, `centred_transport_norm_quadratic` proves

```text
norm(sum_i c_i*(f(T)-f(t_i))) <= M*rho^2*sum_i c_i.
```

The common first derivative cancels before norms. There is no separate
price for each prime count, candidate or phase. The theorem applies to a
genuinely smooth amplitude; it does **not** differentiate hard support
masks or allocation jumps. The owner theorem handles the allocation
separately with its favorable sign. Actual support and funding differences
must still be retained and justified.

`centred_owner_insertions_floor` combines this cancellation with clipped
coverage and the original owner weights. Its derivative bound, favorable
phase signs, ordered shares and centered first moment are explicit
premises. No derivative bound for the whole masked native population or
global capacity theorem is smuggled into the statement.

## Optional unpaid-only probe

[`probe_riesz_clipped_insertions.py`](../scripts/probe_riesz_clipped_insertions.py)
rejects paid/out-of-support inputs before subset recursion. It uses the
same original/current count ceilings, occupied logarithmic bins, core
window, canonical owner, physical upper cutoff and allocation as the
generic detector. Its additional roughness requirement selects a **model
subset**, not the whole native core.

The final scan uses native index 1024 and the exact rational radius
`10001/20000`. Forty-five complete families have whole counts
`56,57,64,65,301`, with `51..70` occupied cofactor bins against the paid
ceiling `45`. Eighteen paid count/few-bin/dense records are rejected before
subset calculation. All 300 inserted responses resolve exactly for the
supplied finite binary logs; 225 have `tau'>log r` and were outside the
older inserted-inner-hinge hypothesis. All subset signs and endpoints
remain represented. Exhausting the recursion budget leaves the entire
family unresolved, with no cost/sign claim.

Thirty families use constructed candidates on both sides of the original
total log. Their rational fractional coefficients satisfy exact coverage,
are between zero and one individually, and have exactly zero first gap
moment. This is a **finite model inventory**, not a proof that actual primes
provide those candidates or that different original labels can spend them
without collision.

The transport diagnostic uses the unallocated smooth amplitude; the full
complex phase and factorial amplitude ratio are retained. At
fixed heights `54,65,100`, gap radius `1e-3` gives relative joined transport
about `0.00146..0.00500`; radius `1e-6` gives `1.46e-9..5.00e-9`. At the
smaller radius the joined cost is about `2.7e-5..5.0e-5` of the separate
transport costs. These are floating **relative model costs**, not interval
certificates or native source credits. Constant gap radii do not by
themselves beat the full source growth `(2u)^N`.

The full allocated transport is not numerically evaluated. The original
allocation is retained as a Chernoff enclosure, including
its log bound when the displayed float underflows. It is not silently set
to zero in an asserted arithmetic equality. The moving length's separate
rounding error is reported. Nominal zero-gap models keep their actual tiny
finite-binary gap; no zero-gap arithmetic equality is inferred from them.

Reproduce from `formal/`:

```sh
../.venv/bin/python scripts/probe_riesz_clipped_insertions.py \
  --counts 20 55 56 63 64 300 4000 \
  --output .lake/riesz-clipped-insertion/unpaid-final.json
```

The next arithmetic obligation is actual two-sided prime inventory and
fractional capacity with the original funding and masks. It must control
the **whole** remaining joined transport and signed unmatched labels.
There is no new paid native population, independent floor, ceiling,
zero exclusion or RH contradiction from the model scan.
