# Paying the large-owner remainder from the joint reserve

The later [sharp joint budget](zeta-riesz-sharp-joint-budget.md) strengthens
the same whole-sum comparisons to `47*G_N/8`, with every population and
signed remainder below unchanged. The original `3*G_N/8` results remain
available.

The whole-sum comparisons now pay every remaining nonzero core label with
some prime log share at least `119/200 = 0.595`, across **all prime counts
and the entire core window**. The original allocation supplies the saving.
This strengthens the previous fixed positive-five payment and keeps it in
the same ledger; it does not assume either zero simplicity or RH.

The final `-79/1000-o(1)` floor and `3/2+o(1)` ceiling for the whole `J+C`
remain open. In particular, a smaller signed rest is not a bound for that
rest.

## Quantitative arithmetic estimate

For an eligible prime `p` with

```math
\frac{119}{200}\log n\le\log p\le\frac{13}{20}\log n,
```

the cofactor share lies in `7/20..81/200`. Tilting the **original** binomial
allocation by `201/200` proves the exact upper-tail rate

```math
\log\frac{40081}{40000}-\frac{13}{32}\log\frac{201}{200}
\le-\frac1{400000}.
```

The lower tail has more room. For `N>=320`, the actual missing allocation
satisfies `1-theta_N(n) <= 3 exp(-N/400000)`. This is the existing allocation,
with its integer order endpoints; no new factorial mask is imposed.

Use the already summable divisor-log majorant at the fixed exponent
`sigma = 1+1/100000000`. For the selected finite population `D` in **any**
original support, the literal unnormalized atom norms obey

```math
\sum_{n\in D}|c^{\rm residual}_{L,N}(n)K_N(3/2+iy,n)|
\le 3M_\sigma\,2^N e^{-N/500000}.
```

`M_sigma` is the repository's proved finite `zetaMoebiusLogMajorantMass`.
The estimate retains the actual coefficient, every additional support mask,
and the original allocation. It is uniform in phase height and prime count.
No prime-density approximation or numerical population model is used.

This rate need not vanish after multiplication by `u^(N+1)`. Its useful
comparison is with the already proved central credit

```math
G_N=\frac{\pi u e^{-1}}{24000|y|}\frac{(2u)^N}{N+1}.
```

For every fixed nonzero `y` and every `epsilon>0`, the selected normalized
norm mass is eventually at most `epsilon G_N`. The ratio is bounded by a
constant depending on `y` times `(N+1)exp(-N/500000)`, which tends to zero.
The theorem does not provide a numerical starting order.

The ordinary Lean proofs are in
[ZetaRieszJointOwnerPayment.lean](../RiemannGaussian/ZetaRieszJointOwnerPayment.lean):
`missing_allocation_bound`, `norm_mass_le`, and
`eventually_norm_mass_credit`.

## Whole-sum application

Let `P` be the previous paid central population and `B` the positive-five
sector already paid from it. The new population `D` is selected only from
`S \ (P union B)`, so it cannot spend those same labels again. Write `b`, `d`
for their original signed sums and `R` for the exact sum over
`S \ (P union B union D)`.

The cached central-capacity application spends `G_N/8` from the previously
retained `G_N/2`. It proves the following alternative bounds, each using its
own original paid population and signed rest:

```math
\begin{gathered}
u^{N+1}\bigl(\operatorname{Re}R+
 \max(\operatorname{Re}b,0)+\max(\operatorname{Re}d,0)\bigr)
 +\frac38G_N-e_j
 \le\operatorname{Re}\bigl(u^{N+1}(J+C)\bigr),\\
\operatorname{Re}\bigl(u^{N+1}(J+C)\bigr)
 \le u^{N+1}\bigl(\operatorname{Re}R+
 \min(\operatorname{Re}b,0)+\min(\operatorname{Re}d,0)\bigr)
 -\frac38G_N+e_j,\qquad e_j\longrightarrow0.
\end{gathered}
```

These hold eventually on the unchanged dyadic schedule for
`1/2<u<=10001/20000` and fixed `|y|>=54`. The lower and upper credits are
alternative payments, not additive supplies. All earlier positive-five
observations remain. The phase is never changed in the literal sum.

The terminal theorems are
`RieszCentralCapacityTransfer.eventually_joint_owner_floor` and
`RieszCentralCapacityTransfer.eventually_joint_owner_ceiling` in
[the cached application](../scripts/CheckRieszCentralCapacityTransfer.lean).
Their population estimates are discharged by the already checked optional
covers and the new ordinary-library bound. [The audit](riesz-central-capacity-audit.json)
records validation and source hashes. Ordinary builds do not rerun covers.

`remaining_prime_log_lt` also proves that every nonzero label in the new
signed rest has **all** prime shares below `119/200`. The original core
supplies squarefreeness, eligibility, the physical cutoff and the old
`13/20` nondominant restriction; these are not additional unproved premises.
This removes an entire owner-share range from the unresolved arithmetic
part. Balanced triples and other smaller-owner populations still remain,
and the necessary independent whole-sum numerical bounds have not closed.
