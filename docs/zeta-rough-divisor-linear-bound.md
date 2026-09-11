# Linear divisor-correlation cost

The new bound controls the complete nonunit arithmetic correlation for all
pointwise bounded complex divisor weights. Its cutoff cost is linear. The
preceding bound, applied to this class, cost
`D^3 * (1 + log(D^2))`.

The terminal estimates and limits are in
[ZetaRoughDivisorLinearBound.lean](../RiemannGaussian/ZetaRoughDivisorLinearBound.lean).
They use the original convergent correlation and exact lcm expansion from
[ZetaRoughDivisorCorrelation.lean](../RiemannGaussian/ZetaRoughDivisorCorrelation.lean).
The independent strict signed bound for the surviving source remains open.

## Full finite lcm mass

Write

```text
F(P) = P^(-1/2) * sum_(g|P) g^(-1/2),  P > 0.
```

`sum_pair_lcmSqrtFactorMass_le_linear` proves, with a fixed finite constant,

```text
sum_(1<=d,e<=D) F(lcm(d,e)) <= C_0 * D.
```

The proof keeps every ordered pair, including repeated lcm marks. At the
common divisor `g=gcd(d,e)`, submultiplicativity gives

```text
F(lcm(d,e)) <= F(g) * F(d/g) * F(e/g).
```

Both reduced factors have their exact integer cutoff `floor(D/g)`. Each
reduced sum is bounded by a constant times `sqrt(D/g)`, leaving
`D * sum_g F(g)/g`. The established fourth-root bound on the divisor
correction dominates the last summand by `4*g^(-5/4)`. Its series converges.
Thus no divisor-count factor or maximum lcm weight is substituted for the
actual complete sum.

`prime_lcm_eq_three_entries` and `sum_pair_prime_lcm_eq` keep the ordinary
prime correction exactly: for a prime `p`, its only ordered pairs are
`(1,p)`, `(p,1)` and `(p,p)`. The complete correction is bounded using the
existing prime-kernel estimate and `sqrt(D)*log(D) <= 2*D`.

## Genuine arithmetic bound

For every `|y|>1`, `0<r<1`, polynomial `p`, positive divisor cutoff `D`,
moment order `N`, and finite sieve `S` of primes at most `R`,
`RoughDivisorLinear.exists_bounded_remainder_bound` proves

```text
norm(remainder(p,D,S,w,v,N,3/2+i*y))
  <= C(y,r) * D * exp(4*sqrt(R)) * r^(-N) * B_p(r),

B_p(r) = sum_(k in p.support) norm(p.coeff(k)) * r^(-k),
```

provided `norm(w(d))<=1` and `norm(v(d))<=1` through `D`. The constant is
independent of the families, cutoff, sieve and polynomial. Ineligible lcm
marks vanish exactly; the complete prime correction is included.

The signed arithmetic response, original complex phase and all cross terms
remain defined upstream. The norm estimate is a downstream bound for that
same remainder. The earlier coefficient-mass theorem also remains available
for sparse families with individual weights larger than one.

## Enlarged moving cutoff

For a hypothetical right-half zero, retain the original choices

```text
u = 3/2 - Re(rho),  q = u^(-1/4),  D_N = floor(q^N),
eta(rho) = 2*u^(1/8)/(1 + u^(1/8)) < 1.
```

`RoughDivisorLinear.exists_cubic_cutoff_error_bound` proves uniformly over
all bounded complex families and every `1<=Y<=D_N^3` that

```text
norm(C_N(Y,w,v) - w(1)*conj(v(1))*U_N) <= C(rho)*eta(rho)^N.
```

Here `C_N` is the original normalized complete correlation at divisor
cutoff `Y`, with the original sieve and polynomial, and `U_N` is its
unchanged unit response. The full difference is exactly the normalized
nonunit remainder by `normalizedResponse_sub_unit_eq`.

`tendsto_cubic_cutoff_error` allows arbitrary moving cutoffs and weights
satisfying those conditions eventually. `tendsto_cubic_cutoff_source` then
proves that if `w_N(1)*conj(v_N(1))` tends to `c`, the full correlation tends
to `c*m_rho`. The error estimate itself does not use this source limit.

## Remaining obligation

The result enlarges the admissible divisor range in the complete
correlation. It does not extend a physical truncation of the summation
variable, apply to a divisor cutoff varying with that variable, or transfer
the existing small-prime logarithmic decay theorem to the larger cutoff.

For the live large-prime tail, the required independent cofinal upper bound
strictly below the unit source is still unproved. The source limit is a
retention theorem, not that missing upper bound. No additional zero is
excluded, and the proved all-height edge width remains
`1/(10*log(|t|+2))`. No claim of mathematical priority is made for these
divisor estimates.
