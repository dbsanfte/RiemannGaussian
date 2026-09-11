# Complete small-prime logarithmic decay at a larger cutoff

[ZetaRoughPrimeLogLcmBound.lean](../RiemannGaussian/ZetaRoughPrimeLogLcmBound.lean)
improves the complete small-prime logarithmic correction from cutoff cost
`D^3*log(D)` to `D*sqrt(D)*log(D)`. The normalized correction consequently
decays for every moving cutoff through `D_N^2`. The source survives at that
cutoff on products exceeding `D_N^4`.

These are bounds on the complete genuine arithmetic series. Their
independent estimates do not use the surviving source limit. The strict
signed upper bound for that survivor remains open.

## Keeping the marked mass

For a positive divisor mark, retain the existing mass

```text
F(P) = P^(-1/2) * sum_(g|P) g^(-1/2).
```

`RoughSquarefreeBare.exists_response_lcm_bound` keeps `F(P)` in the bound
for every genuine bare marked squarefree response, including all sieve
intersections. Ineligible marks vanish exactly. Exact polynomial logarithm
removal controls the moment of order `N+1` without increasing the envelope.

For a prime `p`, `RoughPrimeLogLcm.mass_prime_lcm` distinguishes

```text
F(lcm(p,P)) = F(P)        if p divides P,
             F(p)*F(P)  otherwise.
```

The logarithms of the distinct prime divisors of `P` sum to at most
`log(P)`. Summing new prime factors uses the independent square-root bound
for `sum_(p<=D) log(p)*F(p)`. Consequently
`sum_prime_log_lcm_mass_le` bounds the complete inserted-prime mass by

```text
F(P) * (C*sqrt(D)*log(D) + log(P)).
```

The previously proved linear complete ordered-pair estimate then gives

```text
sum_(p<=D prime, 1<=d,e<=D) log(p)*F(lcm(p,lcm(d,e)))
  <= C_0*D*sqrt(D)*log(D).
```

`exists_triple_mass_bound` includes repeated lcm values, every shared prime
and both orders of each pair. No maximum mark weight replaces the sum.

## The complete arithmetic estimate

`RoughPrimeLogLcm.exists_smallResponse_bound` proves, for `abs(y)>1`,
`0<r<1`, and every polynomial, moment and eligible finite prime sieve,

```text
norm(smallResponse(p,D,S,N+1,3/2+i*y))
  <= C(y,r)*D*sqrt(D)*log(D)*exp(4*sqrt(R))*r^(-N)*B_p(r),

B_p(r) = sum_(k in p.support) norm(p.coeff(k))*r^(-k).
```

The constant is independent of the cutoff, sieve, polynomial and order.
This is the literal complete small-prime logarithmic correction, with the
original squared Möbius mask and every prime insertion.

## Larger cutoffs and exact remaining support

For a hypothetical right-half zero, keep the original normalization,
polynomial filter, ordinate, quadratic prime sieve and parameters

```text
u = 3/2 - Re(rho), q = u^(-1/4), D_N = floor(q^N),
eta = 2*u^(1/8)/(1+u^(1/8)) < 1.
```

`exists_square_cutoff_bound` proves uniformly for every `N>=1` and
`1<=Y<=D_N^2` that the normalized full small-prime response has norm at
most `C(rho)*(1+N)*eta^N`. `tendsto_square_cutoff` allows arbitrary moving
cutoffs satisfying this range eventually.

The exact identity `normalizedLargeResponse_eq` subtracts that correction
from the complete Möbius-square divisor correlation at the same cutoff.
The independently proved correlation theorem applies throughout this range,
so `tendsto_large_square_cutoff` retains the full analytic multiplicity.

Every nonzero large-prime coefficient has a prime and cofactor strictly
beyond the cutoff. Therefore `coefficient_eq_zero_of_le_square` eliminates
all products up to its square pointwise. `response_eq_square_tail` and
`summable_square_tail` retain both the exact series and its convergence.
At `Y=D_N^2`, the terminal theorems are

- `normalizedLargeResponse_eq_fourth_tail`: the entire response equals
  its convergent tail over `n>D_N^4`;
- `tendsto_doubled_log_cutoff_source`: that same normalized tail tends
  to the full analytic multiplicity.

## Scope

The larger support gap does not by itself bound the oscillatory sum.
The coefficient is real and nonnegative, while the original complex
logarithmic kernel retains the zeta ordinate and polynomial phase. No
independent cofinal real-part upper bound below the unit source is proved.

This prime-tail reduction gives no additional zero exclusion on its own.
The separate [signed pole argument](zeta-signed-pole-zero-free.md) supplies
the improved literal edge region. Neither result closes RH.
