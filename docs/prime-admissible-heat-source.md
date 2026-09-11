# The original prime source at admissible moving Gaussian widths

The fixed-order Gaussian limit can now be used rigorously while the moment
order grows. Lean constructs a height floor at each order and proves the
comparison for every moving family eventually above those floors. The
Gaussian widths remain inside the existing whole-zero budget's admissible
range, and the original prime-tail source survives.

This is a bound for the change of response. The independent signed bound
on the surviving response is still open. No new zero exclusion or RH
theorem follows from this slice.

## The unchanged arithmetic quantities

For a hypothetical right-half zero `rho`, put `u=3/2-Re(rho)` in `(1/2,1)`.
Let `p` be its existing zero-isolating polynomial, `S_N` the existing
quadratic prime sieve, and `D_N` the original moving cutoff. Retain the
original normalized ordinary-prime sum

```text
P_N = u^(N+1)*sum_(r prime, r>D_N, r notin S_N)
  log(r)*K(p,N,3/2+i*Im(rho),r).
```

The full complex kernel still contains all factorial moments and polynomial
coefficients. With the proved global margin `m(H)=m_F(H)`, define

```text
G_N(H) = u^(N+1)*sum_(r prime, r>D_N, r notin S_N)
  log(r)*K(p,N,3/2+i*Im(rho),r)
  *exp(-m(H)^2*log(r)^2)*fermi(-(1-2*m(H))*log(r)).
```

This is `normalizedMarginHeatPrimeResponse` in
[ZetaPrimeAdmissibleHeatSource](../RiemannGaussian/ZetaPrimeAdmissibleHeatSource.lean).
The displayed prime-tail form uses `D_N>=1`. The definition keeps the
original coefficient and is not defined in terms of a desired limit.

## Both actual parameter limits are discharged

`tendsto_zetaFermiZeroMargin` derives `m(H)->0` from the proved exact eventual
formula `m(H)=3/(20*log(H))`. Consequently the Gaussian width `m(H)^2` tends
to zero and the Fermi parameter `1-2*m(H)` tends to one.

`tendsto_gaussianFermiPrimeLogResponse_joint` proves the joint parameter
limit for every fixed complex polynomial, cutoff, sieve and moment order
on the Euler half-plane. The original unweighted complex moment supplies
a common summable norm bound: both the Gaussian and Fermi multipliers
have norm at most one. No cancellation estimate on the prime sum is used.

Thus, for each fixed `N,D`, the actual normalized response `G_N(H)` tends
to the existing Fermi-weighted moment with parameter one, denoted `F_N(1)`.

The same width is admissible at every height:

```text
0 < m_F(H)^2,
m_old(H)^2 <= m_F(H)^2 <= 1.
```

`tendsto_allowance_fermi_margin_square` therefore gives

```text
allowance(m_F(H)^2,H) -> 0.
```

Here `allowance` is the existing scalar bound for the complete outside
zero sum in the Gaussian budget. It is not an allowance obtained after
applying the complex polynomial moment filter.

## A proved floor controls every subsequent height

`exists_primeMomentHeatHeight` proves that for every order `N` and cutoff
`D` there is a height floor `T(N,D)` satisfying

```text
T(N,D) >= N,
T(N,D) >= 1,
T(N,D) >= 2*abs(Im(rho)),
```

and, for every `H>=T(N,D)`,

```text
norm(G_N(H)-F_N(1)) < 1/(N+1),
allowance(m_F(H)^2,H) < 1/(N+1).
```

`primeMomentHeatHeight` chooses a witness of this proved theorem.
`primeMomentHeatHeight_tail_spec` retains the bounds for every later
height. There is no numerical search for coefficients and no assumed
arithmetic lower bound in this construction. The growth rate of these
height floors is not estimated.

The canonical choices tend to infinity for every moving cutoff, and their
Gaussian widths tend to zero. More generally, every height sequence
`H_N>=T(N,D_N)` eventually has vanishing normalized smoothing error and
vanishing standard whole-zero allowance. The two limit operations are
handled by this proved diagonal construction; they are not interchanged
without justification.

## An independent bound at the original source scale

The earlier Fermi comparison independently bounds `P_N-F_N(1)` by a
geometric term. Combining it with the height-floor theorem gives
`exists_actual_prime_marginHeat_bound`:

```text
norm(P_N-G_N(H_N)) <= C*(2*u/(1+u))^N + 1/(N+1).
```

The ratio is strictly below one. One constant works for every moving
cutoff and height family, whenever `D_N>=1` and `H_N>=T(N,D_N)`. No upper
cutoff bound and no zero-source limit are used to prove this error bound.

`tendsto_actual_prime_sub_marginHeat` consequently proves that the full
source-normalized difference tends to zero. On the original squared
cutoff schedule, the already proved hypothetical source is
`P_N -> -multiplicity(rho)`. The terminal
`tendsto_marginHeatPrimeResponse_of_height` proves

```text
G_N(H_N) -> -multiplicity(rho).
```

Every moving height family eventually above the proved floors is allowed.
The canonical `admissibleHeatPrimeResponse` is one explicit mathematically
defined member of that class.

## The exact spectral average and the remaining gap

For the canonical family, `admissibleHeatPrimeResponse_eq_integral`
retains the complete earlier transport:

```text
G_N(H_N) = (u^(N+1)/2)*integral_R
  density(1-2*m(H_N),m(H_N)^2,y)
  *P(p,D_N,S_N,N,1+m(H_N)+i*Im(rho)-i*y) dy.
```

The inner `P` is the original unnormalized complex moment. The averaging
density is nonnegative with unit mass, and the infinite integral and prime
series converge by the earlier full interchange theorem. All phases and
complex coefficients remain inside this average.

The comparison and the standard whole-zero allowance now vanish at
compatible parameters. Positivity of the averaging density still does not
give a favorable sign to the complex moment being averaged. The
independent cofinal lower bound with a fixed positive gap above `-1` for
`Re(G_N(H_N))` remains open, just as for the original `Re(P_N)`. The theorem
does not bound the pole, gamma or zero-tail costs after applying the moment
filter, and does not bound the required growth of `H_N`.

The subsequent [sharper Gaussian endpoint proof](gaussian-fermi-sharp-zero-free.md)
gives eventual zero-free width `9/(50*log(abs(t)))`, with an existential
threshold. The stronger published `4.896` region is not yet
formalized in this repository. RH remains open.

## Local verification

This module passes strict direct elaboration and its focused build, and is
imported by the root library. The four prime-comparison modules pass verbose
declaration lint and 55 terminal axiom checks, using only `propext`,
`Classical.choice` and `Quot.sound`. The later Gaussian endpoint improvement
adds three modules; the current full build, inventory and combined audit
results are recorded in its [verification section](gaussian-fermi-sharp-zero-free.md#local-verification).
