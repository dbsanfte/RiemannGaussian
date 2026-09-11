# Controlled Fermi weighting and exact prime-moment heat transport

The same Fermi factor can now be introduced or removed with a proved
error estimate in two existing arithmetic carriers. In the Gaussian
zero formula its correction is uniformly bounded. In the original
source-normalized ordinary-prime moment its correction decays
geometrically. Both comparisons retain the exact signed difference
before taking its norm.

This controls a change of weight. It does not bound the surviving prime
moment, identify Gaussian positivity with positivity of the complex
moment filter, or prove another zero exclusion. The best eventual
zero-free width is now `9/(50*log(abs(t)))`, with an existential threshold.

## The ordinary Gaussian sum in the full zero formula

Let `f(x)=1/(1+exp(x))`. For real `sigma,B,t`, set

```text
G(sigma,B,t) = sum_n Lambda(n)*exp(-sigma*log(n))
              *exp(-B*log(n)^2)*cos(t*log(n)).
```

This ordinary Gaussian sum includes every prime power. The original
Fermi sum `P_F(2*sigma-1,B,t)` has the same summands multiplied by
`f(-(2*sigma-1)*log(n))`. Exact complement and exponential identities give

```text
G(sigma,B,t) = P_F(2*sigma-1,B,t)+R(sigma,B,t),

R(sigma,B,t) = sum_n Lambda(n)*exp(-(3*sigma-1)*log(n))
              *exp(-B*log(n)^2)*f(-(2*sigma-1)*log(n))
              *cos(t*log(n)).
```

[GaussianFermiPrimeComparison](../RiemannGaussian/GaussianFermiPrimeComparison.lean)
proves the termwise equality, genuine summability and equality of the
complete series. For every fixed `sigma0>2/3`, every `sigma>=sigma0`,
every `B>=0` and every real `t`, it proves

```text
abs(R(sigma,B,t)) <= D(3*sigma0-1),
D(v) = Re(-zeta'(v)/zeta(v)) = sum_n Lambda(n)*n^(-v), v>1.
```

The correction converges even at zero Gaussian width. The main Gaussian
sum and its equality with the original Fermi sum require `B>0`; no
unsmoothed series in the critical strip is declared convergent.

The terminal
`zero_side_eq_poles_digamma_sub_ordinary_add_correction` places the
ordinary Gaussian sum into the actual full zero formula:

```text
sum_rho Q(rho) = polePair-log(pi)/4+digammaAverage-G+R.
```

Every genuine zero and analytic multiplicity is retained. On the
existing interior evaluation lines `sigma=1-m_F(H)>3/4`, the fixed
constant `D(5/4)` controls the whole correction independently of width
and height. This proves that this weighting correction is bounded; it
does not prove a favorable lower bound for `G`.

## The unchanged ordinary-prime moment

The squarefree reductio's remaining ordinary-prime response is

```text
P(p,D,S,N,s) = sum_(r prime, r>D, r notin S) log(r)*K(p,N,s,r),

K(p,N,s,r) = exp(-s*log(r))
            *sum_(k in support(p)) p_k*log(r)^(N+k)/(N+k)!.
```

It has ordinary-prime support, unlike the prime-power Gaussian sum above.
Define its Fermi-weighted version by the same literal multiplier:

```text
F(a,p,D,S,N,s) = sum_(r prime, r>D, r notin S)
               log(r)*K(p,N,s,r)*f(-a*log(r)).
```

The exact identity `1-f(-x)=f(x)` gives

```text
P-F = sum_(r prime, r>D, r notin S)
      log(r)*K(p,N,s,r)*f(a*log(r)).
```

The difference retains the original complex polynomial, factorial
orders, sampling point, sieve and cutoff. Its norm is estimated only
after this signed identity is recorded.

[ZetaPrimeFermiMomentComparison](../RiemannGaussian/ZetaPrimeFermiMomentComparison.lean)
combines `f(a*log(r))<=exp(-a*log(r))` with the existing exponential
moment envelope. For every `q>0` with `Re(s)+a-q>1`, and `Re(s)>1`, it gives

```text
norm(P-F) <= q^(-N)*sum_k norm(p_k)*q^(-k)*D(Re(s)+a-q).
```

This is an estimate of the complete convergent arithmetic series. The
upper bound uses the full von Mangoldt series only as a majorant; it
does not change the ordinary-prime support in either response. There
is no upper bound on `D` or on the size of the finite prime sieve `S`.

## A uniform geometric bound at the original source scale

Take any `0<u<1`, any real `y`, any fixed complex polynomial `p`, and
the original sampling point `s=3/2+i*y`. Choose the exact parameter

```text
q=(1+u)/2,
C=u*sum_k norm(p_k)*q^(-k)*D(2-q).
```

For every `a>=1/2`, every `N`, every cutoff `D>=1` and every finite prime
sieve `S`, the terminal `exists_normalized_primeFermi_bound` proves

```text
norm(u^(N+1)*(P-F)) <= C*(2*u/(1+u))^N.
```

The ratio lies strictly between zero and one. The same constant works
for every ordinate and all the cutoffs, sieves and Fermi parameters. Consequently they may
all vary with `N`; only the polynomial is fixed in this theorem. No
coefficient search, prime cancellation assumption or zero source limit
is used to prove the error estimate.

For a hypothetical right-half zero, the unchanged normalization has
`u=3/2-Re(rho)` in `(1/2,1)`. `tendsto_actual_prime_sub_fermi` applies the
general bound to its actual zero-isolating polynomial and quadratic
prime sieve. The actual Fermi parameter
`a_N=1-2*m_F(H_N)>1/2` is also allowed for every moving height schedule,
as proved by `tendsto_actual_prime_sub_margin_fermi`.

On the original squared cutoff schedule, the existing source theorem
gives `P_N -> -multiplicity(rho)`. The new independent comparison gives
`P_N-F_N -> 0`, so `tendsto_normalizedFermiPrimeLogResponse` proves
`F_N -> -multiplicity(rho)` as well. The correction decays; the surviving
prime source does not disappear under this weighting.

## Exact spectral transport of the complete complex moment

Let `h(a,B,y)` be the repository's actual Gaussian Fermi spectral density.
For `a>0,B>0`, it is nonnegative and has integral one. Its proved
characteristic function is

```text
integral_R h(a,B,y)*exp(i*y*x) dy
  = 2*exp(-B*x^2-a*x/2)*f(-a*x).
```

Define the regulated original moment by

```text
F_B(a,p,D,S,N,s) = sum_(r prime, r>D, r notin S)
  log(r)*K(p,N,s,r)*exp(-B*log(r)^2)*f(-a*log(r)).
```

[ZetaPrimeFermiHeatTransport](../RiemannGaussian/ZetaPrimeFermiHeatTransport.lean)
proves the exact full-series identity, for `Re(s)>1`:

```text
integral_R h(a,B,y)*P(p,D,S,N,s-i*y) dy
  = 2*F_B(a,p,D,S,N,s+a/2).
```

The entire complex polynomial remains inside the averaged moment. A
vertical shift only rotates each kernel. Its integrated norm is exactly
the original term's norm, because the density has unit mass. Summability
of the original Euler moment therefore pays for the complete interchange;
both the full average and its prime series are genuinely integrable.
The displayed ordinary-prime form uses `D>=1` and a finite prime sieve.

For the actual margin `m=m_F(H)>0`, choose `a=1-2*m`. Then
`integral_margin_density_primeLogResponse` proves

```text
integral_R h(1-2*m,B,y)*P(p,D,S,N,1+m+i*t-i*y) dy
  = 2*F_B(1-2*m,p,D,S,N,3/2+i*t).
```

The input line is `1+m`, in the Euler half-plane. Its convergence
hypothesis is discharged by the actual positive margin. This statement
holds for every complex polynomial and finite prime sieve.

The Gaussian multiplier has norm at most one for nonnegative width.
Dominated convergence proves `F_B -> F` as `B -> 0` for each fixed
moment order, and consequently the full spectral averages tend to
`2*F`. The terminal theorems are `tendsto_gaussianFermiPrimeLogResponse`
and `tendsto_integral_density_primeLogResponse`. The moment order, filter
and prime support are fixed during this limit. No interchange with
`N -> infinity` is asserted.

## The remaining analytic step

The full moment now has an exact spectral averaging identity. It does
not follow that the complex moment being averaged has a favorable sign.
The Gaussian zero budget controls a different arithmetic test; its
positivity cannot simply be differentiated or filtered and asserted for
`F_N`. An estimate using the new transport must retain the full complex
polynomial and prime support and remain valid as the moment order grows.
The proved fixed-order regulator limit alone does not pay for that step.

The subsequent [admissible moving-family theorem](prime-admissible-heat-source.md)
constructs order-dependent height floors and proves Gaussian removal along
every family above them, at squared-margin widths. The surviving signed
lower bound is still open; it is not implied by that independent comparison.

An independent cofinal lower bound with a fixed positive gap above
`-1` for the normalized surviving tail would close the original
contradiction. The decay estimate here bounds only `P_N-F_N`; neither
of those two main tails has received that lower bound. The original
unweighted tail remains an explicit definition and theorem interface.
RH remains open.

## Local verification

All three modules pass strict direct Lean elaboration and are imported by
the root library. Their focused build, whole-project declaration lint and
verbose module audits pass. All 34 terminal axiom audits for these modules
use only `propext`, `Classical.choice` and `Quot.sound`.

The latest full build and compiled inventory, including the subsequent
moving-family theorem, are recorded in its [verification section](prime-admissible-heat-source.md#local-verification).
These are local checks; this continuation is uncommitted.
