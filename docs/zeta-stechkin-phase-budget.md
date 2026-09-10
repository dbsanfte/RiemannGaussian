# Reflected Stechkin comparison and the arbitrary-family source budget

The compiled terminals are
`zetaPhase_stechkin_source_add_finite_primeWork_le` and
`phase_shifted_source_add_primeWork_le_stechkin_split` in
[ZetaStechkinPhaseBudget.lean](../RiemannGaussian/ZetaStechkinPhaseBudget.lean).
They reduce the analytic allowance while retaining the full selected
right-half zero source and a proved sign for every omitted zero pair.
The independent arithmetic inequality required for RH remains open.

The [Euler-boundary extension](zeta-stechkin-euler-boundary.md) now proves
the exact limit after subtracting the entire pole family, retaining the
signed completion and the full source at `sigma=1`. This is a proved
boundary passage, not the missing arithmetic lower bound.

## Algebraic comparison

For an evaluation abscissa `sigma >= 1`, set

```
tau = (1 + sqrt(1 + 4*sigma^2))/2
c   = sigma/(2*tau - 1).
```

[ZetaStechkinComparison.lean](../RiemannGaussian/ZetaStechkinComparison.lean)
proves `tau*(tau-1)=sigma^2`, `sigma<tau`, `0<c<1`, and
`1/sqrt(5)<=c`. The coefficient and auxiliary line are defined
mathematically; there is no numerical search.

For `0<beta<1` and any real displacement `t`, write

```
F(sigma,beta,t) = (sigma-beta)/((sigma-beta)^2+t^2)
               + (sigma-1+beta)/((sigma-1+beta)^2+t^2).
```

The parameterized theorem `stechkinPoissonPair_comparison` proves
`c*F(tau,beta,t)<=F(sigma,beta,t)` whenever `sigma<=tau`,
`sigma^2<=tau*(tau-1)`, and `c*(2*tau-1)<=2*sigma-1`.
At the selected ordinate, the stronger condition
`c*(2*tau-1)<=sigma` gives

```
1/(sigma-beta) <= F(sigma,beta,0) - c*F(tau,beta,0).
```

Both conditions hold for the displayed algebraic choice. The proof
retains the reflection displacement in the exact rational numerator;
it does not estimate the two zero atoms separately.

This is a version of the classical Stechkin comparison, discussed in
[Kadiri, *Explicit zero-free regions for Dedekind zeta functions*,
Lemma 2.1](https://www.cs.uleth.ca/~kadiri/articles/zero-free-region-Dedekind-June07-2011.pdf).
The Lean proof is an independent algebraic derivation. No mathematical
priority claim is made for the comparison or its formalized consequences.

## Actual zero sums, with multiplicities

[ZetaStechkinBudget.lean](../RiemannGaussian/ZetaStechkinBudget.lean)
uses the genuine reflection `rho -> 1-conj(rho)`, whose multiplicity
equals that of `rho`. Each summand is half the complete reflected
comparison. Reindexing the absolutely convergent series proves that
its total is exactly the original Poisson mass at `sigma` minus `c`
times the mass at `tau`. Critical-line fixed points are counted once.

Every such combined summand is nonnegative. A right-half zero has a
distinct reflected partner, so selecting both yields its entire
original source `m/(sigma-Re(rho))`. The hypothesis
`1/2<Re(rho)` is explicit; treating a critical-line fixed point as two
distinct zeros would invalidate that source-selection argument.

The prime weights also remain nonnegative:

```
w(m) = Lambda(m)*(exp(-sigma*log(m)) - c*exp(-tau*log(m))) >= 0.
```

The exact signed completion is retained before estimating it. Existing
horizontal monotonicity proves

```
Re R(sigma+it) - c*Re R(tau+it)
  <= (1-c)*(1+log(sigma+abs(t))).
```

Thus the logarithmic coefficient is reduced by at least `1/sqrt(5)`.
This compares the analytic allowance only: the prime weights and pole
budget have also changed.

The transfer theorem `zetaPhase_stechkin_primeWork_bounds` preserves
existing arithmetic floors for every nonnegative phase kernel:
`(1-c)*W_original <= W <= W_original`. This states the exact possible
loss when reusing a previously proved prime-work lower bound.

## All admissible families and shifted sources

Let `a(n)>=0` be summable, with arbitrary real frequencies `omega(n)`.
At each ordinate `y`, assume the logarithmic height cost
`sum a(n)*(1+log(sigma+abs(omega(n)*y)))` is summable. These conditions
include finite and countably infinite support. The complete zero sum
is formed first at each frequency; no exchange of the zero and
frequency sums is asserted.

The exact phase identity retains the complete signed prime work, the
nonnegative reflected zero mass, the elementary pole comparison, and
the signed completion. For a nonnegative phase kernel, any finite
prime-power window gives a lower bound on the complete prime work.
Selecting an actual right-half zero at a frequency equal to one gives
the terminal finite-window inequality.

For integer frequencies, coefficient summability and a summable
logarithmic frequency moment discharge the height condition. Write

```
d = 1-Re(rho),  sigma = 1+kappa*d,  kappa>0,
A = sum(n>=1) a(n),  L = sum(n>=1) a(n)*log(n),
S = a(1)*m/(kappa+1) - a(0)/kappa,
H = a(0)*(1+log(sigma)) + A*(1+log(sigma+abs(Im(rho)))) + L.
```

For the full comparison prime work `W`, the compiled shifted theorem is

```
S + d*W <= d*(1-c)*H + kappa*A*d^2/Im(rho)^2.
```

The normalized source is unchanged. No coefficient family or frequency
count is selected in this theorem.

## Remaining obligation

The full horizontal subtraction from the
[preceding comparison](zeta-horizontal-phase-budget.md) has zero total
horizontal weight and sign-changing zero terms. The present partial
subtraction has positive total weight `1-c`; its logarithmic height
condition and residual Gamma cost remain. It therefore does not
contradict the zero-total-weight positivity obstruction.

The estimate supplies a smaller analytic allowance with a justified
nonnegative omitted zero background. Its
[three-height consequence](zeta-stechkin-zero-free.md) now proves a
literal zero-free strip with edge margin `1/(64*log(abs(t)+22))` above
absolute height one. The independent arithmetic floor needed to beat
the budget for every hypothetical right-half zero remains open. No
new zero-proportion certificate or RH proof follows.
