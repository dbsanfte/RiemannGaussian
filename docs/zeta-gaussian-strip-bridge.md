# The original Gaussian prime sum and complete strip source

The Gaussian prime series, the actual complete xi divisor and the signed
strip boundary now share a proved identity and inequality. The eight modules
in this slice contain 70 public theorems. The terminal theorem
[prime_add_source_le](../RiemannGaussian/ZetaGaussianStripBound.lean)
retains an actual zero's Gaussian source and its own Poisson reserve, with
explicit allowances for the complete zero correction and the completion
error. The preceding signed theorem retains the exact completion difference.

This bridge holds at genuine Euler centers `Re(s)>1`. It does not yet
prove a larger zero-free region or evaluate an existing height threshold.

## One common complex Gaussian average

For `B>0`, write

```text
mass(B) = sqrt(pi/(1/(4B))),
g_B(y) = exp(-y^2/(4B))/mass(B),
Avg_B(f) = integral_R g_B(y)*f(y) dy,
F_B(z) = integral_0^infinity exp(-B*v^2-z*v) dv.
```

[GaussianVerticalAverage](../RiemannGaussian/GaussianVerticalAverage.lean)
proves genuine integrability, mass one, and the full complex Fourier identity
`Avg_B(exp(i*y*x))=exp(-B*x^2)`. The same average acts on the original complex
Euler series. If `s=sigma+i*t` and `sigma>1`, then

```text
P_B(s) = sum_(n>=1) Lambda(n)*n^(-s)*exp(-B*log(n)^2)
       = Avg_B(-zeta'/zeta(s-i*y)).
```

[ZetaGaussianPrimeAverage](../RiemannGaussian/ZetaGaussianPrimeAverage.lean)
proves the complex absolute convergence and infinite sum-integral exchange.
Its real part is the existing `GaussianFermiPrimeComparison.ordinarySum`.
The Gaussian prime series itself is also proved absolutely summable at
`sigma=1`; the Euler averaging theorem is stated only for `sigma>1`.

[GaussianComplexPoleAverage](../RiemannGaussian/GaussianComplexPoleAverage.lean)
proves, for every complex `z` with `Re(z)>0`,

```text
Avg_B(1/(z-i*y)) = F_B(z),
Avg_B(1/(z-i*y)-1/z) = F_B(z)-1/z.
```

The proof uses a genuinely integrable complex product kernel and Fubini.
It retains arbitrary imaginary displacement. No pairing or ordinate
alignment is needed for these identities.

## The complete actual divisor and completion

[ZetaGaussianPoissonAverage](../RiemannGaussian/ZetaGaussianPoissonAverage.lean)
integrates every multiplicity-weighted actual Poisson term. The already
proved summability of the Gaussian divisor mass supplies the complete
sum of norm integrals. Thus, for `Re(s)>=1`,

```text
integral_R g_B(y)*Re(xi'/xi(s-i*y)) dy
  = sum_rho m_rho*Re(F_B(s-rho))
  = Re(xi'/xi(s)) + Re(sum_rho m_rho*(F_B(s-rho)-1/(s-rho))).
```

These real integrals are genuinely integrable, including at `Re(s)=1`.
The unpaired complex pole series is not claimed absolutely convergent.

Let `C(s)=zetaGlobalRegularCorrection(s)` be the original complete
Archimedean correction and `C_B(s)=Avg_B(C(s-i*y))`.
[ZetaGaussianCompletionAverage](../RiemannGaussian/ZetaGaussianCompletionAverage.lean)
retains this full complex response and proves

```text
norm(C_B(s)-C(s)) <= 4B/mass(B),    Re(s)>0.
```

The proof uses the actual correction's complex Lipschitz bound and the
exact first absolute Gaussian moment. No Gamma or rational term is omitted.

The exact complex identity in
[ZetaGaussianSmoothedIdentity](../RiemannGaussian/ZetaGaussianSmoothedIdentity.lean)
is

```text
P_B(s) + Avg_B(xi'/xi(s-i*y)) = F_B(s-1) + C_B(s),    Re(s)>1.
```

Its real projection and the actual divisor formula give the signed relation

```text
Re(P_B(s)) - Re(-zeta'/zeta(s))
  = Re(F_B(s-1)-1/(s-1)) + Re(C_B(s)-C(s))
      - Re(sum_rho m_rho*(F_B(s-rho)-1/(s-rho))).
```

## Retaining all nearby strip zeros

The earlier strip constraint passed one selected zero at the center's
ordinate to the limit. That is insufficient for Gaussian compensation,
which needs the entire nearby cotangent sum.
[ZetaStripFiniteSource](../RiemannGaussian/ZetaStripFiniteSource.lean)
proves the required stronger interface for every finite group `S` of
actual zeros in `abs(Re(rho-c))<eta`:

```text
Re(-zeta'/zeta(c))
  + sum_(rho in S) Re(m_rho*p*cot(p*(c-rho)))
  <= boundary(c,eta,M) + Re(1/(c-1)-1/(c+1)),

p = pi/(2*eta).
```

Here `Re(c)>1`, `eta>0`, `1/2<=Re(c)-eta`, `Re(c)+eta<=3/2`, and `M>=0`.
The two complete vertical integrals in `boundary` retain the original
right sign and the left logarithm clipped at negative depth `M`.

Distinct zeros have distinct disc coordinates. Every selected term is
bounded by the complete favorable finite divisor, and all selected zeros
enter the coordinate windows simultaneously. The finite sum then passes
to its exact cotangent limit. Each ordinate and analytic multiplicity is
retained; no infinite divisor limit is assumed.

The actual open ball `norm(c-rho)<eta` is finite and lies in this strip.
Its cotangent sum is exactly the previous `nearCotangent` carrier, so the
complete nearby source can be inserted in the inequality.

## The resulting Gaussian strip bound

Write `A=24B/eta^2` and let `Q_rho` denote the earlier nonnegative
`compensated` contribution, with its nearby restriction. For every finite
set `S`, the signed terminal bridge is

```text
Re(P_B(s)) + sum_(rho in S) Q_rho
  <= boundary(s,eta,M) + Re(F_B(s-1)) - Re(1/(s+1))
       + Re(C_B(s)-C(s)) + A*Re(xi'/xi(s+eta)).
```

This is [prime_add_selected_le](../RiemannGaussian/ZetaGaussianStripBound.lean).
The original pole term and its smoothing remainder recombine exactly into
`F_B(s-1)`. All nearby losses and the complete distant divisor are paid for
by the previously proved compensation; no zero-side sign premise remains.

If `delta=sigma+eta-1<=1/4`, the last two terms have explicit allowances

```text
Re(C_B(s)-C(s)) <= 4B/mass(B),
Re(xi'/xi(s+eta)) <= C_delta(t),
C_delta(t) = delta/(delta^2+t^2) + 1/delta + 448*log(22)
                + log(1+delta+abs(t))/2.
```

For a selected `rho=beta+i*gamma`, put `s=sigma+i*gamma` and
`d=sigma-beta<eta`. Its exact source is

```text
Q_rho = m_rho*[halfGaussian(B,d)+p*cot(p*d)-1/d]
           + A*m_rho/(d+eta)
      >= m_rho*[halfGaussian(B,d)-pi^2*d/(8eta^2)]
           + A*m_rho/(d+eta).
```

`prime_add_source_le` inserts this lower bound and both explicit allowances
into the same literal prime/strip inequality. The richer exact identities
remain available for sharper estimates.

## Remaining quantitative work

The subsequent [full Gaussian phase-family theorem](zeta-gaussian-phase-band.md)
now combines this inequality on a common scale and proves a complete rational
surplus on an explicit height band. It retains all three prime responses,
charges the right Euler cost only to the constant channel, and keeps the
selected source with its multiplicity. The existing exact family supplies
every hypothesis of the resulting actual zero exclusion.

A boundary version at `sigma=1` still needs a justified limit of the final
inequality or a proved boundary identity. Directly substituting `sigma=1`
inside the Euler pole average can lose its boundary mass and is not licensed
by the Euler-half-plane theorem. Keeping a positive center shift is also
available if its full quantitative cost is acceptable.

For future region integration, proved exclusions combine by union, preserving
their height domains and endpoint conventions. The existing
[general band interface](../RiemannGaussian/ZetaZeroFreeRegionBand.lean)
combines valid widths by their maximum. The underlying signed identities,
zero terms and arithmetic estimates remain separate reusable inputs; an
envelope of region widths alone does not encode them.

The downstream band has explicit heights and three exact benchmark-function
comparisons. The eventual component retains its unevaluated thresholds.
An exhaustive world-record and historical novelty audit, the independent
ordinary-prime floor and RH remain open.

## Local validation

All eight modules pass direct elaboration with warnings treated as errors
and are imported by the root library. The focused build passes 4,805 jobs;
the full build passes 10,339. Root verbose lint reports zero errors across
19,776 declarations and 11,620 automatically generated declarations, with
all 14 linters. Whole-project declaration lint also passes. All 70 public
theorems have explicit transitive axiom audits containing only `propext`,
`Classical.choice` and `Quot.sound`.

The compiled inventory contains 1,492 project modules, 31,434 declarations
and 27,584 theorems. It has zero project axioms and zero placeholder-dependent
declarations; `rhImplied` remains false. These counts record the original
eight-module bridge checkpoint.
