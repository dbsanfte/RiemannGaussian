# Nearby Gaussian-cotangent compensation

The nearby-sign gap in the Gaussian strip comparison is now closed for
the actual zeta divisor. Every unselected nearby zero is compensated by
its own retained Poisson mass. Any selected finite set survives with its
exact complex source and full analytic multiplicities. These four modules
contain 43 public theorems. This is an analytic ingredient for the smoothed
prime/strip comparison. The downstream
[full phase-family surplus](zeta-gaussian-phase-band.md) now proves an
explicit zero-free band using this compensation.

## The complete source, including its center

For `B>0`, `eta>0`, set

```text
F_B(z) = integral_0^infinity exp(-B*v^2-z*v) dv,
p = pi/(2*eta),
G(B,eta,z) = F_B(z) + p*cot(p*z) - 1/z       (z != 0).
```

[CotangentRegularization](../RiemannGaussian/CotangentRegularization.lean)
constructs the entire divided sine using `dslope sin 0`, proves its true
center value is one and its center derivative is zero, and proves it has
no zero in the open disc of radius `pi`. Its scaled logarithmic derivative
is the genuine analytic representative of `p*cot(p*z)-1/z` on `norm(z)<2*eta`.
Consequently `G(B,eta,0)=F_B(0)`, with an actual analytic continuation
through the canceled pole. The singular quotient is not assigned a
convenient center value.

The exact signed cotangent identity is

```text
Re(cot(z)) = sin(Re(z))*cos(Re(z)) / norm(sin(z))^2.
```

It retains every imaginary coordinate and gives the favorable cotangent
sign for `0<=Re(z)<=pi/2`. On the imaginary diameter, the analytic
cotangent correction has real part zero, including at the center.

## Why the full nearby source has a lower bound

[AnalyticHalfDiscMinimum.re_lower_bound](../RiemannGaussian/AnalyticHalfDiscMinimum.lean)
proves a general real-part minimum principle on a complete closed right
half-disc. The proof applies the maximum-modulus principle to `exp(-F)`;
both endpoints, the entire diameter and the center remain in the domain.

[SmoothedCotangentSource.source_re_lower](../RiemannGaussian/SmoothedCotangentSource.lean)
then applies to every analytic transform with nonnegative real data on
the diameter and `norm(F(z)-1/z)<=C` on the semicircle. It proves
`Re(F(z)+correction(eta,z))>=-C` everywhere in the half-disc. This theorem
is general; no particular coefficient family is chosen.

For the actual Gaussian, the previously proved complete cosine sign and
cubic pole-remainder bound discharge every hypothesis. Thus

```text
Re(G(B,eta,z)) >= -12*B/eta^3
    when Re(z)>=0 and norm(z)<=eta.
```

See `gaussian_source_re_lower`. This controls the complete blended source;
positivity of the pure transform alone would not suffice.

## Compensation on the actual zeta divisor

Write `m_rho` for analytic multiplicity and `z_rho=s-rho`. For `Re(s)>=1`,
every `Re(z_rho)>0`. Put `A=24*B/eta^2`. On the open nearby ball
`norm(z_rho)<eta`, the existing shifted Poisson reserve is

```text
P_rho = m_rho*(Re(z_rho)+eta)/norm(z_rho+eta)^2
      >= m_rho/(2*eta).
```

The two coefficients match exactly:

```text
m_rho*Re(G(B,eta,z_rho)) + A*P_rho >= 0.
```

[compensated_nonneg](../RiemannGaussian/ZetaGaussianNearCancellation.lean)
proves this for every actual zero, with both terms restricted to the same
nearby ball. The complete cutoff boundary belongs to the far complement.
No simplicity assumption or unproved sign hypothesis is used.

The near carriers have genuinely finite divisor support. The original
complex pole remainder is absolutely summable, and Lean proves the exact
complex identity before taking real parts:

```text
sum_rho m_rho*(F_B(s-rho)-1/(s-rho))
  + sum_near m_rho*p*cot(p*(s-rho))
  = sum_near m_rho*G(B,eta,s-rho)
      + sum_far m_rho*(F_B(s-rho)-1/(s-rho)).
```

Call either side `E(B,eta,s)`. Combining pointwise compensation with the
retained far bound gives, for every finite set `S` of nearby zeros,

```text
-Re(E(B,eta,s)) <= A*Re(xi'/xi(s+eta))
  - sum_(rho in S) [m_rho*Re(G(B,eta,s-rho)) + A*P_rho].
```

`neg_re_tsum_le_sub_sum` actually allows any finite `S`, with the nearby
restriction explicit in its `compensated` summands. All unselected nearby
losses and the complete far tail are discharged. The exact signed
identity remains available upstream of this inequality.

## A selected zero at its own ordinate

For an actual zero `rho=beta+i*gamma`, let `u=1-beta`, and suppose
`0<u<eta<=1/4`. At `s=1+i*gamma`, the selected term is exactly

```text
Q(B,eta,rho) = m_rho*[halfGaussian(B,u)+p*cot(p*u)-1/u]
                 + A*m_rho/(u+eta).
```

Lean proves `Q>=0` and the unconditional comparison

```text
-Re(E(B,eta,1+i*gamma)) <= A*C_eta(gamma) - Q(B,eta,rho),

C_eta(t) = eta/(eta^2+t^2) + 1/eta + 448*log(22)
             + log(1+eta+abs(t))/2.
```

The terminal theorem is
[neg_re_tsum_le_elementary_sub_source](../RiemannGaussian/ZetaGaussianNearCancellation.lean).
There is no unknown xi value or omitted divisor tail in its allowance.

The elementary bounds `sin(x)<=x` and `cos(x)>=1-x^2/2` also prove
`cot(x)>=1/x-x/2` on `0<x<=pi/2`. Thus the selected correction obeys

```text
p*cot(p*u)-1/u >= -pi^2*u/(8*eta^2),

Q(B,eta,rho) >= m_rho*[halfGaussian(B,u)-pi^2*u/(8*eta^2)]
                 + A*m_rho/(u+eta).
```

The loss tends to zero linearly as `u` tends to zero at fixed `eta`.
`neg_re_tsum_le_elementary_gaussian_source` substitutes this lower bound
into the complete signed comparison. The exact cotangent source theorem
is retained alongside that estimate.

## Remaining obligation and scope

The subsequent [Gaussian prime/strip bridge](zeta-gaussian-strip-bridge.md)
now proves the exact original complex Gaussian von-Mangoldt identity and
its signed strip comparison at `Re(s)>1`. The whole nearby divisor retains
its ordinates and multiplicities; the smoothed pole recombines exactly and
the complete Archimedean response has an explicit averaging allowance.
The boundary evaluation `Re(s)=1` still requires the appropriate proved
limit or boundary identity.

The [previous remainder development](zeta-gaussian-pole-remainder.md) and
[complete unsmoothed strip budget](zeta-strip-phase-budget.md) provide the
upstream ingredients. The subsequent
[full phase-family cost](zeta-gaussian-phase-band.md) now proves a rational
surplus, an explicit zero-free band, and three exact matching-height width
comparisons. The independent ordinary-prime lower bound and RH remain open.
Exhaustive world-record and historical novelty review remains.

## Local validation

All four modules pass direct elaboration with warnings treated as errors
and are imported by the root library. The focused build passes 4,625 jobs;
the full build passes 10,331. Root verbose lint reports zero errors across
19,689 declarations and 11,606 generated declarations, using all 14 linters.
Whole-project declaration lint also passes. All 43 public theorems have
explicit transitive axiom audits containing only `propext`,
`Classical.choice` and `Quot.sound`.

The full compiled-environment status audit passes, with zero project axioms
and zero placeholder-dependent declarations; `rhImplied` remains false.
The source scan includes untracked Lean files. These counts record the
original four-module compensation checkpoint.
