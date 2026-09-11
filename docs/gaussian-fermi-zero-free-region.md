# A stronger eventual zero-free region from the Fermi phase budget

Lean now proves an unconditional stronger region at sufficiently large
height. There is a finite `T>=1` such that every genuine nontrivial zeta
zero `rho=beta+i*t` with `abs(t)>=T` satisfies

```text
3/(20*log(abs(t))) < beta < 1-3/(20*log(abs(t))).
```

The same development proves literal nonvanishing on the closed right edge
`Re(s)>=1-3/(20*log(abs(Im(s))))`, for sufficiently large `abs(Im(s))`.
It also proves that this width strictly exceeds the preceding
[all-height reserve margin](zeta-pole-reserve-bootstrap.md) at sufficiently
large ordinates.

The threshold is proved to exist; it is not numerically evaluated.
In particular, the algebraic condition `log(abs(t))>=4000` used below is
not by itself a certified full threshold: the complete divisor-tail
allowance must also be below one. The previous explicit all-height
region remains available at every ordinate.

The terminal theorems in
[GaussianFermiZeroFree](../RiemannGaussian/GaussianFermiZeroFree.lean) are
`exists_eventual_right_margin`, `exists_eventual_strip`,
`exists_eventual_nonvanishing` and `exists_eventual_improved_region`.
No arithmetic hypothesis remains in these statements. This is a stronger
result within the repository; no historical novelty or best-published-region
claim is made. The external `4.896` theorem, the original signed
ordinary-prime-tail bound and RH remain open.

## The analytic inputs were already connected to the actual divisor

The [general resonant budget](gaussian-fermi-resonant-budget.md) selects
both distinct horizontal partners of an actual right-half zero. Their
equal analytic multiplicities cancel the pair-counting factor of two.
At the zero's own ordinate, the source is at least one full multiplicity
times a Gaussian half-line transform. The full prime series has its
favorable sign only after the finite phases are combined.

The constant Fermi pole has a Gaussian upper bound with an exact
subtractive reserve, while the target pair has a Gaussian lower bound
with an exact additive reserve. Both identities remain upstream. The
gamma bound is explicit and uniform over shrinking scales. The whole
outside divisor is paid for by the previously proved vanishing allowance.

This continuation proves the independent scalar comparison that was
missing from that budget. Four new root-imported modules implement it:

- [GaussianHalfLaplaceBounds](../RiemannGaussian/GaussianHalfLaplaceBounds.lean):
  exact Gaussian reflection and dilation, an integrated tangent, and
  rational enclosures for the two required integrals.
- [GaussianFermiProfileSurplus](../RiemannGaussian/GaussianFermiProfileSurplus.lean):
  a strict surplus for every coefficient family satisfying coarse bounds,
  instantiated for the repository's existing exact phase family.
- [GaussianFermiHeightBounds](../RiemannGaussian/GaussianFermiHeightBounds.lean):
  the actual normalized margin interval, admissible scales, and complete
  finite-family pole and gamma upper bounds.
- [GaussianFermiZeroFree](../RiemannGaussian/GaussianFermiZeroFree.lean):
  the actual-zero contradiction, tail removal, both strip edges, literal
  nonvanishing and strict comparison with the preceding region.

## Exact Gaussian identities give rational bounds

Retain the genuine integral

```text
G_B(x) = integral_(u>0) exp(-B*u^2-x*u) du,  B>0.
```

The Gaussian moment and exponential tangent give

```text
G_B(0) = sqrt(pi/B)/2,
integral_(u>0) u*exp(-B*u^2) du = 1/(2*B),
G_B(x) >= sqrt(pi/B)/2-x/(2*B).
```

The two reflections reconstruct the entire real Gaussian atom:

```text
G_B(x)+G_B(-x) = sqrt(pi/B)*exp(x^2/(4*B)).
```

Consequently the same tangent gives an upper bound at negative damping:

```text
G_B(-x) <= sqrt(pi/B)*(exp(x^2/(4*B))-1/2)+x/(2*B).
```

Every real damping argument has genuine Gaussian integrability. Exact
positive dilation also gives

```text
r*G_(B*r^2)(x*r) = G_B(x),  r>0.
```

The new rational enclosures, proved from these identities and mathlib's
checked bounds on `pi` and the exponential, are

```text
G_1(3/20) >= 811/1000,
G_1(-63/200) <= 109/100.
```

No floating-point value enters the proof.

## A uniform surplus for coarse coefficient bounds

Let `a0` be the constant coefficient, `a1` the coefficient at frequency
one, and `M` the total nonconstant coefficient mass. For every family with

```text
0<=a0<=37/200,  a1>=79/250,  M<=61/100,
```

and every normalized interior margin `1/10<=mu<=21/200`, monotonicity and
the two Gaussian enclosures prove

```text
a0*G_1(-3*mu) + M/12 + 1/400
  <= a1*G_1(3*(3/20-mu)).
```

`profile_surplus` is general over these coefficient bounds. The existing
exact contact family satisfies them by its already proved rational
enclosures. Its full coefficient mass is also at most one. All nine
frequencies `0,1,2,3,4,7,10,13,24`, including the small higher-frequency
coefficients, remain in these mass bounds. No new coefficient family is
fitted.

For `L>0`, `B=1/(9*L^2)`, `mu=L*m` and any edge distance
`d<=3/(20*L)`, exact dilation transfers the surplus to

```text
a0*G_B(-m) + M*L/4 + 3*L/400 <= a1*G_B(d-m).
```

`scaled_profile_surplus` is the general statement, and
`exact_scaled_profile_surplus` is its actual exact-family instance.

## The existing width supplies the entire parameter interval

For a possible zero at height `t=abs(Im(rho))`, set

```text
L=log(t),  H=48*t,  m=m_old(H),  sigma=1-m,
B=1/(9*L^2),  b=c=B/2.
```

All exact-family evaluation ordinates lie inside `H/2`. The existing
closed formula for `m_old` and elementary logarithmic comparisons prove

```text
1/10 <= L*m_old(48*t) <= 21/200     when L>=2000.
```

This is `normalized_margin_bounds`, proved for the actual margin rather
than supplied as an assumption about zeros. `scale_admissible` then proves
`m^2<=B<=1`. The existing region also places every zero in the height band
inside the reflection-positivity strip.

## Bounded remaining costs cannot absorb the growing surplus

For `L>=4000`, the previously proved derivative cost is at most `3440*L`.
Every nonconstant frequency in the exact family is at least one, so its
pole is at most one. The gamma upper bound is at most `L/4+7` for every
nonconstant mode and at most `7` for the constant mode. The full
coefficient mass is at most one. `exact_phase_cost_le` therefore proves

```text
sum_j a_j*(PoleUpper_j+GammaUpper_j)
  <= a0*G_B(-m)+M*L/4+8.
```

Once the actual whole-divisor allowance `E(B,H)` is below one, its weighted
cost is also at most one. The genuine resonant budget would then require

```text
a1*G_B(d-m) <= a0*G_B(-m)+M*L/4+9.
```

The independent Gaussian surplus makes this impossible for
`d<=3/(20*L)`: it adds `3*L/400`, which is at least `30` when `L>=4000`.
The actual multiplicity is at least one, so multiple zeros cannot weaken
the contradiction.

`margin_lt_one_sub_re_of_allowance_lt_one` proves this finite-height
implication. `exists_eventual_right_margin` then discharges the tail
condition with the existing **uniform** allowance theorem, valid for all
admissible scales. Reflection supplies the other edge. The pole-removed
zeta bridge proves literal nonvanishing, including points outside the
critical strip, without assuming in advance that a putative zero is
nontrivial.

## Scope and next work

The coefficient `3/20` is exact. The height threshold is existential, and
the stronger width tends to zero as height grows. This is not a global
half-strip exclusion or a proof of RH. It does not independently bound
the original signed ordinary-prime tail.

The [subsequent arithmetic transport](zeta-fermi-arithmetic-transport.md)
now proves an all-height monotone margin, larger analytic discs and
stronger geometric decay for every fixed marked squarefree response.
The [subsequent interior bootstrap](gaussian-fermi-bootstrap-zero-free.md)
now proves the stronger eventual coefficient `4/25`, with no larger
outside allowance. A numerical all-height application also
needs the threshold evaluated and the remaining finite heights covered.
The published `4.896` region has not been reproduced.

## Local verification

All local gates pass: strict direct elaboration of all four new modules,
the focused build (4,623 jobs), the full warning-as-error build (10,136
jobs), all 14 declaration linters, 26 terminal axiom audits, the
whole-project declaration lint and the compiled-environment soundness
generator. The inventory contains 1,289 modules and 24,895 theorems, with
zero project axioms and zero placeholder-dependent declarations. Audited
theorems use only `propext`, `Classical.choice` and `Quot.sound`. Source,
whitespace, README links and table formatting pass; Current Direction is
one paragraph of 448 characters. These are local validation results; remote CI is checked separately on the exact commit.
