# Gaussian source comparison for genuine right-half zeros

The general Fermi phase budget now has a quantitative target-zero lower
bound and a proved pole upper envelope. The resulting theorem compares
one-dimensional Gaussian integrals, explicit gamma costs and the complete
outside-zero allowance. Every analytic hypothesis is discharged for the
actual zeros and transforms.

The new root-imported modules are
[GaussianFermiLaplaceOrder](../RiemannGaussian/GaussianFermiLaplaceOrder.lean)
and [GaussianFermiResonantBudget](../RiemannGaussian/GaussianFermiResonantBudget.lean).
The terminal theorem is `resonant_pair_phase_bound`.

The [subsequent Gaussian comparison](gaussian-fermi-zero-free-region.md)
now proves the stronger eventual width `3/(20*log(abs(t)))`, including
literal nonvanishing and strict improvement over the preceding region.
Its finite height threshold is proved to exist, not numerically evaluated.
The published `4.896` region, the original signed ordinary-prime-tail bound
and RH remain unproved here.

## Keep the exact signed partition before comparing the two sides

For `B>0`, use the original ideal transform and the Gaussian half-line
integral:

```text
F_(a,B)(x) = integral_(u>0) exp(-B*u^2-x*u)/(1+exp(-a*u)) du,
G_B(x)    = integral_(u>0) exp(-B*u^2-x*u) du.
```

At real `x`, the original complex Fermi transform has this real part.
Both integrals are finite for every real damping, including negative
values. The positive integrands show that each is decreasing in `x`.
`transform_real_partition` specializes the existing exact identity:

```text
F(x) + F(a+x) = G_B(x).
```

The next two comparisons use the same identity with different damping
arguments. Their exact signed remainders remain available upstream.

## The target-zero pair gains a nonnegative reserve

At any real displacement `x`, the exact reflected pair is

```text
F(x) + F(a-x) = G_B(x) + [F(a-x)-F(a+x)].
```

For `x>=0`, monotonicity makes the bracket nonnegative. Consequently

```text
F(x) + F(a-x) >= G_B(x).
```

`real_pair_eq_halfGaussian_add_reserve` retains the full identity;
`halfGaussian_le_real_pair` proves its lower-bound consequence. No norm
separates the original two terms before the reserve's sign is proved.

For an actual zero `rho=beta+i*gamma`, evaluation at its own ordinate
`s=sigma+i*gamma` makes both physical partner arguments real:

```text
x=sigma-beta,             a=2*sigma-1,
s-rho=x,                 s-(1-conj(rho))=a-x.
```

`contribution_at_ordinate` proves this exact specialization. The existing
zero-free margin supplies `x>=0` on the chosen interior evaluation line.

There is a normalization issue that must be retained through this step.
The contribution function is

```text
Q_(B,sigma,gamma)(rho) = multiplicity(rho)/2 * [F(x)+F(a-x)].
```

For `beta>1/2`, the zero and its horizontal partner `1-conj(rho)` are
distinct genuine zeros. Their analytic multiplicities are equal and
their full `Q` contributions are equal. Therefore selecting both gives

```text
sum_(eta in {rho,1-conj(rho)}) Q_(B,sigma,gamma)(eta)
  = 2*Q_(B,sigma,gamma)(rho)
  >= multiplicity(rho)*G_B(sigma-beta).
```

`sum_partner_pair_eq` proves the exact factor, and
`halfGaussian_le_partner_pair` proves the Gaussian lower bound. No
simplicity assumption is used.

## The constant pole loses a nonnegative reserve

The actual constant-frequency pole is

```text
Pole_(B,sigma)(0) = F_(a,B)(sigma)+F_(a,B)(sigma-1).
```

Applying the partition at `sigma-1` gives the exact identity

```text
Pole_(B,sigma)(0)
  = G_B(sigma-1) - [F_(a,B)(3*sigma-2)-F_(a,B)(sigma)].
```

For `sigma<=1`, `3*sigma-2<=sigma`, so monotonicity makes this bracket
nonnegative. Thus the complete constant pole is at most
`G_B(sigma-1)`. A separate absolute estimate on each pole would miss this
useful sign. The exact identity and its upper bound are both proved in
`pole_zero_eq_halfGaussian_sub_reserve` and `pole_zero_le_halfGaussian`.

For nonzero frequency `v`, the earlier whole-pair integrations by parts
already supply

```text
abs(Pole_(B,sigma)(v)) <= C(2*sigma-1,B,1-sigma)/v^2,
C(a,B,delta) = exp(1/2)*(34*B+2*(2*a+delta)^2+1)*sqrt(pi/(B/4)).
```

`abs_polePair_le` discharges its geometry for
`1/2<=sigma<=1` and `(1-sigma)^2<=B`. Combining both cases defines the
explicit envelope

```text
U_(B,sigma)(v) = G_B(sigma-1)                        if v=0,
              = C(2*sigma-1,B,1-sigma)/v^2           otherwise.
```

`polePair_le_poleUpper` proves `Pole(v)<=U(v)` at every real frequency.
The nonzero-frequency estimate retains its frequency dependence; a
family with small or changing frequencies must pay that cost.

## The resulting general theorem for actual zeros

Let `rho=beta+i*gamma` be a genuine zero with `beta>1/2`. Take any finite
index set `J`, nonnegative weights `w_j`, and real frequencies `omega_j`
such that

```text
sum_j w_j*cos(omega_j*x) >= 0   for every real x.
```

Choose an index `j0` with `omega_j0=1`, so that this phase evaluates at
the zero's own ordinate. Let

```text
sigma=1-m(H),   B=b+c,
A(v)=5/4+abs(v),
GammaUpper(v)=(log(A(v))-log(pi))/4+7/(8*A(v)).
```

The exact hypotheses are

```text
H>=1,  b,c>0,  m(H)^2<=B<=1,
abs(gamma)<=H,  2*abs(omega_j*gamma)<=H for every j in J.
```

`resonant_pair_phase_bound` proves

```text
w_j0 * multiplicity(rho) * G_B(sigma-beta)
  <= sum_j w_j * [U_(B,sigma)(omega_j*gamma)
                  + GammaUpper(omega_j*gamma)]
       + (sum_j w_j)*E(B,H).
```

The earlier allowance theorem gives
`E(B,H)<=K*log(H+2)/sqrt(H)`, uniformly over the admissible Gaussian
scales. The prime series has its favorable sign by the full finite-phase
theorem. The [gamma estimate](gaussian-fermi-gamma-bound.md) is explicit
and uniform. All remaining selected zero contributions are nonnegative
by the proved region, so keeping one resonant phase gives a valid lower
bound for the full weighted selected-zero sum.

This is a proved necessary inequality for every such actual zero and
every admissible finite family. It assumes no arithmetic tail bound.
The [subsequent independent surplus](gaussian-fermi-zero-free-region.md)
chooses admissible scales and uses the already defined exact phase family
to prove that its Gaussian source exceeds these upper costs for the
eventual width `3/(20*log(abs(t)))`. All tail conditions are discharged.
A numerical height threshold has not yet been certified.

## Local verification of the resonant checkpoint

All local gates pass: direct warning-as-error checks for both modules,
the focused build (4,619 jobs), full build (10,132 jobs), all 14 declaration
linters, 16 terminal axiom audits, the whole-project declaration lint and
the compiled-environment soundness generator. The inventory contains
1,285 modules and 24,832 theorems, with zero project axioms and zero
placeholder-dependent declarations. Audited theorems use only `propext`,
`Classical.choice` and `Quot.sound`. Source, whitespace, README links and
table formatting pass; Current Direction is one paragraph of 449
characters. These are local validation results; remote CI is checked
separately on the exact commit.
