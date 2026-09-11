# A second proved zero-free improvement from Fermi feedback

Feeding the first proved Fermi region back into the actual zero budget
now gives a strictly stronger unconditional eventual region. Lean proves
that there exists a finite `T>=1` such that every genuine nontrivial zeta
zero `rho=beta+i*t` with `abs(t)>=T` satisfies

```text
4/(25*log(abs(t))) < beta < 1-4/(25*log(abs(t))).
```

The coefficient is exact. The threshold is existential and is not
numerically evaluated. The same development proves literal zeta
nonvanishing on the corresponding closed right edge and strict
improvement over the preceding global Fermi margin.

The terminal theorems are `exists_eventual_right_margin`,
`exists_eventual_strip`, `exists_eventual_nonvanishing` and
`exists_eventual_improved_region` in
[GaussianFermiBootstrapZeroFree](../RiemannGaussian/GaussianFermiBootstrapZeroFree.lean).
They have no remaining arithmetic or analytic premise. This is an
improvement within the repository, not a claim of a best published region
or historical priority. The external `4.896` theorem, the independent
signed ordinary-prime-tail bound and RH remain unproved here.

## A wider band margin does not increase the tail cost

The previous budget had its evaluation line fixed to the old reserve
margin. [GaussianFermiMarginBudget](../RiemannGaussian/GaussianFermiMarginBudget.lean)
allows any proved common margin `m` for the actual zeros in the height
band, with

```text
m_old(H) <= m <= 1/4,
m <= Re(rho) <= 1-m  whenever abs(Im(rho)) <= H,
m^2 <= B.
```

The full derivative cost at the line `sigma=1-m` is

```text
C(1-2*m,B,m)
 = exp(1/2)*(34*B+2*(2-3*m)^2+1)*sqrt(pi/(B/4)).
```

At fixed `B`, this decreases as `m` increases through the allowed range.
`integralCost_antitone_margin` proves that comparison, and
`outside_cost_le_allowance` transports it to the complete actual divisor
tail. Thus the **same old allowance** `E(B,H)` pays for every omitted
zero; the larger shift introduces no new tail hypothesis.

The general selected-zero and resonant-pair budgets retain the exact
prime phase combination, every selected zero, both distinct horizontal
partners and their actual analytic multiplicity. Exact signed pole and
target remainder identities remain available upstream. The source has
one full multiplicity, with no simplicity assumption.

In particular, `selected_zero_phase_budget_with_prime` keeps the literal
signed prime sum on the same side as the selected zero source:

```text
selected zero source + sum_j w_j*primeSum(1-2*m,B,omega_j*t)
 <= exact pole/gamma cost + (sum_j w_j)*E(B,H).
```

This theorem does not require a nonnegative cosine test. The sign-only
budget is a named downstream consequence for nonnegative tests. Any
independent stronger lower bound for this precise prime combination
would improve the source comparison by the same amount.

`fermi_resonant_pair_phase_bound` instantiates this interface with the
[already proved global Fermi margin](zeta-fermi-arithmetic-transport.md).
Its all-height strip and antitone property discharge the entire common
band hypothesis. This avoids assuming that the next proposed region is
already true.

## The new normalized interval comes from the earlier theorem

For a possible zero at positive height `t`, take

```text
L=log(t), H=48*t, m=m_F(H), sigma=1-m,
B=1/(9*L^2), b=c=B/2.
```

The preceding theorem proves that eventually
`m_F(H)=3/(20*log(H))`. Elementary bounds on `log(48)` then give

```text
149/1000 <= L*m <= 3/20
```

when `L>=100000` and that eventual formula applies. This is
`normalized_margin_bounds_of_eq` in
[GaussianFermiBootstrapProfile](../RiemannGaussian/GaussianFermiBootstrapProfile.lean).
The new scale lemma covers the general condition `L*m<=1/3`, which
proves `m^2<=B<=1` here. The old margin is no larger, so the old scale
condition required by the uniform allowance theorem also holds.

## Exact Gaussian bounds give another strict surplus

Retain the genuine Gaussian half-line transform

```text
G_B(x)=integral_(u>0) exp(-B*u^2-x*u) du.
```

The existing exact reflection, integrated tangent and dilation identities
give the rational bounds

```text
G_1(33/1000) >= 1739/2000,
G_1(-9/20) <= 121/100.
```

For every coarse coefficient family satisfying

```text
0<=a0<=37/200, a1>=79/250, M<=61/100,
```

the entire normalized interval above therefore satisfies

```text
a0*G_1(-3*mu)+M/12+1/20000
 <= a1*G_1(3*(4/25-mu)).
```

This is a general scalar theorem before its exact-family instance. The
same previously defined phase coefficients satisfy all the bounds;
none are fitted or changed. All small higher-frequency coefficients
remain in the total mass.

Exact dilation gives, for any candidate edge distance `d<=4/(25*L)`,

```text
a0*G_B(-m)+M*L/4+3*L/20000 <= a1*G_B(d-m).
```

The existing pole and gamma theorem bounds their full cost by
`a0*G_B(-m)+M*L/4+8`. Once the old allowance is below one, the weighted
tail cost is at most one. The actual resonant zero budget would then
require `3*L/20000<=9`, contradicting `L>=100000`.

The unconditional terminal theorem chooses a height beyond the actual
earlier margin transition, the elementary logarithmic threshold and the
uniform allowance threshold. Genuine reflection supplies the other
strip edge; the pole-removed zeta bridge supplies literal nonvanishing.

## What this establishes and what remains

One feedback step produces a proved additional exclusion without a larger
outside error. It does not prove that indefinitely repeating the method
converges to the critical line. Both widths are reciprocal-logarithmic
and tend to zero with height.

The numerical threshold is not `exp(100000)` alone: the earlier margin
transition and the whole-divisor allowance must also have become valid.
The former explicit all-height reserve region remains available. The
existing squarefree radius transport currently uses the first Fermi
width `3/20`; it is not silently replaced by the new coefficient.

The next analytic question is what part of the full margin budget could
force an exclusion deeper into the strip, including the retained prime
contribution. Another local edge improvement alone does not pay the
independent signed ordinary-prime tail needed by the original reductio.
The subsequent [all-family heat and profile audit](gaussian-phase-profile-ceiling.md)
proves a finite ceiling for this coarse Gaussian comparison at every
positive scale, including infinite phase families. It leaves the richer
signed explicit formula available for a stronger estimate.

## Local verification

All three modules pass strict direct elaboration. The focused build
passes with 4,627 jobs and the full warning-as-error build with 10,141
jobs. All 14 declaration linters pass in each new module; 20 explicit
theorem axiom audits use only `propext`, `Classical.choice` and
`Quot.sound`. Whole-project declaration lint and the compiled-environment
status audit pass. The inventory contains 1,294 project modules and
24,949 theorems, with zero project axioms and zero placeholder-dependent
declarations. Source, local links, README table formatting and whitespace
checks pass; Current Direction is one paragraph of 425 characters.
These are local validation results; remote CI is checked separately on the exact commit.
