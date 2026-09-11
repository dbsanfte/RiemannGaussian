# Heat constraints and the scope of Gaussian feedback

Two new modules test the present Gaussian feedback mechanism over every
summable nonnegative phase family, including countably infinite support.
They prove a necessary spectral constraint and a ceiling for the specific
source-versus-cost profile used in the zero-free comparison. They do not
prove a new zero-free region or an obstruction to RH itself.

The latest unconditional eventual zero-free width remains
`4/(25*log(abs(t)))`, with an existential height threshold. See the
[actual zero-free theorem and proof](gaussian-fermi-bootstrap-zero-free.md).

## Keep the entire heat spectrum first

Let `a_n>=0`, `sum_n a_n<infinity`, and let `omega_n` be arbitrary real
frequencies. Assume the full cosine kernel is nonnegative:

```text
P(y) = sum_n a_n*cos(omega_n*y) >= 0  for every real y.
```

This is the phase-test design condition already used in the arithmetic
chain, not an unproved condition on zeta. No frequency spacing,
integrality, injectivity or finite-support assumption is made.

[GaussianPhaseHeatConstraint](../RiemannGaussian/GaussianPhaseHeatConstraint.lean)
uses the existing positive Fermi Gaussian probability density `density(1,c,y)`,
with `c>0`. Its exact characteristic weight is

```text
q_c(x) = 2*signal(1,c,x)
       = exp(-c*x^2)*q_0(x).
```

The Fermi factor stays in `q_0`; this is not an identification with a
bare Gaussian probability measure. Positivity and exact unit mass give
`0<=q_c(x)<=1`.

The exact product-to-sum identity, integrated against the actual density,
gives

```text
sum_n a_n*[q_c(omega_n)
  -(q_c(omega_n+xi)+q_c(omega_n-xi))/2]
 = integral density(1,c,y)*P(y)*(1-cos(xi*y)) dy
 >= 0.
```

`integral_probe`, `heat_deficit_eq_integral` and `heat_deficit_nonneg`
prove the individual evaluation, full signed identity and nonnegative
full sum. `summable_integral_norm_probe` pays for the entire
interchange with the explicit envelope `2*a_n`. The finite-scale theorem
retains both translated frequencies and their proximity to resonance;
it remains available before the following limit is taken.

## Exact mass extraction, including accumulating frequencies

Define

```text
A(xi) = sum_(omega_n=xi) a_n,
H_c(xi) = sum_n a_n*q_c(omega_n-xi),
M = sum_(omega_n!=0) a_n.
```

Every restricted sum is genuinely summable. As `c` tends to infinity,
`q_c(x)` tends to one at zero and to zero elsewhere. Domination by `a_n`
justifies taking this limit through the entire infinite sum, even when
frequencies accumulate at `xi`:

```text
H_c(xi) -> A(xi).
```

Consequently the finite-scale constraint gives

```text
A(xi)+A(-xi) <= 2*A(0).
```

The terminals are `tendsto_heatMass` and `opposite_frequencyMass_le`.
For nonzero `xi`, `opposite_frequencyMass_le_nonconstantMass` also proves
`A(xi)+A(-xi)<=M`. All repeated occurrences are included in each mass.
These are necessary conditions on an admissible family, not a claimed
complete characterization of all nonnegative kernels or a historical
novelty claim for Fourier coefficient bounds.

## A ceiling for the actual coarse Gaussian profile

Write

```text
G(x) = integral_(u>0) exp(-u^2-x*u) du,
a0=A(0), a1=A(1)+A(-1).
```

At a positive scale `ell`, the unit-multiplicity profile compares

```text
source = a1*G(ell*(nu-mu)),
cost   = a0*G(-ell*mu)+M/(4*ell).
```

Here `mu` is the normalized input margin and `nu>=mu` is the proposed
normalized output. The leading gamma cost is the particular coarse
`M/(4*ell)` term. It is not identified with the exact frequency-dependent
gamma average for every possible moving family.

[GaussianPhaseProfileCeiling](../RiemannGaussian/GaussianPhaseProfileCeiling.lean)
proves that, for every such family and every `ell>0`, strict surplus forces

```text
mu < pi/4,
nu < mu+4,
nu < pi/4+4.
```

`family_profile_ceiling` derives all coefficient constraints from the
actual full cosine kernel; it does not choose or optimize a phase count.
The bounds are deliberately coarse, not an exact optimum.

The proof uses two inequalities for the genuine integral. Its exponential
tangent gives `G(-ell*mu)>=sqrt(pi)/2+ell*mu/2`. The square
`(ell*sqrt(pi)/2-1)^2>=0`, together with `a1<=2*a0` and `a1<=M`, makes
the cost dominate the source whenever `mu>=pi/4`. Separately, positive
damping gives `G(x)<=1/x`, so an advance `nu-mu>=4` is already dominated
by the gamma cost alone.

`halfGaussian_unit_rescale` and `scaled_family_profile_ceiling` connect
the same ceiling to the unnormalized quantities used in the zero-free
chain. For arbitrary `L>0`, `ell>0`, `B=1/(ell^2*L^2)` and `d>=m`,

```text
a0*G_B(-m)+M*L/4 < a1*G_B(d-m)
  implies L*m<pi/4 and L*d<L*m+4<pi/4+4.
```

For `L=log(t)`, this particular sufficient comparison therefore cannot
produce a fixed positive edge distance as height grows, even by varying
the family and Gaussian scale. It is a method audit, not an achieved
zero-exclusion milestone.

## What needs stronger information

The existing
[signed selected-zero budget](../RiemannGaussian/GaussianFermiMarginBudget.lean)
retains the full prime combination alongside the selected zero source.
The exact Fermi target and pole reserves, additional zeros, their actual
multiplicities, and the frequency-dependent gamma average also remain
available upstream. The ceiling does not apply after those terms supply
a stronger source or a smaller cost than the profile above. It also does
not rule out families whose frequencies move with height and whose gamma
cost can be treated more accurately.

The next task is an estimate using that retained information. Merely
varying coefficients within the same coarse comparison cannot remove
the proved finite ceiling. A positive constant contribution to the prime
budget alone is smaller than the leading logarithmic profile cost at
large height; an improvement of that leading comparison needs an
appropriately scaled estimate.

The original normalized ordinary-prime tail in the squarefree reductio
is a different quantity from this Fermi prime combination. Its independent
fixed-gap lower bound and RH remain open.

## Local verification

Both modules pass direct elaboration with warnings treated as errors.
The root library imports both modules. The focused build passes with
4,616 jobs and the full warning-as-error build with 10,143 jobs. All 14
declaration linters pass in each new module. All 22 explicit terminal
axiom audits use only `propext`, `Classical.choice` and `Quot.sound`.
Whole-project declaration lint and the compiled-environment status
audit pass. The inventory contains 1,296 project modules and 25,002
theorems, with zero project axioms and zero placeholder-dependent
declarations. Source, local-link, README table and whitespace checks
pass; Current Direction is one paragraph of 394 characters. The theorem
inventory retains the actual zero-free milestone and labels the new
metadata as a method constraint. These are local validation results; remote CI is checked separately on the exact commit.
