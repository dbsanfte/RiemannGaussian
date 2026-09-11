# Sharper zero exclusion from the retained Gaussian endpoint

Lean proves an unconditional eventual zero-free width with exact coefficient
`9/50`. There is a finite `T>=1` such that every nontrivial zeta zero
`rho=beta+i*t` with `abs(t)>=T` satisfies

```text
9/(50*log(abs(t))) < beta < 1-9/(50*log(abs(t))).
```

The new edge width is `9/8` times the preceding `4/25` width. The threshold
is existential and has not been numerically evaluated. The terminal
theorems `exists_eventual_strip`, `exists_eventual_nonvanishing` and
`exists_eventual_improved_region` in
[GaussianFermiSharpZeroFree](../RiemannGaussian/GaussianFermiSharpZeroFree.lean)
state actual zero exclusion and literal zeta nonvanishing with all analytic
and arithmetic premises discharged. This improves the repository's region;
it is not a historical novelty or best-published-region claim.

## The information retained

For the original half-Gaussian Laplace transform

```text
G_b(x) = integral_(u>0) exp(-b*u^2-x*u) du,
```

completing the square gives, for every `b>0` and real `x`,

```text
G_b(-x) = exp(x^2/(4*b)) *
  (sqrt(pi/b)/2 + integral_(-x/(2*b))^0 exp(-b*u^2) du).
```

`halfGaussian_neg_shift` in
[GaussianHalfLaplaceShift](../RiemannGaussian/GaussianHalfLaplaceShift.lean)
preserves this finite interval exactly, including its orientation for
negative `x`. Translation of the integral and integrability are proved.
For `x>=0`, bounding only this interval by its length gives

```text
G_b(-x) <= exp(x^2/(4*b))*(sqrt(pi/b)/2+x/(2*b)).
```

The earlier reflection estimate used a tangent bound for the opposite
half-line. The shifted identity gives a tighter pole estimate in the
parameter range used here. It remains available upstream of its upper
bound for further curvature estimates.

## A uniform surplus without changing phase coefficients

[GaussianFermiSharpProfile](../RiemannGaussian/GaussianFermiSharpProfile.lean)
proves the exact rational enclosures

```text
G_1(31/400) >= 3389/4000,
G_1(-3/8) <= 557/500.
```

The first follows from the integrated exponential tangent. The second uses
the shifted identity, checked bounds on pi, and
`exp(9/256)<=256/247`. No floating-point computation is trusted.

For every coefficient triple and normalized margin satisfying

```text
0<=a0<=37/200, a1>=79/250, M<=61/100,
149/1000<=mu<=3/20,
```

the resulting general scalar theorem is

```text
a0*G_1(-(5/2)*mu)+M/10+1/2000
  <= a1*G_1((5/2)*(9/50-mu)).
```

The previously defined exact phase row satisfies these same coefficient
bounds. Its frequencies and coefficients are unchanged; every nonconstant
coefficient contributes to `M`.

## The actual zero budget closes at the larger edge

For a proposed zero, choose

```text
L=log(abs(t)), H=48*abs(t), m=m_F(H),
B=4/(25*L^2), b=c=B/2.
```

The **first proved global Fermi margin** is eventually
`m_F(H)=3/(20*log(H))`. Its existing normalized-margin theorem gives
`149/1000<=L*m<=3/20` at sufficiently large height. This uses a previously
proved region, not the region being established. The general scale lemma
`L*m<=2/5` gives `m^2<=B<=1`, hence the old margin's scale condition too.

Exact Gaussian dilation now proves, for every candidate edge distance
`d<=9/(50*L)`,

```text
a0*G_B(-m)+M*L/4+L/800 <= a1*G_B(d-m).
```

The original full pole and gamma cost is at most
`a0*G_B(-m)+M*L/4+8`. The uniform whole-divisor allowance is eventually
below one, so its weighted cost is at most one. Both horizontal partners
are retained in the resonant source, with their actual analytic
multiplicity at least one. The genuine zero budget would therefore force

```text
L/800 <= 9,
```

contradicting `L>=100000`. Horizontal reflection supplies the other edge;
the pole-removed zeta bridge supplies literal nonvanishing on the closed
right edge. No assumption about simple zeros is made.

## Scope and the remaining arithmetic gap

The threshold must exceed the existing margin transition and the uniform
whole-divisor allowance threshold as well as `exp(100000)`. That exponential
alone is not a proved sufficient numerical threshold.

Both the old and new widths tend to zero as height grows. The larger
coefficient narrows the possible zero strip but does not establish
convergence to the critical line. The existing all-height margin and
squarefree-radius transport still use their proved `3/20` eventual formula;
they are not silently replaced by `9/50`.

The original signed prime moment and its admissible Gaussian form remain
connected by the [proved vanishing comparison](prime-admissible-heat-source.md).
An independent cofinal lower bound with a fixed positive gap above `-1`
for their real part is still missing. The larger edge exclusion does not
pay that remaining bound or control the complex moment-filtered pole and
gamma costs. The published `4.896` region is not formalized here, and RH
remains open.

## Local verification

All three new modules pass strict direct elaboration and the focused
warning-as-error build (4,629 jobs). The full build passes with 10,150 jobs.
Whole-project declaration lint and verbose audits of all seven uncommitted
modules pass. All 68 explicit terminal axiom checks across this checkpoint
use only `propext`, `Classical.choice` and `Quot.sound`.

The compiled inventory contains 1,303 project modules, 28,678 declarations
and 25,093 theorems, with zero project axioms and zero placeholder-dependent
declarations. Generated-status freshness, source scans, root imports,
Markdown links and README formatting are checked before committing. Remote
CI is verified separately for the exact pushed commit.
