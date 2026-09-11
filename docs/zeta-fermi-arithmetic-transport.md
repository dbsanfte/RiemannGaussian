# The stronger Fermi region in the squarefree theorem chain

The stronger eventual zero-free region now reaches the actual squarefree
response. Two root-imported Lean modules prove the entire transport:

- [ZetaFermiGlobalMargin](../RiemannGaussian/ZetaFermiGlobalMargin.lean)
  combines the old explicit all-height region with the proved eventual
  Fermi region, retaining monotonicity in absolute height.
- [ZetaSquarefreeEulerFermiRadius](../RiemannGaussian/ZetaSquarefreeEulerFermiRadius.lean)
  proves a larger analytic disc for `zeta(s)/zeta(2*s)`, transfers it to
  every valid arithmetic mark and complex polynomial, and proves stronger
  geometric decay for each fixed marked response.

Every analytic and zero-free premise in the terminal theorems is
discharged. The finite height thresholds are proved to exist and are not
numerically evaluated. The external published `4.896` region and the
independent signed ordinary-prime-tail estimate have not been proved here.

## A global margin that works on whole height bands

Write `m_old(t)` for the preceding explicit
[reserve margin](zeta-pole-reserve-bootstrap.md). The
[eventual Fermi theorem](gaussian-fermi-zero-free-region.md) proves the
existence of a threshold above which every actual zero obeys both strict
edge margins `3/(20*log(abs(t)))`.

Choose a witness of that already proved theorem and enlarge it to
`T0>=exp(4000)`. Put

```text
c = m_old(T0),
m_F(t) = max(m_old(t), min(c, 3/(20*log(max(T0,abs(t)))))).
```

The choice uses only Lean's permitted `Classical.choice` applied to an
unconditional existence theorem. It is not a hypothesis about zeros or
a numerical certificate for `T0`.

The logarithm is positive at every ordinate. Lean proves

```text
0 < m_F(t) < 1/4,
m_old(t) <= m_F(t),
abs(a) <= abs(b)  implies  m_F(b) <= m_F(a).
```

Below `T0`, the old antitone margin dominates the cap, so
`m_F(t)=m_old(t)` exactly. Above `T0`, the capped new part is no larger
than the proved Fermi width. Both cases therefore give, for every actual
nontrivial zero `rho=beta+i*t`,

```text
m_F(t) < beta < 1-m_F(t).
```

`riemannZeta_ne_zero_of_fermi_margin` also proves literal nonvanishing
on `Re(s)>=1-m_F(Im(s))`, explicitly away from the pole `s=1`.

Finally, `exists_eventual_fermiZeroMargin_eq` proves that beyond another
finite threshold the cap is inactive:

```text
m_F(t) = 3/(20*log(abs(t))) > m_old(t).
```

The maximum with `T0` avoids an unnecessary shift inside the eventual
logarithm. The exact coefficient `3/20` is retained.

## The enlarged disc is proved safe for the literal quotient

For `abs(y)>1`, define

```text
r_F(y) = 1 + min((abs(y)-1)/2, m_F(2*abs(y)+3)/2).
```

Lean proves `1<r_F(y)<min(abs(y),9/8)`. The closed disc centered at
`3/2+i*y` with this radius avoids the numerator pole, the doubled
denominator pole and every zero of `zeta(2*s)`. The antitone margin is
what lets the pointwise zero theorem cover every ordinate in the disc.

`analyticOnNhd_squarefreeEulerResponse_fermi` proves analyticity of the
genuine quotient on a neighbourhood of that entire closed disc. The
new radius never decreases the preceding reserve radius `r_old(y)`.
The unconditional theorem
`exists_eventual_squarefreeEulerFermiRadius_gain` gives, at sufficiently
large absolute ordinates,

```text
r_old(y) < r_F(y) = 1+3/(40*log(2*abs(y)+3)).
```

## The actual arithmetic estimate and its precise gain

`exists_squarefreeEuler_fermi_radius_bound` supplies one `C_y>0` such
that for every `0<r<=r_F(y)`, every finite prime set `S`, every squarefree
mark `P` having no prime factor in `S`, every complex polynomial `p` and
every moment order `N`,

```text
norm(RoughSquarefreeBare.response(p,S,P,N,3/2+i*y))
 <= C_y * squarefreeEulerBudget(3/2-r,S,P) * r^(-N)
      * sum_(k in support(p)) norm(p_k)*r^(-k).
```

This is the original complete arithmetic series, including ordinary
primes. The radius, polynomial phases and finite Euler allowance remain
explicit. The constant `C_y` is common to all marks and polynomials;
their dependence is in the displayed factors.

For each fixed `S`, `P` and `p`, the Euler and polynomial factors at
`r=r_F(y)` are independent of `N`. Thus
`tendsto_squarefreeEuler_scaled_response_fermi` proves convergence of
the full complex response to zero after multiplication by `a^N` for
every `0<=a<r_F(y)`. In particular,
`exists_eventual_squarefreeEuler_reserve_scaled_decay` proves

```text
r_old(y)^N * RoughSquarefreeBare.response(p,S,P,N,3/2+i*y) --> 0
```

for all sufficiently large `abs(y)` and every fixed valid mark and
polynomial. The decay follows from the strict ratio
`(r_old(y)/r_F(y))^N`, with all other factors finite and fixed. This
turns the geometric radius gain into an actual arithmetic limit.

## Remaining obstruction

For growing sieves or moving marks, the radius-dependent Euler budget
must still be paid. A larger radius alone does not prove that their
entire bound improves. The complete squarefree series also still
includes the ordinary-prime contribution whose independent signed
lower bound would close the existing reductio.

The [subsequent feedback theorem](gaussian-fermi-bootstrap-zero-free.md)
now uses this margin inside the Fermi reflection budget and proves the
stronger eventual coefficient `4/25` without a larger outside allowance.
The radius and arithmetic theorems in this document still use the first
Fermi width `3/20`. The reciprocal-logarithmic widths shrink with height;
no limiting approach to the critical line or proof of RH is asserted.

## Local verification

Both modules pass strict direct elaboration. The focused build passes
with 4,817 jobs and the full warning-as-error build with 10,138 jobs.
All 14 declaration linters pass for both modules. The 19 explicit theorem
axiom audits use only `propext`, `Classical.choice` and `Quot.sound`.
The whole-project declaration lint and compiled-environment status audit
also pass: 1,291 project modules, 24,920 theorems, zero project axioms and
zero placeholder-dependent declarations. Source, local Markdown links,
README table formatting and whitespace checks pass; Current Direction
is one paragraph of 440 characters. These are local validation results; remote CI is checked separately on the exact commit.
