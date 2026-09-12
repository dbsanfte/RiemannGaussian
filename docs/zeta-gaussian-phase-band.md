# A full phase-family Gaussian bound and explicit zero-free band

[exact_strip](../RiemannGaussian/ZetaGaussianBandExclusion.lean) proves that
every actual nontrivial zeta zero `rho=beta+i*t` satisfies

```text
1/450000 < beta < 1-1/450000
```

whenever `1000000 <= abs(t)` and `log(abs(t)+2) <= 320000`.
The endpoints and both height inequalities are literal. The same module's
`nonvanishing` proves zeta nonvanishing on the closed right edge. There is
no unevaluated starting height for this component, unproved prime-sum
premise, numerical oracle or Euler boundary-limit assumption.

## The full countable family

Take `a_n>=0`, `sum a_n<infinity`, `omega_0=0`, `omega_1=1`,
`omega_n>=1` for `n!=0`, and finite logarithmic frequency cost. Write

```text
K(u) = sum_n a_n*cos(omega_n*u),
W = sum_(n!=0) a_n,
J = sum_(n!=0) a_n*log(omega_n).
```

[ZetaGaussianPhaseArithmetic](../RiemannGaussian/ZetaGaussianPhaseArithmetic.lean)
first retains the complex kernel and proves the full absolutely convergent
double-series identity. Its real projection is the actual Gaussian prime
sum against `K(t*log m)`. No frequency moment is required for this prime
identity; its Gaussian series converges for `sigma>2/3`.

For the strip argument let

```text
delta_k=(k+2)/(2^(k+2)-2), sigma=1+x, eta=delta_k+x,
tau=1+delta_k+2x, b=2eta/pi, A=24B/eta^2.
```

The shifted xi response and the right strip boundary lie on the **same
line `tau`**. [ZetaGaussianPhaseAllowance](../RiemannGaussian/ZetaGaussianPhaseAllowance.lean)
therefore keeps the right Euler prime work with the xi mass:

```text
sum_(n!=0) a_n*Re(xi'/xi(tau+i*omega_n*t))
  + sum_m Lambda(m)*m^(-tau)*K(t*log m)
  = a_0*(-zeta'/zeta(tau))
      + sum_(n!=0) a_n*Re(1/(tau+i*omega_n*t-1)+C(tau+i*omega_n*t)).
```

The Euler real-axis cost is charged only to `a_0`. The full identity is
retained independently of the positivity argument.

[ZetaGaussianStripPhaseFamily](../RiemannGaussian/ZetaGaussianStripPhaseFamily.lean)
couples three original arithmetic responses: the Gaussian prime sum, the
right Euler prime sum weighted by `A`, and the right averaged logarithmic
Euler series divided by `2eta`. Its terminal signed inequality retains all
three plus the selected Gaussian source. If `K>=0`, each full arithmetic
response is nonnegative. This discharges the entire prime series without
discarding its phases before they are used.

The exact budget also retains the signed left mean, rational vertical
correction, smoothed pole and complete Archimedean difference. In
[ZetaGaussianStripExplicit](../RiemannGaussian/ZetaGaussianStripExplicit.lean),
the original rational pole cancellation is used before estimating the
Gaussian error, giving `12B/abs(t)^3 + 4B/mass(B)` for each nonconstant
channel. The actual half-Gaussian remains on the constant channel.

## An unconditional rational surplus

The quantitative theorem is uniform over **all** eligible families with

```text
a_0 <= 37/200, a_1 >= 79/250, W <= 61/100, J <= 1/4.
```

No coefficients were selected or optimized for this theorem. The existing
mathematically defined contact family satisfies these bounds.

Choose the analytic parameters

```text
u=1/450000, x=u/1000, B=4u^2, k=9.
```

[GaussianStripProfile](../RiemannGaussian/GaussianStripProfile.lean)
uses the exact displaced Gaussian interval and reflection to prove
`F_B(x+u)>=152000` and `F_B(x)<=199575`. These are rational enclosures of
genuine integrals, proved without trusting a floating-point evaluation.

[ZetaGaussianBandBudget](../RiemannGaussian/ZetaGaussianBandBudget.lean)
pays for every term of the full cost on the stated band and proves
`budget<=47500`. If an actual zero had `1-beta<=u`, monotonicity, the
cotangent loss bound, its positive multiplicity and its retained Poisson
reserve would give `selected_source>=48000`. The literal theorem chain
also gives `selected_source<=budget`, a contradiction. Reflection supplies
the left edge with the same height conditions.

## Matching heights and the union of regions

[ZetaGaussianBandFrontier](../RiemannGaussian/ZetaGaussianBandFrontier.lean)
proves the full comparison interval in ordinary logarithmic height:

```math
L_*<L\le\log(e^{320000}-2),\qquad
\frac{981}{50}L_*=450000\log L_*,\qquad 288000<L_*<289000.
```

The root is unique on the large branch. At it, the Littlewood benchmark
width equals `1/450000`; above it all three headline widths are strictly
smaller. The ceiling includes the actual enlarged height's plus two.
Literal zeta nonvanishing holds on the entire closed crossover-to-ceiling
interval and includes the closed right edge.

The [literature-frontier table](zero-free-literature-frontier.md) records
primary source versions, applicable heights, boundary conventions and
unresolved retrieval or proof-status checks. It also includes the
[Lean comparisons of intermediate published expressions](../RiemannGaussian/ZetaGaussianLiteratureComparison.lean).
These are comparisons of explicit functions, not imported external proofs
or an exhaustive world-record determination.

`union_with_eventual` combines this band with the repository's proved
eventual Littlewood component using their maximum wherever both height
conditions hold. The eventual component retains its coefficient-dependent,
unevaluated threshold. The finite band has its own explicit domain and
remains usable independently of that threshold. Underlying identities and
arithmetic estimates are retained alongside the width envelope.

## Remaining work

Resolve the remaining literature-source coverage, improve or widen the explicit
height band using the general cost theorem, and transport the resulting
region into the remaining prime-tail argument with the relevant height windows intact.
The [uniform squarefree transport](zeta-squarefree-gaussian-band.md) now
discharges the local window and bounds the complete logarithmic matrix
throughout the explicit center domain, including moving selected zeros.
The independent fixed-ordinate ordinary-prime floor and RH remain open.

## Validation

The Gaussian band and exact comparison modules are imported by the root
library. The extended comparison passes its focused warning-as-error build,
and the complete slice passes the full package build. Public theorem audits
and whole-project lint enforce the standard-only axiom invariant; generated
status and explorer artifacts record the current compiled inventory.

The [uniform arithmetic transport](zeta-squarefree-gaussian-band.md) shares
this verification slice. See the [proof status](proof-status.json) and
[exported chain audit](theorem-explorer/audit.json) for the generated counts
and source coverage. `rhImplied` remains false. CI repeats the strict build,
whole-project audit and artifact checks before publishing the explorer.
