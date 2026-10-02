# Aligned phases with negative joined divisor correlations

The `-79/1000` floor remains **open**. This slice proves an independent
one-sided geometric estimate for one branch of the actual signed energy.
It does not supply the numerical bound for the energy of the remaining
whole population.

Proof: [ZetaRieszAlignedNegativeCredit.lean](../RiemannGaussian/ZetaRieszAlignedNegativeCredit.lean).
Local validation: [proof audit](riesz-aligned-negative-credit-audit.json).

## The branch is selected after the entire cutoff Gram is joined

Let `S` be the entire remaining squarefree core, `w` its original
source-normalized real weight, and `K^-` the original adverse cutoff set
selected once from that entire signed sum. Retain

\[
G(n,m)=\sum_{k\in K^-}\frac{\operatorname{sharp}(k,n)
  \operatorname{sharp}(k,m)}{k}.
\]

No individual cutoff or prime count is clipped before selecting `G`.
The earlier antiphase theorem retains a negative credit on positive `G`
at opposite phases. The new branch instead has **negative** `G` and
aligned total-label phases, over every even phase period, with log-width

\[
\varepsilon_N=\frac{e^{-N/10000}}{1+|y|}.
\]

All earlier paid diagonal, large-gcd, nearby-label and thinner aligned
edges stay excluded. The new and old credits are disjoint by the sign of
the same `G`. Every physical, radial, count and allocation condition remains
inside the literal weights.

Write `w(n)=-a(n)cos(y log n)` with the exact nonnegative amplitude `a`.
On the new branch the actual interaction is exactly

\[
w(n)w(m)G(n,m)
=-a(n)a(m)(-G(n,m))\frac{c_n^2+c_m^2}{2}
 +a(n)a(m)(-G(n,m))\frac{(c_n-c_m)^2}{2},
\qquad c_n=\cos(y\log n).
\]

`alignedReserve` is the first nonnegative magnitude and `alignedLeakage`
is the second. The first stays as a negative credit. Only the second is
estimated by a norm. Alignment gives `|c_n-c_m|<=e^(-N/10000)`.

## An actual one-sided estimate, with explicit scope

The reciprocal capacity of the entire even-period union contributes one
width and the squared phase difference contributes two more. After
retaining the true squared source growth, Lean proves

\[
0\le\operatorname{alignedLeakage}_N
\le C_y(N+1)^4e^{-N/20000}.
\]

`C_y` is the same finite, unevaluated constant used for the old antiphase
leakage. No effective starting order or numerical constant is claimed.
The bound is independent of any zero hypothesis and applies to every
literal-window subset; it does not assume density or cancellation.

In particular, `aligned_contribution_upper_bound` proves that the entire
newly selected signed branch is at most that geometric allowance. This is
an **upper** estimate on a signed contribution. It is not a norm estimate
for that branch and not a lower bound on the reserve's native mass.

With both branches joined, the exact ledger is

\[
E=\operatorname{signedRemainder}
  -\operatorname{antiphaseReserve}-\operatorname{alignedReserve}
  +\operatorname{antiphaseLeakage}+\operatorname{alignedLeakage}.
\]

`energy_le_remainder_sub_reserves` adds only
`2*C_y*(N+1)^4*exp(-N/20000)` to the signed main on the right.

## What this does not save automatically

The checked comparison
`combinedMain_eq_previous_sub_leakage` is important:

\[
\underbrace{\operatorname{signedRemainder}
 -\operatorname{antiphaseReserve}-\operatorname{alignedReserve}}
 _{\text{new combined main}}
=\underbrace{\operatorname{signedRest}
 -\operatorname{antiphaseReserve}}_{\text{previous signed main}}
 -\operatorname{alignedLeakage}.
\]

The previous main already retained the actual negative interactions.
Thus exposing a second reserve does **not** produce its magnitude as a
free new energy saving. The old and new budget problems differ only by
the geometrically small mismatch. `previousMain_le_combinedMain_add_error`
proves the reverse quantitative comparison. This prevents double counting
or presenting a second band credit as a global budget estimate.

The existing native-mask numerical probe motivated this branch: it exhibits
both signs of the joined Gram, with highly variable credit coverage. Its
constructed subsets select their own adverse cutoff sets, have rescaled
amplitudes and are not full native populations. No new cofinal numerical
estimate is inferred from those observations.

## Connection to the current original carrier

`eventually_joined_floor` applies both credits to the entire actual core
below the recently proved `K/768+1` count ceiling, with integer division.
Its left-hand carrier is still the **original** `joinedPhysical` at original
`K`. The four earlier pair prices, original core/joined bridge and new
count-tail allowance occur once; the two mismatch prices are each
`leakagePrice y N`, tending to zero for fixed height.

The remaining independent sufficient estimate is still

\[
\operatorname{signedRemainder}
 -\operatorname{antiphaseReserve}-\operatorname{alignedReserve}
\le\frac{3}{320(N+1)}
\]

cofinally on the entire remaining native support. It is **unproved**.
The floor, ceiling, contradiction and new zero exclusion remain unproved.
The next meaningful arithmetic work must bound this whole joined quantity,
or the original carrier directly; another credit identity alone cannot
close the gap.

Seventeen public theorems receive focused direct/targeted Lean,
ordinary-root, namespace-linter and transitive standard-axiom checks.
Earlier mathematical sources, staged semiprime files and published
README/explorer endpoints remain unchanged. Work remains local, without
commits, pushes, subagents or broader publication gates.
