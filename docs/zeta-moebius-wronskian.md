# Differential separation of the Möbius contributions

A new checked differential identity separates the leading zeta-zero
source from its prime-divisor contribution. It applies to every
hypothetical zero strictly right of one half, with its actual analytic
multiplicity. The surviving arithmetic series is supported on squarefree
composite Möbius indices and retains the exact leading complex coefficient.

This is a structural result about actual zeta and its convergent arithmetic
series. It does not yet give a new zero exclusion or the independent signed
bound required by the active RH goal. Literature priority has not been
established.

## The differential cancellation

Put `h = zeta'` and `F = -zeta'/zeta`. Wherever zeta is analytic and nonzero,

\[
\boxed{hF'-h'F=\frac{h^3}{\zeta^2}.}
\]

`deriv_coupled_neg_logDeriv` proves the underlying analytic identity;
`zetaMoebiusWronskian_eq_coupled` instantiates it on actual zeta. The
second-derivative terms cancel before taking any norm.

For a selected nontrivial zero `rho` of genuine multiplicity `m >= 1`, let

\[
C_\rho(s)=\frac{\zeta'(s)^2}{(s-\rho)^{m-1}},\qquad
J_\rho(s)=C_\rho(s)\frac{\zeta'(s)}{\zeta(s)^2}.
\]

The cofactor has order `m-1` at `rho`. Lean constructs its actual removable
extension and proves that extension analytic everywhere except `s=1`:
`analyticAt_zetaMoebiusWronskianCofactorRegular_of_ne_one`. Totalized
division at the selected point is not used as an analyticity argument.

Write locally `zeta(s)=(s-rho)^m g(s)`, with `g(rho) != 0`. The checked
order and trailing-coefficient theorems give

\[
\boxed{\operatorname{ord}_\rho J_\rho=-2,\qquad
\lim_{s\to\rho}(s-\rho)^2J_\rho(s)=m^3g(\rho)\ne0.}
\]

The limit is punctured. Its formal statements are
`meromorphicOrderAt_zetaMoebiusWronskian`,
`tendsto_zetaMoebiusWronskian_mul_sq`, and
`meromorphicTrailingCoeffAt_zetaMoebiusWronskian_ne_zero`.
The coefficient keeps the full leading zeta phase and multiplicity.

## Literal prime and composite series

In the Euler half-plane `Re s>1`, absolute convergence and differentiation
of the actual reciprocal Möbius series give

\[
L_\mu(s)=\sum_{n\ge1}\mu(n)\log n\,n^{-s}
       =\frac{\zeta'(s)}{\zeta(s)^2}.
\]

Let

\[
E(s)=\sum_{n\text{ a proper prime power}}\Lambda(n)n^{-s}.
\]

The existing independent proper-prime-power estimate proves this series
analytic on `Re s>1/2`. Restricting `L_mu` to primes gives the exact identity

\[
L_{\mu,\mathrm{prime}}(s)
=-\sum_p\log p\,p^{-s}
=\frac{\zeta'(s)}{\zeta(s)}+E(s).
\]

Theorems `LSeriesHasSum_zetaMoebiusDerivative` and
`LSeriesHasSum_zetaMoebiusPrimeDerivative` prove these as genuine convergent
series. The continuation beyond `Re s>1` is meromorphic; the prime series
itself is not asserted to converge there.

Define the prime and composite responses using the identical cofactor:

\[
P_\rho=C_\rho L_{\mu,\mathrm{prime}},\qquad
Q_\rho=J_\rho-P_\rho
      =C_\rho\sum_{n\text{ composite}}\mu(n)\log n\,n^{-s}
      \quad(\Re s>1).
\]

`hasSum_zetaMoebiusCompositeWronskian` supplies this literal series.
`zetaMoebiusCompositeDerivativeCoefficient_support` proves every nonzero
coefficient requires a squarefree composite integer. These are the Möbius
indices inside the cofactor-weighted sum; expanding the cofactor's zeta
derivatives into further Dirichlet factors is a separate convolution.

## The exact order separation

Lean proves the identity

\[
\boxed{P_\rho=\zeta J_\rho+C_\rho E.}
\]

At the selected zero, `C_rho E` has an explicitly constructed analytic
extension. The theorems `zetaMoebiusPrimeWronskian_eq` and
`zetaMoebiusPrimeWronskian_analytic_remainder` keep this full identity.
Consequently,

\[
\operatorname{ord}_\rho P_\rho=m-2,\qquad
(s-\rho)^2P_\rho(s)\longrightarrow0,\qquad
(s-\rho)^2Q_\rho(s)\longrightarrow m^3g(\rho).
\]

These are `meromorphicOrderAt_zetaMoebiusPrimeWronskian`,
`tendsto_zetaMoebiusPrimeWronskian_mul_sq`, and
`tendsto_zetaMoebiusCompositeWronskian_mul_sq`. The composite response has
exact order `-2` and the same leading coefficient as the complete response.

Other singularities are also checked, without assuming the selected zero
is nearest to the evaluation point:

| Point | Full response `J_rho` | Prime response `P_rho` |
| --- | --- | --- |
| Selected zero, multiplicity `m` | order `-2` | order `m-2` |
| Other zero in `Re s>1/2`, multiplicity `k` | order `k-3` | order `2k-3` |
| Zeta's pole at `1` | order `-4` | order `-5` |

Thus every zero pole of the full response is at most double, and every zero
pole of the prime response is at most simple. The prime response needs
five orders of cancellation at `s=1`. The `_other_zero` and `_one` terminal
theorems in both modules establish this complete order accounting.

## Relevance to the open bound

The subsequent [global moment estimate](zeta-wronskian-global-moments.md)
now cancels every other pole in the explicit evaluation disc, controls the
analytic remainder, and retains the selected double-pole coefficient.
The normalized prime contribution is bounded by `C/(N+1)` and tends to
zero. The normalized composite response converges to its full nonzero
complex source with an error of that same order.

The newer [positive convolution identity](zeta-positive-composite-response.md)
then keeps one logarithmic derivative factor inside the signed Möbius
sum, proving that the resulting arithmetic coefficients are nonnegative.
The corresponding fixed zeta response has leading coefficient `-m^2` at
every right-half zero. Its exact bridge back to these moments keeps all
cofactor phases. The whole filtered composite response still needs an
independent signed inequality; coefficient positivity does not by itself
control a complex filter. The earlier
[distinct-prime tail bound](zeta-moebius-distinct-prime-tail.md) remains
valid for its original carrier.

## Local verification

Both modules are imported by the root library. Validation comprises direct
warnings-as-errors elaboration, focused and full builds, whole-project
declaration lint, root-imported module lint and public-theorem axiom
audits, and source/whitespace checks. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Work remains local under the user's commit hold.
