# Exact coefficients on complete quotient cells

[SuzukiDivisorQuotientOptimizer.lean](../RiemannGaussian/SuzukiDivisorQuotientOptimizer.lean)
constructs an explicit family attaining the Suzuki divisor optimum for
every cutoff and center. There is no numerical coefficient search and no
approximation error in the Lean result. The certificate still needs an
independent uniform lower bound; this slice does not give a new zero bound.

## The explicit family

Write

\[
A_q=\sum_{k\le q}\frac{\mu(k)}{\sqrt k},\qquad
D_q=\sum_{k\le q}\frac{\mu(k)\log k}{\sqrt k}.
\]

Then use

\[
\boxed{w_{N,r}(m)=
 \frac{A_{\lfloor N/m\rfloor}(\log m-r)+D_{\lfloor N/m\rfloor}}{\sqrt m}.}
\]

Both coefficients are mathematically defined finite sums. They are
independent of `r`, and depend on `N,m` only through the exact quotient.
`suzukiQuotientWeight_eq_mobiusInverse` identifies this with

\[
w_{N,r}(m)=\sum_{k\le N/m}\mu(k)
 \frac{\log(mk)-r}{\sqrt{mk}}.
\]

This is classical finite Möbius inversion applied to the actual Suzuki
target, not a new inversion theorem or a conjectural cancellation estimate.
The proof reuses the repository's exact finite hyperbola regrouping from
`EtaMoebiusFinitePrefix.lean`.

`suzukiDivisorDualKernel_mobiusInverse` proves the inversion for an arbitrary
finite target, using the exact identity `sum_{k|n} mu(k) = 1_{n=1}`.
Its specialization `suzukiDivisorDualKernel_quotientWeight` proves

\[
\boxed{\sum_{k\le N/d}w_{N,r}(dk)
       =\frac{\log d-r}{\sqrt d}\quad(1\le d\le N).}
\]

Thus the family is feasible with zero slack, including on every prime
power. `suzukiQuotientWeight_log_sum` identifies its logarithmic sum with
the original linear form. At the exact mass center,
`suzukiMassLegendrePotential_eq_quotient_certificate` proves that its
certificate is exactly the original nonlinear potential.

## Why quotient boundaries matter

On a complete cell where `floor(N/m)=q`, the scaled weight `sqrt(m)*w(m)`
is affine in `log(m)`. This is `suzukiQuotientWeight_same_cell`.
The relevant boundaries include `N/3`, `N/5`, and the other reciprocal
integers; an ordinary dyadic subdivision need not preserve them.

The adjacent coefficients are linked:

\[
A_{q+1}-A_q=\frac{\mu(q+1)}{\sqrt{q+1}},\qquad
D_{q+1}-D_q=\log(q+1)(A_{q+1}-A_q).
\]

`suzukiQuotientCoefficient_step` proves their joint increment without
replacing either coefficient by an absolute bound. At the real boundary
`m=X/(q+1)`, `suzukiQuotientCoefficient_boundary` gives the exact difference
between the two scaled formulas:

\[
\frac{\mu(q+1)}{\sqrt{q+1}}(\log X-r).
\]

Consequently the endpoint-centered formulas (`r=log X`) join in value.
They can still have different slopes. At the actual mass center the
signed displacement remains; it must not be silently omitted. This is
a precise structural explanation of the quotient pattern, not a proof
that any particular coarse family fails asymptotically.

`suzukiQuotientCell_card_le` proves

\[
\#\{\lfloor N/m\rfloor:1\le m\le N\}
\le 2\lfloor\sqrt N\rfloor.
\]

The proof separates `m<=floor(sqrt N)` from the remaining positions,
whose quotients are at most `floor(sqrt N)`. This bounds the number of
coefficient pairs needed to represent the exact weights. It does not
bound their magnitudes, give a constant-size family, or assert that their
Möbius sums can be computed in sublinear time.

## Numerical checks and the remaining obligation

The exploratory script now supports the proved prime-power-only minorant
test and reports numerical comparison masses for entire tested spaces.
For the smooth dyadic family with 16 subdivisions per shell at `N=131072`,
removing the other constraints decreases the observed weighted slack
from about `0.134` to `0.111`. The lower certificate remains about
`-0.0554`, so this experiment does not establish a floor. Solver residuals
and floating-point repairs are reported; these are not exact LP certificates.

The explicit quotient diagnostic uses no LP. At the same endpoint, 723
complete quotient cells recover the original potential, approximately
`0.0553091`; its numerical kernel residual is below `2e-13` and its
certificate discrepancy below `2e-12`. Lean proves the corresponding
identities exactly for all endpoints, independently of those samples.

The source of the approximation loss can therefore be removed completely.
The next task is genuinely arithmetic: prove a common finite lower bound
for

\[
C+4e^{r_N/2}+c r_N+
\sum_{m\le N}\frac{\log m}{\sqrt m}
 \bigl(A_{\lfloor N/m\rfloor}(\log m-r_N)
       +D_{\lfloor N/m\rfloor}\bigr),
\]

where `r_N` is the actual mass center. This expression equals `B_N`;
its equality to the original potential does not prove its lower bound.
The same qualification applies to all-coefficient optimization. Further
coarse coefficient tuning is unnecessary for attaining the finite optimum,
and controlling the two signed coefficients separately is not justified
as a route to the needed joint bound.

No asymptotic class obstruction, uniform floor, RH proof, or improved
zero-proportion certificate is claimed. The nine public theorems have
direct warning-as-error validation, focused and full builds, whole-project
declaration lint, and a root-import explicit axiom audit. All use only
the permitted standard axioms; `rhImplied:false` remains unchanged.
