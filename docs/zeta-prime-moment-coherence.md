# Converse prime-moment coherence

The actual complete ordinary-prime moment sequence identifies a zeta zero
and its exact analytic multiplicity. Put

\[
a_k=u^{k+1}\sum_p\frac{(\log p)^{k+1}}{k!}\,p^{-3/2-iy},
\qquad \rho=\frac32-u+iy.
\]

For **`0<u<1`**, if `a_k` tends to `-m` for a positive integer `m`, then
`rho` is a genuine nontrivial zeta zero with analytic multiplicity exactly
`m`. The converse requires neither exposure nor a Riesz floor hypothesis.

The terminal theorem is
[`exists_zero_multiplicity_of_tendsto`](../RiemannGaussian/ZetaPrimeMomentCoherence.lean).
Under an exposure hypothesis held fixed, the existing forward theorem and
the converse give
[`multiplicity_iff_source`](../RiemannGaussian/ZetaPrimeMomentCoherenceExposed.lean):
the specified multiplicity is equivalent to the coherent prime source.
Convergence is **not** asserted to imply exposure.

## Generating series and the Euler boundary

Convergent coefficients give an analytic generating series on `|z|<1`.
On the real Euler segment `r>=0`, `u*r<1/2`, its exact value is

\[
A(r)=\sum_{k\ge0}a_k r^k
 =u\sum_p\frac{\log p}{p^{3/2+iy-ur}}.
\]

The double series is absolutely convergent before summation is exchanged.
Abel convergence then gives `(1-r)*A(r) -> -m` as `r` tends to one from below.
For the campaign's `u>1/2`, the literal prime Dirichlet series does not
converge all the way to that endpoint. The proof continues a **pole-cleared
analytic identity**, rather than substituting into that series outside its
Euler half-plane.

Let `g(s)=(s-1)*zeta(s)` with its filled value `g(1)=1`, and let `Q` be the
proper-prime-power series, analytic for `Re(s)>1/2`. The continued identity is

\[
(s-1)g(s)[A(z)+uQ(s)]
 +u(s-1)g'(s)-ug(s)=0,
\qquad s=\frac32+iy-uz.
\]

The restriction `u<1` makes the entire unit-disk path lie in that
proper-power half-plane. Abel convergence forces a zero of `(rho-1)*g(rho)`.
The candidate `rho=1` would have source `+1`, contradicting the assumed
negative source. Therefore `g(rho)=0`, giving an actual nontrivial zero.
Along the punctured approach the identity also gives

\[
(s_r-\rho)\left(-\frac{\zeta'}{\zeta}(s_r)\right)
 =(1-r)A(r)+u(1-r)Q(s_r)\longrightarrow-m.
\]

The general local logarithmic-residue theorem identifies the same limit
as minus the analytic order. Uniqueness of limits gives multiplicity `m`.
Every factorial order is retained.

## Scope and validation

This is a structural characterization of the coherent obstruction. It
does not bound the joined energy minus correlation credit, prove a floor
or ceiling, or exclude an additional zero. The independent cofinal
`399/5000` arithmetic estimate remains open. It precisely explains why
an estimate preventing this kind of coherence would require additional
information about genuine primes.

[`CheckPrimeMomentCoherence.lean`](../scripts/CheckPrimeMomentCoherence.lean)
runs both namespace linters and checks the transitive axioms of every
declaration, including private helpers. The
[publication audit](prime-moment-coherence-audit.json) records the wider
gates. All earlier multi-height no-gos and semiprime results are preserved.
