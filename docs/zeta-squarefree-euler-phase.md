# Retained prime harmonics in the actual squarefree Euler multiplier

The verified result bounds the complete higher-order Euler remainder
uniformly over all finite prime sets. It retains the lower prime harmonics
as an exact complex sum and transports that information to the actual
marked arithmetic response. It does not bound the surviving signed prime
source or prove a larger zero-free region.

## Exact decomposition before taking norms

For a finite set of primes `S`, write

\[
z_p(s)=p^{-s},\qquad
\Phi_{J,S}(s)=\sum_{p\in S}\sum_{k=1}^{J}
  \frac{(-1)^{k+1}}{k}z_p(s)^k,
\]

\[
E_{J,S}(s)=\Phi_{J,S}(s)-\sum_{p\in S}\log(1+z_p(s)).
\]

For `Re(s)>0`, each `abs(z_p(s))<1`, so every local factor is nonzero.
The finite product satisfies the exact complex identity

\[
\prod_{p\in S}(1+z_p(s))^{-1}
 =\exp\bigl(-\Phi_{J,S}(s)+E_{J,S}(s)\bigr).
\]

This does not take a logarithm of the whole product or equate principal
logarithms across a branch cut. Each local logarithm is exponentiated
before the factors are combined.

For a valid squarefree divisibility mark `P` disjoint from `S`, the
repository's actual multiplier satisfies

\[
M_{S,P}(s)=M_{\varnothing,P}(s)
 \exp\bigl(-\Phi_{J,S}(s)+E_{J,S}(s)\bigr).
\]

The declarations are `inverse_product_eq_exp` and `multiplier_eq` in
[ZetaSquarefreeEulerPhase.lean](../RiemannGaussian/ZetaSquarefreeEulerPhase.lean).
The source retains the actual mark factor and every excluded prime.

## The independently bounded part

The exact finite remainder allowance is

\[
|E_{J,S}(s)|\le
 \sum_{p\in S}
 \frac{|z_p(s)|^{J+1}}{(J+1)(1-|z_p(s)|)}.
\]

Fix `sigma>0` and an integer `J>=0` with `(J+1)*sigma>1`.
Then there is a constant `C>0`, independent of `S` and `s`, such that

\[
\Re s\ge\sigma\quad\Longrightarrow\quad |E_{J,S}(s)|\le C.
\]

The proof bounds every local denominator using the prime `2` and sums
the remaining `p^(-(J+1)*sigma)` majorant over all positive integers.
It uses a genuinely convergent series. Neither the size of `S`, its
largest prime, its spacing, nor the ordinate needs a bound.

In particular the compensated reciprocal product is bounded both above
and away from zero:

\[
e^{-C}\le
 \left|e^{\Phi_{J,S}(s)}\prod_{p\in S}(1+p^{-s})^{-1}\right|
 \le e^C.
\]

The original uniform squarefree-mark theorem separately gives one
constant `A>0` for all valid `P`, so

\[
|M_{S,P}(s)|\le A\exp\bigl(-\Re\Phi_{J,S}(s)\bigr).
\]

See `norm_remainder_le`, `exists_uniform_remainder_bound`,
`exists_compensated_product_bounds`, and `exists_uniform_mark_bound` in
[the phase module](../RiemannGaussian/ZetaSquarefreeEulerPhase.lean).
The criterion on the first omitted harmonic is sufficient; no optimality
or historical novelty is claimed.

## Two harmonics cover the actual Cauchy discs

At `sigma=3/8`, two harmonics suffice because `3*sigma=9/8>1`.
Their exact sum is

\[
\Phi_{2,S}(s)=\sum_{p\in S}p^{-s}
                 -\frac12\sum_{p\in S}p^{-2s}.
\]

For `s=sigma+i*t`, its real part is

\[
\sum_{p\in S}p^{-\sigma}\cos(t\log p)
 -\frac12\sum_{p\in S}p^{-2\sigma}\cos(2t\log p).
\]

The doubled frequency therefore comes with a specific negative
coefficient and its own stronger damping. It is not an independently
chosen weight or frequency. `phase_two` and `phase_two_re` prove these
identities.

Let `c=3/2+i*y`, and define the finite compact maximum

\[
\mathcal A_{S}(c,r)=
 \max_{|s-c|\le r}\exp\bigl(-\Re\Phi_{2,S}(s)\bigr).
\]

Any proved analytic disc for the genuine quotient
`Q(s)=zeta(s)/zeta(2*s)` of radius at most `9/8` lies in the required
half-plane. A single constant then gives the original marked response
the bound

\[
|\operatorname{response}_{S,P,p,N}(c)|\le
 C\mathcal A_S(c,r)r^{-N}
   \sum_{k\in\operatorname{support}(p)}|p_k|r^{-k}.
\]

The constant is independent of `r`, `S`, the valid squarefree mark `P`,
the polynomial `p`, and the order `N`. Its dependence on the fixed
outer disc remains. The unconditional Fermi disc discharges the analytic
premise for every `abs(y)>1` and every smaller positive radius.

The declarations are `hasSum_marked`, `exists_response_bound_of_analytic`,
and `exists_response_bound` in
[ZetaSquarefreeEulerPhaseBound.lean](../RiemannGaussian/ZetaSquarefreeEulerPhaseBound.lean).
The original arithmetic series is identified where it genuinely
converges, `Re(s)>1`. The subsequent Cauchy argument uses the proved
analytic continuation; it does not assert series convergence throughout
`Re(s)>=3/8`.

## What remains open

The new estimate replaces the absolute local Euler cost by an explicit
signed two-harmonic maximum plus a uniform constant. It controls the
higher-harmonic part independently, but supplies no uniform small bound
for that maximum over growing prime sets. Taking a compact maximum is
itself a loss of information; the exact complex product identity remains
available upstream for arguments using correlations across the disc.

The complete squarefree response already had an independent decay
theorem. Its ordinary-prime source was kept separately. A bound for the
new phase maximum is not, by itself, the conflicting signed lower bound
for that original source. Any further application must retain the actual
cutoffs, growing sieve and every accumulated heat correction.

The latest zero-free region, including its existential unevaluated
height threshold, remains unchanged. The independent signed prime
estimate and RH remain open.
