# A comparison estimate for the literal masked carrier

The independent floor `-79/1000-o(1)` remains **open**. This pass derives
an unconditional comparison inequality for the actual masked carrier,
with all counts and both Riesz hinges joined. The stronger follow-up also
absorbs excluded-prime and repeated-owner holes into the reference measure.
It does not prove that its
remaining error tends to zero, or bound its signed main by a numerical
constant. None of floor estimates1–5 is closed by this comparison alone.

The proof is in
[ZetaRieszLongCutoffError.lean](../RiemannGaussian/ZetaRieszLongCutoffError.lean);
the focused validation and source hashes are in
[riesz-long-cutoff-error-audit.json](riesz-long-cutoff-error-audit.json).

## The longer cutoff is within the literal support

The existing signed squarefree prefix is retained:

\[
\operatorname{sharp}(D,a)=\sum_{d\le D,\ d\mid a}\mu(d),\qquad
\operatorname{densityPrefix}(D)
=\sum_{d\le D}\mu(d)\operatorname{density}(\operatorname{primeFactors}(d)).
\]

Using the convergent squared-divisor Dirichlet series at `17/16` gives
one fixed finite arithmetic constant `countingConstant = C > 0` and

\[
\left|\sum_{a\le X,\ a\text{ squarefree}}\operatorname{sharp}(D,a)
-\operatorname{densityPrefix}(D)X\right|
\le C X^{3/4}D^{5/16}.
\]

Consequently `D^4 <= X^3` gives the power error `C X^(63/64)`.
This replaces the previous square-root cutoff restriction. There is no
prime-density approximation, phase substitution or bilinear hypothesis.

For every original core label, put `p = largestPrime(n)`, `a = n/p`
and `L = length(u,N)`. `core_translated_log_margin` proves exactly

\[
4(L-\log p)+N/4+\log p<3\log a.
\]

The assumptions are `u >= 1/2`, `N >= 2` and membership in the original
core band. They use its actual lower radial bound and physical length.
For `N >= 32`, `literal_masked_support` proves that every active adjacent
jump of an owner column satisfies `R^4 <= k^3` and `exp(N/2) <= k`,
where `R = floor(exp(L-log p))`. These range conditions are discharged
for the actual masks, rather than left as assumptions about a smooth shell.

## Put squarefreeness inside the reference measure

Let `rho = SquarefreeCounting.density(empty)`. The existing density
correction identity implies `rho > 0`; the existing signed prefix bound
is `abs(densityPrefix(D)) <= 2`.

The new comparison centers both sums against the same squarefree measure:

\[
\begin{split}
\bigg|\rho\sum_{a\le X,\ a\text{ squarefree}}q(a)\operatorname{sharp}(D,a)
&-\operatorname{densityPrefix}(D)
  \sum_{a\le X,\ a\text{ squarefree}}q(a)\bigg|\\
&\le 3C e^{-N/128}\sum_{k\le X}k|q(k)-q(k+1)|.
\end{split}
\]

`beforeSquaresWeight` retains the original owner, count, physical,
radial, allocation and phase masks. Repeated-owner labels are excluded
exactly. `beforeSquares_eq_literal` proves on **every integer** that
applying the squarefree indicator to this weight recovers the literal
squarefree owner column. Thus squarefree holes are no longer charged as
variation of `q`. The other masks are still present in `q`, including
their discontinuities. This is not a completion of the prime/count support.

## The assembled inequality

`literal_joined_carrier_estimate` applies to any selected `B` contained in
the original `coreBand`, retaining every condition of `B`. Let

\[
\begin{gathered}
S=B\cap\{n:n\text{ squarefree}\},\quad
X=\max(1,\max_{n\in B} n/\operatorname{largestPrime}(n)),\\
P=\{\operatorname{largestPrime}(n):n\in S\},\quad
c_p=L-\log p,\\
H_p=\sum_{1\le D\le\lfloor e^{c_p}\rfloor}
\big[(c_p-\log D)_+-(c_p-\log(D+1))_+\big]
\operatorname{densityPrefix}(D).
\end{gathered}
\]

Write `w_p` for the actual squarefree owner column, including the chosen
real scale, and `q_p` for its exact weight before squarefree holes are
inserted. The source-carrying quantity and comparison main are

\[
\begin{split}
J&=\operatorname{scale}\operatorname{Re}
  \sum_{n\in S}\operatorname{residualCoefficient}(A,L,N,n)
                  K_N(3/2+iy,n),\\
\mathcal M&=\sum_{p\in P}
 \left[\rho\sum_{a\le X}w_p(a)R_L(a)-H_p\sum_{a\le X}w_p(a)\right].
\end{split}
\]

The checked terminal theorem is

\[
\boxed{\displaystyle
|\rho J-\mathcal M|
\le 3C e^{-N/128}
\sum_{p\in P}(L-\log p)_+
       \sum_{k\le X} k|q_p(k)-q_p(k+1)|.}
\]

This assembles all original owner columns and counts. The untranslated
hinge `R_L` remains in the **signed main**, together with the signed
density-profile scalar times the whole signed weight sum. Neither main
term is paid by taking its termwise absolute value. The comparison is
independent of a hypothetical-zero phase assumption.

For the restricted radius, `source_rate_bound` also checks
`(2u)^N exp(-N/128) <= exp(-N/200)`. This is a rate comparison only:
it does **not** bound the displayed mask variation by `(2u)^N` or prove
source-normalized decay of the whole error.

## Stronger comparison for all original owner columns

### Stronger estimate using the raw owner weights

`literal_whole_carrier_estimate` now improves the comparison for the
**entire original squarefree core**, without adding a lower prime cutoff.
Its variation uses the raw owner weight

\[
q_p(a)=\operatorname{maskedWeight}(A,\operatorname{ownerRows}(B),L,y,
\operatorname{scale},N,a,p).
\]

Squarefreeness and the repeated-owner exclusion are both placed inside
the measure. Their exact bridge is `raw_rough_eq_literal`; in particular,
conditioning out the owner prime changes the density by exactly
`p/(p+1)`. `rough_owner_normalization` restores the **common** density
`rho` before summing owner columns. No density ratio is approximated.

Define the signed owner-conditioned scalar

\[
\widehat H_p=\frac{p+1}{p}
\sum_{1\le D\le\lfloor e^{c_p}\rfloor}
\big[(c_p-\log D)_+-(c_p-\log(D+1))_+\big]
\operatorname{roughDensityPrefix}(\{p\},D).
\]

The prefix is the signed Möbius sum of the actual marked squarefree
density after the owner prime has been excluded. With the same actual
`J` and `w_p` as above, put

\[
\widehat{\mathcal M}=\sum_{p\in P}
\left[\rho\sum_{a\le X}w_p(a)R_L(a)
-\widehat H_p\sum_{a\le X}w_p(a)\right].
\]

The unconditional checked bound is

\[
\boxed{\displaystyle
|\rho J-\widehat{\mathcal M}|
\le6C e^{-N/128}
\sum_{p\in P}(2+(c_p)_+)(c_p)_+
\sum_{k\le X}k|q_p(k)-q_p(k+1)|.}
\]

Unlike the earlier weight, this `q_p` has neither a squarefree nor a
repeated-owner zero extension. Its count, canonical-largest-prime,
physical, radial, phase and exact allocation masks are still literal.
The untranslated hinge and the owner-conditioned signed scalar remain
joined in `M`; their signed arithmetic control is still open.

### Physical exclusions retain a geometric comparison prefactor

The general `literal_normalized_raw_carrier_estimate` keeps a selected
finite prime-exclusion set `F` inside the same measure. Its actual label
set is precisely
`B.filter (fun n => Squarefree n && no prime of F divides n)` in logical
notation. The owner-conditioned prefix uses `insert p F`, and the same
estimate has the additional factor

\[
\operatorname{sieveCost}(3/4,F)
=\prod_{q\in F}\big[1+q^{-3/4}(1+q^{-3/4})\big].
\]

This is a literal **subpopulation** when `F` is nonempty. The whole
original core does not require all its prime factors to exceed `N^2`.
No proof pays the deleted population merely by choosing `F`.

For any `F` consisting of primes at most `N^2`, the new bound is

\[
\operatorname{sieveCost}(3/4,F)
\le \exp(2\operatorname{prefixMass}N^{17/32}),\qquad
\operatorname{sieveCost}(3/4,F)e^{-N/128}
\le e^{-N/256}\quad\text{eventually}.
\]

Both statements are Lean theorems; the order threshold is existential.
The optional [cost probe](../scripts/probe_riesz_long_cutoff_cost.py)
evaluates the exact finite product for all primes through `N^2`.
At the radius ceiling it finds log source-rate prefactors about `7.53`
at `N=640`, `4.63` at `N=1536`, and `-8.80` at `N=4096` (about
`1.51e-4`). These are floating-point diagnostics of **only the rate
prefactor**. They omit `C`, hinge factors and the remaining literal
variation, and are not masked-error or floor certificates. The probe is
manual and outside ordinary CI.

## What still has to be bounded

The next mathematical inputs are a sufficient bound for the summed
owner/count/cutoff/allocation variation of `q_p`, and joint signed control
of `M` with the existing funding/complement ledger. The squarefree and
repeated-owner parts have been removed from the variation cost exactly;
finite coprimality exclusions can also be absorbed in the measure. The remaining arithmetic
support has not been replaced by a complete shell.

The earlier absolute-variation and debit-growth no-gos remain valid for
their stated envelopes. This new centered comparison does not invalidate
them, assume a missing bilinear estimate, or give a new zero exclusion.
Focused warning-as-error compilation, ordinary-root import, namespace
lint and all 39 public transitive axiom checks are local validations.
No commit, push, wider CI, README or public endpoint update is part of
this pass.
