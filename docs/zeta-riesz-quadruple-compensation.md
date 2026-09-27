# Signed four-prime compensation inside the actual core

[`ZetaRieszQuadrupleCompensation`](../RiemannGaussian/ZetaRieszQuadrupleCompensation.lean)
proves an independent signed inequality between actual three-prime and
four-prime sums. For every fixed nonzero height, a selected positive
four-prime population eventually pays the entire norm of one fixed-width
balanced triple box. The proportion spent is at most `B/(N+1)`, for a
constant depending on the fixed parameters. No zero hypothesis is used.

The theorem retains the original Riesz coefficient, factorial kernel,
allocation fraction, phase and core masks. It does **not** pay all balanced
triples, give a source-normalized small error, or prove the
[whole joint floor](zeta-riesz-joint-floor.md).

## Actual labels and their signs

Write `f_N(n)` for the existing `residualCoefficient * zetaPrimeLogKernel`,
with the actual intermediate-prime allocation set and moving length.
The previously defined `tripleProducts a hT` takes one prime from each of
three ordered intervals of fixed logarithmic width `hT`, starting at
`a`, `a+hT`, `a+2*hT`, where

\[
2N/3\le a\le2N/3+C_T.
\]

Both `hT` and `C_T` are fixed as `N` grows. This is not a whole share band
of width proportional to `N`.

The compensating labels are products of four distinct actual primes. For
`0<=i,j<floor(N/(1000*h))`, their log intervals have width `h` and start at

\[
11N/25+ih,\quad12N/25+jh,\quad13N/25,\quad
14N/25-(i+j)h+v.
\]

The first two translations are balanced in the fourth prime. Thus the
total logarithm lies in `(2N+v,2N+v+4h]` for every grid cell. Unique prime
factorization proves the products are distinct across cells; they are
also disjoint from the triple box by prime count. Every supply label
eventually belongs to the original `coreBand`, including its physical,
count, squarefree, window and nondominant conditions.

For `137N/100<=L<=7N/5`, all pair cutoffs saturate and all complementary
triple cutoffs lie beyond `L`. The existing reflected linear identity
therefore gives, with `T=log n`,

\[
c_L(n)=\frac{T}{L}(2T-3L)\le-\frac{N}{20}.
\]

For each fixed `y!=0`, the existing phase-window theorem supplies fixed
`h>0`, `C>=0` and a translation `0<=v_N<=C` with
`cos(y*T)<=-1/2` throughout the supply window. Its coefficients and its
cosine are both negative, so its actual real contribution is positive.
The old allocation leaves at least half the factorial weight eventually.
The height and all actual phases remain in the sums.

## Quantitative signed comparison

Let

\[
Q_N=e^{-3N}(2N)^N/N!,\quad
X_N=\sum_{n\in\mathrm{tripleProducts}(a,h_T)}f_N(n),\quad
Y_N=\sum_{n\in\mathrm{supply}(N,h,v_N)}f_N(n).
\]

`eventually_interval_card_lower` applies the proved prime number theorem
to fixed-width multiplicative intervals, uniformly in their starting log
between `N/3` and `N`. It gives an actual population lower bound. It is
not an approximation of a signed prime sum by its density. The two grid
coordinates supply two powers of `N`, so

\[
\#\mathrm{supply}\ge c\frac{e^{2N}}{(N+1)^2},\qquad
\Re Y_N\ge c'\frac{N e^{2N}}{(N+1)^2}Q_N>0.
\]

Chebyshev's elementary upper bound for the triple intervals, combined
with the unchanged kernel, gives

\[
\|X_N\|\le B'\frac{N e^{2N}}{(N+1)^3}Q_N.
\]

`eventually_spending_bound` compares these **actual** sums:

\[
\boxed{\quad\|X_N\|\le\frac{B}{N+1}\Re Y_N.\quad}
\]

Consequently `eventually_joint_box_nonneg` proves `Re(X_N+Y_N)>=0`.
Constants and eventual thresholds depend on the fixed widths and height;
this does not provide a certified finite starting index.

## Spend only what is needed

Discarding the whole positive supply after paying a much smaller triple
box would lose its unused credit. The primary terminal theorem is instead
`eventually_core_spending`. Define

\[
\theta_N=\frac{\max(-\Re X_N,0)}{\Re Y_N},\qquad
W_N=\sum_{n\in\mathrm{coreBand}\setminus
 (\mathrm{tripleProducts}\cup\mathrm{supply})}f_N(n).
\]

On the unchanged dyadic schedule and `1/2<u<=10001/20000`, it proves

\[
\boxed{
\begin{gathered}
0\le\theta_N\le B/(N+1),\qquad\theta_N\le1,\\
\Re\bigl(u^{N+1}\mathrm{coreResponse}_N\bigr)
=u^{N+1}\bigl(\Re W_N+\max(\Re X_N,0)
+(1-\theta_N)\Re Y_N\bigr).
\end{gathered}}
\]

This is exact. All adverse triple credit is paid, all positive triple
credit and unused supply remain, and the complement is still signed.
`tendsto_spending_cap` proves the relative cap tends to zero. Neither the
spent amount nor the unused supply is asserted to vanish at source scale.
The same positive supply cannot be spent again without an explicit
remaining-credit budget.

The weaker `eventually_re_core_ge_without_box` deletes the whole pair at
zero lower-bound cost. It is not the preferred endgame: its discarded
surplus can be large, and it proves no useful floor for what remains.

## Scope of the progress

The [extension audit](zeta-riesz-core-extensions.md) ruled out appending
factors to one fixed balanced triple as its sole compensation. This
result uses different large-prime configurations and proves genuine
cross-count signed compensation. It covers one fixed-width triple box,
not the full collection of dangerous configurations. A joint bound for
the preserved complement **together with** its unused positive credit
remains necessary. The cofinal `-79/1000-o(1)` floor and the restricted
zero contradiction remain open.

The [subsequent band theorem](zeta-riesz-band-compensation.md) enlarges the
supply to three free prime-log coordinates. It pays a whole fixed-positive
share-width triple band in `2N<=log n<=2N+1` using at most half the supply.
Its exact ledger retains the unspent credit. The two supplies overlap;
these results cannot be added as independent credit budgets.

## Optional quantitative diagnostic

The [probe](../scripts/probe_riesz_quadruple_compensation.py) and its
[output](riesz-quadruple-compensation-probe.json) use the exact grid,
moving length, signed subset enumeration, total phase and factorial
radial weight, with fixed sample height `54`. They replace prime measures
by their ordinary density and omit allocation and further arithmetic
eligibility tests. No actual primes are enumerated. The height is not
asserted to be a zero ordinate, and the quadrature is not certified.

With `h=1/550`, the modeled positive supply divided by the triple box's
absolute mass is about `2.51,10.69,43.52,174.96` at
`N=4096,16384,65536,262144`. The modeled fraction spent on the adverse real
part is about `0.360,0.0845,0.0207,0.00516`. Two scrambled samples give
consistent diagnostics, not a rigorous enclosure. These values illustrate
the extra power of `N`; they do not certify those indices for the Lean
eventual theorem or control any unselected core labels. The probe is
optional and is not run by ordinary CI.
