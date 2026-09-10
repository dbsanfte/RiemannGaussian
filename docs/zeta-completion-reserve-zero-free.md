# Retained completion reserve and a wider actual zero exclusion

Lean now proves that every genuine nontrivial zeta zero `rho=beta+i*t`
satisfies

\[
\frac{1}{10\log(|t|+2)}<\beta<1-\frac{1}{10\log(|t|+2)}.
\]

The new excluded width is strictly greater than six fifths of the previous
`1/(12*log(|t|+22))` at every real ordinate. The literal nonvanishing theorem
covers the closed right-edge region at all heights, explicitly excluding
the pole at one. The independent bound in the remaining right-half strip
is still open. This is a stronger project theorem, with no claim of a best
published zero-free region or a proof of RH.

## Recovering a favorable constant

Write `G(sigma,t)` for the real part of the genuine regular completion.
The existing horizontal comparison and Euler-digamma estimate give

\[
G(\sigma,t)\le\frac12\left[
\log\frac{\sigma+2+2|t|}{2}-\log\pi\right].
\]

For `sigma>=1`, the logarithm's argument is at most
`(pi/2)*(sigma+|t|)`. Thus the same proved ingredients give

\[
G(\sigma,t)+\frac{\log2}{2}
\le\frac12\log(\sigma+|t|).
\]

The previous half-logarithm budget dropped this negative constant. That
was a valid weakening; keeping it supplies a usable reserve. The exact
signed completion identity remains available upstream.

Let `c` and `tau` be the original Stechkin coefficient and auxiliary
abscissa. Horizontal monotonicity gives the stronger signed estimate

\[
G(\sigma,t)-cG(\tau,t)+(1-c)\frac{\log2}{2}
\le (1-c)\frac12\log(\sigma+|t|).
\]

Summation preserves `(1-c)*(log 2/2)*sum a_n` for every nonnegative summable
family of real frequencies with the stated logarithmic height moment.
This includes finite and countably infinite families. No frequency count,
optimizer, or prime-work sign is assumed in that general budget.

Compiled entry points in
[ZetaCompletionReserve.lean](../RiemannGaussian/ZetaCompletionReserve.lean):

- `re_zetaGlobalRegularCorrection_add_log_two_le_half_log`
- `zeta_stechkin_regular_add_log_two_le_half_log`
- `zetaPhase_stechkin_primeWork_add_zeroMass_add_completionReserve_le`
- `zetaPhase_stechkin_source_add_primeWork_add_completionReserve_le`
- `phase_shifted_source_add_primeWork_add_completionReserve_le`

The full genuine zero sum is kept before extracting the selected zero's
analytic multiplicity. The actual signed prime work remains beside it.

## Paying the finite costs with the existing exact family

For the already proved exact optimizer, Lean certifies

\[
a_0\le\frac{37}{200},\quad
\sum a_n\ge\frac34,\quad
A:=\sum_{n\ge1}a_n\le\frac{61}{100},\quad
B:=\sum_{n\ge1}a_n\log n\le\frac14.
\]

Since `log 2/2>1/3`, its recovered completion reserve is at least `1/4`.
All coefficients are unchanged. The family's proved nonnegative phase
kernel makes the complete actual Stechkin prime work nonnegative.

Put `d=1-beta` and retain the original sampling line `sigma=1+(13/4)*d`.
The source remains at least `11/625`. After subtracting the retained
reserve, the full zero budget is

\[
\begin{aligned}
\frac{11}{625}+d\,\mathrm{PrimeWork}
\le{}&d(1-c)\left[
\frac{481}{1600}d+
\frac{61}{200}\log(1+(13/4)d+|t|)-\frac18\right]\\
&+\frac{793}{400}\frac{d^2}{t^2}.
\end{aligned}
\]

This is `phaseContactExact_completionReserve_zero_budget`. The negative
`1/8` is essential to the new estimate; the quadratic pole cost is still
explicit. No cancellation premise for an unknown arithmetic sum is added.

## The independent strict inequality

At any actual nontrivial zero, the existing centered Euler eta theorem
gives `t^2>3`. Lean derives `L:=log(|t|+2)>6/5`. In the candidate edge
region `d*L<=1/10`, this implies `d<=1/12`, so
`log(1+(13/4)*d+|t|)<=L`.

The existing Stechkin bound `c>=4/9`, together with those inequalities,
proves

\[
\begin{aligned}
&d(1-c)\left[\frac{481}{1600}d+\frac{61}{200}L-\frac18\right]
+\frac{793}{400}\frac{d^2}{t^2}\\
&\hspace{2em}\le\frac{61}{360}dL-\frac{79}{172800}d
\le\frac{61}{3600}
=\frac{11}{625}-\frac{59}{90000}.
\end{aligned}
\]

Thus the whole explicit allowance, after every completion and pole cost,
lies at least `59/90000` below the retained source. Nonnegative actual
prime work makes the putative zero impossible. This is a strict signed
inequality for the stated region, rather than a proposed sufficient premise.

Compiled entry points in
[ZetaCompletionReserveZeroFree.lean](../RiemannGaussian/ZetaCompletionReserveZeroFree.lean):

- `phaseContactExactFamily_completionReserve_ge`
- `phaseContactExact_completionReserve_zero_budget`
- `six_fifths_lt_log_abs_im_add_two`
- `zetaCompletionReserve_allowance_le`
- `zetaCompletionReserve_allowance_add_gap_le`
- `zetaCompletionReserve_margin_lt_one_sub_re`
- `nontrivialZetaZero_mem_completionReserve_strip`
- `riemannZeta_ne_zero_of_completionReserve_margin`
- `six_fifths_phaseHalfLog_margin_lt_completionReserve`

## Remaining full goal

The completion reserve applies to all admissible families. Its successful
instantiation here improves the actual zero region without a coefficient
search. Its logarithmic height cost still grows, so this result does not
extend the contradiction to every point right of the critical line.

The [sieved odd-reflection correlation](zeta-sieved-fourier-reflection.md)
and its full multiplicity source remain available for zeros in the smaller
remaining strip. We still need an independent strict upper bound for that
correlation, or another signed inequality covering every such zero.
The full goal remains active. Checks are local; commits and remote CI remain
held at the user's request.
