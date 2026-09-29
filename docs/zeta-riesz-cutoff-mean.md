# Uniform all-count control of Riesz cutoff changes

The sharp Möbius divisor quadratic is now bounded by one constant at every
cutoff. This gives a joint second-moment estimate for the **literal change**
in the Riesz response, on every integer interval. It removes the growing
logarithm from the cutoff-change budget. Neither whole-carrier threshold
is proved: the independent floor `-79/1000-o(1)` and ceiling `3/2+o(1)`
remain open.

## Checked arithmetic estimates

Write

\[
M_R(n)=\sum_{\substack{d\mid n\\d\le R}}\mu(d),\qquad
\mathcal R_L(n)=\sum_{d\mid n}\mu(d)(L-\log d)_+.
\]

[ZetaRieszSharpSieve](../RiemannGaussian/ZetaRieszSharpSieve.lean) proves
that there is a single real constant `E>0` such that, for every integer
cutoff `R`,

\[
\boxed{\sum_{d,e\le R}\frac{\mu(d)\mu(e)}{[d,e]}\le E.}
\]

For every `0 <= Y <= X`, it also proves

\[
\boxed{\sum_{Y<n\le X}M_R(n)^2\le E(X-Y)+R^2.}
\]

The constant is **existential and unevaluated**. In particular, it is not
the approximately `0.4407` seen in the finite numerical probe. The bound
does not assume an unproved sieve estimate or a hypothetical zero.

The proof uses the repository's proved harmonic Möbius decay, with every
excluded prime retained. A log-weighted recursion costs
`product_(p|g) (1-1/sqrt(p))^(-1)` on a common-divisor row. Its square is
averaged using a divisor-square Dirichlet series, already proved summable
at `3/2`. Summing the rows gives a constant independent of `R`.

For intervals, the exact count of multiples is the difference of two
integer floors. Their combined error has absolute value at most one.
Thus the main term uses `X-Y`, while the finite error is still only `R^2`.
This is not obtained by subtracting two upper bounds.

## Literal cutoff differences and both signed sides

Let `A <= B` and `exp(B) < R+1`; taking `R=floor(exp(B))` is allowed.
[ZetaRieszCutoffMean](../RiemannGaussian/ZetaRieszCutoffMean.lean) proves

\[
\boxed{\sum_{Y<n\le X}
  \bigl(\mathcal R_B(n)-\mathcal R_A(n)\bigr)^2
  \le (B-A)^2\bigl(E(X-Y)+R^2\bigr).}
\]

The exact coefficient is

\[
(B-\log d)_+-(A-\log d)_+
=\min\{B-A,(B-\log d)_+\}.
\]

Finite summation by parts expresses this decreasing coefficient as a
positive mixture of sharp prefixes. The mixing mass is at most `B-A`.
Weighted Cauchy--Schwarz transfers the uniform prefix estimate before
any prime-count split or divisor-wise absolute bound.

For any finite `S` in `(Y,X]` and arbitrary real weights `w(n)`, the terminal
theorem `exists_masked_difference_bounds` gives

\[
J=\sum_{n\in S}w(n)\bigl(\mathcal R_B(n)-\mathcal R_A(n)\bigr),
\qquad -K\le J\le K,
\]

\[
K^2=\left(\sum_{n\in S}w(n)^2\right)(B-A)^2
       \bigl(E(X-Y)+R^2\bigr).
\]

The selection and weights can retain the actual phase, allocation,
ownership, factorial kernel, rough-prime support and clipped endpoints.
There is no dependence on a count ceiling or a share-geometry partition.
The theorem applies to fixed endpoints `A,B` on each such selection;
it does not silently allow independently varying cutoffs for each label.

## What this does not yet pay

The `R^2` error is useful when the physical cutoff is small relative to
the interval length. It is not uniformly absorbed on all campaign
geometries. The stronger classical estimate `sum M_R(n)^2=O(X)`, uniform
even when `R^2>X`, is not proved here. See the
[literature and numerical audit](zeta-riesz-sieve-mean.md#numerical-probe-and-literature-audit).

The literal weight energy, moving endpoints, and total source-normalized
cost across the unpaid prime periods still need bounds. The preceding
absolute-crossing divergence theorem remains intact; this estimate does
not revive a separate absolute payment of every crossing. Previously
credited sectors cannot be added again after completing their periods.
There is no new zero exclusion or RH claim.

The next target is to use this cutoff-independent arithmetic constant in
the retained prime moments **together with** their cutoff correction,
controlling the actual interval lengths and moving endpoints. The
finite counting error must either be paid on those geometries or replaced
by a stronger arithmetic estimate.

## Quantitative next test: cross-cutoff correlations

The optional `scripts/probe_riesz_cutoff_correlation.py` computes the
actual finite signed form

\[
Q(R,S)=\sum_{d\le R,e\le S}\frac{\mu(d)\mu(e)}{[d,e]}.
\]

With `R=100000`, its floating values are approximately `0.44074` at
`S=100000`, `0.06018` at `S=10000`, and `0.001314` at `S=100`.
The following [cross-cutoff slice](zeta-riesz-cross-cutoff.md) now proves
inverse-square decay in `log(R/S)` and a joint bound across separated
cutoffs using the same harmonic rows and the repository's finite Schur
inequality. Its integer mean retains the combined finite floor error.
The finite probe itself retains no campaign masks or source normalization.

See [the machine-readable audit](riesz-cutoff-mean-audit.json). All proofs
remain local until publication is requested.
