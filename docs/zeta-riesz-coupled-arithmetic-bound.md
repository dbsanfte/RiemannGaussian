# An independent arithmetic bound for joined energy minus credit

`ZetaRieszCoupledArithmeticBound` proves a bound for the **actual complete
ordinary-prime** `D_N-Q_N`, without an exposed-zero, simple-zero or rightmost
hypothesis. It independently reaches `399/5000` on the height range already
covered by the repository's zero-free region. It does **not** close the
global floor or prove a new zero-free region.

## One common order, with the credit retained

For a positive ratio `q`, put `a'_i=a_i/q^i`. The exact antidiagonal gives

\[
D_N(a)-Q_N(a)=q^{N-1}\bigl(D_N(a')-Q_N(a')\bigr).
\]

This rescales the signed incidence **as a whole**. It does not rescale
the separate diagonal energy and credit incorrectly or take separate norms
of two legs. All orders, including zero and one, remain.

If `|a_i| <= C q^i` then the checked one-sided inequality is

\[
D_N(a)-Q_N(a)\le q^{N-1}
 \left(C^2\sum_{i<N}|r_i|-Q_N(a')\right).
\]

The whole radius-matched credit stays negative. The checked two-sided bound
also gives

\[
|D_N(a)-Q_N(a)|\le C^2q^{N-1}\sum_{i<N}|r_i|.
\]

These are inequalities, not a replacement arithmetic carrier. They are
applied to the original `ordinaryArray` and the exact native cutoff.

## Actual arithmetic input and concrete cofinal bound

`ZetaRieszJoinedPhaseRadius.exists_ordinary_moment_bound` independently
supplies, at every fixed `|y|>=54`, constants `R_y,C_y` with

\[
\tfrac12<R_y<\tfrac34,\qquad
|\mathrm{ordinaryPrimeLogMoment}_i(\tfrac32+iy)|
 \le C_y R_y^{-i}.
\]

This comes from actual zeta nonvanishing on `Re s=1`, compactness and Cauchy
bounds, with the proper-prime-power correction included. It is not an
assumed arithmetic floor. Therefore `a_i` is bounded by
`C_y u (u/R_y)^i`. Joining before the estimate gives

\[
|D_N-Q_N|\le
 \frac{41}{12}(C_yu)^2(u/R_y)^{N-1},\qquad N\ge65536.
\]

The uniform `41/12` is a deliberately coarse checked coefficient bound:
the central price is at most `1/2`, the successor price at most `3/2`,
`b<=3/2`, and the earlier joined contraction subtracts `1/3`. The stronger
one-sided theorem retains the **actual** coefficient variation and
radius-matched credit rather than this coarse envelope.

On the already-proved range `log(|y|+3) <= 1800`, the actual analytic radius
is explicitly `100011/200000`. Uniformly for `1/2 <= u <= 10001/20000`,

\[
\boxed{|D_N-Q_N|\le C_y^2
 \left(\frac{100010}{100011}\right)^{N-1}.}
\]

Lean proves both convergence to zero and an eventual `D_N-Q_N < 399/5000`,
uniformly in this entire radius strip for each fixed covered height. The
constant and the eventual starting order can depend on height. No numerical
starting order is certified.

`false_of_cofinal_energy_sub_credit_bound` connects any actual independent
cofinal `399/5000+o(1)` estimate directly to the existing **all-multiplicity**
contradiction endpoint. It uses the proved adjacent-order payment and old
whole-completion/square budgets once. The arithmetic target remains an
explicit premise at uncovered heights; the implication is not itself a
new exclusion.

## Exact remaining limitation

At larger heights the independently proved `R_y>1/2` need not exceed `u`.
The geometric ratio may then be at least one, so this radius estimate
does not yield the global floor. The competing-mode exposed radius `R>u`
is a different object: it omits the selected singularity and cannot be
substituted for the full ordinary-prime analytic radius.

The coherent selected source still tends to `m^2*(1-retainedCost(u))`.
At the ceiling its unit-multiplicity gap above `0.0798` remains about
`0.0000717970349442`. No part of that gap has been paid by this slice at
uncovered heights. A new independent signed correlation estimate, or
stronger proved analytic coverage, is still required there.

## Local checks and optional numerical regression

The warning-as-error leaf build, namespace linters and transitive standard-
axiom check are local. See `scripts/CheckRieszCoupledArithmeticBound.lean`
and `docs/riesz-coupled-arithmetic-bound-audit.json`.

The optional 640/760-bit regression retains exact integer primes and full
complex phases, replaying 12 fixed finite-prime controls with 96 ball and
width comparisons. It checks the common-order identity and signed credit
inequality at three ratios below/above one. Controls are at `N=256`, below
native entry order, and heights are not zero assertions. Their finite-order
envelope is **not** an order-uniform Cauchy constant for all primes. No
numerical floor or mask-completion certificate follows. These scripts are
not proof dependencies and do not run in ordinary CI.

Every earlier proof, negative audit, literal mask and semiprime file is
preserved. The work is local: no commit/push, wider gates, root registration
or public-frontier update.
