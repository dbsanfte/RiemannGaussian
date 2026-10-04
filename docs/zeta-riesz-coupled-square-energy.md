# An additional arithmetic estimate for joined energy minus credit

`ZetaRieszCoupledSquareEnergy` bounds the **actual complete ordinary-prime**
`D_N-Q_N` by one finite square budget after common-radius scaling. The full
correlation credit remains negative. No exposed-zero hypothesis enters the
arithmetic bound. The work does **not** close the uncovered global floor.

## The additional signed inequality

Write `a_i = ordinaryArray u y i`, `q=u/R` and `a'_i=a_i/q^i`. For every
positive order and `0<=b<=3/2`, Lean proves the native symmetric coefficient
bound

\[
|r_{N,i}|\le \frac4N.
\]

The coefficient is formed after joining both native factorial degrees and
swapped incidences. Therefore

\[
D_N(a')\le\frac4N\sum_{i<N}|a'_i|^2.
\]

For the complete ordinary-prime moments, define

\[
B_y(R)=\sum_{i\ge0}
 \left|\operatorname{ordinaryPrimeLogMoment}_i(\tfrac32+iy)\right|^2 R^{2i}.
\]

Analyticity of the full logarithmic derivative on a neighborhood of the
closed radius-`R` disk proves that this sum converges. The proof enlarges the
disk slightly and includes the proper-prime-power correction. It is not a
finite-prime extrapolation. If a larger disk `r>R` supplies the independent
Cauchy bound `|moment_i|<=C/r^i`, the checked quantitative certificate is

\[
B_y(R)\le\frac{C^2}{1-(R/r)^2}.
\]

The resulting arithmetic estimate, for the original native order
`N>=65536` and `1/2<=u<=10001/20000`, is

\[
\boxed{
D_N-Q_N\le (u/R)^{N-1}
 \left(\frac{4u^2B_y(R)}N-Q_N(a')\right).
}
\]

`ordinary_energy_sub_credit_le_square_budget` proves this inequality.
`abs_ordinary_energy_sub_credit_le_square_budget` also proves

\[
|D_N-Q_N|\le\frac{4u^2B_y(R)}N (u/R)^{N-1}.
\]

The new budget is independent of `N`. All logged orders, including zero
and one, and the entire complex ordinary-prime phase remain. The native
cutoff, moving length and the definition of `D-Q` are unchanged.

## Keep the smaller proved price

The square-budget estimate does not dominate the former pointwise-envelope
price at every finite order. Lean therefore proves

\[
D_N-Q_N\le (u/R)^{N-1}
\left[
\min\!\left((Cu)^2\sum_{i<N}|r_{N,i}|,
             \frac{4u^2B_y(R)}N\right)-Q_N(a')
\right].
\]

This minimum is taken between two **diagonal prices after the entire signed
incidence has been joined**. The same correlation credit is subtracted once;
it is not minimized, split or norm-paid.

## Concrete coverage and the remaining gap

At every fixed `|y|>=54`, Lean independently supplies some full analytic
radius `1/2<R_y<3/4` and a finite square budget. It does not guarantee `u<R_y`.

On the existing proved range `log(|y|+3)<=1800`, the same concrete radius
`100011/200000` used in the preceding slice gives

\[
|D_N-Q_N|\le\frac{B_y'}N
 \left(\frac{100010}{100011}\right)^{N-1}.
\]

`B_y'>0` depends on height, not order or `u`. Lean proves geometric decay
even after multiplying `|D_N-Q_N|` by `N`. This sharpens an existing covered
estimate; it supplies no new zero-free region, uncovered floor credit or
numerically certified starting order.

The limitation is checked, not just noted: if the actual ordinary-prime
array has any nonzero limiting source, its square budget at the source
radius is **not summable**. This applies to every exposed zero with its
actual multiplicity. Thus the new `1/N` factor cannot erase the selected
source by assuming a finite budget at `R=u`. The definition of a real `tsum`
does not license use of a nonsummable budget; the arithmetic bounds require
and prove summability from full-disk analyticity.

At uncovered heights the rate `(u/R)^(N-1)` can still grow. The global
independent `399/5000` target, the ceiling and RH remain open.

## Scoped validation and optional controls

The warning-as-error leaf build, 14 namespace linters and transitive
all-declaration standard-axiom check pass. See
`scripts/CheckRieszCoupledSquareEnergy.lean` and the scoped audit JSON.

The optional 640-bit producer and independent 760-bit replay retain exact
integer prime seeds, the full complex phase, native factorial indices and
moving length. They test 18 finite-prime rows at orders 256, 4096 and 65536,
at ratios below and above one. Three rows reach native entry order, but
their fixed finite universe is not the full arithmetic population. No test
height is asserted to be a zero ordinate.

In these controls the new price exceeds the old sharp price at order 256,
so the minimum retains the old one. For the same fixed prime universe at
orders 4096 and 65536, the new price is approximately 9.5% and 0.59% of the
old price. These are finite-control comparisons, not cofinal source savings.
The complete-prime square budget is proved analytically, not inferred from
these sampled values. The probes are not proof dependencies or ordinary CI
jobs, and certify no numerical floor.

All prior proofs, negative audits, masks and semiprime work are preserved.
This slice remains local, without commit/push, root registration, public
frontier changes or wider checks.
