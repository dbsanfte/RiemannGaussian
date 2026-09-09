# Prime-phase constraints on actual zeros

The main reusable result of this slice is a constraint coupling an actual
zeta zero to the complete signed arithmetic phase sum. It applies to every
nonnegative coefficient family with finite mass and logarithmic moment,
including infinite support. It does not require the eight-frequency
optimizer, its linear cost, or positivity of the phase kernel.

The exact optimizer supplies one fully discharged application: a stronger
unconditional edge exclusion than the project's previous theorem. The
structural constraint is retained separately so that further arithmetic
information can improve on that scalar consequence.

This is progress in the repository's proved bounds. Mathematical novelty
or a record zero-free region is not established. RH and the independent
global signed arithmetic bound remain open.

## A general constraint, with the signed arithmetic information retained

Write

\[
P_a(t)=\sum_{n\ge0}a_n\cos(nt),\qquad
M_a=\sum_{n\ge1}a_n,\qquad B_a=\sum_{n\ge1}a_n\log n,
\]

\[
L(y)=\log(|y|+22),\qquad
W_{\sigma,a}(y)=\sum_{m\ge1}\frac{\Lambda(m)}{m^\sigma}P_a(y\log m).
\]

Assume `a_n >= 0`, `sum a_n < infinity`, and `sum a_n log n < infinity`.
All height costs and arithmetic sums used here genuinely converge;
`summable_phase_height_of_logFrequency` proves the additional height
summability from these two moment hypotheses.

For a literal nontrivial zero `rho = beta + i gamma`, let
`delta = 1-beta > 0` and let `m(rho)` be its analytic multiplicity.
For `beta >= 3/4`, `kappa > 0`, and `kappa*delta <= 1/4`, the compiled
`phase_shifted_source_add_primeWork_le_split_budget` proves

\[
\boxed{
\frac{a_1m(\rho)}{\kappa+1}-\frac{a_0}{\kappa}
 +\delta W_{1+\kappa\delta,a}(\gamma)
\le
448\delta\bigl[a_0\log22+M_aL(\gamma)+B_a\bigr]
 +\frac{\kappa M_a\delta^2}{\gamma^2}.
}
\]

The zero's nonzero imaginary part is discharged by the repo's eta theorem.
The preceding theorem `phase_shifted_source_add_primeWork_le` retains the
exact height sum before bounding it by mass and logarithmic moment.
The upstream `zetaPhase_primeWork_add_localZeros_le` also retains every
local zero contribution before selecting this zero.

The coefficient family is indexed by integer frequencies in this slice.
The earlier arbitrary-real-frequency transport and asymptotic cost
theorems remain available in
[the general phase modules](zeta-general-phases-and-prime-recurrence.md).

## What a hypothetical zero would force on the primes

Suppose additionally that `P_a(t) >= 0` for every real `t`. Define the
remaining allowance

\[
R_a(\rho,\kappa)=
448\delta[a_0\log22+M_aL(\gamma)+B_a]
+\frac{\kappa M_a\delta^2}{\gamma^2}
-\left[\frac{a_1m(\rho)}{\kappa+1}-\frac{a_0}{\kappa}\right].
\]

For **every finite set** `S` of natural numbers,
`phase_finite_primeWork_le_zero_defect` proves

\[
\boxed{
\delta\sum_{m\in S}\frac{\Lambda(m)}{m^{1+\kappa\delta}}
 P_a(\gamma\log m)\le R_a(\rho,\kappa).
}
\]

Thus a zero near the allowed edge would force every finite prime-phase
window to fit inside the remaining allowance. A proved lower bound for
one such window exceeding that allowance gives a contradiction. This
interface permits prime-power recurrences, contact geometry, or coupled
prime blocks to be used without rebuilding the analytic argument.
Omitted arithmetic terms have a proved nonnegative sign. Excess
multiplicity decreases the available allowance.

The theorem does not itself supply such a decisive arithmetic lower bound
throughout the right half of the critical strip. In particular, the
previous positive floor from a fixed prime block has no proved height
growth sufficient to pay the growing analytic cost.
The selected-zero estimate in this module requires `beta >= 3/4`.
The [canonical boundary-weight successor](zeta-canonical-boundary-source.md)
now retains each pole with its regular correction and proves a signed
source inequality for every `beta > 1/2`. Its exact canonical source and
its critical-distance lower bound are kept as separate statements. The
independent arithmetic inequality needed for a contradiction remains open.

The separate [Suzuki actual-cutoff route](suzuki-phase-curvature-and-actual-cutoff.md)
still needs its eventual upper bound on the finite logarithmic prime
average. This slice does not prove that missing estimate.

## A fully discharged application to the exact family

`ZetaPhaseExactZeroBound.lean` instantiates the general theorem with the
already proved exact optimizer at `kappa = 13/4`. Its support is
`{0,1,2,3,4,7,10,13,24}`. The exact coefficients and contact root keep their
mathematical definitions; rational enclosures only bound their costs.

The compiled bounds are

\[
a_0\le\frac{37}{200},\quad M_a\le\frac{61}{100},\quad
B_a\le\frac14,\quad
\lambda=\frac4{17}a_1-\frac4{13}a_0\ge\frac{11}{625},
\]

and consequently

\[
\sum_n a_nL(n\gamma)\le\frac{61}{100}L(\gamma)+\frac{83}{100}.
\]

`phaseContactExact_source_add_primeWork_le` retains the exact source,
the excess-multiplicity term `(4/17)*a_1*(m(rho)-1)`, and the full
arithmetic sum. `phaseContactExact_finite_primeWork_le_zero_defect` gives
the explicit finite-window constraint with all family assumptions proved.

Only the downstream `phaseContactExact_zero_source_le` drops these
nonnegative arithmetic and excess-multiplicity terms. For `beta >= 15/16`
it gives

\[
\frac{11}{625}\le
448\delta\left[\frac{61}{100}L(\gamma)+\frac{83}{100}\right]
+\frac{793}{400}\frac{\delta^2}{\gamma^2}.
\]

Using `|gamma| >= 1` and completion reflection, the terminal theorem
`nontrivialZetaZero_mem_phaseContact_strip` proves

\[
\boxed{
\frac1{15600L(\gamma)+21200}<\beta<
1-\frac1{15600L(\gamma)+21200}.
}
\]

Since `L(gamma) > 3`, this also gives the simpler uniform margin
`1/(23000*L(gamma))`, strictly improving the former `1/(27500*L(gamma))`.
`riemannZeta_ne_zero_of_phaseContact_margin` and
`riemannZeta_ne_zero_of_phaseContact_reciprocal_log_margin` state literal
zeta nonvanishing on the corresponding closed right-edge regions.

The structural reason for the saving is that the growing height cost
depends on nonconstant coefficient mass. Higher frequencies incur their
actual logarithmic overhead, and the constant phase incurs a fixed cost.
The former linear-frequency optimum therefore does not specify an
intrinsic preferred phase count of zeta. It also has not been proved
optimal for this different, actual analytic budget.

## Local verification

Both modules are root-imported. Direct warning-as-error elaboration, the
focused build (4,414 jobs), the full build (9,785 jobs), whole-project
declaration lint, and source/whitespace checks passed with the pinned Lean
toolchain. The root-import audit checks all 23 new public theorems; every
transitive axiom list contains only `propext`, `Classical.choice`, and
`Quot.sound`. No commit or remote CI run is part of this slice, following
the user's local-iteration instruction.
