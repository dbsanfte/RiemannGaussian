# Prime support strengthens the actual arithmetic floor

The actual Stechkin prime work now has a stronger independent lower bound,
with the same phase coefficients. The underlying comparison applies to every
admissible finite or countable family of real frequencies. Its full phase
energy also reaches the retained completion budget. The independent signed
inequality throughout the remaining right-half strip is still open.

## The support information used

Write `tau=zetaStechkinAbscissa(sigma)` and `c=zetaStechkinWeight(sigma)`.
For every natural index `m`, the actual arithmetic weight is exactly

\[
\Lambda(m)m^{-\sigma}-c\Lambda(m)m^{-\tau}
=\bigl(1-c e^{-(\tau-\sigma)\log m}\bigr)\Lambda(m)m^{-\sigma}.
\]

The Lean identity uses real exponentials, so indices zero and one are
handled by their zero von Mangoldt coefficients. For `sigma>=1`, the factor
is increasing with the positive index. The first possible prime support is
two, giving

\[
F_\sigma=1-c e^{-(\tau-\sigma)\log2}>1-c.
\]

For every nonnegative summable coefficient family `a` and arbitrary real
frequencies `omega`, assume the actual kernel
`K(t)=sum a_n*cos(omega_n*t)` is nonnegative. Genuine convergence gives

\[
F_\sigma\sum_m\Lambda(m)m^{-\sigma}K(y\log m)
\le\sum_m\bigl(\Lambda(m)m^{-\sigma}-c\Lambda(m)m^{-\tau}\bigr)K(y\log m),
\qquad \sigma>1.
\]

This comparison does not require a particular phase count or coefficient
optimizer. The exact index-dependent identity stays available before the
uniform support estimate.

On `1<=sigma<=5/4`, Lean proves `tau-sigma>=10/17`, `c<1/2`, and
`exp(-(tau-sigma)*log(2))<=2/3`. Consequently

\[
F_\sigma\ge\frac23\ge\frac65(1-c).
\]

The final comparison uses the existing `c>=4/9`. This is at least a 20%
improvement of the **Stechkin transfer factor**, not a 20% increase in the
zero-free width. The original single-line arithmetic floor is unchanged.

Compiled entry points in
[ZetaStechkinSupportFloor.lean](../RiemannGaussian/ZetaStechkinSupportFloor.lean):

- `zetaStechkinPrimeWeight_eq_supportFactor`
- `zetaStechkinSupportFactor_mono`
- `six_fifths_weight_gap_le_zetaStechkinSupportFactor`
- `zetaPhase_stechkin_primeWork_ge_supportFactor`
- `zetaPhase_binomial_energy_le_mass`
- `zetaPhase_stechkin_binomial_energy_support_floor`
- `phaseContactExact_stechkin_one_sixtieth_floor`

## Keeping every linked phase

Define the centered binomial energy and its coefficient by

\[
E_a(\theta)=\sum_n a_n(2+2\cos(\omega_n\theta))^{10}
-184756\sum_n a_n,
\qquad
v_\sigma=\frac{\log2}{77520}e^{-4\sigma\log2}.
\]

The all-family arithmetic estimate retains `F_sigma*v_sigma*E_a(y*log(2))`.
It does not assume this centered energy is nonnegative. For the existing
exact family, the earlier independent estimate does make it positive and
gives the stronger actual Stechkin floor

\[
\frac1{60}e^{-4(\sigma-1)\log2}
\le F_\sigma\frac1{40}e^{-4(\sigma-1)\log2}
\le F_\sigma v_\sigma E_a(y\log2)
\le\mathrm{StechkinPrimeWork}(\sigma,y).
\]

The finite expression `phaseContactExactSupportEnergy` equals the middle
energy exactly, with all nine existing coefficients and phases. No new
coefficients are selected or optimized.

## Transport to the actual zero inequality

The general source theorem combines the entire energy with the
[negative completion reserve](zeta-completion-reserve-zero-free.md), the
selected analytic zero multiplicity, and the actual signed pole subtraction.

For an actual nontrivial zero `rho=beta+i*t` with `beta>=12/13`, put
`d=1-beta`, `sigma=1+(13/4)*d`, and let `R(sigma,t)` denote the explicit finite
support energy. Lean proves the necessary inequality

\[
\begin{aligned}
\frac{11}{625}+dR(\sigma,t)
\le{}&d(1-c)\left[\frac{481}{1600}d+
\frac{61}{200}\log(\sigma+|t|)-\frac18\right]
+\frac{793}{400}\frac{d^2}{t^2}.
\end{aligned}
\]

In particular its left side is at least
`11/625+(d/60)*exp(-13*d*log(2))`. Every arithmetic premise in this necessary
zero inequality is proved. The literal nonvanishing theorem says that a
point in the stated real-part range is nonzero whenever its **explicit**
right side is strictly below `11/625+d*R(sigma,t)`. The strict test has not
been proved throughout that range.

Compiled entry points in
[ZetaCompletionSupportBudget.lean](../RiemannGaussian/ZetaCompletionSupportBudget.lean):

- `zetaPhase_source_add_supportEnergy_add_completionReserve_le`
- `phaseContactExactSupportEnergy_eq`
- `phaseContactExactSupportEnergy_le_primeWork`
- `phaseContactExactSupportEnergy_ge_one_sixtieth`
- `phaseContactExactSupportEnergy_le_at_zero`
- `phaseContactExact_completionReserve_support_energy_zero_budget`
- `phaseContactExact_completionReserve_support_floor_zero_budget`
- `riemannZeta_ne_zero_of_completion_support_energy`

## What this leaves open

The proved uniform zero-free width remains `1/(10*log(abs(t)+2))`. This slice
improves the actual arithmetic contribution in its source budget; it does
not claim a new uniform zero-free curve.

There is also a checked limitation applying to all the coefficient families,
not just the exact optimizer. For every degree `N`,

\[
\sum_n a_n(2+2\cos(\omega_n\theta))^N
-\binom{2N}{N}\sum_n a_n
\le\left(4^N-\binom{2N}{N}\right)\sum_n a_n.
\]

Thus the centered tenth-degree energy is at most `863820` per unit mass,
uniformly over every finite or countable real-frequency spectrum. Lean
also proves `phaseContactExactSupportEnergy(sigma,t)` is at most its value
at `t=0`, for every `sigma>=1`. These are ceilings on this **energy test**;
they are not upper bounds on the actual prime work.

At a fixed sampling line, this finite reserve is bounded while the
displayed logarithmic height allowance grows. Adding more phases within
the fixed-degree test cannot remove that obstruction at fixed total mass.
A growing-degree or changing-scale argument would have to control its
arithmetic lag costs as well. The current bounded floor alone does not
supply the global RH inequality.

The full task remains to obtain an independent signed inequality excluding
every right-half zero. In the
[sieved odd-reflection formulation](zeta-sieved-fourier-reflection.md), it
is enough to beat the full surviving multiplicity source by any fixed margin
after the already vanishing error. That correlation and its signed structure
remain available. The full local build, declaration lints, and transitive
axiom audit pass; the repository workflow checks each published commit.
