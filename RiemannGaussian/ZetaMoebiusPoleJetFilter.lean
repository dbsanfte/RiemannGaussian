/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaMoebiusHeadRegular

/-!
# Preserving a selected zero while cancelling the convolution's pole jet

One extra spectral factor preserves the selected geometric signal and
kills the complete double pole of every finite Möbius head. The resulting
head estimate is uniform in the moment order and allows a genuinely
growing divisor cutoff. The remaining signed Möbius tail still needs an
independent arithmetic estimate.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- An additional pole factor, normalized to preserve the selected mode. -/
def zetaPoleJetLift (p : Polynomial ℂ) (b c : ℂ) : Polynomial ℂ :=
  Polynomial.C (b - c)⁻¹ * ((Polynomial.X - Polynomial.C c) * p)

/-- The added factor preserves evaluation at the selected mode. -/
theorem zetaPoleJetLift_eval_self (p : Polynomial ℂ) {b c : ℂ} (hbc : b ≠ c) :
    (zetaPoleJetLift p b c).eval b = p.eval b := by
  simp only [zetaPoleJetLift, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hbc), one_mul]

/-- The added factor kills the pole value exactly. -/
theorem zetaPoleJetLift_eval_pole (p : Polynomial ℂ) (b c : ℂ) :
    (zetaPoleJetLift p b c).eval c = 0 := by
  simp [zetaPoleJetLift]

/-- If the original filter kills the pole value, the lifted filter
also kills the derivative there: the entire double-pole jet vanishes. -/
theorem zetaPoleJetLift_derivative_eval_pole (p : Polynomial ℂ) (b c : ℂ) (hp : p.eval c = 0) :
    (zetaPoleJetLift p b c).derivative.eval c = 0 := by
  simp [zetaPoleJetLift, Polynomial.derivative_mul, hp]

/-- The lifted filter is the exact signed adjacent-moment difference,
including its fixed complex normalization. -/
theorem zetaMomentSequenceFilter_poleJetLift (p : Polynomial ℂ) (a : ℕ → ℂ) (N : ℕ) (b c : ℂ) :
    zetaMomentSequenceFilter (zetaPoleJetLift p b c) a N =
      (b - c)⁻¹ * (zetaMomentSequenceFilter p a (N + 1) - c * zetaMomentSequenceFilter p a N) := by
  rw [zetaPoleJetLift, zetaMomentSequenceFilter_C_mul, sub_mul,
    zetaMomentSequenceFilter_sub, zetaMomentSequenceFilter_X_mul, zetaMomentSequenceFilter_C_mul]

/-- A fixed normalized source survives the extra pole factor with its
same full complex amplitude. This uses a proved source limit, not a
new assumption on the signed arithmetic remainder. -/
theorem tendsto_zetaMomentSequenceFilter_poleJetLift (p : Polynomial ℂ) (a : ℕ → ℂ)
    {u c L : ℂ} (hu : u ≠ 0) (huc : u⁻¹ ≠ c)
    (h : Tendsto (fun N ↦ u ^ (N + 1) * zetaMomentSequenceFilter p a N) atTop (𝓝 L)) :
    Tendsto (fun N ↦ u ^ (N + 1) * zetaMomentSequenceFilter (zetaPoleJetLift p u⁻¹ c) a N) atTop (𝓝 L) := by
  have hshift := (h.comp (tendsto_add_atTop_nat 1)).const_mul u⁻¹
  have hh := (hshift.sub (h.const_mul c)).const_mul (u⁻¹ - c)⁻¹
  have hlim : (u⁻¹ - c)⁻¹ * (u⁻¹ * L - c * L) = L := by
    rw [← sub_mul, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr huc), one_mul]
  rw [hlim] at hh
  apply hh.congr'
  filter_upwards [] with N
  rw [zetaMomentSequenceFilter_poleJetLift]
  dsimp only [Function.comp_apply]
  rw [pow_succ u (N + 1)]
  field_simp

private theorem rightHalf_inverse_mode_ne_pole (rho : NontrivialZetaZero) :
    (((3 / 2 - rho.1.re : ℝ) : ℂ)⁻¹) ≠ ((3 / 2 + I * (rho.1.im : ℂ)) - 1)⁻¹ := by
  intro h
  have he := congrArg Complex.re (inv_injective h)
  norm_num at he
  linarith [NontrivialZetaZero.re_lt_one rho]

/-- The actual zero-isolating filter with its pole root promoted to
order two. It is defined by exact algebra on the original local divisor. -/
def zetaRightHalfPoleJetFilter (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) : Polynomial ℂ :=
  zetaPoleJetLift (zetaRightHalfZeroModeFilter rho hrho) (((3 / 2 - rho.1.re : ℝ) : ℂ)⁻¹)
    ((3 / 2 + I * (rho.1.im : ℂ)) - 1)⁻¹

/-- The complete pole jet vanishes for the actual lifted filter,
without any additional condition on the hypothetical selected zero. -/
theorem zetaRightHalfPoleJetFilter_pole_jet (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    (zetaRightHalfPoleJetFilter rho hrho).eval ((3 / 2 + I * (rho.1.im : ℂ)) - 1)⁻¹ = 0 ∧
      (zetaRightHalfPoleJetFilter rho hrho).derivative.eval ((3 / 2 + I * (rho.1.im : ℂ)) - 1)⁻¹ = 0 := by
  exact ⟨zetaPoleJetLift_eval_pole _ _ _, zetaPoleJetLift_derivative_eval_pole _ _ _
    (zetaRightHalfZeroModeFilter_eval_pole rho hrho)⟩

/-- The promoted filter retains the original negative multiplicity
limit of the actual convergent prime-moment series, at every right-half zero. -/
theorem tendsto_zetaRightHalfPoleJetFilter (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaPrimeLogFilter (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im))
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : ((3 / 2 - rho.1.re : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (by linarith [NontrivialZetaZero.re_lt_one rho])
  exact tendsto_zetaMomentSequenceFilter_poleJetLift (zetaRightHalfZeroModeFilter rho hrho)
    (fun n ↦ zetaPrimeLogMoment n (3 / 2 + I * rho.1.im)) hu (rightHalf_inverse_mode_ne_pole rho)
    (tendsto_zetaRightHalfZeroModeFilter rho hrho)

/-- An exact exponentially growing divisor cutoff with its floor retained. -/
def zetaMoebiusGeometricCutoff (q : ℝ) (N : ℕ) : ℕ := ⌊q ^ N⌋₊

/-- Every geometric cutoff with base greater than one is cofinal in
the natural divisor scale; it is not a fixed finite prefix. -/
theorem tendsto_zetaMoebiusGeometricCutoff {q : ℝ} (hq : 1 < q) :
    Tendsto (zetaMoebiusGeometricCutoff q) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_pow_atTop_atTop_of_one_lt hq)

private theorem cutoff_square_le {q : ℝ} (hq : 1 ≤ q) (N : ℕ) :
    (zetaMoebiusGeometricCutoff q N + 1 : ℝ) ^ 2 ≤ 4 * (q ^ 2) ^ N := by
  have hp : 0 ≤ q ^ N := pow_nonneg (zero_le_one.trans hq) N
  have hf : (zetaMoebiusGeometricCutoff q N : ℝ) ≤ q ^ N := Nat.floor_le hp
  have h1 : 1 ≤ q ^ N := one_le_pow₀ hq
  have he : (q ^ N) ^ 2 = (q ^ 2) ^ N := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  calc
    _ ≤ (2 * q ^ N) ^ 2 := by nlinarith [sq_nonneg (q ^ N - (zetaMoebiusGeometricCutoff q N : ℝ))]
    _ = _ := by rw [mul_pow, he]; norm_num

/-- The exact quantitative rate for every filtered geometric divisor
head. Its constant is independent of the moment order, and no arithmetic
cancellation estimate is assumed. -/
theorem exists_zetaMoebiusHeadFilter_geometric_bound (p : Polynomial ℂ) (y : ℝ)
    {u : ℂ} {q : ℝ} (hq : 1 ≤ q)
    (hp : p.eval ((3 / 2 + I * (y : ℂ)) - 1)⁻¹ = 0)
    (hp' : p.derivative.eval ((3 / 2 + I * (y : ℂ)) - 1)⁻¹ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖u ^ (N + 1) * zetaMomentSequenceFilter p
        (fun n ↦ zetaMoebiusHeadMoment (zetaMoebiusGeometricCutoff q N) n (3 / 2 + I * y)) N‖ ≤
          C * (‖u‖ * q ^ 2) ^ N := by
  obtain ⟨C, hC, hbound⟩ := exists_zetaMoebiusHeadFilter_bound y
  let S : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _)
  have hb (N : ℕ) :
      ‖u ^ (N + 1) * zetaMomentSequenceFilter p
        (fun n ↦ zetaMoebiusHeadMoment (zetaMoebiusGeometricCutoff q N) n (3 / 2 + I * y)) N‖ ≤
        (4 * ‖u‖ * C * S) * (‖u‖ * q ^ 2) ^ N := by
    rw [norm_mul, norm_pow]
    calc
      _ ≤ ‖u‖ ^ (N + 1) * (C * (zetaMoebiusGeometricCutoff q N + 1 : ℝ) ^ 2 * S) :=
        mul_le_mul_of_nonneg_left (hbound p _ N hp hp') (by positivity)
      _ ≤ ‖u‖ ^ (N + 1) * (C * (4 * (q ^ 2) ^ N) * S) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (cutoff_square_le hq N) hC.le) hS) (by positivity)
      _ = _ := by rw [pow_succ, mul_pow]; ring
  exact ⟨4 * ‖u‖ * C * S, by positivity, hb⟩

/-- The complete double-pole cancellation gives independent decay for
an exponentially growing Möbius head whenever its quadratic cutoff cost
is strictly below the selected geometric source. -/
theorem tendsto_zetaMoebiusHeadFilter_geometricCutoff (p : Polynomial ℂ) (y : ℝ)
    {u : ℂ} {q : ℝ} (hq : 1 ≤ q) (huq : ‖u‖ * q ^ 2 < 1)
    (hp : p.eval ((3 / 2 + I * (y : ℂ)) - 1)⁻¹ = 0)
    (hp' : p.derivative.eval ((3 / 2 + I * (y : ℂ)) - 1)⁻¹ = 0) :
    Tendsto (fun N : ℕ ↦ u ^ (N + 1) * zetaMomentSequenceFilter p
      (fun n ↦ zetaMoebiusHeadMoment (zetaMoebiusGeometricCutoff q N) n (3 / 2 + I * y)) N)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_zetaMoebiusHeadFilter_geometric_bound (u := u) p y hq hp hp'
  apply squeeze_zero_norm hb
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg (norm_nonneg u) (sq_nonneg q)) huq).const_mul
      C

/-- A mathematically defined divisor-growth base for the selected source;
its fourth power is the inverse of the source normalization. -/
def zetaMoebiusHeadGrowth (u : ℝ) : ℝ := (Real.sqrt (Real.sqrt u))⁻¹

/-- The chosen base exceeds one at every off-critical source scale. -/
theorem one_lt_zetaMoebiusHeadGrowth {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    1 < zetaMoebiusHeadGrowth u := by
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hs1 : Real.sqrt u < 1 := by nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg u]
  have hss : 0 < Real.sqrt (Real.sqrt u) := Real.sqrt_pos.mpr hsu
  apply (one_lt_inv₀ hss).mpr
  nlinarith [Real.sq_sqrt hsu.le, Real.sqrt_nonneg (Real.sqrt u)]

/-- The exact remaining geometric ratio is `sqrt(u)`, strictly below
one for each right-half zero. This discharges the growing-head rate test. -/
theorem zetaMoebiusHeadGrowth_rate {u : ℝ} (hu : 0 < u) :
    u * zetaMoebiusHeadGrowth u ^ 2 = Real.sqrt u := by
  have hs : Real.sqrt u ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  rw [zetaMoebiusHeadGrowth, inv_pow, Real.sq_sqrt (Real.sqrt_nonneg u)]
  rw [← div_eq_mul_inv]
  apply (div_eq_iff hs).mpr
  simpa only [pow_two] using (Real.sq_sqrt hu.le).symm

/-- The actual zero-isolating head has a geometric quantitative bound
with ratio `sqrt(3/2 - re rho)`, strictly below one. Its cutoff grows
exponentially and its constant is independent of the moment order. -/
theorem exists_zetaRightHalfPoleJetHead_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaMomentSequenceFilter (zetaRightHalfPoleJetFilter rho hrho)
          (fun n ↦ zetaMoebiusHeadMoment
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) n
            (3 / 2 + I * rho.1.im)) N‖ ≤ C * (Real.sqrt (3 / 2 - rho.1.re)) ^ N := by
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  obtain ⟨hp, hp'⟩ := zetaRightHalfPoleJetFilter_pole_jet rho hrho
  obtain ⟨C, hC, hb⟩ := exists_zetaMoebiusHeadFilter_geometric_bound
    (u := ((3 / 2 - rho.1.re : ℝ) : ℂ)) _ _ (one_lt_zetaMoebiusHeadGrowth hu hu1).le hp hp'
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, zetaMoebiusHeadGrowth_rate hu] at hb
  refine ⟨C + 1, by linarith, fun N ↦ (hb N).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (Real.sqrt_nonneg _) N)

/-- The promoted filter's actual growing Möbius head is independently
negligible at every selected off-critical zero, with all jet and rate
hypotheses discharged. -/
theorem tendsto_zetaRightHalfPoleJetHead (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaMomentSequenceFilter (zetaRightHalfPoleJetFilter rho hrho)
        (fun n ↦ zetaMoebiusHeadMoment
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) n
          (3 / 2 + I * rho.1.im)) N) atTop (𝓝 0) := by
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : 3 / 2 - rho.1.re < 1 := by linarith
  obtain ⟨hp, hp'⟩ := zetaRightHalfPoleJetFilter_pole_jet rho hrho
  apply tendsto_zetaMoebiusHeadFilter_geometricCutoff _ _
    (one_lt_zetaMoebiusHeadGrowth hu hu1).le _ hp hp'
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, zetaMoebiusHeadGrowth_rate hu]
  nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg (3 / 2 - rho.1.re)]

end

end RiemannGaussian
