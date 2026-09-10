/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStechkinPhaseBudget

/-!
# A half-logarithm bound for the genuine zeta completion

Horizontal monotonicity permits a height-dependent positive shift before
the real Euler-digamma bound is applied. The shifted real part pays one
power of the ordinate inside that bound. This retains the exact completion
identity while halving its logarithmic growth allowance for all phase families.
-/

namespace RiemannGaussian
noncomputable section
open Complex

/-- A horizontal comparison absorbs one of the two ordinate powers in
the Euler-digamma estimate. The full genuine regular completion has this
explicit bound at every positive abscissa and every real ordinate. -/
theorem re_zetaGlobalRegularCorrection_le_shifted_half_log {σ : ℝ}
    (hσ : 0 < σ) (y : ℝ) :
    (zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re ≤
      (Real.log ((σ + 2 + 2 * |y|) / 2) - Real.log Real.pi) / 2 := by
  let τ := σ + |y|
  let z : ℂ := ((τ : ℂ) + I * y) / 2 + 1
  have hτ : 0 < τ := add_pos_of_pos_of_nonneg hσ (abs_nonneg y)
  have hmono := re_zetaGlobalRegularCorrection_sub_nonpos hσ
    (show σ ≤ τ by dsimp [τ]; linarith [abs_nonneg y]) y
  rw [sub_re] at hmono
  have hz : 0 < z.re := by dsimp [z]; simp only [add_re, div_ofNat_re,
    mul_re, ofReal_re, ofReal_im, I_re, I_im, zero_mul, one_mul, sub_zero]; linarith
  have hψ := re_digamma_le_log_normSq_div_re hz
  have hden : 0 < normSq z / z.re := div_pos
    (normSq_pos.mpr (ne_zero_of_re_pos hz)) hz
  have hratio : normSq z / z.re ≤ (σ + 2 + 2 * |y|) / 2 := by
    apply (div_le_iff₀ hz).mpr
    dsimp [z, τ]
    simp only [normSq_apply, add_re, add_im, div_ofNat_re, div_ofNat_im,
      mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, one_re, one_im,
      zero_mul, one_mul, mul_zero, sub_zero, add_zero, zero_add]
    nlinarith [sq_abs y, mul_nonneg hσ.le (abs_nonneg y)]
  have hlog := Real.log_le_log hden hratio
  have he := zetaGlobalRegularCorrection_eq_shifted
    (s := (τ : ℂ) + I * y) (by simpa using hτ)
  have hre := congrArg Complex.re he
  simp only [sub_re, div_ofNat_re, log_re, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at hre
  change (zetaGlobalRegularCorrection ((τ : ℂ) + I * y)).re =
    (Complex.digamma z).re / 2 - Real.log Real.pi / 2 at hre
  linarith

/-- The true completion allowance on the entire closed Euler half-plane
is at most half a logarithm, without the previous additive constant. -/
theorem re_zetaGlobalRegularCorrection_le_half_log {σ : ℝ}
    (hσ : 1 ≤ σ) (y : ℝ) :
    (zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re ≤
      Real.log (σ + |y|) / 2 := by
  have hσ0 : 0 < σ := by linarith
  have hp : 0 < (σ + 2 + 2 * |y|) / 2 := by positivity
  have hsum : 0 < σ + |y| := by positivity
  have hb : (σ + 2 + 2 * |y|) / 2 ≤ Real.pi * (σ + |y|) := by
    have h := mul_le_mul_of_nonneg_right (show (3 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_three]) hsum.le
    nlinarith [abs_nonneg y]
  have hlog := Real.log_le_log hp hb
  rw [Real.log_mul Real.pi_ne_zero hsum.ne'] at hlog
  linarith [re_zetaGlobalRegularCorrection_le_shifted_half_log hσ0 y]

/-- The exact signed Stechkin completion inherits the same half-logarithm
bound and the original reduction factor. No zero terms are removed. -/
theorem zeta_stechkin_regular_le_half_log {σ : ℝ} (hσ : 1 ≤ σ) (y : ℝ) :
    (zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re -
      zetaStechkinWeight σ *
        (zetaGlobalRegularCorrection ((zetaStechkinAbscissa σ : ℝ) + I * y)).re ≤
      (1 - zetaStechkinWeight σ) * (Real.log (σ + |y|) / 2) := by
  have hmono := re_zetaGlobalRegularCorrection_sub_nonpos
    (show 0 < σ by linarith) (lt_zetaStechkinAbscissa hσ).le y
  rw [sub_re] at hmono
  have hc := zetaStechkinWeight_mem_Ioo hσ
  have h1 := mul_le_mul_of_nonneg_left (show
      (zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re ≤
        (zetaGlobalRegularCorrection ((zetaStechkinAbscissa σ : ℝ) + I * y)).re by linarith) hc.1.le
  have h2 := mul_le_mul_of_nonneg_left (re_zetaGlobalRegularCorrection_le_half_log hσ y)
    (show 0 ≤ 1 - zetaStechkinWeight σ by linarith [hc.2])
  nlinarith only [h1, h2]

private theorem half_log_summable {a ω : ℕ → ℝ} (hs : Summable a) (σ y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * y|)))) :
    Summable (fun n : ℕ => a n * (Real.log (σ + |ω n * y|) / 2)) := by
  apply ((hH.sub hs).div_const 2).congr
  intro n
  ring

/-- Every admissible finite or countable real-frequency family has a
half-logarithm completion budget. The full arithmetic work and every
genuine reflected zero pair are retained on the left. -/
theorem zetaPhase_stechkin_primeWork_add_zeroMass_le_half_log {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {σ : ℝ} (hσ : 1 < σ) (y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * y|)))) :
    (∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) +
      (∑' n : ℕ, a n * ∑' rho : NontrivialZetaZero,
        zetaStechkinPoissonSummand σ (ω n * y) rho) ≤
      (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * y)) +
        (1 - zetaStechkinWeight σ) *
          ∑' n : ℕ, a n * (Real.log (σ + |ω n * y|) / 2) := by
  rw [zetaPhase_stechkin_primeWork_add_zeroMass_eq ha hs hσ y hH]
  apply add_le_add le_rfl
  rw [← tsum_mul_left]
  apply (summable_zetaPhase_stechkin_regular ha hs hσ y hH).tsum_le_tsum _
    ((half_log_summable hs σ y hH).mul_left (1 - zetaStechkinWeight σ))
  intro n
  have h := mul_le_mul_of_nonneg_left (zeta_stechkin_regular_le_half_log hσ.le (ω n * y)) (ha n)
  nlinarith only [h]

/-- The full multiplicity source of a selected right-half zero survives
the smaller completion allowance for every admissible phase family. -/
theorem zetaPhase_stechkin_source_add_primeWork_le_half_log {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (j : ℕ) (hj : ω j = 1)
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) {σ : ℝ} (hσ : 1 < σ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * rho.1.im|)))) :
    a j * (analyticZetaZeroMultiplicity rho : ℝ) / (σ - rho.1.re) +
      (∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (rho.1.im * Real.log m)) ≤
      (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * rho.1.im)) +
        (1 - zetaStechkinWeight σ) *
          ∑' n : ℕ, a n * (Real.log (σ + |ω n * rho.1.im|) / 2) := by
  have h := zetaPhase_stechkin_primeWork_add_zeroMass_le_half_log ha hs hσ rho.1.im hH
  have hb := (summable_zetaPhase_stechkin_zeroMass ha hs hσ rho.1.im hH).le_tsum j
    (fun n _ => mul_nonneg (ha n)
      (tsum_nonneg (fun z => zetaStechkinPoissonSummand_nonneg hσ.le (ω n * rho.1.im) z)))
  rw [hj, one_mul] at hb
  have hsource := mul_le_mul_of_nonneg_left (zetaStechkin_source_le_total rho hρ hσ.le) (ha j)
  rw [← mul_div_assoc] at hsource
  linarith

/-- The integer-frequency half-logarithm allowance separates into the
constant mode, oscillatory mass and logarithmic frequency moment. There
is no additive constant-frequency mass cost. -/
theorem phase_global_half_log_le_split_budget {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    (∑' n : ℕ, a n * (Real.log (σ + |(n : ℝ) * y|) / 2)) ≤
      (a 0 * Real.log σ + phaseOscillatoryMass a * Real.log (σ + |y|) +
        phaseLogFrequencyMass a) / 2 := by
  have hH := summable_phase_globalHeight_of_logFrequency ha hs hlog hσ y
  have hL : Summable (fun n : ℕ => a n * Real.log (σ + |(n : ℝ) * y|)) := by
    apply (hH.sub hs).congr
    intro n
    ring
  have hsum : (∑' n : ℕ, a n * (1 + Real.log (σ + |(n : ℝ) * y|))) =
      (∑' n : ℕ, a n) + ∑' n : ℕ, a n * Real.log (σ + |(n : ℝ) * y|) := by
    simpa only [mul_add, mul_one] using hs.tsum_add hL
  have hmass : (∑' n : ℕ, a n) = a 0 + phaseOscillatoryMass a := hs.tsum_eq_zero_add
  have h := phase_global_height_le_split_budget ha hs hlog hσ y
  rw [hsum, hmass] at h
  simp_rw [← mul_div_assoc]
  rw [tsum_div_const]
  nlinarith only [h]

/-- Every positive displacement from the Euler boundary has the same
full normalized source and exact prime work with the smaller all-family
completion cost. All other genuine reflected zeros have proved sign. -/
theorem phase_shifted_source_add_primeWork_le_stechkin_half_log {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) {κ : ℝ} (hκ : 0 < κ) :
    phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ +
      (1 - rho.1.re) * (∑' m : ℕ,
        zetaStechkinPrimeWeight (1 + κ * (1 - rho.1.re)) m *
          phaseContactKernel a (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + κ * (1 - rho.1.re))) *
        ((a 0 * Real.log (1 + κ * (1 - rho.1.re)) +
          phaseOscillatoryMass a * Real.log (1 + κ * (1 - rho.1.re) + |rho.1.im|) +
            phaseLogFrequencyMass a) / 2) +
        κ * phaseOscillatoryMass a * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  let d := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hx : 0 < κ * d := mul_pos hκ hd
  have hσ : 1 < 1 + κ * d := by linarith
  have hH := summable_phase_globalHeight_of_logFrequency ha hs hlog hσ rho.1.im
  have hmain := zetaPhase_stechkin_source_add_primeWork_le_half_log
    (ω := fun n => (n : ℝ)) ha hs 1 (by norm_num) rho hρ hσ hH
  have hP := summable_zetaPhase_exactPole (ω := fun n => (n : ℝ)) ha hs hx rho.1.im
  have hpole : (∑' n : ℕ, a n * zetaStechkinPoleBudget (1 + κ * d) ((n : ℝ) * rho.1.im)) ≤
      ∑' n : ℕ, a n * (κ * d / ((κ * d) ^ 2 + ((n : ℝ) * rho.1.im) ^ 2)) := by
    apply (summable_zetaPhase_stechkin_pole (ω := fun n => (n : ℝ)) ha hs hσ rho.1.im).tsum_le_tsum _ hP
    intro n
    apply mul_le_mul_of_nonneg_left _ (ha n)
    unfold zetaStechkinPoleBudget
    rw [add_sub_cancel_left]
    apply sub_le_self
    have hc := (zetaStechkinWeight_mem_Ioo hσ.le).1.le
    have ht := hσ.trans (lt_zetaStechkinAbscissa hσ.le)
    positivity
  have hsplit := phase_exactPole_le_split_budget ha hs hx
    (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
  have hcost := mul_le_mul_of_nonneg_left
    (phase_global_half_log_le_split_budget ha hs hlog hσ rho.1.im)
    (show 0 ≤ 1 - zetaStechkinWeight (1 + κ * d) by
      linarith [(zetaStechkinWeight_mem_Ioo hσ.le).2])
  rw [show 1 + κ * d - rho.1.re = κ * d + d by dsimp [d]; ring] at hmain
  simp only [zetaPhaseKernel_natCast] at hmain
  have hsum : a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ * d + d) +
      (∑' m : ℕ, zetaStechkinPrimeWeight (1 + κ * d) m *
        phaseContactKernel a (rho.1.im * Real.log m)) ≤
      a 0 / (κ * d) + phaseOscillatoryMass a * (κ * d) / rho.1.im ^ 2 +
        (1 - zetaStechkinWeight (1 + κ * d)) *
          ((a 0 * Real.log (1 + κ * d) + phaseOscillatoryMass a * Real.log (1 + κ * d + |rho.1.im|) +
            phaseLogFrequencyMass a) / 2) := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hsum hd.le
  have he1 : d * (a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ * d + d)) =
      a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ + 1) := by
    have hk1 : κ + 1 ≠ 0 := by positivity
    field_simp
  have he0 : d * (a 0 / (κ * d)) = a 0 / κ := by field_simp
  simp only [mul_add] at hm
  rw [he1, he0] at hm
  unfold phaseShiftSource
  dsimp only [d] at hm ⊢
  linear_combination hm

end
end RiemannGaussian
