/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaCompletionHalfLogBound

/-!
# A retained negative completion constant for all phase families

The full completion contains a favorable constant which the previous
half-logarithm upper bound omitted. Its uniform reserve is `log 2 / 2`
per unit coefficient mass. The reserve survives the signed Stechkin
comparison and the complete countable phase sum. The genuine zero
multiplicity and prime-power work remain on the same side of the budget.
-/

namespace RiemannGaussian
noncomputable section
open Complex

/-- The genuine completion is uniformly below the preceding half-log
allowance by `log 2 / 2`. The logarithm of pi is used before weakening
the constant, rather than dropping its favorable sign. -/
theorem re_zetaGlobalRegularCorrection_add_log_two_le_half_log {σ : ℝ}
    (hσ : 1 ≤ σ) (y : ℝ) :
    (zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re + Real.log 2 / 2 ≤
      Real.log (σ + |y|) / 2 := by
  have hσ0 : 0 < σ := by linarith
  have hp : 0 < (σ + 2 + 2 * |y|) / 2 := by positivity
  have hsum : 0 < σ + |y| := by positivity
  have hb : (σ + 2 + 2 * |y|) / 2 ≤ (Real.pi / 2) * (σ + |y|) := by
    have hm := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hsum.le
    nlinarith [abs_nonneg y]
  have hlog := Real.log_le_log hp hb
  rw [Real.log_mul (by positivity : Real.pi / 2 ≠ 0) hsum.ne',
    Real.log_div Real.pi_ne_zero (by norm_num : (2 : ℝ) ≠ 0)] at hlog
  linarith [re_zetaGlobalRegularCorrection_le_shifted_half_log hσ0 y]

/-- The actual signed Stechkin completion retains the same reserve
with its exact positive factor `1-c`; no reflected zero is removed. -/
theorem zeta_stechkin_regular_add_log_two_le_half_log {σ : ℝ}
    (hσ : 1 ≤ σ) (y : ℝ) :
    (zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re -
      zetaStechkinWeight σ *
        (zetaGlobalRegularCorrection ((zetaStechkinAbscissa σ : ℝ) + I * y)).re +
      (1 - zetaStechkinWeight σ) * (Real.log 2 / 2) ≤
      (1 - zetaStechkinWeight σ) * (Real.log (σ + |y|) / 2) := by
  have hmono := re_zetaGlobalRegularCorrection_sub_nonpos
    (show 0 < σ by linarith) (lt_zetaStechkinAbscissa hσ).le y
  rw [sub_re] at hmono
  have hc := zetaStechkinWeight_mem_Ioo hσ
  have h1 := mul_le_mul_of_nonneg_left (show
      (zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re ≤
        (zetaGlobalRegularCorrection ((zetaStechkinAbscissa σ : ℝ) + I * y)).re by linarith) hc.1.le
  have h2 := mul_le_mul_of_nonneg_left
    (re_zetaGlobalRegularCorrection_add_log_two_le_half_log hσ y)
    (show 0 ≤ 1 - zetaStechkinWeight σ by linarith [hc.2])
  nlinarith only [h1, h2]

private theorem half_log_summable {a ω : ℕ → ℝ} (hs : Summable a) (σ y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * y|)))) :
    Summable (fun n : ℕ => a n * (Real.log (σ + |ω n * y|) / 2)) := by
  apply ((hH.sub hs).div_const 2).congr
  intro n
  ring

/-- Every summable nonnegative real-frequency family retains the
completion reserve proportional to its full mass. Both complete signed
prime work and the genuine reflected zero sum precede the estimate. -/
theorem zetaPhase_stechkin_primeWork_add_zeroMass_add_completionReserve_le
    {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * y|)))) :
    (∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) +
      (∑' n : ℕ, a n * ∑' rho : NontrivialZetaZero,
        zetaStechkinPoissonSummand σ (ω n * y) rho) +
      (1 - zetaStechkinWeight σ) * (Real.log 2 / 2) * (∑' n, a n) ≤
      (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * y)) +
        (1 - zetaStechkinWeight σ) *
          ∑' n : ℕ, a n * (Real.log (σ + |ω n * y|) / 2) := by
  have hr := summable_zetaPhase_stechkin_regular (ω := ω) ha hs hσ y hH
  have hc := hs.mul_right ((1 - zetaStechkinWeight σ) * (Real.log 2 / 2))
  have hu := (half_log_summable hs σ y hH).mul_left (1 - zetaStechkinWeight σ)
  have hb := (hr.add hc).tsum_le_tsum (fun n ↦ by
    have h := mul_le_mul_of_nonneg_left
      (zeta_stechkin_regular_add_log_two_le_half_log hσ.le (ω n * y)) (ha n)
    nlinarith only [h]) hu
  rw [hr.tsum_add hc, tsum_mul_right, tsum_mul_left] at hb
  rw [zetaPhase_stechkin_primeWork_add_zeroMass_eq ha hs hσ y hH]
  nlinarith only [hb]

/-- The full selected multiplicity remains in the all-family budget
with the recovered completion reserve and the actual arithmetic work. -/
theorem zetaPhase_stechkin_source_add_primeWork_add_completionReserve_le
    {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (j : ℕ) (hj : ω j = 1)
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) {σ : ℝ} (hσ : 1 < σ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * rho.1.im|)))) :
    a j * (analyticZetaZeroMultiplicity rho : ℝ) / (σ - rho.1.re) +
      (∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (rho.1.im * Real.log m)) +
      (1 - zetaStechkinWeight σ) * (Real.log 2 / 2) * (∑' n, a n) ≤
      (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * rho.1.im)) +
        (1 - zetaStechkinWeight σ) *
          ∑' n : ℕ, a n * (Real.log (σ + |ω n * rho.1.im|) / 2) := by
  have h := zetaPhase_stechkin_primeWork_add_zeroMass_add_completionReserve_le ha hs hσ rho.1.im hH
  have hb := (summable_zetaPhase_stechkin_zeroMass ha hs hσ rho.1.im hH).le_tsum j
    (fun n _ => mul_nonneg (ha n)
      (tsum_nonneg (fun z => zetaStechkinPoissonSummand_nonneg hσ.le (ω n * rho.1.im) z)))
  rw [hj, one_mul] at hb
  have hsource := mul_le_mul_of_nonneg_left (zetaStechkin_source_le_total rho hρ hσ.le) (ha j)
  rw [← mul_div_assoc] at hsource
  linarith

/-- Every positive Euler displacement transports the reserve without
altering the source or the trigonometric family. This is a general
countable-family inequality, independent of any coefficient optimizer. -/
theorem phase_shifted_source_add_primeWork_add_completionReserve_le
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) {κ : ℝ} (hκ : 0 < κ) :
    phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ +
      (1 - rho.1.re) * (∑' m : ℕ,
        zetaStechkinPrimeWeight (1 + κ * (1 - rho.1.re)) m *
          phaseContactKernel a (rho.1.im * Real.log m)) +
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + κ * (1 - rho.1.re))) *
        (Real.log 2 / 2) * (∑' n, a n) ≤
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
  have hmain := zetaPhase_stechkin_source_add_primeWork_add_completionReserve_le
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
        phaseContactKernel a (rho.1.im * Real.log m)) +
      (1 - zetaStechkinWeight (1 + κ * d)) * (Real.log 2 / 2) * (∑' n, a n) ≤
      a 0 / (κ * d) + phaseOscillatoryMass a * (κ * d) / rho.1.im ^ 2 +
        (1 - zetaStechkinWeight (1 + κ * d)) *
          ((a 0 * Real.log (1 + κ * d) + phaseOscillatoryMass a * Real.log (1 + κ * d + |rho.1.im|) +
            phaseLogFrequencyMass a) / 2) := by linarith
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
