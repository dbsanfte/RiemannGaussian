/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaStechkinBudget
import RiemannGaussian.ZetaGlobalPhaseBudget
import RiemannGaussian.ZetaPhaseHorizontalBudget

/-!
# Arbitrary phase families with a reflected Stechkin budget

The actual comparison applies to every nonnegative summable phase family
whose logarithmic height cost is summable. No frequency count or optimizer
is prescribed. The zero sum is formed first inside each frequency; every
reflection pair has a proved nonnegative sign, and the full selected
right-half source survives the subtraction.

The signed arithmetic identity is retained before passing to finite
prime-power windows. The reduced Gamma allowance still grows with height,
and these theorems do not close the RH arithmetic inequality.
-/

namespace RiemannGaussian
noncomputable section
open Complex

variable {ω : ℕ → ℝ}

/-- The partial horizontal subtraction has its literal convergent
prime-power expansion for every admissible coefficient family. -/
theorem hasSum_zetaPhase_stechkin_arithmetic {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    HasSum (fun m : ℕ => zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m))
      (∑' n : ℕ, a n *
        ((-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re -
          zetaStechkinWeight σ * (-logDeriv riemannZeta
            ((zetaStechkinAbscissa σ : ℝ) + I * ((ω n * y : ℝ) : ℂ))).re)) := by
  have hτ := hσ.trans (lt_zetaStechkinAbscissa hσ.le)
  have h := (hasSum_zetaPhase_arithmetic (ω := ω) ha hs hσ y).sub
    ((hasSum_zetaPhase_arithmetic (ω := ω) ha hs hτ y).mul_left (zetaStechkinWeight σ))
  rw [← tsum_mul_left, ← (summable_zetaPhase_logDeriv (ω := ω) ha hs hσ y).tsum_sub
    ((summable_zetaPhase_logDeriv (ω := ω) ha hs hτ y).mul_left (zetaStechkinWeight σ))] at h
  convert! h using 1
  · funext m
    unfold zetaStechkinPrimeWeight
    ring
  · congr 1
    funext n
    ring

/-- Previously proved floors for any nonnegative phase kernel transfer
to the complete comparison work, retaining the exact factor `1-c`. -/
theorem zetaPhase_stechkin_primeWork_bounds {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    (1 - zetaStechkinWeight σ) *
      (∑' m : ℕ, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) ≤
        (∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) ∧
      (∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) ≤
        (∑' m : ℕ, zetaPhasePrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) := by
  have hold := (hasSum_zetaPhase_arithmetic (ω := ω) ha hs hσ y).summable
  have hnew := (hasSum_zetaPhase_stechkin_arithmetic (ω := ω) ha hs hσ y).summable
  constructor
  · rw [← tsum_mul_left]
    apply (hold.mul_left (1 - zetaStechkinWeight σ)).tsum_le_tsum _ hnew
    intro m
    have h := mul_le_mul_of_nonneg_right (zetaStechkinPrimeWeight_bounds hσ.le m).1
      (hp (y * Real.log m))
    nlinarith only [h]
  · apply hnew.tsum_le_tsum _ hold
    intro m
    exact mul_le_mul_of_nonneg_right (zetaStechkinPrimeWeight_bounds hσ.le m).2 (hp _)

/-- Complete reflected zero blocks remain summable over the entire
phase family. No exchange of zero and frequency sums is needed. -/
theorem summable_zetaPhase_stechkin_zeroMass {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {σ : ℝ} (hσ : 1 < σ) (y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * y|)))) :
    Summable (fun n : ℕ => a n *
      ∑' rho : NontrivialZetaZero, zetaStechkinPoissonSummand σ (ω n * y) rho) := by
  have he : 1 + (σ - 1) = σ := by ring
  have hZ := summable_zetaPhase_globalZeros (ω := ω) ha hs (by linarith : 0 < σ - 1) y
    (by simpa only [he] using hH)
  simp only [he] at hZ
  have hD := summable_zetaPhase_horizontal_zeroMass (ω := ω) ha hs hσ
    (lt_zetaStechkinAbscissa hσ.le).le y
  apply ((hZ.mul_left (1 - zetaStechkinWeight σ)).add
    (hD.mul_left (zetaStechkinWeight σ))).congr
  intro n
  rw [tsum_zetaStechkinPoissonSummand hσ.le]
  unfold zetaHorizontalPoissonSummand
  rw [(summable_zetaGlobalPoissonSummand (s := (σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))
    (by simpa using hσ.le)).tsum_sub (summable_zetaGlobalPoissonSummand
      (s := ((zetaStechkinAbscissa σ : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ))
        (by simpa using hσ.le.trans (lt_zetaStechkinAbscissa hσ.le).le))]
  ring

/-- The exact signed pole terms are summable with coefficient
summability alone. -/
theorem summable_zetaPhase_stechkin_pole {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {σ : ℝ} (hσ : 1 < σ) (y : ℝ) :
    Summable (fun n : ℕ => a n * zetaStechkinPoleBudget σ (ω n * y)) := by
  have hP := summable_zetaPhase_exactPole (ω := ω) ha hs (by linarith : 0 < σ - 1) y
  have ht := hσ.trans (lt_zetaStechkinAbscissa hσ.le)
  have hQ := summable_zetaPhase_exactPole (ω := ω) ha hs
    (by linarith : 0 < zetaStechkinAbscissa σ - 1) y
  apply (hP.sub (hQ.mul_left (zetaStechkinWeight σ))).congr
  intro n
  unfold zetaStechkinPoleBudget
  ring

/-- The literal completion comparison converges. Its bounded horizontal
difference requires no extra height moment at the auxiliary abscissa. -/
theorem summable_zetaPhase_stechkin_regular {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {σ : ℝ} (hσ : 1 < σ) (y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * y|)))) :
    Summable (fun n : ℕ => a n *
      ((zetaGlobalRegularCorrection ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re -
        zetaStechkinWeight σ * (zetaGlobalRegularCorrection
          ((zetaStechkinAbscissa σ : ℝ) + I * ((ω n * y : ℝ) : ℂ))).re)) := by
  have he : 1 + (σ - 1) = σ := by ring
  have hR := summable_zetaPhase_globalRegular (ω := ω) ha hs (by linarith : 0 < σ - 1) y
    (by simpa only [he] using hH)
  simp only [he] at hR
  have hD := summable_zetaPhase_horizontal_gamma (ω := ω) ha hs
    (by linarith : 0 < σ) (lt_zetaStechkinAbscissa hσ.le).le y
  apply ((hR.mul_left (1 - zetaStechkinWeight σ)).sub
    (hD.mul_left (zetaStechkinWeight σ))).congr
  intro n
  simp only [Complex.sub_re]
  ring

/-- The complete phase identity retains the signed arithmetic work,
all actual reflected zero blocks, and the exact completion comparison. -/
theorem zetaPhase_stechkin_primeWork_add_zeroMass_eq {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {σ : ℝ} (hσ : 1 < σ) (y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * y|)))) :
    (∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) +
      (∑' n : ℕ, a n * ∑' rho : NontrivialZetaZero,
        zetaStechkinPoissonSummand σ (ω n * y) rho) =
      (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * y)) +
        ∑' n : ℕ, a n *
          ((zetaGlobalRegularCorrection ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re -
            zetaStechkinWeight σ * (zetaGlobalRegularCorrection
              ((zetaStechkinAbscissa σ : ℝ) + I * ((ω n * y : ℝ) : ℂ))).re) := by
  rw [(hasSum_zetaPhase_stechkin_arithmetic (ω := ω) ha hs hσ y).tsum_eq]
  have hτ := hσ.trans (lt_zetaStechkinAbscissa hσ.le)
  have hD : Summable (fun n : ℕ => a n *
      ((-logDeriv riemannZeta ((σ : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re -
        zetaStechkinWeight σ * (-logDeriv riemannZeta
          ((zetaStechkinAbscissa σ : ℝ) + I * ((ω n * y : ℝ) : ℂ))).re)) := by
    apply ((summable_zetaPhase_logDeriv (ω := ω) ha hs hσ y).sub
      ((summable_zetaPhase_logDeriv (ω := ω) ha hs hτ y).mul_left (zetaStechkinWeight σ))).congr
    intro n
    ring
  have hZ := summable_zetaPhase_stechkin_zeroMass (ω := ω) ha hs hσ y hH
  have hP := summable_zetaPhase_stechkin_pole (ω := ω) ha hs hσ y
  have hR := summable_zetaPhase_stechkin_regular (ω := ω) ha hs hσ y hH
  rw [← hD.tsum_add hZ, ← hP.tsum_add hR]
  apply tsum_congr
  intro n
  have h := zeta_stechkin_real_budget hσ (ω n * y)
  linear_combination a n * h

/-- Every admissible finite or countably infinite phase family obeys
the reduced logarithmic budget, with the complete nonnegative reflected
zero mass still present. -/
theorem zetaPhase_stechkin_primeWork_add_zeroMass_le {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) {σ : ℝ} (hσ : 1 < σ) (y : ℝ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * y|)))) :
    (∑' m : ℕ, zetaStechkinPrimeWeight σ m * zetaPhaseKernel a ω (y * Real.log m)) +
      (∑' n : ℕ, a n * ∑' rho : NontrivialZetaZero,
        zetaStechkinPoissonSummand σ (ω n * y) rho) ≤
      (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * y)) +
        (1 - zetaStechkinWeight σ) * ∑' n : ℕ, a n * (1 + Real.log (σ + |ω n * y|)) := by
  rw [zetaPhase_stechkin_primeWork_add_zeroMass_eq ha hs hσ y hH]
  apply add_le_add le_rfl
  rw [← tsum_mul_left]
  apply (summable_zetaPhase_stechkin_regular (ω := ω) ha hs hσ y hH).tsum_le_tsum _
    (hH.mul_left (1 - zetaStechkinWeight σ))
  intro n
  have h := mul_le_mul_of_nonneg_left (zeta_stechkin_regular_le hσ.le (ω n * y)) (ha n)
  nlinarith only [h]

/-- The entire original multiplicity source of a selected right-half
zero survives for every admissible phase family. -/
theorem zetaPhase_stechkin_source_add_primeWork_le {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (r : ℕ) (hr : ω r = 1)
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) {σ : ℝ} (hσ : 1 < σ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * rho.1.im|)))) :
    a r * (analyticZetaZeroMultiplicity rho : ℝ) / (σ - rho.1.re) +
      (∑' m : ℕ, zetaStechkinPrimeWeight σ m *
        zetaPhaseKernel a ω (rho.1.im * Real.log m)) ≤
      (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * rho.1.im)) +
        (1 - zetaStechkinWeight σ) * ∑' n : ℕ, a n * (1 + Real.log (σ + |ω n * rho.1.im|)) := by
  have h := zetaPhase_stechkin_primeWork_add_zeroMass_le ha hs hσ rho.1.im hH
  have hb := (summable_zetaPhase_stechkin_zeroMass ha hs hσ rho.1.im hH).le_tsum r
    (fun n _ => mul_nonneg (ha n)
      (tsum_nonneg (fun z => zetaStechkinPoissonSummand_nonneg hσ.le (ω n * rho.1.im) z)))
  rw [hr, one_mul] at hb
  have hsource := mul_le_mul_of_nonneg_left (zetaStechkin_source_le_total rho hρ hσ.le) (ha r)
  rw [← mul_div_assoc] at hsource
  linarith

/-- Every finite prime-power window strengthens the same source bound
when the whole phase kernel is nonnegative. All omitted arithmetic terms
and all omitted reflected zero pairs have independently proved signs. -/
theorem zetaPhase_stechkin_source_add_finite_primeWork_le {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hp : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    (r : ℕ) (hr : ω r = 1) (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re)
    {σ : ℝ} (hσ : 1 < σ)
    (hH : Summable (fun n : ℕ => a n * (1 + Real.log (σ + |ω n * rho.1.im|)))) (S : Finset ℕ) :
    a r * (analyticZetaZeroMultiplicity rho : ℝ) / (σ - rho.1.re) +
      (∑ m ∈ S, zetaStechkinPrimeWeight σ m *
        zetaPhaseKernel a ω (rho.1.im * Real.log m)) ≤
      (∑' n : ℕ, a n * zetaStechkinPoleBudget σ (ω n * rho.1.im)) +
        (1 - zetaStechkinWeight σ) * ∑' n : ℕ, a n * (1 + Real.log (σ + |ω n * rho.1.im|)) := by
  have hf := (hasSum_zetaPhase_stechkin_arithmetic (ω := ω) ha hs hσ rho.1.im).summable.sum_le_tsum S
    (fun m _ => mul_nonneg (zetaStechkinPrimeWeight_nonneg hσ.le m) (hp _))
  have h := zetaPhase_stechkin_source_add_primeWork_le ha hs r hr rho hρ hσ hH
  linarith

/-- At every positive shift the same normalized source survives, while
the entire logarithmic height allowance is multiplied by the reduced
Stechkin factor. Integer families need only the stated logarithmic moment. -/
theorem phase_shifted_source_add_primeWork_le_stechkin {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) {κ : ℝ} (hκ : 0 < κ) :
    phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ +
      (1 - rho.1.re) * (∑' m : ℕ,
        zetaStechkinPrimeWeight (1 + κ * (1 - rho.1.re)) m *
          phaseContactKernel a (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + κ * (1 - rho.1.re))) *
        (∑' n : ℕ, a n * (1 + Real.log (1 + κ * (1 - rho.1.re) + |(n : ℝ) * rho.1.im|))) +
        κ * phaseOscillatoryMass a * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  let d := 1 - rho.1.re
  have hd : 0 < d := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hx : 0 < κ * d := mul_pos hκ hd
  have hσ : 1 < 1 + κ * d := by linarith
  have hH := summable_phase_globalHeight_of_logFrequency ha hs hlog hσ rho.1.im
  have hmain := zetaPhase_stechkin_source_add_primeWork_le
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
  rw [show 1 + κ * d - rho.1.re = κ * d + d by dsimp [d]; ring] at hmain
  simp only [zetaPhaseKernel_natCast] at hmain
  have hsum : a 1 * (analyticZetaZeroMultiplicity rho : ℝ) / (κ * d + d) +
      (∑' m : ℕ, zetaStechkinPrimeWeight (1 + κ * d) m *
        phaseContactKernel a (rho.1.im * Real.log m)) ≤
      a 0 / (κ * d) + phaseOscillatoryMass a * (κ * d) / rho.1.im ^ 2 +
        (1 - zetaStechkinWeight (1 + κ * d)) *
          ∑' n : ℕ, a n * (1 + Real.log (1 + κ * d + |(n : ℝ) * rho.1.im|)) := by
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
  simp only [mul_add, mul_one] at hm ⊢
  linear_combination hm

/-- The normalized all-family source budget with constant-frequency,
oscillatory-mass, and logarithmic-frequency costs made explicit. -/
theorem phase_shifted_source_add_primeWork_le_stechkin_split {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hlog : Summable (fun n : ℕ => a n * Real.log n))
    (rho : NontrivialZetaZero) (hρ : 1 / 2 < rho.1.re) {κ : ℝ} (hκ : 0 < κ) :
    phaseShiftSource (a 0) (a 1 * (analyticZetaZeroMultiplicity rho : ℝ)) κ +
      (1 - rho.1.re) * (∑' m : ℕ,
        zetaStechkinPrimeWeight (1 + κ * (1 - rho.1.re)) m *
          phaseContactKernel a (rho.1.im * Real.log m)) ≤
      (1 - rho.1.re) * (1 - zetaStechkinWeight (1 + κ * (1 - rho.1.re))) *
        (a 0 * (1 + Real.log (1 + κ * (1 - rho.1.re))) +
          phaseOscillatoryMass a * (1 + Real.log (1 + κ * (1 - rho.1.re) + |rho.1.im|)) +
            phaseLogFrequencyMass a) +
        κ * phaseOscillatoryMass a * (1 - rho.1.re) ^ 2 / rho.1.im ^ 2 := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have hσ : 1 < 1 + κ * (1 - rho.1.re) := by nlinarith [mul_pos hκ hd]
  have hc := (zetaStechkinWeight_mem_Ioo hσ.le).2.le
  have hb := mul_le_mul_of_nonneg_left
    (phase_global_height_le_split_budget ha hs hlog hσ rho.1.im)
    (mul_nonneg hd.le (sub_nonneg.mpr hc))
  exact (phase_shifted_source_add_primeWork_le_stechkin ha hs hlog rho hρ hκ).trans
    (add_le_add hb le_rfl)

end
end RiemannGaussian
