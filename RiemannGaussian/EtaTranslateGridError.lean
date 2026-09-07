import RiemannGaussian.EtaTranslateDifference
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Full critical-square error from perturbing a finite eta translate grid

The complex coefficients and both actual translate families are retained
before applying weighted Cauchy--Schwarz. The resulting global estimate
depends on the coefficient absolute sum, rather than the dimension, and
uses the original support-mismatch modulus including its entire tail.
-/

open Complex Filter MeasureTheory Set

namespace RiemannGaussian

noncomputable section

/-- The entire weighted square difference between two grids carrying the same complex coefficients. -/
def pairedEtaTranslateGridError {d : ℕ} (a b : Fin d → ℝ) (c : Fin d → ℂ) : ℝ :=
  ∫ t : ℝ in Ioi 0, Real.exp (-t) *
    ‖pairedEtaTranslatedCombination a c t - pairedEtaTranslatedCombination b c t‖ ^ 2

/-- The original grid error retains the complete complex sum of signed colour differences. -/
theorem pairedEtaTranslatedCombination_sub_eq_sum {d : ℕ}
    (a b : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) :
    pairedEtaTranslatedCombination a c t - pairedEtaTranslatedCombination b c t =
      ∑ j, c j * ((pairedEtaTranslatedColour (a j) t - pairedEtaTranslatedColour (b j) t : ℝ) : ℂ) := by
  simp only [pairedEtaTranslatedCombination, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]

/-- Weighted Cauchy--Schwarz keeps each actual colour-pair square until after summing the complex coefficients. -/
theorem pairedEtaTranslatedCombination_sub_norm_sq_le {d : ℕ}
    (a b : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) :
    ‖pairedEtaTranslatedCombination a c t - pairedEtaTranslatedCombination b c t‖ ^ 2 ≤
      (∑ j, ‖c j‖) * ∑ j, ‖c j‖ *
        (pairedEtaTranslatedColour (a j) t - pairedEtaTranslatedColour (b j) t) ^ 2 := by
  let v := fun j ↦ pairedEtaTranslatedColour (a j) t - pairedEtaTranslatedColour (b j) t
  have hnorm : ‖pairedEtaTranslatedCombination a c t - pairedEtaTranslatedCombination b c t‖ ≤
      ∑ j, ‖c j‖ * |v j| := by
    rw [pairedEtaTranslatedCombination_sub_eq_sum]
    apply (norm_sum_le _ _).trans_eq
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, v]
  have hsq := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
    (r := fun j ↦ ‖c j‖ * |v j|) (f := fun j ↦ ‖c j‖) (g := fun j ↦ ‖c j‖ * v j ^ 2)
    (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ by positivity)
    (fun j _ ↦ by rw [mul_pow, sq_abs]; ring_nf; exact le_rfl)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hsq

/-- The complete critical square error of the two actual finite grids is genuinely integrable. -/
theorem integrableOn_pairedEtaTranslateGridError {d : ℕ}
    (a b : Fin d → ℝ) (c : Fin d → ℂ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) *
      ‖pairedEtaTranslatedCombination a c t - pairedEtaTranslatedCombination b c t‖ ^ 2) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  apply hi.mul_bdd (((measurable_pairedEtaTranslatedCombination a c).sub
    (measurable_pairedEtaTranslatedCombination b c)).norm.pow_const 2).aestronglyMeasurable
  refine Eventually.of_forall fun t ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add
    (norm_pairedEtaTranslatedCombination_le a c t) (norm_pairedEtaTranslatedCombination_le b c t))) 2

/-- The full grid error is nonnegative before any coefficient or displacement estimate. -/
theorem pairedEtaTranslateGridError_nonneg {d : ℕ} (a b : Fin d → ℝ) (c : Fin d → ℂ) :
    0 ≤ pairedEtaTranslateGridError a b c := integral_nonneg (fun _ ↦ by positivity)

/-- Interchanging the actual grids preserves the full complex square error. -/
theorem pairedEtaTranslateGridError_symm {d : ℕ} (a b : Fin d → ℝ) (c : Fin d → ℂ) :
    pairedEtaTranslateGridError a b c = pairedEtaTranslateGridError b a c := by
  unfold pairedEtaTranslateGridError
  simp_rw [norm_sub_rev]

/-- The entire grid error is bounded by the original coefficient weights times the full individual colour distances. -/
theorem pairedEtaTranslateGridError_le_weighted {d : ℕ}
    (a b : Fin d → ℝ) (c : Fin d → ℂ) :
    pairedEtaTranslateGridError a b c ≤
      (∑ j, ‖c j‖) * ∑ j, ‖c j‖ * pairedEtaTranslateDifferenceEnergy (a j) (b j) := by
  let g := fun j t ↦ ‖c j‖ * (Real.exp (-t) *
    (pairedEtaTranslatedColour (a j) t - pairedEtaTranslatedColour (b j) t) ^ 2)
  have hg (j : Fin d) : IntegrableOn (g j) (Ioi 0) :=
    (integrableOn_pairedEtaTranslateDifference (a j) (b j) 0).const_mul _
  have hsum := integrable_finsetSum Finset.univ (fun j _ ↦ hg j)
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, (∑ j, ‖c j‖) * ∑ j, g j t := by
      apply integral_mono_ae (integrableOn_pairedEtaTranslateGridError a b c) (hsum.const_mul _)
      exact Eventually.of_forall fun t ↦ by
        have h := mul_le_mul_of_nonneg_left (pairedEtaTranslatedCombination_sub_norm_sq_le a b c t)
          (Real.exp_pos (-t)).le
        apply h.trans_eq
        rw [← mul_assoc, mul_comm (Real.exp (-t)), mul_assoc, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        dsimp [g]
        ring
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun j _ ↦ hg j)]
      simp only [g, integral_const_mul, pairedEtaTranslateDifferenceEnergy]

/-- Every sufficiently small grid perturbation has a global square-error bound independent of the number of coefficients. -/
theorem pairedEtaTranslateGridError_le_sqrt {d : ℕ}
    {a b : Fin d → ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (c : Fin d → ℂ) {r : ℝ} (hr : r ≤ 1 / 8)
    (hshift : ∀ j, c j ≠ 0 → |a j - b j| ≤ r) :
    pairedEtaTranslateGridError a b c ≤ 8 * Real.sqrt r * (∑ j, ‖c j‖) ^ 2 := by
  calc
    _ ≤ (∑ j, ‖c j‖) * ∑ j, ‖c j‖ * (8 * Real.sqrt r) := by
      apply (pairedEtaTranslateGridError_le_weighted a b c).trans
      apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
      apply Finset.sum_le_sum
      intro j _
      by_cases hc : c j = 0
      · simp [hc]
      · exact mul_le_mul_of_nonneg_left
          (pairedEtaTranslateDifferenceEnergy_le_sqrt (ha j) (hb j) hr (hshift j hc)) (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end

end RiemannGaussian
