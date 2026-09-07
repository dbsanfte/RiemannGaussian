import RiemannGaussian.EtaTranslatedHeadPairing
import RiemannGaussian.EtaTranslatedProjectionBound

/-!
# A finite arithmetic budget for the full eta projection residual

The compact target, its exact complex linear pairing, and the complete
finite overlap Gram give the original residual energy below the odd eta
cutoff. Every mixed coefficient is retained. The full omitted tail is then
added with its proved coefficient norm cost.
-/

open Complex Filter MeasureTheory Set
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The full finite quadratic residual form, with every complex cross coefficient retained. -/
def pairedEtaTranslatedFiniteResidualForm {d : ℕ} (N : ℕ) (T : ℝ)
    (a : Fin d → ℝ) (c : Fin d → ℂ) : ℝ :=
  1 + (∑ j, ∑ k, (c j * conj (c k)).re * pairedEtaTranslatedFiniteGram N T (a j) (a k)) -
    2 * ∑ j, (c j).re * pairedEtaTranslatedHeadPairing (a j)

/-- The literal finite interval formula with its complete infinite-tail allowance at the original odd endpoint. -/
def pairedEtaTranslatedFiniteResidualBudget {d : ℕ} (N : ℕ)
    (a : Fin d → ℝ) (c : Fin d → ℂ) : ℝ :=
  pairedEtaTranslatedFiniteResidualForm N (Real.log (2 * N + 1 : ℝ)) a c +
    (∑ j, ‖c j‖) ^ 2 / (2 * N + 1 : ℝ)

/-- The target square is integrable on every finite interval. -/
theorem integrableOn_pairedEtaProjectionHead_weighted_sq (T : ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * ‖pairedEtaProjectionHead t‖ ^ 2) (Ioc 0 T) := by
  simp_rw [pairedEtaProjectionHead_weighted_sq]
  exact ((Real.continuous_exp.integrableOn_Icc).mono_set Ioc_subset_Icc_self).indicator measurableSet_Ioc

/-- Once the finite cutoff includes the target, its full exact square mass is one. -/
theorem integral_Ioc_pairedEtaProjectionHead_weighted_sq {T : ℝ} (hT : Real.log 2 ≤ T) :
    (∫ t : ℝ in Ioc 0 T, Real.exp (-t) * ‖pairedEtaProjectionHead t‖ ^ 2) = 1 := by
  have h := integral_pairedEtaProjectionHead_weighted_sq
  simp_rw [pairedEtaProjectionHead_weighted_sq] at h ⊢
  rw [integral_indicator measurableSet_Ioc] at h
  rw [setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (Ioc_subset_Ioc le_rfl hT)]
  exact h

/-- The actual combination square is integrable before its full Gram expansion is evaluated. -/
theorem integrableOn_pairedEtaTranslatedCombination_weighted_sq {d : ℕ}
    (a : Fin d → ℝ) (c : Fin d → ℂ) (T : ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * ‖pairedEtaTranslatedCombination a c t‖ ^ 2) (Ioc 0 T) := by
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioc 0 T) :=
    (show Continuous (fun t : ℝ ↦ Real.exp (-t)) by fun_prop).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply hi.mul_bdd ((measurable_pairedEtaTranslatedCombination a c).norm.pow_const 2).aestronglyMeasurable
  exact Eventually.of_forall fun t ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_pairedEtaTranslatedCombination_le a c t) 2

/-- The complete residual square retains the target, all quadratic terms, and the signed complex cross term. -/
theorem pairedEtaTranslatedResidual_weighted_sq_eq {d : ℕ}
    (a : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) :
    Real.exp (-t) * ‖pairedEtaTranslatedResidual a c t‖ ^ 2 =
      (Real.exp (-t) * ‖pairedEtaProjectionHead t‖ ^ 2 +
        Real.exp (-t) * ‖pairedEtaTranslatedCombination a c t‖ ^ 2) -
      2 * (Real.exp (-t) * (pairedEtaProjectionHead t * conj (pairedEtaTranslatedCombination a c t)).re) := by
  rw [pairedEtaTranslatedResidual, Complex.sq_norm, Complex.normSq_sub,
    ← Complex.sq_norm, ← Complex.sq_norm]
  ring

/-- Every finite actual residual energy is exactly its full elementary overlap Gram form. -/
theorem pairedEtaTranslatedResidualEnergyCutoff_eq_finiteForm {d N : ℕ} {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) {T : ℝ}
    (hTlow : Real.log 2 ≤ T) (hThigh : T ≤ Real.log (2 * N + 1 : ℝ)) :
    pairedEtaTranslatedResidualEnergyCutoff a c T = pairedEtaTranslatedFiniteResidualForm N T a c := by
  have hH := integrableOn_pairedEtaProjectionHead_weighted_sq T
  have hB := integrableOn_pairedEtaTranslatedCombination_weighted_sq a c T
  have hC : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) *
      (pairedEtaProjectionHead t * conj (pairedEtaTranslatedCombination a c t)).re) (Ioc 0 T) := by
    have h := (integrableOn_pairedEtaProjectionHead_mul_conj_combination ha c T).re
    rw [RCLike.re_eq_complex_re] at h
    simpa only [IntegrableOn, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, mul_zero, add_zero, mul_sub, mul_assoc] using h
  have hsum : IntegrableOn (fun t : ℝ ↦
      Real.exp (-t) * ‖pairedEtaProjectionHead t‖ ^ 2 +
        Real.exp (-t) * ‖pairedEtaTranslatedCombination a c t‖ ^ 2) (Ioc 0 T) := hH.add hB
  unfold pairedEtaTranslatedResidualEnergyCutoff
  simp_rw [pairedEtaTranslatedResidual_weighted_sq_eq]
  rw [integral_sub hsum (hC.const_mul 2), integral_add hH hB, integral_const_mul,
    integral_Ioc_pairedEtaProjectionHead_weighted_sq hTlow,
    integral_pairedEtaTranslatedCombination_sq_eq_finiteGram ha c hThigh,
    integral_re_pairedEtaProjectionHead_mul_conj_combination ha c hTlow]
  rfl

/-- The finite quadratic form is nonnegative because it is the unchanged actual residual energy. -/
theorem pairedEtaTranslatedFiniteResidualForm_nonneg {d N : ℕ} {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) {T : ℝ}
    (hTlow : Real.log 2 ≤ T) (hThigh : T ≤ Real.log (2 * N + 1 : ℝ)) :
    0 ≤ pairedEtaTranslatedFiniteResidualForm N T a c := by
  rw [← pairedEtaTranslatedResidualEnergyCutoff_eq_finiteForm ha c hTlow hThigh]
  exact integral_nonneg (fun _ ↦ by positivity)

/-- The full infinite residual has an explicit finite arithmetic bound for every coefficient family and original cutoff. -/
theorem pairedEtaTranslatedResidualEnergy_le_finiteBudget {d N : ℕ} (hN : 1 ≤ N)
    {a : Fin d → ℝ} (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) :
    pairedEtaTranslatedResidualEnergy a c ≤ pairedEtaTranslatedFiniteResidualBudget N a c := by
  have hT : Real.log 2 ≤ Real.log (2 * N + 1 : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h := pairedEtaTranslatedResidualEnergy_le_cutoff a c hT
  rw [pairedEtaTranslatedResidualEnergyCutoff_eq_finiteForm ha c hT le_rfl,
    Real.exp_neg, Real.exp_log (by positivity : 0 < (2 * N + 1 : ℝ))] at h
  unfold pairedEtaTranslatedFiniteResidualBudget
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The full finite arithmetic budget is nonnegative without assuming any matrix inequality. -/
theorem pairedEtaTranslatedFiniteResidualBudget_nonneg {d N : ℕ} (hN : 1 ≤ N)
    {a : Fin d → ℝ} (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) :
    0 ≤ pairedEtaTranslatedFiniteResidualBudget N a c :=
  (pairedEtaTranslatedResidualEnergy_nonneg a c).trans (pairedEtaTranslatedResidualEnergy_le_finiteBudget hN ha c)

/-- A fully finite arithmetic inequality controls every actual right-half zero, with all tails and complex mixed terms included. -/
theorem two_mul_re_sub_one_mul_head_norm_sq_le_finiteBudget {d N : ℕ} (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (hN : 1 ≤ N) {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) :
    (2 * rho.1.re - 1) * ‖pairedEtaProjectionHeadTransform rho.1‖ ^ 2 ≤
      pairedEtaTranslatedFiniteResidualBudget N a c :=
  (two_mul_re_sub_one_mul_head_norm_sq_le_residual rho hrho ha c).trans
    (pairedEtaTranslatedResidualEnergy_le_finiteBudget hN ha c)

end

end RiemannGaussian
