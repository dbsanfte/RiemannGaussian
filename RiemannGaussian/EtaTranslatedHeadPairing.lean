import RiemannGaussian.EtaTranslatedFiniteGram

/-!
# The exact compact-target pairing with every eta translate

Only the first translated interval can meet the compact target. Its full
complex pairing therefore has an explicit interval length, with no
infinite remainder. Complex coefficients and conjugation are retained
before the real part enters the residual energy.
-/

open Complex Filter MeasureTheory Set
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The exact first-interval overlap length of a nonnegative eta translate. -/
def pairedEtaTranslatedHeadPairing (a : ℝ) : ℝ := max 0 (Real.log 2 - a)

/-- The critical weight cancels the target's exponential exactly on its original support. -/
theorem exp_neg_mul_pairedEtaProjectionHead (t : ℝ) :
    (Real.exp (-t) : ℂ) * pairedEtaProjectionHead t =
      (Ioc 0 (Real.log 2)).indicator (fun _ ↦ (1 : ℂ)) t := by
  by_cases ht : t ∈ Ioc 0 (Real.log 2)
  · simp only [pairedEtaProjectionHead, indicator_of_mem ht, ← Complex.ofReal_mul,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  · simp [pairedEtaProjectionHead, ht]

/-- The compact target times one full eta translate is exactly its first interval intersection. -/
theorem exp_neg_mul_pairedEtaProjectionHead_mul_colour {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    (Real.exp (-t) : ℂ) * pairedEtaProjectionHead t * (pairedEtaTranslatedColour a t : ℂ) =
      (Ioc a (Real.log 2)).indicator (fun _ ↦ (1 : ℂ)) t := by
  rw [exp_neg_mul_pairedEtaProjectionHead]
  by_cases ht : t ∈ Ioc a (Real.log 2)
  · have ht0 : t ∈ Ioc 0 (Real.log 2) := ⟨ha.trans_lt ht.1, ht.2⟩
    have hmem : t - a ∈ pairedEtaLogSupport := Ioc_zero_log_two_subset_pairedEtaLogSupport
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp [ht, ht0, pairedEtaTranslatedColour, pairedEtaLogIndicator, hmem]
  · by_cases ht0 : t ∈ Ioc 0 (Real.log 2)
    · have hta : t ≤ a := by
        by_contra h
        exact ht ⟨lt_of_not_ge h, ht0.2⟩
      have hz : pairedEtaTranslatedColour a t = 0 := pairedEtaLogIndicator_eq_zero_of_nonpos (by linarith)
      simp [ht, ht0, hz]
    · simp [ht, ht0]

/-- The complete complex head-colour pairing is integrable over every finite interval. -/
theorem integrableOn_pairedEtaProjectionHead_mul_colour {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    IntegrableOn (fun t : ℝ ↦ (Real.exp (-t) : ℂ) * pairedEtaProjectionHead t *
      (pairedEtaTranslatedColour a t : ℂ)) (Ioc 0 T) := by
  simp_rw [exp_neg_mul_pairedEtaProjectionHead_mul_colour ha]
  exact (integrableOn_const (by simp : volume (Ioc 0 T) ≠ ⊤)).indicator measurableSet_Ioc

/-- Once the target is included, its complex pairing has the exact overlap length at every cutoff. -/
theorem integral_pairedEtaProjectionHead_mul_colour {a T : ℝ} (ha : 0 ≤ a) (hT : Real.log 2 ≤ T) :
    (∫ t : ℝ in Ioc 0 T, (Real.exp (-t) : ℂ) * pairedEtaProjectionHead t *
      (pairedEtaTranslatedColour a t : ℂ)) = (pairedEtaTranslatedHeadPairing a : ℂ) := by
  simp_rw [exp_neg_mul_pairedEtaProjectionHead_mul_colour ha]
  rw [setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (show Ioc a (Real.log 2) ⊆ Ioc 0 T from fun _ ht ↦ ⟨ha.trans_lt ht.1, ht.2.trans hT⟩),
    setIntegral_const, Real.volume_real_Ioc]
  simp [pairedEtaTranslatedHeadPairing, max_comm]

/-- The compact target's full complex cross term retains the conjugate of every original coefficient. -/
theorem exp_neg_mul_pairedEtaProjectionHead_mul_conj_combination {d : ℕ}
    (a : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) :
    (Real.exp (-t) : ℂ) * pairedEtaProjectionHead t * conj (pairedEtaTranslatedCombination a c t) =
      ∑ j, conj (c j) * ((Real.exp (-t) : ℂ) * pairedEtaProjectionHead t * (pairedEtaTranslatedColour (a j) t : ℂ)) := by
  rw [pairedEtaTranslatedCombination, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- The finite sum of complete head-colour kernels is genuinely integrable. -/
theorem integrableOn_pairedEtaProjectionHead_mul_conj_combination {d : ℕ}
    {a : Fin d → ℝ} (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) (T : ℝ) :
    IntegrableOn (fun t : ℝ ↦ (Real.exp (-t) : ℂ) * pairedEtaProjectionHead t *
      conj (pairedEtaTranslatedCombination a c t)) (Ioc 0 T) := by
  simp_rw [exp_neg_mul_pairedEtaProjectionHead_mul_conj_combination]
  exact integrable_finsetSum _ (fun j _ ↦ (integrableOn_pairedEtaProjectionHead_mul_colour (ha j) T).const_mul (conj (c j)))

/-- Integration of the full complex head pairing has no tail or unresolved coefficient hypothesis. -/
theorem integral_pairedEtaProjectionHead_mul_conj_combination {d : ℕ}
    {a : Fin d → ℝ} (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) {T : ℝ} (hT : Real.log 2 ≤ T) :
    (∫ t : ℝ in Ioc 0 T, (Real.exp (-t) : ℂ) * pairedEtaProjectionHead t *
      conj (pairedEtaTranslatedCombination a c t)) =
      ∑ j, conj (c j) * (pairedEtaTranslatedHeadPairing (a j) : ℂ) := by
  simp_rw [exp_neg_mul_pairedEtaProjectionHead_mul_conj_combination]
  rw [integral_finsetSum _ (fun j _ ↦ (integrableOn_pairedEtaProjectionHead_mul_colour (ha j) T).const_mul (conj (c j)))]
  simp_rw [integral_const_mul, integral_pairedEtaProjectionHead_mul_colour (ha _) hT]

/-- Taking the real part only after the complex pairing gives the linear term of the exact residual energy. -/
theorem integral_re_pairedEtaProjectionHead_mul_conj_combination {d : ℕ}
    {a : Fin d → ℝ} (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) {T : ℝ} (hT : Real.log 2 ≤ T) :
    (∫ t : ℝ in Ioc 0 T, Real.exp (-t) *
      (pairedEtaProjectionHead t * conj (pairedEtaTranslatedCombination a c t)).re) =
      ∑ j, (c j).re * pairedEtaTranslatedHeadPairing (a j) := by
  have h := congrArg Complex.re (integral_pairedEtaProjectionHead_mul_conj_combination ha c hT)
  have hre : (∫ t : ℝ in Ioc 0 T, (Real.exp (-t) : ℂ) * pairedEtaProjectionHead t *
      conj (pairedEtaTranslatedCombination a c t)).re =
      ∫ t : ℝ in Ioc 0 T, ((Real.exp (-t) : ℂ) * pairedEtaProjectionHead t *
        conj (pairedEtaTranslatedCombination a c t)).re :=
    (integral_re (integrableOn_pairedEtaProjectionHead_mul_conj_combination ha c T)).symm
  rw [hre] at h
  simpa only [Complex.re_sum, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, mul_zero, sub_zero, zero_mul, add_zero, mul_sub, mul_assoc] using h

end

end RiemannGaussian
