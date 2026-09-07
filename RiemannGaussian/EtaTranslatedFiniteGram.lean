import RiemannGaussian.EtaTranslatedFiniteIntervals

/-!
# Explicit complete finite Gram arithmetic of eta translates

Every matrix entry is evaluated from the literal translated intervals,
including the original cutoff and all overlaps. The finite prefix agrees
with the actual infinite colour throughout that cutoff. No cross entry is
dropped, and no positivity premise replaces its arithmetic value.
-/

open Complex Filter MeasureTheory Set
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The full product of two interval colours retains their literal intersection. -/
theorem pairedEtaTranslatedInterval_product (a b t : ℝ) (n m : ℕ) :
    Real.exp (-t) * (pairedEtaTranslatedInterval a n).indicator (fun _ ↦ (1 : ℝ)) t *
      (pairedEtaTranslatedInterval b m).indicator (fun _ ↦ (1 : ℝ)) t =
      (pairedEtaTranslatedInterval a n ∩ pairedEtaTranslatedInterval b m).indicator
        (fun u : ℝ ↦ Real.exp (-u)) t := by
  by_cases hn : t ∈ pairedEtaTranslatedInterval a n <;>
    by_cases hm : t ∈ pairedEtaTranslatedInterval b m <;> simp [hn, hm]

/-- Each pair of original translated intervals has the exact cutoff overlap mass. -/
theorem integral_pairedEtaTranslatedInterval_product (T a b : ℝ) (n m : ℕ) :
    (∫ t : ℝ in Ioc 0 T, Real.exp (-t) *
      (pairedEtaTranslatedInterval a n).indicator (fun _ ↦ (1 : ℝ)) t *
      (pairedEtaTranslatedInterval b m).indicator (fun _ ↦ (1 : ℝ)) t) =
      pairedEtaTranslatedOverlapMass T a b n m := by
  simp_rw [pairedEtaTranslatedInterval_product]
  unfold pairedEtaTranslatedInterval
  rw [setIntegral_indicator (measurableSet_Ioc.inter measurableSet_Ioc)]
  rw [Ioc_inter_Ioc, Ioc_inter_Ioc, integral_Ioc_exp_neg_eq_intervalMass]
  rfl

/-- The full real product on a finite interval is integrable, even when its support intersection is empty. -/
theorem integrableOn_pairedEtaTranslatedInterval_product (T a b : ℝ) (n m : ℕ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) *
      (pairedEtaTranslatedInterval a n).indicator (fun _ ↦ (1 : ℝ)) t *
      (pairedEtaTranslatedInterval b m).indicator (fun _ ↦ (1 : ℝ)) t) (Ioc 0 T) := by
  simp_rw [pairedEtaTranslatedInterval_product]
  exact ((show Continuous (fun t : ℝ ↦ Real.exp (-t)) by fun_prop).integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator
    (measurableSet_Ioc.inter measurableSet_Ioc)

/-- Integration of the finite two-colour product preserves every original interval pair. -/
theorem integral_pairedEtaTranslatedColourPrefix_product (N : ℕ) (T a b : ℝ) :
    (∫ t : ℝ in Ioc 0 T, Real.exp (-t) * pairedEtaTranslatedColourPrefix N a t *
      pairedEtaTranslatedColourPrefix N b t) = pairedEtaTranslatedFiniteGram N T a b := by
  simp only [pairedEtaTranslatedColourPrefix, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun n _ ↦ integrable_finsetSum _ (fun m _ ↦
    integrableOn_pairedEtaTranslatedInterval_product T a b m n))]
  simp_rw [integral_finsetSum _ (fun m _ ↦ integrableOn_pairedEtaTranslatedInterval_product T a b m _),
    integral_pairedEtaTranslatedInterval_product]
  rw [Finset.sum_comm]
  rfl

/-- Every actual infinite-colour Gram entry below the original odd cutoff is explicit finite interval arithmetic. -/
theorem integral_pairedEtaTranslatedColour_product_eq_finiteGram {N : ℕ} {T a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : T ≤ Real.log (2 * N + 1 : ℝ)) :
    (∫ t : ℝ in Ioc 0 T, Real.exp (-t) * pairedEtaTranslatedColour a t * pairedEtaTranslatedColour b t) =
      pairedEtaTranslatedFiniteGram N T a b := by
  rw [← integral_pairedEtaTranslatedColourPrefix_product]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [pairedEtaTranslatedColour_eq_prefix ha (ht.2.trans hT),
    pairedEtaTranslatedColour_eq_prefix hb (ht.2.trans hT)]

/-- The actual finite-interval Gram kernel is genuinely integrable before it is evaluated. -/
theorem integrableOn_pairedEtaTranslatedColour_product (T a b : ℝ) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * pairedEtaTranslatedColour a t * pairedEtaTranslatedColour b t) (Ioc 0 T) := by
  have hi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioc 0 T) :=
    (show Continuous (fun t : ℝ ↦ Real.exp (-t)) by fun_prop).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have ha : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * pairedEtaTranslatedColour a t) (Ioc 0 T) := by
    apply hi.mul_bdd (measurable_pairedEtaTranslatedColour a).aestronglyMeasurable
    exact Eventually.of_forall (show ∀ t, ‖pairedEtaTranslatedColour a t‖ ≤ (1 : ℝ) from fun t ↦ by
      rcases pairedEtaTranslatedColour_eq_zero_or_one a t with h | h <;> simp [h])
  apply ha.mul_bdd (measurable_pairedEtaTranslatedColour b).aestronglyMeasurable
  exact Eventually.of_forall (show ∀ t, ‖pairedEtaTranslatedColour b t‖ ≤ (1 : ℝ) from fun t ↦ by
    rcases pairedEtaTranslatedColour_eq_zero_or_one b t with h | h <;> simp [h])

/-- The exact complex norm square is the full double coefficient sum, including all mixed phases. -/
theorem norm_pairedEtaTranslatedCombination_sq {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) :
    ‖pairedEtaTranslatedCombination a c t‖ ^ 2 =
      ∑ j, ∑ k, (c j * conj (c k)).re * pairedEtaTranslatedColour (a j) t * pairedEtaTranslatedColour (a k) t := by
  rw [Complex.sq_norm]
  have hnorm (z : ℂ) : Complex.normSq z = (z * conj z).re := by rw [Complex.mul_conj, Complex.ofReal_re]
  rw [hnorm, pairedEtaTranslatedCombination, map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, map_mul, Complex.conj_ofReal]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.conj_re, Complex.conj_im]
  ring

/-- The entire complex combination's weighted square is exactly its finite arithmetic Gram form. -/
theorem integral_pairedEtaTranslatedCombination_sq_eq_finiteGram {d N : ℕ} {a : Fin d → ℝ}
    (ha : ∀ j, 0 ≤ a j) (c : Fin d → ℂ) {T : ℝ} (hT : T ≤ Real.log (2 * N + 1 : ℝ)) :
    (∫ t : ℝ in Ioc 0 T, Real.exp (-t) * ‖pairedEtaTranslatedCombination a c t‖ ^ 2) =
      ∑ j, ∑ k, (c j * conj (c k)).re * pairedEtaTranslatedFiniteGram N T (a j) (a k) := by
  simp_rw [norm_pairedEtaTranslatedCombination_sq, Finset.mul_sum]
  have he (t : ℝ) (j k : Fin d) :
      Real.exp (-t) * ((c j * conj (c k)).re * pairedEtaTranslatedColour (a j) t * pairedEtaTranslatedColour (a k) t) =
        (c j * conj (c k)).re * (Real.exp (-t) * pairedEtaTranslatedColour (a j) t * pairedEtaTranslatedColour (a k) t) := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦
    (integrableOn_pairedEtaTranslatedColour_product T (a j) (a k)).const_mul ((c j * conj (c k)).re)))]
  simp_rw [integral_finsetSum _ (fun k _ ↦
    (integrableOn_pairedEtaTranslatedColour_product T _ (a k)).const_mul _), integral_const_mul,
    integral_pairedEtaTranslatedColour_product_eq_finiteGram (ha _) (ha _) hT]

end

end RiemannGaussian
