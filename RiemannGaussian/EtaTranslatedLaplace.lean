import RiemannGaussian.EtaLogSupportShift
import Mathlib.MeasureTheory.Group.Integral

/-!
# Exact Laplace transforms of actual eta translates

The literal infinite support indicator is translated before any norm is
taken. Every nonnegative translate and every finite complex combination
annihilates an actual zeta zero. Integrability and the translation factor
are proved for the complete support, without a finite-tail assumption.
-/

open Complex Filter MeasureTheory Set
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A real translation of the unchanged infinite eta colour. -/
def pairedEtaTranslatedColour (a t : ℝ) : ℝ := pairedEtaLogIndicator (t - a)

/-- The full complex Laplace kernel of one actual eta translate. -/
def pairedEtaTranslatedLaplaceKernel (s : ℂ) (a t : ℝ) : ℂ :=
  (pairedEtaTranslatedColour a t : ℂ) * Complex.exp (-s * t)

/-- The literal eta colour vanishes at every nonpositive logarithmic time. -/
theorem pairedEtaLogIndicator_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    pairedEtaLogIndicator t = 0 := by
  apply Set.indicator_of_notMem
  exact fun h ↦ (not_lt_of_ge ht) (pairedEtaLogSupport_subset_Ioi_zero h)

/-- The translate remains measurable. -/
theorem measurable_pairedEtaTranslatedColour (a : ℝ) :
    Measurable (pairedEtaTranslatedColour a) :=
  measurable_pairedEtaLogIndicator.comp (measurable_id.sub_const a)

/-- Translating by a nonnegative time preserves positive-half-line support. -/
theorem pairedEtaTranslatedColour_eq_zero_of_nonpos {a t : ℝ} (ha : 0 ≤ a) (ht : t ≤ 0) :
    pairedEtaTranslatedColour a t = 0 :=
  pairedEtaLogIndicator_eq_zero_of_nonpos (by linarith)

/-- Each translated colour still has only the original two values. -/
theorem pairedEtaTranslatedColour_eq_zero_or_one (a t : ℝ) :
    pairedEtaTranslatedColour a t = 0 ∨ pairedEtaTranslatedColour a t = 1 :=
  pairedEtaLogIndicator_eq_zero_or_one (t - a)

/-- The unshifted complex colour kernel is exactly a restricted-support indicator. -/
theorem pairedEtaTranslatedLaplaceKernel_zero (s : ℂ) :
    pairedEtaTranslatedLaplaceKernel s 0 =
      pairedEtaLogSupport.indicator (fun t : ℝ ↦ Complex.exp (-s * t)) := by
  funext t
  by_cases ht : t ∈ pairedEtaLogSupport <;>
    simp [pairedEtaTranslatedLaplaceKernel, pairedEtaTranslatedColour, pairedEtaLogIndicator, ht]

/-- The translation retains its exact complex exponential multiplier. -/
theorem pairedEtaTranslatedLaplaceKernel_eq_translate (s : ℂ) (a t : ℝ) :
    pairedEtaTranslatedLaplaceKernel s a t =
      Complex.exp (-s * a) * pairedEtaTranslatedLaplaceKernel s 0 (t - a) := by
  unfold pairedEtaTranslatedLaplaceKernel pairedEtaTranslatedColour
  simp only [sub_zero]
  have he : Complex.exp (-s * t) = Complex.exp (-s * a) * Complex.exp (-s * (t - a)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he]
  push_cast
  ring

/-- The complete translated kernel is integrable on the full real line when the real exponent is positive. -/
theorem integrable_pairedEtaTranslatedLaplaceKernel {s : ℂ} (hs : 0 < s.re) (a : ℝ) :
    Integrable (pairedEtaTranslatedLaplaceKernel s a) := by
  have hi : Integrable (pairedEtaTranslatedLaplaceKernel s 0) := by
    rw [pairedEtaTranslatedLaplaceKernel_zero]
    apply (integrable_indicator_iff measurableSet_pairedEtaLogSupport).mpr
    exact integrable_exp_neg_mul_pairedEtaLogMeasure hs
  have hshift := (hi.comp_add_right (-a)).const_mul (Complex.exp (-s * a))
  simpa only [← sub_eq_add_neg, ← pairedEtaTranslatedLaplaceKernel_eq_translate] using hshift

/-- Integration over the full translated support gives the original eta transform with its exact phase factor. -/
theorem integral_pairedEtaTranslatedLaplaceKernel {s : ℂ} (hs : 0 < s.re) (a : ℝ) :
    (∫ t : ℝ, pairedEtaTranslatedLaplaceKernel s a t) =
      Complex.exp (-s * a) * pairedEtaLaplacePartition s := by
  have he : pairedEtaTranslatedLaplaceKernel s a =
      fun t ↦ Complex.exp (-s * a) * pairedEtaTranslatedLaplaceKernel s 0 (t - a) :=
    funext (pairedEtaTranslatedLaplaceKernel_eq_translate s a)
  rw [he, integral_const_mul, integral_sub_right_eq_self, pairedEtaTranslatedLaplaceKernel_zero,
    integral_indicator measurableSet_pairedEtaLogSupport]
  change _ * (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogMeasure) = _
  rw [integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition hs]

/-- For nonnegative translates, the positive-half-line integral is the same complete eta transform. -/
theorem integral_Ioi_pairedEtaTranslatedLaplaceKernel {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 ≤ a) :
    (∫ t : ℝ in Ioi 0, pairedEtaTranslatedLaplaceKernel s a t) =
      Complex.exp (-s * a) * pairedEtaLaplacePartition s := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact integral_pairedEtaTranslatedLaplaceKernel hs a
  · intro t ht
    have hz := pairedEtaTranslatedColour_eq_zero_of_nonpos ha (le_of_not_gt ht)
    simp only [pairedEtaTranslatedLaplaceKernel, hz, Complex.ofReal_zero, zero_mul]

/-- A finite complex combination keeps each individual translated colour and coefficient. -/
def pairedEtaTranslatedCombination {d : ℕ} (a : Fin d → ℝ) (c : Fin d → ℂ) (t : ℝ) : ℂ :=
  ∑ j, c j * (pairedEtaTranslatedColour (a j) t : ℂ)

/-- Every finite complex combination has an integrable full Laplace kernel in the positive half-plane. -/
theorem integrable_pairedEtaTranslatedCombination {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    (a : Fin d → ℝ) (c : Fin d → ℂ) :
    Integrable (fun t : ℝ ↦ pairedEtaTranslatedCombination a c t * Complex.exp (-s * t)) := by
  simp only [pairedEtaTranslatedCombination, Finset.sum_mul, mul_assoc]
  exact integrable_finsetSum _ (fun j _ ↦ (integrable_pairedEtaTranslatedLaplaceKernel hs (a j)).const_mul (c j))

/-- The combination has its complete common eta factor before any zero equation or norm is used. -/
theorem integral_pairedEtaTranslatedCombination {d : ℕ} {s : ℂ} (hs : 0 < s.re)
    (a : Fin d → ℝ) (c : Fin d → ℂ) :
    (∫ t : ℝ, pairedEtaTranslatedCombination a c t * Complex.exp (-s * t)) =
      (∑ j, c j * Complex.exp (-s * a j)) * pairedEtaLaplacePartition s := by
  simp only [pairedEtaTranslatedCombination, Finset.sum_mul, mul_assoc]
  change (∫ t : ℝ, ∑ j, c j * pairedEtaTranslatedLaplaceKernel s (a j) t) = _
  rw [integral_finsetSum _ (fun j _ ↦ (integrable_pairedEtaTranslatedLaplaceKernel hs (a j)).const_mul (c j))]
  simp_rw [integral_const_mul, integral_pairedEtaTranslatedLaplaceKernel hs]

/-- Every actual nontrivial zero annihilates the entire finite complex translate combination. -/
theorem integral_pairedEtaTranslatedCombination_eq_zero {d : ℕ} (rho : NontrivialZetaZero)
    (a : Fin d → ℝ) (c : Fin d → ℂ) :
    (∫ t : ℝ, pairedEtaTranslatedCombination a c t * Complex.exp (-rho.1 * t)) = 0 := by
  rw [integral_pairedEtaTranslatedCombination (NontrivialZetaZero.zero_lt_re rho),
    pairedEtaLaplacePartition_eq_zero_of_nontrivialZetaZero rho, mul_zero]

end

end RiemannGaussian
