/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CotangentRegularization
import RiemannGaussian.AnalyticHalfDiscMinimum
import RiemannGaussian.ZetaGaussianLaplaceMass

/-!
# The complete smoothed cotangent source on the nearby half-disc

An arbitrary analytic transform with nonnegative boundary cosine data and
a bounded pole remainder on the curved edge has a lower bound throughout
the nearby half-disc. The Gaussian discharges every hypothesis at every
positive scale, giving exactly the cost matched by the retained nearby
Poisson reserve. The full complex source and its center value remain intact.
-/

namespace RiemannGaussian.SmoothedCotangentSource
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open CotangentRegularization

/-- The original transform plus the genuine analytic cotangent correction. -/
def source (F : ℂ → ℂ) (η : ℝ) (z : ℂ) : ℂ := F z + correction η z

/-- Away from the removed pole, the complete complex source has the
original Laplace-plus-cotangent-minus-pole expression. -/
theorem source_eq (F : ℂ → ℂ) {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : z ≠ 0) (hzn : ‖z‖ < 2 * η) :
    source F η z = F z + (frequency η : ℂ) * Complex.cot ((frequency η : ℂ) * z) - 1 / z := by
  rw [source, correction_eq hη hz hzn]
  ring

/-- The source retains the original transform's true center value. -/
theorem source_zero (F : ℂ → ℂ) (η : ℝ) : source F η 0 = F 0 := by
  simp [source, correction_zero]

/-- The entire source is analytic through its canceled pole and on a
neighborhood of every point of the nearby closed half-disc. -/
theorem analyticAt_source {F : ℂ → ℂ} {η : ℝ} (hη : 0 < η) {z : ℂ}
    (hzn : ‖z‖ < 2 * η) (hF : AnalyticAt ℂ F z) : AnalyticAt ℂ (source F η) z :=
  hF.add (analyticAt_correction hη hzn)

/-- A general transform's boundary sign and original pole remainder
control the complete source everywhere in the nearby half-disc. -/
theorem source_re_lower {F : ℂ → ℂ} {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hF : ∀ z : ℂ, ‖z‖ ≤ η → AnalyticAt ℂ F z)
    (hdiameter : ∀ z : ℂ, ‖z‖ ≤ η → z.re = 0 → 0 ≤ (F z).re)
    (hremainder : ∀ z : ℂ, ‖z‖ = η → 0 ≤ z.re → ‖F z - 1 / z‖ ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ η) (hzre : 0 ≤ z.re) : -C ≤ (source F η z).re := by
  apply AnalyticHalfDiscMinimum.re_lower_bound
    (fun w hw => analyticAt_source hη (by linarith) (hF w hw)) ?_ ?_ hz hzre
  · intro w hw hwre
    have hf := hdiameter w hw hwre
    rw [source, Complex.add_re, correction_re_zero hη hwre (by linarith), add_zero]
    linarith
  · intro w hw hwre
    have hw0 : w ≠ 0 := norm_pos_iff.mp (by rw [hw]; exact hη)
    have hreal := (Complex.abs_re_le_norm (F w - 1 / w)).trans (hremainder w hw hwre)
    have hc := scaled_cot_re_nonneg hη hwre ((Complex.re_le_norm w).trans_eq hw)
    rw [source_eq F hη hw0 (by linarith)]
    simp only [Complex.sub_re, Complex.add_re] at hreal ⊢
    linarith [(abs_le.mp hreal).1]

/-- The original pure Gaussian transform is entire, by the exact Fermi
partition with its complete normalization retained. -/
theorem analyticAt_gaussian_transform {B : ℝ} (hB : 0 < B) (z : ℂ) :
    AnalyticAt ℂ (GaussianComplexHalfMoments.transform B) z := by
  have he : GaussianComplexHalfMoments.transform B = fun w : ℂ =>
      FermiLaplaceReflection.transform 0 (GaussianFermiZeroPair.window B) w +
        FermiLaplaceReflection.transform 0 (GaussianFermiZeroPair.window B) w := by
    funext w
    have h := FermiLaplaceReflection.transform_partition 0 (GaussianFermiZeroPair.continuous_window B)
      (GaussianFermiZeroPair.integrable_window_exp hB) w
    simp only [Complex.ofReal_zero, zero_add] at h
    rw [ZetaGaussianLaplaceMass.transform_eq_laplace]
    exact h.symm
  rw [he]
  exact (GaussianFermiZeroPair.analyticAt_gaussian_transform hB 0 z).add
    (GaussianFermiZeroPair.analyticAt_gaussian_transform hB 0 z)

/-- Every actual Gaussian scale discharges the full nearby source bound.
The coefficient is exactly the amount paid by the retained Poisson reserve. -/
theorem gaussian_source_re_lower {B η : ℝ} (hB : 0 < B) (hη : 0 < η)
    {z : ℂ} (hz : ‖z‖ ≤ η) (hzre : 0 ≤ z.re) :
    -(12 * B / η ^ 3) ≤ (source (GaussianComplexHalfMoments.transform B) η z).re := by
  apply source_re_lower hη (by positivity)
    (fun w _ => analyticAt_gaussian_transform hB w) ?_ ?_ hz hzre
  · intro w _ hw
    exact ZetaGaussianLaplaceMass.transform_re_nonneg hB (by rw [hw])
  · intro w hw hwre
    have hw0 : w ≠ 0 := norm_pos_iff.mp (by rw [hw]; exact hη)
    have h := GaussianLaplacePoleRemainder.norm_remainder_le hB hwre hw0
    simpa only [GaussianLaplacePoleRemainder.remainder, hw] using h

/-- At positive real displacement the source keeps its exact original
half-Gaussian value and the complete real cotangent correction. -/
theorem gaussian_source_real {η u : ℝ} (hη : 0 < η) (B : ℝ) (hu : 0 < u) (hu' : u < 2 * η) :
    (source (GaussianComplexHalfMoments.transform B) η (u : ℂ)).re =
      GaussianFermiLaplaceOrder.halfGaussian B u + frequency η * Real.cot (frequency η * u) - 1 / u := by
  rw [source_eq _ hη (Complex.ofReal_ne_zero.mpr hu.ne')
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu] using hu'),
    GaussianComplexHalfMoments.transform_real]
  have hc : ((frequency η : ℂ) * Complex.cot ((frequency η : ℂ) * (u : ℂ))) =
      ((frequency η * Real.cot (frequency η * u) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hc, ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_add,
    ← Complex.ofReal_sub, Complex.ofReal_re]

/-- The selected Gaussian source loses only an explicit term linear in its
real displacement. The exact source remains available before this estimate. -/
theorem gaussian_source_real_lower {η u : ℝ} (hη : 0 < η) (B : ℝ)
    (hu : 0 < u) (hu' : u ≤ η) :
    GaussianFermiLaplaceOrder.halfGaussian B u - Real.pi ^ 2 * u / (8 * η ^ 2) ≤
      (source (GaussianComplexHalfMoments.transform B) η (u : ℂ)).re := by
  rw [gaussian_source_real hη B hu (by linarith)]
  linarith [scaled_cot_real_lower hη hu hu']

end
end RiemannGaussian.SmoothedCotangentSource
