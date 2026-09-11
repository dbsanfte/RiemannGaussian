/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianHalfLaplaceBounds

/-!
# Retaining the shifted Gaussian endpoint

Completing the square expresses the negative-damping half transform as a
Gaussian half mass plus an exact finite interval. Bounding only that interval
gives a sharper pole estimate for the actual Fermi zero budget. The identity
is retained separately so that subsequent estimates can use its curvature.
-/

namespace RiemannGaussian.GaussianHalfLaplaceShift

noncomputable section
open MeasureTheory Set
open GaussianFermiZeroPair GaussianFermiLaplaceOrder GaussianHalfLaplaceBounds

/-- Completing the square retains the entire finite interval cut out by
the displacement of the Gaussian center. The damping may have either sign. -/
theorem halfGaussian_neg_shift {b : ℝ} (hb : 0 < b) (x : ℝ) :
    halfGaussian b (-x) = Real.exp (x ^ 2 / (4 * b)) *
      (Real.sqrt (Real.pi / b) / 2 + ∫ u in -(x / (2 * b))..0, window b u) := by
  let c := x / (2 * b)
  have hi : Integrable (window b) := by
    simpa using integrable_window_exp hb 0
  have htranslate : (∫ u in Ioi (0 : ℝ), window b (u - c)) =
      ∫ u in Ioi (-c), window b u := by
    have he : MeasurableEmbedding (fun u : ℝ => u - c) := by
      change MeasurableEmbedding (fun u : ℝ => u + -c)
      exact (Homeomorph.addRight (-c)).isClosedEmbedding.measurableEmbedding
    have h := he.setIntegral_map (μ := volume) (window b) (Ioi (-c))
    simpa [map_sub_right_eq_self] using h.symm
  have hpoint (u : ℝ) : window b u * Real.exp (-(-x) * u) =
      Real.exp (x ^ 2 / (4 * b)) * window b (u - c) := by
    unfold window
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [c]
    field_simp
    ring
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi'
    (hi.integrableOn (s := Ioi (-c))) (hi.integrableOn (s := Ioi 0))
  have hzero : (∫ u in Ioi (0 : ℝ), window b u) = Real.sqrt (Real.pi / b) / 2 := by
    simpa [halfGaussian] using halfGaussian_zero b
  rw [hzero] at hsplit
  calc
    _ = Real.exp (x ^ 2 / (4 * b)) * ∫ u in Ioi (0 : ℝ), window b (u - c) := by
      simp only [halfGaussian, hpoint, integral_const_mul]
    _ = Real.exp (x ^ 2 / (4 * b)) * ∫ u in Ioi (-c), window b u := by rw [htranslate]
    _ = _ := by congr 1; linarith

/-- For nonnegative displacement, the exact retained interval is at most
its length. This improves the negative-damping pole envelope. -/
theorem halfGaussian_neg_shift_upper {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    halfGaussian b (-x) ≤ Real.exp (x ^ 2 / (4 * b)) *
      (Real.sqrt (Real.pi / b) / 2 + x / (2 * b)) := by
  have hc : 0 ≤ x / (2 * b) := by positivity
  have hint : (∫ u in -(x / (2 * b))..0, window b u) ≤ x / (2 * b) := by
    have h := intervalIntegral.integral_mono_on (μ := volume)
      (by linarith : -(x / (2 * b)) ≤ 0)
      ((continuous_window b).intervalIntegrable _ _) intervalIntegrable_const
      (fun u _ => show window b u ≤ (1 : ℝ) by
        unfold window
        exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u]))
    simpa using h
  rw [halfGaussian_neg_shift hb x]
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le

end
end RiemannGaussian.GaussianHalfLaplaceShift
