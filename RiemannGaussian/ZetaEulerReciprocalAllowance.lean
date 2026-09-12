/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourSafeZeta
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The explicit Euler-side logarithmic allowance near the one-line

The complete Mobius series is exactly reciprocal zeta on its genuine
absolute-convergence half-plane. An integral comparison pays for its
full coefficient mass uniformly as the real coordinate tends to one.
This supplies the center-value cost in shrinking-disc zero estimates.
-/

namespace RiemannGaussian.ZetaEulerReciprocalAllowance
noncomputable section
open MeasureTheory Set
open scoped LSeries.notation

/-- The full positive Dirichlet mass has the elementary pole allowance,
with the exceptional zero term and complete tail both accounted for. -/
theorem pseries_mass_bound {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤ 1 + 1 / (σ - 1) := by
  have hq : -σ < -1 := by linarith
  have ha : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Ici 1) := by
    intro x hx y _ hxy
    change 1 ≤ x at hx
    exact Real.rpow_le_rpow_of_nonpos (by linarith : 0 < x) hxy (by linarith)
  have hi := integrableOn_Ioi_rpow_of_lt hq (by norm_num : (0 : ℝ) < 1)
  have ht := AntitoneOn.tsum_comp_add_le_integral (f := fun x : ℝ => x ^ (-σ)) 1
    (by simpa only [Nat.cast_one] using ha) (by simpa only [Nat.cast_one] using hi)
    (by intro y hy; simp only [Nat.cast_one, mem_Ioi] at hy
        exact Real.rpow_nonneg (by linarith) _)
  simp only [Nat.cast_one] at ht
  rw [integral_Ioi_rpow_of_lt hq (by norm_num : (0 : ℝ) < 1)] at ht
  simp only [Real.one_rpow, Nat.add_assoc, Nat.reduceAdd] at ht
  have hs := Real.summable_nat_rpow.mpr hq
  rw [← hs.sum_add_tsum_nat_add 2]
  have hzero : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow (by linarith)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero,
    Nat.cast_one, hzero, Real.one_rpow, zero_add]
  have he : -(1 : ℝ) / (-σ + 1) = 1 / (σ - 1) := by
    rw [show -σ + 1 = -(σ - 1) by ring, neg_div_neg_eq]
  linarith

/-- The full complex Mobius coefficient is bounded only downstream of
its exact L-series term, on the absolute-convergence half-plane. -/
theorem moebius_term_bound (s : ℂ) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ ≤
      (n : ℝ) ^ (-s.re) := by
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, norm_zero, Nat.cast_zero]
    exact Real.rpow_nonneg (by norm_num) _
  · rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    rw [Real.rpow_neg (Nat.cast_nonneg n), ← one_div]
    exact div_le_div_of_nonneg_right hmu (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Exact recovery of the reciprocal zeta value from the genuine
complex Mobius L-series; all coefficients and phases remain upstream. -/
theorem inverse_eq_moebius {s : ℂ} (hs : 1 < s.re) :
    (riemannZeta s)⁻¹ = L (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s := by
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  apply mul_left_cancel₀ hz
  rw [mul_inv_cancel₀ hz, ← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs]

/-- The reciprocal of actual zeta has an explicit norm bound uniform
over the complete right half-plane of absolute convergence. -/
theorem inverse_zeta_bound {s : ℂ} (hs : 1 < s.re) :
    ‖(riemannZeta s)⁻¹‖ ≤ 1 + 1 / (s.re - 1) := by
  rw [inverse_eq_moebius hs]
  have hsum := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term
        (fun m : ℕ => ((ArithmeticFunction.moebius m : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s.re) :=
      hsum.norm.tsum_le_tsum (moebius_term_bound s)
        (Real.summable_nat_rpow.mpr (by linarith))
    _ ≤ _ := pseries_mass_bound hs

/-- The negative center logarithm has a fully explicit Euler allowance;
no reciprocal lower bound is left as a theorem hypothesis. -/
theorem neg_log_norm_zeta_le {s : ℂ} (hs : 1 < s.re) :
    -Real.log ‖riemannZeta s‖ ≤ Real.log (1 + 1 / (s.re - 1)) := by
  have hn : 0 < ‖(riemannZeta s)⁻¹‖ :=
    norm_pos_iff.mpr (inv_ne_zero (riemannZeta_ne_zero_of_one_lt_re hs))
  have h := Real.log_le_log hn (inverse_zeta_bound hs)
  rwa [norm_inv, Real.log_inv] at h

end
end RiemannGaussian.ZetaEulerReciprocalAllowance
