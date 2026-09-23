/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianDigammaGauss
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A quantitative complex midpoint approximation to digamma

The reciprocal Euler sum is compared with centered logarithmic cells.
The odd first-order error integrates to zero; the retained quadratic error
has a summable explicit envelope. This is an analytic input for bounding
the unwrapped Gamma phase in a complete zeta-zero count.
-/

namespace RiemannGaussian.DigammaMidpointApproximation
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped Interval

/-- The signed difference between a logarithmic cell and its midpoint. -/
def cell (w : ℂ) : ℂ := log (w + 1 / 2) - log (w - 1 / 2) - w⁻¹

private theorem shifted_ne {w : ℂ} (hw : (3 / 2 : ℝ) ≤ w.re)
    {t : ℝ} (ht : t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) : w + t ≠ 0 := by
  apply Complex.ne_zero_of_re_pos
  simp only [add_re, ofReal_re]
  linarith [ht.1]

private theorem reciprocal_integrable {w : ℂ} (hw : (3 / 2 : ℝ) ≤ w.re) :
    IntervalIntegrable (fun t : ℝ => (w + t)⁻¹) volume (-1 / 2 : ℝ) (1 / 2) := by
  apply ContinuousOn.intervalIntegrable
  apply (continuous_const.add continuous_ofReal).continuousOn.inv₀
  intro t ht
  exact shifted_ne hw (by simpa only [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] using ht)

/-- The logarithmic cell is an exact integral of the full quadratic error. -/
theorem cell_eq_integral {w : ℂ} (hw : (3 / 2 : ℝ) ≤ w.re) :
    cell w = ∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2),
      (t : ℂ) ^ 2 / (w ^ 2 * (w + t)) := by
  have hw0 : w ≠ 0 := Complex.ne_zero_of_re_pos (by linarith)
  have hd (t : ℝ) (ht : t ∈ [[(-1 / 2 : ℝ), (1 / 2)]]) :
      HasDerivAt (fun u : ℝ => log (w + u)) (w + t)⁻¹ t := by
    have ht' : t ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
      simpa only [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] using ht
    have hl : w + t ∈ slitPlane := Complex.mem_slitPlane_iff.mpr <| Or.inl (by
      simp only [add_re, ofReal_re]; linarith [ht'.1])
    simpa only [one_div, Complex.ofReal_one, id_eq] using ((hasDerivAt_id t).ofReal_comp.const_add w).clog_real hl
  have hlog := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (reciprocal_integrable hw)
  have hid : IntervalIntegrable (fun t : ℝ => (t : ℂ) / w ^ 2)
      volume (-1 / 2 : ℝ) (1 / 2) := (continuous_ofReal.div_const _).intervalIntegrable _ _
  have heq (t : ℝ) (ht : t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
      (w + t)⁻¹ - w⁻¹ + (t : ℂ) / w ^ 2 =
        (t : ℂ) ^ 2 / (w ^ 2 * (w + t)) := by
    field_simp [hw0, shifted_ne hw ht]
    ring
  have hid0 : (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2), (t : ℂ) / w ^ 2) = 0 := by
    rw [intervalIntegral.integral_div]
    have hh : (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2), (t : ℂ)) = 0 := by
      rw [intervalIntegral.integral_ofReal]
      norm_num [integral_id]
    rw [hh, zero_div]
  calc
    cell w = ∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2), (w + t)⁻¹ - w⁻¹ + (t : ℂ) / w ^ 2 := by
      rw [intervalIntegral.integral_add ((reciprocal_integrable hw).sub intervalIntegrable_const) hid,
        intervalIntegral.integral_sub (reciprocal_integrable hw) intervalIntegrable_const,
        hlog, hid0, intervalIntegral.integral_const]
      norm_num [cell, sub_eq_add_neg]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact heq t (by simpa only [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] using ht)

/-- The quadratic error retains the gain from the cancelled odd term. -/
theorem norm_cell_le {w : ℂ} (hw : (3 / 2 : ℝ) ≤ w.re) :
    ‖cell w‖ ≤ 1 / (4 * (w.re - 1 / 2) ^ 3) := by
  let a : ℝ := w.re - 1 / 2
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  rw [cell_eq_integral hw]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (C := 1 / (4 * a ^ 3)) (f := fun t : ℝ => (t : ℂ) ^ 2 / (w ^ 2 * (w + t))) (by
      intro t ht
      rw [uIoc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at ht
      have ht' : |t| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      have hn : a ≤ ‖w‖ := (by dsimp [a]; linarith [Complex.re_le_norm w])
      have hnt : a ≤ ‖w + t‖ := by
        have hh := Complex.re_le_norm (w + t)
        simp only [add_re, ofReal_re] at hh
        dsimp [a]
        linarith [ht.1]
      rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      calc
        |t| ^ 2 / (‖w‖ ^ 2 * ‖w + t‖) ≤ (1 / 2 : ℝ) ^ 2 / (a ^ 2 * a) := by
          apply div_le_div₀ (by positivity) (by nlinarith [abs_nonneg t]) (by positivity)
          exact mul_le_mul (pow_le_pow_left₀ ha0.le hn 2) hnt ha0.le (by positivity)
        _ = _ := by field_simp; ring)
  simpa only [show (1 / 2 : ℝ) - (-1 / 2) = 1 by norm_num, abs_one, mul_one] using hb

private theorem envelope_le_telescope {a : ℝ} (ha : 1 ≤ a) :
    1 / (4 * a ^ 3) ≤ (1 / 2 : ℝ) * (1 / a ^ 2 - 1 / (a + 1) ^ 2) := by
  have ha0 : 0 < a := by linarith
  field_simp
  nlinarith [sq_nonneg (a - 1)]

/-- Every finite sum of cell errors has the same explicit inverse-square budget. -/
theorem sum_norm_cell_le {z : ℂ} (hz : (3 / 2 : ℝ) ≤ z.re) (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖cell (z + n)‖) ≤
      (1 / 2 : ℝ) * (1 / (z.re - 1 / 2) ^ 2 - 1 / (z.re + N - 1 / 2) ^ 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hn : (3 / 2 : ℝ) ≤ (z + N).re := by simp; linarith [Nat.cast_nonneg (α := ℝ) N]
    have hb := (norm_cell_le hn).trans (envelope_le_telescope (by simp; linarith [Nat.cast_nonneg (α := ℝ) N]))
    simp only [add_re, natCast_re] at hb
    apply (add_le_add ih hb).trans_eq
    push_cast
    rw [show z.re + (N : ℝ) - 1 / 2 + 1 = z.re + (N + 1) - 1 / 2 by ring]
    ring

/-- The finite complex midpoint corrections telescope exactly. -/
theorem sum_cell (z : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, cell (z + n)) =
      log (z + N - 1 / 2) - log (z - 1 / 2) -
        ∑ n ∈ Finset.range N, (z + n)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, cell]
    push_cast
    rw [show z + (N : ℂ) + 1 / 2 = z + (N + 1) - 1 / 2 by ring]
    ring

private theorem log_shift_sub_log_tendsto_zero {c : ℂ} (hc : 0 < c.re) :
    Tendsto (fun N : ℕ => log ((N : ℂ) + c) - log (N : ℂ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun N : ℕ => (N : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  have hh : Tendsto (fun N : ℕ => (1 : ℂ) + c / (N : ℂ)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      tendsto_const_nhds.add (hi.const_mul c)
  have hl := (Complex.differentiableAt_log Complex.one_mem_slitPlane).continuousAt.tendsto.comp hh
  rw [Complex.log_one] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc0 : (1 : ℂ) + c / (N : ℂ) ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    rw [← Complex.ofReal_natCast, Complex.add_re, Complex.one_re, Complex.div_ofReal_re]
    positivity
  have he : ((1 : ℂ) + c / (N : ℂ)) * N = (N : ℂ) + c := by field_simp
  have heq := Complex.log_mul_ofReal (N : ℝ) hn ((1 : ℂ) + c / (N : ℂ)) hc0
  simp only [Complex.ofReal_natCast, he] at heq
  have hr : log (N : ℂ) = (Real.log (N : ℝ) : ℂ) := by
    exact (Complex.ofReal_log hn.le).symm
  simp only [Function.comp_apply]
  rw [heq, hr]
  ring

/-- Actual digamma differs from the centered logarithm by an explicit
inverse-square budget, uniformly in the imaginary part. -/
theorem norm_digamma_sub_log_midpoint_le {z : ℂ} (hz : (3 / 2 : ℝ) ≤ z.re) :
    ‖Complex.digamma z - log (z - 1 / 2)‖ ≤ 1 / (2 * (z.re - 1 / 2) ^ 2) := by
  have he := Complex.digamma_tendsto_euler (s := z) (by linarith)
  have hl := log_shift_sub_log_tendsto_zero (c := z + 1 / 2) (by simp; linarith)
  have ht := ((hl.add he).sub_const (log (z - 1 / 2))).norm
  simp only [zero_add] at ht
  apply le_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro N
  have hs := sum_cell z (N + 1)
  have hb := (norm_sum_le (Finset.range (N + 1)) (fun n => cell (z + n))).trans
    (sum_norm_cell_le hz (N + 1))
  have ht0 : 0 ≤ 1 / (z.re + (N + 1 : ℕ) - 1 / 2) ^ 2 := by positivity
  have hrewrite :
      (log ((N : ℂ) + (z + 1 / 2)) - log (N : ℂ) +
        (log (N : ℂ) - ∑ n ∈ Finset.range (N + 1), (z + n)⁻¹)) - log (z - 1 / 2) =
      ∑ n ∈ Finset.range (N + 1), cell (z + n) := by
    rw [hs]
    push_cast
    rw [show (N : ℂ) + (z + 1 / 2) = z + (N + 1) - 1 / 2 by ring]
    ring
  rw [hrewrite]
  calc
    _ ≤ (1 / 2 : ℝ) * (1 / (z.re - 1 / 2) ^ 2 -
        1 / (z.re + (N + 1 : ℕ) - 1 / 2) ^ 2) := hb
    _ ≤ (1 / 2 : ℝ) * (1 / (z.re - 1 / 2) ^ 2) := by linarith
    _ = _ := by rw [one_div_mul_one_div]

end
end RiemannGaussian.DigammaMidpointApproximation
