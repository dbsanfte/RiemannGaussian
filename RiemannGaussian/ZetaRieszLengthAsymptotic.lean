/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHeadAdaptive

/-!
# The actual physical length at the source scale

The exact integer floor and damping cost give the logarithmic length and head-prefactor limits independently of hypothetical zeros.
-/

namespace RiemannGaussian.ZetaRieszLengthAsymptotic
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- The exact floor retains its logarithmic damping cost in the lower
physical-length bound; the added two is not dropped from the definition. -/
theorem length_lower {u : ℝ} (hu : 0 < u) (N : ℕ) :
    -2 * Real.log u * N - 2 * Real.log (N + 1) ≤
      SquarefreeVaughanLogSource.length u N := by
  have hfloor : u⁻¹ ^ N / (N + 1) <
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hb : u⁻¹ ^ N / (N + 1) ≤
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) := by linarith
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < u⁻¹ ^ N / (N + 1)) hb
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_inv] at hh
  unfold SquarefreeVaughanLogSource.length
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- The floor-defined logarithmic length has its exact source-scale
limit. The proof keeps the logarithmic damping error to the last step. -/
theorem tendsto_length_div_succ {u : ℝ} (hu : 0 < u) (huq : u ≤ 3 / 5) :
    Tendsto (fun N : ℕ => SquarefreeVaughanLogSource.length u N / (N + 1))
      atTop (nhds (-2 * Real.log u)) := by
  have hu1 : u < 1 := by linarith
  have hlu : Real.log u < 0 := Real.log_neg hu hu1
  have hn : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun N : ℕ => Real.log (N + 1) / (N + 1)) atTop (nhds 0) := by
    simpa only [Function.comp_def, pow_zero, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hn
  have herr := (hlog.const_mul 2).sub (hn.const_div_atTop (2 * Real.log u))
  simp only [mul_zero, sub_zero] at herr
  have he : Tendsto (fun N : ℕ => SquarefreeVaughanLogSource.length u N / (N + 1) +
      2 * Real.log u) atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun N : ℕ =>
      2 * (Real.log (N + 1) / (N + 1)) - (2 * Real.log u) / (N + 1)) (by
      filter_upwards [eventually_ge_atTop 3] with N hN
      have hM : (0 : ℝ) < N + 1 := by positivity
      have hlo := length_lower hu N
      have hhi := ZetaRieszHeadAdaptive.length_le_source_log hu huq hN
      have hlM : 0 ≤ Real.log (N + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
      have hb : |SquarefreeVaughanLogSource.length u N + 2 * Real.log u * (N + 1)| ≤
          2 * Real.log (N + 1) - 2 * Real.log u := by
        apply abs_le.mpr
        constructor <;> nlinarith
      rw [Real.norm_eq_abs]
      calc
        _ = |SquarefreeVaughanLogSource.length u N + 2 * Real.log u * (N + 1)| / (N + 1) := by
          rw [show SquarefreeVaughanLogSource.length u N / (N + 1) + 2 * Real.log u =
            (SquarefreeVaughanLogSource.length u N + 2 * Real.log u * (N + 1)) / (N + 1) by
              field_simp, abs_div, abs_of_pos hM]
        _ ≤ (2 * Real.log (N + 1) - 2 * Real.log u) / (N + 1) :=
          div_le_div_of_nonneg_right hb hM.le
        _ = _ := by ring)
    exact herr
  have h := he.sub_const (2 * Real.log u)
  simpa only [add_sub_cancel_right, zero_sub, neg_mul] using h

/-- The original head's length prefactor has an exact limiting value,
with no numerical approximation of the source radius. -/
theorem tendsto_head_length_factor {u : ℝ} (hu : 0 < u) (huq : u ≤ 3 / 5) :
    Tendsto (fun N : ℕ => (N + 1 : ℝ) / (u * SquarefreeVaughanLogSource.length u N))
      atTop (nhds (1 / (-2 * u * Real.log u))) := by
  have hlu : Real.log u < 0 := Real.log_neg hu (by linarith)
  have hp : 0 < u * (-2 * Real.log u) := mul_pos hu (by nlinarith)
  have h := ((tendsto_length_div_succ hu huq).const_mul u).inv₀
    hp.ne'
  convert! h using 1
  · funext N
    simp only [mul_inv_rev, inv_div]
    ring
  · congr 1
    ring

end
end RiemannGaussian.ZetaRieszLengthAsymptotic
