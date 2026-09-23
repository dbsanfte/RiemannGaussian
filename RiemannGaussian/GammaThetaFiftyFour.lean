/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertifiedArctan
import RiemannGaussian.GammaPhaseApproximation

/-!
# A kernel-checked unwrapped theta bound at height fifty-four

Nine rational arctangent brackets and two logarithms enclose the finite
shift-eight Gamma approximation. The proved analytic error then bounds
the actual unwrapped phase. All proposed brackets are checked in Lean.
-/

namespace RiemannGaussian.GammaThetaFiftyFour
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval GammaPhaseApproximation

private def cfg : DyadicConfig := {precision := -32, taylorDepth := 12}

private def argument (i : ℕ) : ℚ :=
  if i = 0 then 108 / 31 else 108 / (4 * (i - 1 : ℕ) + 1)

private def lower (i : ℕ) : ℚ :=
  ([12912, 15615, 15245, 14876, 14510, 14146, 13787, 13433, 13084] : List ℚ)[i]?.getD 0 / 10000

private def angleInterval (i : ℕ) : IntervalRat :=
  ⟨lower i, lower i + 1 / 10000, by linarith⟩

private theorem checked_angles : ∀ i : Fin 9,
    CertifiedArctan.check cfg (argument i) (angleInterval i).lo (angleInterval i).hi = true := by
  decide +kernel

private def intervalEnv (i : ℕ) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat (if i < 9 then angleInterval i else piBounds) cfg.precision

private noncomputable def realEnv (i : ℕ) : ℝ :=
  if i < 9 then Real.arctan (argument i) else Real.pi

private theorem env_mem : envMemDyadic realEnv intervalEnv := by
  intro i
  apply IntervalDyadic.mem_ofIntervalRat (prec := cfg.precision) (hprec := by decide)
  by_cases hi : i < 9
  · simp only [realEnv, hi, if_true]
    exact CertifiedArctan.bounds_of_check (checked_angles ⟨i, hi⟩)
  · simp only [realEnv, hi, if_false]
    exact ⟨Real.pi_gt_d20.le, Real.pi_lt_d20.le⟩

private def angleSum : ℕ → Expr
  | 0 => .const 0
  | n + 1 => .add (angleSum n) (.var (n + 1))

private def expression : Expr :=
  .add (.add (.add (.mul (.const (31 / 4)) (.var 0))
    (.mul (.const (27 / 2)) (.log (.const (12625 / 16))))) (.const (-27)))
    (.add (.neg (angleSum 8)) (.neg (.mul (.const 27) (.log (.var 9)))))

private theorem expression_eq : Expr.eval realEnv expression = thetaApproximation 8 54 := by
  rw [thetaApproximation, shiftedApproximation, primitive_eq_real (by norm_num)]
  norm_num [expression, angleSum, Expr.eval, realEnv, argument, Finset.sum_range_succ]
  ring

private def checked : Bool :=
  match evalIntervalDyadicChecked expression intervalEnv cfg with
  | .error _ => false
  | .ok B => decide ((61 / 2 : ℚ) ≤ B.lo.toRat ∧ B.hi.toRat ≤ 123 / 4)

private theorem checked_value : checked = true := by decide +kernel

/-- The entire shift-eight finite theta expression has a checked rational
enclosure, including every phase-shift term and the logarithm of pi. -/
theorem approximation_bounds : (61 / 2 : ℝ) ≤ thetaApproximation 8 54 ∧
    thetaApproximation 8 54 ≤ (123 / 4 : ℝ) := by
  have hc := checked_value
  cases he : evalIntervalDyadicChecked expression intervalEnv cfg with
  | error err => simp only [checked, he, Bool.false_eq_true] at hc
  | ok B =>
    simp only [checked, he, decide_eq_true_eq] at hc
    have hh := evalIntervalDyadicChecked_correct expression realEnv intervalEnv env_mem
      cfg (by decide) B he
    rw [expression_eq] at hh
    have hl := Rat.cast_le (K := ℝ) |>.mpr hc.1
    have hu := Rat.cast_le (K := ℝ) |>.mpr hc.2
    norm_num at hl hu
    exact ⟨hl.trans hh.1, hh.2.trans hu⟩

/-- The actual unwrapped theta phase at height fifty-four lies strictly
between thirty and thirty-one. Its analytic error is paid explicitly. -/
theorem theta_bounds : (30 : ℝ) < theta 54 ∧ theta 54 < 31 := by
  have hh := abs_phase_sub_shiftedApproximation_le (by norm_num : (0 : ℝ) < 1 / 4)
    8 (by norm_num) 27
  have he : theta 54 - thetaApproximation 8 54 =
      phase (1 / 4) 27 - shiftedApproximation (1 / 4) 8 27 := by
    norm_num [theta, thetaApproximation]
  rw [← he] at hh
  norm_num at hh
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  constructor <;> linarith [approximation_bounds.1, approximation_bounds.2]

end RiemannGaussian.GammaThetaFiftyFour
