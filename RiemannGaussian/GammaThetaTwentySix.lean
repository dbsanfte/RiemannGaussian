/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertifiedArctan
import RiemannGaussian.GammaPhaseApproximation

/-!
# A kernel-checked unwrapped theta bound at height twenty-six

Nine rational arctangent brackets and two logarithms enclose the finite
shift-eight Gamma approximation. The proved analytic error then bounds
the actual unwrapped phase. All proposed brackets are checked in Lean.
-/

namespace RiemannGaussian.GammaThetaTwentySix
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval GammaPhaseApproximation

private def cfg : DyadicConfig := {precision := -32, taylorDepth := 12}

private def argument (i : ℕ) : ℚ :=
  if i = 0 then 52 / 31 else 52 / (4 * (i - 1 : ℕ) + 1)

private def lower (i : ℕ) : ℚ :=
  ([10332, 15515, 14749, 13994, 13258, 12548, 11869, 11226, 10620] : List ℚ)[i]?.getD 0 / 10000

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
    (.mul (.const (13 / 2)) (.log (.const (3665 / 16))))) (.const (-13)))
    (.add (.neg (angleSum 8)) (.neg (.mul (.const 13) (.log (.var 9)))))

private theorem expression_eq : Expr.eval realEnv expression = thetaApproximation 8 26 := by
  rw [thetaApproximation, shiftedApproximation, primitive_eq_real (by norm_num)]
  norm_num [expression, angleSum, Expr.eval, realEnv, argument, Finset.sum_range_succ]
  ring

private def checked : Bool :=
  match evalIntervalDyadicChecked expression intervalEnv cfg with
  | .error _ => false
  | .ok B => decide ((101 / 20 : ℚ) ≤ B.lo.toRat ∧ B.hi.toRat ≤ 51 / 10)

private theorem checked_value : checked = true := by decide +kernel

/-- The entire shift-eight finite theta expression has a checked rational
enclosure, including every phase-shift term and the logarithm of pi. -/
theorem approximation_bounds : (101 / 20 : ℝ) ≤ thetaApproximation 8 26 ∧
    thetaApproximation 8 26 ≤ (51 / 10 : ℝ) := by
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

/-- The actual unwrapped theta phase at height twenty-six lies strictly
between forty-nine tenths and fifty-three tenths. Its analytic error is paid explicitly. -/
theorem theta_bounds : (49 / 10 : ℝ) < theta 26 ∧ theta 26 < 53 / 10 := by
  have hh := abs_phase_sub_shiftedApproximation_le (by norm_num : (0 : ℝ) < 1 / 4)
    8 (by norm_num) 13
  have he : theta 26 - thetaApproximation 8 26 =
      phase (1 / 4) 13 - shiftedApproximation (1 / 4) 8 13 := by
    norm_num [theta, thetaApproximation]
  rw [← he] at hh
  norm_num at hh
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  constructor <;> linarith [approximation_bounds.1, approximation_bounds.2]

end RiemannGaussian.GammaThetaTwentySix
