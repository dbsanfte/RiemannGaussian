/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertifiedComplexInterval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Checked rational arctangent brackets

Each proposed bracket is verified by the signs of sin(a)-x*cos(a) at its
two endpoints. Proved pi bounds keep both endpoints in the monotonicity
interval of tangent. The checker uses the existing certified sine and
cosine evaluator, including all rounding and Taylor errors.
-/

namespace RiemannGaussian.CertifiedArctan
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval

/-- Signed tangent comparison, without a numerical division by cosine. -/
def residual (x a : ℚ) : Expr :=
  .add (.sin (.const a)) (.neg (.mul (.const x) (.cos (.const a))))

/-- Check a proposed rational arctangent bracket. Domain and numerical
failures both return false, so neither supplies a mathematical bound. -/
def check (cfg : DyadicConfig) (x a b : ℚ) : Bool :=
  decide (cfg.precision ≤ 0 ∧
    -piBounds.lo / 2 < a ∧ a < piBounds.lo / 2 ∧
    -piBounds.lo / 2 < b ∧ b < piBounds.lo / 2) &&
  match evalIntervalDyadicChecked (residual x a) (fun _ => default) cfg,
      evalIntervalDyadicChecked (residual x b) (fun _ => default) cfg with
  | .ok A, .ok B => decide (A.hi.toRat ≤ 0 ∧ 0 ≤ B.lo.toRat)
  | _, _ => false

private theorem mem_env : envMemDyadic (fun _ => (0 : ℝ)) (fun _ => default) := by
  intro i
  exact CertifiedIntervalProgram.envMem_of_forall₂ (xs := []) (ys := []) .nil i

private theorem angle_range {a : ℚ} (ha : -piBounds.lo / 2 < a)
    (ha' : a < piBounds.lo / 2) : (a : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  have hl := Rat.cast_lt (K := ℝ) |>.mpr ha
  have hu := Rat.cast_lt (K := ℝ) |>.mpr ha'
  norm_num [piBounds] at hl hu
  constructor <;> linarith [Real.pi_gt_d20]

/-- A successful computation proves the proposed bracket for the actual
arctangent, with no assumed transcendental values or native proof step. -/
theorem bounds_of_check {cfg : DyadicConfig} {x a b : ℚ}
    (hc : check cfg x a b = true) : (a : ℝ) ≤ Real.arctan x ∧ Real.arctan x ≤ (b : ℝ) := by
  unfold check at hc
  obtain ⟨hg, he⟩ := Bool.and_eq_true_iff.mp hc
  simp only [decide_eq_true_eq] at hg
  obtain ⟨hp, ha, ha', hb, hb'⟩ := hg
  cases hA : evalIntervalDyadicChecked (residual x a) (fun _ => default) cfg with
  | error err => simp only [hA, Bool.false_eq_true] at he
  | ok A =>
    cases hB : evalIntervalDyadicChecked (residual x b) (fun _ => default) cfg with
    | error err => simp only [hA, hB, Bool.false_eq_true] at he
    | ok B =>
      simp only [hA, hB, decide_eq_true_eq] at he
      have hAr := evalIntervalDyadicChecked_correct (residual x a) (fun _ => 0)
        (fun _ => default) mem_env cfg hp A hA
      have hBr := evalIntervalDyadicChecked_correct (residual x b) (fun _ => 0)
        (fun _ => default) mem_env cfg hp B hB
      simp only [residual, Expr.eval] at hAr hBr
      have hle : Real.sin a - (x : ℝ) * Real.cos a ≤ 0 := by
        have hh : (A.hi.toRat : ℝ) ≤ 0 := by exact_mod_cast he.1
        linarith [hAr.2]
      have hge : 0 ≤ Real.sin b - (x : ℝ) * Real.cos b := by
        have hh : (0 : ℝ) ≤ B.lo.toRat := by exact_mod_cast he.2
        linarith [hBr.1]
      have hapos := angle_range ha ha'
      have hbpos := angle_range hb hb'
      constructor
      · calc
          (a : ℝ) = Real.arctan (Real.tan a) :=
            (Real.arctan_tan hapos.1 hapos.2).symm
          _ ≤ Real.arctan x := Real.arctan_mono (by
            rw [Real.tan_eq_sin_div_cos, div_le_iff₀ (Real.cos_pos_of_mem_Ioo hapos)]
            linarith)
      · calc
          Real.arctan x ≤ Real.arctan (Real.tan b) := Real.arctan_mono (by
            rw [Real.tan_eq_sin_div_cos, le_div_iff₀ (Real.cos_pos_of_mem_Ioo hbpos)]
            linarith)
          _ = b := Real.arctan_tan hbpos.1 hbpos.2

end RiemannGaussian.CertifiedArctan
