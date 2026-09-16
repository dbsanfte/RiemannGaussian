/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCycleIteration

/-!
# Every earlier exact cycle retains its actual scalar fraction

Exact target profiles, original complex directions and separately retained
capacities give proved arithmetic cycle budgets. All failed tests and
remaining original terms stay accounted for. Sufficient aggregate saving
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszRetainedFraction
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTransportPhase ZetaRieszConditionedEnergy

/-- The actual retained scalar after every earlier exact-cycle test.
It is determined by the original amplitudes and the processed list. -/
def retainedFraction (f : ℕ → ℂ) : List (ℕ × ℕ × ℕ) → ℕ → ℝ
  | [] => fun _ => 1
  | e :: es => fun n => retainedFraction (ZetaRieszCycleIteration.cycleStep f e) es n *
      (1 - ZetaRieszCycleIteration.removedFraction f e n)

/-- Earlier cycles retain a fraction in [0,1] of each original amplitude. -/
theorem retainedFraction_bounds (f : ℕ → ℂ) (es : List (ℕ × ℕ × ℕ)) (n : ℕ) :
    0 ≤ retainedFraction f es n ∧ retainedFraction f es n ≤ 1 := by
  induction es generalizing f with
  | nil => exact ⟨zero_le_one, le_rfl⟩
  | cons e es ih =>
    obtain ⟨h0, h1⟩ := ZetaRieszCycleIteration.removedFraction_bounds f e n
    obtain ⟨hi0, hi1⟩ := ih (ZetaRieszCycleIteration.cycleStep f e)
    change 0 ≤ _ * _ ∧ _ * _ ≤ 1
    refine ⟨mul_nonneg hi0 (sub_nonneg.mpr h1), ?_⟩
    exact (mul_le_mul_of_nonneg_right hi1 (sub_nonneg.mpr h1)).trans (by linarith)

/-- The complete original phase is unchanged by every earlier cycle;
only its actual retained scalar is spent. -/
theorem cycleResidual_eq_retainedFraction (f : ℕ → ℂ) (es : List (ℕ × ℕ × ℕ)) (n : ℕ) :
    ZetaRieszCycleIteration.cycleResidual f es n = retainedFraction f es n • f n := by
  induction es generalizing f with
  | nil => simp [ZetaRieszCycleIteration.cycleResidual, retainedFraction]
  | cons e es ih =>
    simp only [ZetaRieszCycleIteration.cycleResidual, retainedFraction, ih,
      ZetaRieszCycleIteration.cycleStep, smul_smul]

/-- Earlier exact-cycle lists compose without changing their original
labels or reintroducing any spent amplitudes. -/
theorem cycleResidual_append (f : ℕ → ℂ) (as bs : List (ℕ × ℕ × ℕ)) :
    ZetaRieszCycleIteration.cycleResidual f (as ++ bs) =
      ZetaRieszCycleIteration.cycleResidual (ZetaRieszCycleIteration.cycleResidual f as) bs := by
  induction as generalizing f with
  | nil => rfl
  | cons e es ih =>
    simp only [List.cons_append, ZetaRieszCycleIteration.cycleResidual, ih]

end
end RiemannGaussian.ZetaRieszRetainedFraction
