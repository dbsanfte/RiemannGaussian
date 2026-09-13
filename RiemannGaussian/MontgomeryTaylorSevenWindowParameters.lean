/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorWindowEnergy
import Mathlib.Tactic.IntervalCases

/-!
# Exact parameters of the seven-point candidate

The candidate uses nonuniform position weights under the same separation
budget as the consecutive-window method of `ainta/zeta-simple-zeros`.
The rational parameters and their budgets are checked here. This module
does not assert the uniform numerical kernel floor.
-/

namespace RiemannGaussian.MontgomeryTaylorSevenWindowParameters
noncomputable section
open scoped BigOperators

/-- Integer numerators of all position-dependent pair weights. -/
def pairNumerator (s i : ℕ) : ℕ :=
  (match s with
    | 0 => #[21884, 33405, 44711, 44711, 33405, 21884]
    | 1 => #[74396, 25604, 0, 25604, 74396]
    | 2 => #[32469, 67531, 67531, 32469]
    | 3 => #[100000, 0, 100000]
    | 4 => #[100000, 100000]
    | 5 => #[200000]
    | _ => #[])[i]?.getD 0

/-- Exact real pair coefficients, with zero outside the six separations. -/
def pairWeight (s i : ℕ) : ℝ := (pairNumerator s i : ℝ) / 100000

/-- Integer numerators of the six gap-pressure coefficients. -/
def pressureNumerator (i : ℕ) : ℕ :=
  (#[208856, 325508, 465636, 465636, 325508, 208856] : Array ℕ)[i]?.getD 0

/-- Exact gap pressures; their total is one five-hundredth. -/
def pressureWeight (i : ℕ) : ℝ := (pressureNumerator i : ℝ) / 1000000000

/-- Proposed uniform floor for the actual kernel, still requiring a
complete numerical proof. -/
def targetFloor : ℝ := 79 / 20000

/-- A slightly stronger model floor pays the entire coefficient-rounding
allowance before transferring to the actual kernel. -/
def modelFloor : ℝ := 395002 / 100000000

/-- Every pair weight is nonnegative, including entries outside the window. -/
theorem pairWeight_nonneg (s i : ℕ) : 0 ≤ pairWeight s i := by
  unfold pairWeight
  positivity

/-- Each positive separation has exactly the full two-orientation budget. -/
theorem pairWeight_budget {s : ℕ} (hs : s < 6) :
    (∑ i ∈ Finset.range (6 - s), pairWeight s i) = 2 := by
  interval_cases s <;> norm_num [pairWeight, pairNumerator, Finset.sum_range_succ]

/-- Every pressure weight is nonnegative. -/
theorem pressureWeight_nonneg (i : ℕ) : 0 ≤ pressureWeight i := by
  unfold pressureWeight
  positivity

/-- The exact total span charge of the candidate. -/
theorem pressureWeight_sum :
    (∑ i ∈ Finset.range 6, pressureWeight i) = 1 / 500 := by
  norm_num [pressureWeight, pressureNumerator, Finset.sum_range_succ]

/-- Each nearest-neighbor correlation has enough weight to settle a gap
at most one third using the analytic small-separation bound. -/
theorem nearestWeight_lower {i : ℕ} (hi : i < 6) :
    (1 : ℝ) / 5 ≤ pairWeight 0 i := by
  interval_cases i <;> norm_num [pairWeight, pairNumerator]

/-- Every gap pays enough positive pressure to settle the unbounded tail
once that gap reaches twenty cycles. -/
theorem pressureWeight_lower {i : ℕ} (hi : i < 6) :
    (1 : ℝ) / 5000 ≤ pressureWeight i := by
  interval_cases i <;> norm_num [pressureWeight, pressureNumerator]

/-- The total pair budget is exactly twelve. -/
theorem total_pairWeight :
    (∑ s ∈ Finset.range 6, ∑ i ∈ Finset.range (6 - s), pairWeight s i) = 12 := by
  calc
    _ = ∑ _s ∈ Finset.range 6, (2 : ℝ) := Finset.sum_congr rfl
      (fun s hs => pairWeight_budget (Finset.mem_range.mp hs))
    _ = _ := by norm_num

/-- The model floor leaves room for every squared-kernel rounding error. -/
theorem modelFloor_pays_error : targetFloor + 12 / 1000000000 ≤ modelFloor := by
  norm_num [targetFloor, modelFloor]

/-- Summing 253 overlapping seven-point floors gives the exact reserve
needed for a 259-point spectral block. This implication leaves the local
floor as its explicit, unproved numerical input. -/
theorem block_floor_of_local_floors (w : ℝ → ℝ) (hw : ∀ t, 0 ≤ w t)
    (x : ℕ → ℝ) (hx : Monotone x)
    (hfloor : ∀ start < 253, targetFloor ≤
      MontgomeryTaylorWindowEnergy.windowEnergy w pairWeight x 6 start +
        MontgomeryTaylorWindowEnergy.windowPressure pressureWeight x 6 start) :
    (19987 : ℝ) / 20000 ≤ MontgomeryTaylorWindowEnergy.lagEnergy w x 259 +
      (1 / 500 : ℝ) * (x 258 - x 0) := by
  have h := MontgomeryTaylorWindowEnergy.floor_transport w hw pairWeight pressureWeight x hx
    (q := 6) (n := 259) (by norm_num)
    (fun s _ i _ => pairWeight_nonneg s i)
    (fun s hs => (pairWeight_budget hs).le)
    (fun i _ => pressureWeight_nonneg i) hfloor
  norm_num [targetFloor, pressureWeight_sum] at h
  exact h

end
end RiemannGaussian.MontgomeryTaylorSevenWindowParameters
