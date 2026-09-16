/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnedCells

/-!
# A stronger cell bound after arithmetic cycle cancellation

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszRetainedCells
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTargetProfile ZetaArithmeticBandCorrelation ZetaRieszConditionedEnergy
open ZetaRieszPrimeCells
open ZetaRieszCellOrders
open ZetaRieszOwnedCells

/-- Exact original cells allow arbitrary complex prior weights inside
both adjacent-order responses, retaining all surviving correlations. -/
def weightedCellResponse (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (eta : ℕ → ℂ) (K : ℕ × Finset ℕ) : ℂ :=
  (cellCoefficient L K.1 K.2 : ℂ) *
      (∑ m ∈ originalCell L P N t K, eta m * bandAmplitude L P N t m) +
    (divisorSlope K.2 : ℂ) *
      (∑ m ∈ originalCell L P N t K, eta m * raisedBandAmplitude L P N t m)

/-- The weighted cell remains exactly its signed original packet. -/
theorem weightedCellResponse_eq_sum (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (eta : ℕ → ℂ) (K : ℕ × Finset ℕ) :
    weightedCellResponse L P N t eta K =
      ∑ m ∈ originalCell L P N t K, eta m * bandWeight L P N t m := by
  unfold weightedCellResponse
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hactive, hkey⟩ := Finset.mem_filter.mp hm
  rw [original_atom_eq_adjacent L P N t hactive, hkey]
  ring

/-- The complete weighted cell partition preserves every original-band
term; it discards only amplitudes already equal to zero. -/
theorem weighted_cells_eq_band_sum (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (eta : ℕ → ℂ) :
    (∑ K ∈ originalCells L P N t, weightedCellResponse L P N t eta K) =
      ∑ m ∈ zetaPrimeLogBand N, eta m * bandWeight L P N t m := by
  simp_rw [weightedCellResponse_eq_sum]
  have hs := Finset.sum_fiberwise_of_maps_to
    (s := ZetaRieszWholeWindow.activeOriginalBand L P N t)
    (t := originalCells L P N t) (g := originalCellKey L)
    (fun m hm => Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    (fun m => eta m * bandWeight L P N t m)
  change (∑ K ∈ originalCells L P N t,
    ∑ m ∈ ZetaRieszWholeWindow.activeOriginalBand L P N t with originalCellKey L m = K,
      eta m * bandWeight L P N t m) = _
  rw [hs, ZetaRieszWholeWindow.activeOriginalBand, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hf : bandWeight L P N t m = 0 <;> simp [hf]

/-- Taking norms only after the complete coupled cell response never
costs more than the remaining original absolute mass. -/
theorem weighted_cell_mass_le (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (eta : ℕ → ℂ) :
    (∑ K ∈ originalCells L P N t, ‖weightedCellResponse L P N t eta K‖) ≤
      ∑ m ∈ zetaPrimeLogBand N, ‖eta m * bandWeight L P N t m‖ := by
  calc
    _ ≤ ∑ K ∈ originalCells L P N t,
        ∑ m ∈ originalCell L P N t K, ‖eta m * bandWeight L P N t m‖ := by
      apply Finset.sum_le_sum
      intro K hK
      rw [weightedCellResponse_eq_sum]
      exact norm_sum_le _ _
    _ = ∑ m ∈ ZetaRieszWholeWindow.activeOriginalBand L P N t,
        ‖eta m * bandWeight L P N t m‖ :=
      Finset.sum_fiberwise_of_maps_to
        (fun m hm => Finset.mem_image.mpr ⟨m, hm, rfl⟩) _
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (fun _ hm => (Finset.mem_filter.mp hm).1) (fun _ _ _ => norm_nonneg _)

/-- Regrouping the actual arithmetic-cycle residual by exact cells
retains the complete original carrier, including all prior spent fractions. -/
theorem cycle_cells_sum_eq_actual (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ))
    (he : ∀ e ∈ es, e ∈ ZetaRieszCycleIteration.actualCycles N) :
    (∑ K ∈ originalCells L P N t,
      weightedCellResponse L P N t
        (fun m => (ZetaRieszRetainedFraction.retainedFraction (bandWeight L P N t) es m : ℂ)) K) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
  rw [weighted_cells_eq_band_sum]
  have hs := ZetaRieszCycleIteration.sum_cycleResidual (zetaPrimeLogBand N)
    (bandWeight L P N t) es
    (fun e he' => ZetaRieszCycleIteration.actualCycles_valid (he e he'))
  simp only [ZetaRieszRetainedFraction.cycleResidual_eq_retainedFraction, Complex.real_smul] at hs
  rw [hs]
  unfold bandWeight zetaArithmeticBand
  exact Finset.sum_congr rfl (fun m hm => by rw [if_pos hm])

/-- Every actual arithmetic cycle list can be followed by exact cell
cancellation, with a full-band bound and no new analytic premise. -/
theorem norm_actual_band_le_cycle_cell_mass (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ))
    (he : ∀ e ∈ es, e ∈ ZetaRieszCycleIteration.actualCycles N) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      ∑ K ∈ originalCells L P N t,
        ‖weightedCellResponse L P N t
          (fun m => (ZetaRieszRetainedFraction.retainedFraction (bandWeight L P N t) es m : ℂ)) K‖ := by
  rw [← cycle_cells_sum_eq_actual L P N t es he]
  exact norm_sum_le _ _

/-- The exact post-cycle cell budget is never larger than the earlier
proved arithmetic allowance. This recovers all uncredited local removal
and retains further cancellation inside each surviving canonical cell. -/
theorem cycle_cell_mass_le_arithmetic_allowance (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ))
    (he : ∀ e ∈ es, e ∈ ZetaRieszCycleIteration.actualCycles N) :
    (∑ K ∈ originalCells L P N t,
      ‖weightedCellResponse L P N t
        (fun m => (ZetaRieszRetainedFraction.retainedFraction (bandWeight L P N t) es m : ℂ)) K‖) ≤
      (∑ m ∈ zetaPrimeLogBand N, ‖bandWeight L P N t m‖) -
        ZetaRieszArithmeticCycles.arithmeticSavings L P N t [] es := by
  have hm := ZetaRieszCycleIteration.mass_cycleResidual (zetaPrimeLogBand N)
    (bandWeight L P N t) es
    (fun e he' => ZetaRieszCycleIteration.actualCycles_valid (he e he'))
  simp only [ZetaRieszRetainedFraction.cycleResidual_eq_retainedFraction, Complex.real_smul] at hm
  have ha := ZetaRieszArithmeticCycles.arithmeticSavings_le_totalSaving L P N t [] es
  change _ ≤ ZetaRieszCycleIteration.totalSaving (bandWeight L P N t) es at ha
  exact (weighted_cell_mass_le L P N t _).trans (hm.le.trans (sub_le_sub_left ha _))

/-- The fully specified available arithmetic list has the stronger
canonical cell bound, with all support and eligibility tests discharged. -/
theorem norm_actual_band_le_available_cell_mass (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      ∑ K ∈ originalCells L P N t,
        ‖weightedCellResponse L P N t
          (fun m => (ZetaRieszRetainedFraction.retainedFraction (bandWeight L P N t)
            (ZetaRieszArithmeticCycles.availableArithmeticCycles L P N t).toList m : ℂ)) K‖ := by
  exact norm_actual_band_le_cycle_cell_mass L P N t _ (fun _ he =>
    (ZetaRieszArithmeticCycles.availableArithmeticCycles_valid (Finset.mem_toList.mp he)).1)

/-- The stronger fully specified cell allowance never exceeds the previous
arithmetic budget at any cutoff, order, height or full polynomial filter. -/
theorem available_cell_mass_le_arithmetic_allowance (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    (∑ K ∈ originalCells L P N t,
      ‖weightedCellResponse L P N t
        (fun m => (ZetaRieszRetainedFraction.retainedFraction (bandWeight L P N t)
          (ZetaRieszArithmeticCycles.availableArithmeticCycles L P N t).toList m : ℂ)) K‖) ≤
      (∑ m ∈ zetaPrimeLogBand N, ‖bandWeight L P N t m‖) -
        ZetaRieszArithmeticCycles.arithmeticSavings L P N t []
          (ZetaRieszArithmeticCycles.availableArithmeticCycles L P N t).toList := by
  exact cycle_cell_mass_le_arithmetic_allowance L P N t _ (fun _ he =>
    (ZetaRieszArithmeticCycles.availableArithmeticCycles_valid (Finset.mem_toList.mp he)).1)

/-- The stronger exact cell response after the complete available
arithmetic list retains the full pole-jet source without exposure,
simplicity or any restriction to the unfiltered carrier. -/
theorem tendsto_available_cycle_cell_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Filter.Tendsto (fun N =>
      let L := SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N
      let P := zetaRightHalfPoleJetFilter rho hrho
      let t := rho.1.im
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        ∑ K ∈ originalCells L P N t,
          weightedCellResponse L P N t
            (fun m => (ZetaRieszRetainedFraction.retainedFraction (bandWeight L P N t)
              (ZetaRieszArithmeticCycles.availableArithmeticCycles L P N t).toList m : ℂ)) K)
      Filter.atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  apply h.congr'
  filter_upwards [] with N
  dsimp only
  rw [cycle_cells_sum_eq_actual _ _ _ _ _ (fun _ he =>
    (ZetaRieszArithmeticCycles.availableArithmeticCycles_valid (Finset.mem_toList.mp he)).1)]
  push_cast
  rfl
end
end RiemannGaussian.ZetaRieszRetainedCells
