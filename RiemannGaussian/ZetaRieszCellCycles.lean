/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszArithmeticCells

/-!
# Cancellation between complete arithmetic prime intervals

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszCellCycles
noncomputable section
open scoped BigOperators Classical
open ZetaRieszTargetProfile ZetaArithmeticBandCorrelation ZetaRieszConditionedEnergy
open ZetaRieszPrimeEndpoint
open ZetaRieszCycleIteration ZetaRieszRetainedFraction
open ZetaRieszCellOrders
open ZetaRieszOwnedCells
open ZetaRieszArithmeticCells

/-- A unique natural label allows the existing exact-cycle implementation
to act on the arithmetic cells without changing their prime content. -/
def cellCode (K : ℕ × Finset ℕ) : ℕ := Encodable.encode K

/-- No distinct cofactor-and-divisor cells share a cycle label. -/
theorem cellCode_injective : Function.Injective cellCode := Encodable.encode_injective

/-- Only the codes of actual, fixed arithmetic cells are available. -/
def cellCodes (L : ℝ) (N : ℕ) : Finset ℕ :=
  (arithmeticCells L N).image cellCode

/-- The cycle input is each complete signed prime-interval response. -/
def cellSignal (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) (i : ℕ) : ℂ :=
  match Encodable.decode (α := ℕ × Finset ℕ) i with
  | none => 0
  | some K => arithmeticCellResponse L P N t K

/-- Encoding and decoding leave the complete complex cell unchanged. -/
theorem cellSignal_code (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (K : ℕ × Finset ℕ) : cellSignal L P N t (cellCode K) =
      arithmeticCellResponse L P N t K := by
  simp [cellSignal, cellCode, Encodable.encodek]

/-- The supported cell codes still sum to the full original carrier. -/
theorem sum_cellSignal (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    (∑ i ∈ cellCodes L N, cellSignal L P N t i) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
  rw [cellCodes, Finset.sum_image (fun _ _ _ _ h => cellCode_injective h)]
  simp_rw [cellSignal_code]
  exact (actual_band_eq_arithmetic_cells L P N t).symm

/-- Supported distinct cells are the only bookkeeping condition for a
cycle; its signed-area eligibility is tested by the exact cycle itself. -/
def validCellCycle (L : ℝ) (N : ℕ) (e : ℕ × ℕ × ℕ) : Prop :=
  e.1 ∈ cellCodes L N ∧ e.2.1 ∈ cellCodes L N ∧ e.2.2 ∈ cellCodes L N ∧ distinctTriple e

/-- Every whole-cell cycle list preserves the full carrier exactly. -/
theorem sum_cellResidual (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ)) (he : ∀ e ∈ es, validCellCycle L N e) :
    (∑ i ∈ cellCodes L N, cycleResidual (cellSignal L P N t) es i) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
  rw [sum_cycleResidual _ _ es he, sum_cellSignal]

/-- The exact retained fraction belongs to a complete cell, rather than
to selected primes inside that interval. -/
def cellRetention (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ)) (K : ℕ × Finset ℕ) : ℝ :=
  retainedFraction (cellSignal L P N t) es (cellCode K)

/-- No original cell is amplified or charged for more than its capacity. -/
theorem cellRetention_bounds (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ)) (K : ℕ × Finset ℕ) :
    0 ≤ cellRetention L P N t es K ∧ cellRetention L P N t es K ≤ 1 :=
  retainedFraction_bounds _ _ _

/-- The residual on a cell is a scalar times its complete complex
response, so both adjacent prime moments remain coupled. -/
theorem cellResidual_eq_retained (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ)) (K : ℕ × Finset ℕ) :
    cycleResidual (cellSignal L P N t) es (cellCode K) =
      cellRetention L P N t es K • arithmeticCellResponse L P N t K := by
  rw [cycleResidual_eq_retainedFraction, cellSignal_code]
  rfl

/-- The full original carrier is a retained sum of complete prime
intervals, without any prime-by-prime phase-selection mask. -/
theorem retained_cells_eq_actual (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ)) (he : ∀ e ∈ es, validCellCycle L N e) :
    (∑ K ∈ arithmeticCells L N,
      cellRetention L P N t es K • arithmeticCellResponse L P N t K) =
        zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
  rw [← sum_cellResidual L P N t es he, cellCodes,
    Finset.sum_image (fun _ _ _ _ h => cellCode_injective h)]
  simp_rw [cellResidual_eq_retained]

/-- Every original prime in a cell receives the same exact retained
scalar. The complete interval sums can therefore be estimated first. -/
theorem retained_cell_eq_prime_moments (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ)) {K : ℕ × Finset ℕ} (hK : K ∈ arithmeticCells L N) :
    cycleResidual (cellSignal L P N t) es (cellCode K) =
      cellRetention L P N t es K •
        ((cellCoefficient L K.1 K.2 : ℂ) *
          (∑ p ∈ intervalPrimes L N K.1 K.2,
            ZetaArithmeticBandCorrelation.bandAmplitude L P N t (p * K.1)) +
         (divisorSlope K.2 : ℂ) *
          (∑ p ∈ intervalPrimes L N K.1 K.2, raisedBandAmplitude L P N t (p * K.1))) := by
  rw [cellResidual_eq_retained, arithmeticCellResponse_eq_prime_moments L P N t hK]

/-- Whole-cell cancellation saves from the cell norm sum itself, after
all internal prime cancellation has already been retained. -/
theorem norm_actual_band_le_cell_saving (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ)) (he : ∀ e ∈ es, validCellCycle L N e) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      (∑ K ∈ arithmeticCells L N, ‖arithmeticCellResponse L P N t K‖) -
        totalSaving (cellSignal L P N t) es := by
  have h := norm_sum_le_total_saving (cellCodes L N) (cellSignal L P N t) es he
  rw [sum_cellSignal, cellCodes,
    Finset.sum_image (fun _ _ _ _ heq => cellCode_injective heq)] at h
  simpa only [cellSignal_code] using h

/-- No supported list can make the cell norm allowance negative; the
budget is exactly the actual remaining cell norm sum. -/
theorem cell_allowance_eq_retained_mass (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ)) (he : ∀ e ∈ es, validCellCycle L N e) :
    (∑ K ∈ arithmeticCells L N, ‖arithmeticCellResponse L P N t K‖) -
        totalSaving (cellSignal L P N t) es =
      ∑ K ∈ arithmeticCells L N,
        cellRetention L P N t es K * ‖arithmeticCellResponse L P N t K‖ := by
  have h := mass_cycleResidual (cellCodes L N) (cellSignal L P N t) es he
  rw [cellCodes, Finset.sum_image (fun _ _ _ _ heq => cellCode_injective heq),
    Finset.sum_image (fun _ _ _ _ heq => cellCode_injective heq)] at h
  simp_rw [cellSignal_code, cellResidual_eq_retained, norm_smul,
    Real.norm_of_nonneg (cellRetention_bounds L P N t es _).1] at h
  exact h.symm

/-- Any independently proved whole-interval envelope may be used after
the exact cycles, with its actual cellwise fraction and no variation cost. -/
theorem norm_actual_band_le_interval_envelopes (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (es : List (ℕ × ℕ × ℕ)) (he : ∀ e ∈ es, validCellCycle L N e)
    (B : (ℕ × Finset ℕ) → ℝ)
    (hB : ∀ K ∈ arithmeticCells L N, ‖arithmeticCellResponse L P N t K‖ ≤ B K) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      ∑ K ∈ arithmeticCells L N, cellRetention L P N t es K * B K := by
  have h := norm_actual_band_le_cell_saving L P N t es he
  rw [cell_allowance_eq_retained_mass L P N t es he] at h
  exact h.trans (Finset.sum_le_sum (fun K hK =>
    mul_le_mul_of_nonneg_left (hB K hK) (cellRetention_bounds L P N t es K).1))

/-- Every supported whole-cell strategy retains the full pole-jet source,
with arbitrary zero multiplicity and no exposure or local-u restriction. -/
theorem tendsto_retained_cell_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (es : ℕ → List (ℕ × ℕ × ℕ))
    (he : ∀ N, ∀ e ∈ es N,
      validCellCycle (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) N e) :
    Filter.Tendsto (fun N => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ K ∈ arithmeticCells (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) N,
        cellRetention (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im (es N) K •
        arithmeticCellResponse (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im K)
      Filter.atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  apply h.congr'
  filter_upwards [] with N
  rw [retained_cells_eq_actual _ _ _ _ _ (he N)]
  push_cast
  rfl
end
end RiemannGaussian.ZetaRieszCellCycles
