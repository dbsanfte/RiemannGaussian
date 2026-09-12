/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MonotonePhaseBlocks
import Mathlib.Data.Int.Interval

/-!
# Exact resonance cells for a finite monotone phase sequence

The translated floor of an increment tags its unique resonance cell.
Every finite original summand is partitioned into a short band near that
resonance and a complete nonresonant band. The decomposition is an exact
complex identity for arbitrary summands. A proved cardinality estimate
retains the two endpoint cells when bounding the number of cells touched.
-/

namespace RiemannGaussian.FiniteResonancePartition
noncomputable section
open MonotonePhaseBlocks
open scoped Classical

/-- The resonance cell containing a given real increment, with the
lower boundary shifted by the specified allowance. -/
def cellIndex (η x : ℝ) : ℤ := ⌊(x + η) / (2 * Real.pi)⌋

/-- The complete finite integer range between the first and last
resonance tags. Empty cells are retained harmlessly. -/
def cells (d : ℕ → ℝ) (N : ℕ) (η : ℝ) : Finset ℤ :=
  Finset.Icc (cellIndex η (d 0)) (cellIndex η (d (N - 1)))

/-- Cell tags preserve the ordering of the original increments. -/
theorem cellIndex_mono (η : ℝ) : Monotone (cellIndex η) := by
  intro x y hxy
  exact Int.floor_mono (div_le_div_of_nonneg_right (by linarith : x + η ≤ y + η)
    (by positivity : 0 ≤ 2 * Real.pi))

/-- Each tag is equivalent to membership in its exact half-open cell,
including a precise convention for points on the boundary. -/
theorem cellIndex_eq_iff (η x : ℝ) (m : ℤ) :
    cellIndex η x = m ↔ (m : ℝ) * (2 * Real.pi) - η ≤ x ∧
      x < (m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η := by
  rw [cellIndex, Int.floor_eq_iff,
    le_div_iff₀ (by positivity : 0 < 2 * Real.pi),
    div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

/-- Every original index belongs to the complete range of touched
cells. No bound on its integer winding is imposed in advance. -/
theorem cellIndex_mem_cells {d : ℕ → ℝ} {N : ℕ} (hd : MonotoneOn d (Set.Iio N))
    (η : ℝ) {n : ℕ} (hn : n < N) : cellIndex η (d n) ∈ cells d N η := by
  apply Finset.mem_Icc.mpr
  constructor
  · exact cellIndex_mono η (hd (show 0 < N by omega) hn (Nat.zero_le n))
  · exact cellIndex_mono η (hd hn (show N - 1 < N by omega) (by omega))

/-- The exact fibre of a resonance tag is its original value band. -/
theorem cell_eq_filter (d : ℕ → ℝ) (N : ℕ) (η : ℝ) (m : ℤ) :
    band d N ((m : ℝ) * (2 * Real.pi) - η)
      ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η) =
        (Finset.range N).filter (fun n ↦ cellIndex η (d n) = m) := by
  ext n
  simp only [mem_band, Finset.mem_filter, Finset.mem_range, cellIndex_eq_iff]

/-- Splitting a value band at an interior threshold partitions the
complete complex sum exactly, assigning the boundary to the upper band. -/
theorem band_sum_split (d : ℕ → ℝ) (N : ℕ) (f : ℕ → ℂ) {u w v : ℝ}
    (huw : u ≤ w) (hwv : w ≤ v) :
    (∑ n ∈ band d N u v, f n) =
      (∑ n ∈ band d N u w, f n) + ∑ n ∈ band d N w v, f n := by
  have hl : (band d N u v).filter (fun n ↦ d n < w) = band d N u w := by
    ext n
    simp only [Finset.mem_filter, mem_band]
    constructor
    · rintro ⟨⟨hn, hu, _⟩, hw⟩
      exact ⟨hn, hu, hw⟩
    · rintro ⟨hn, hu, hw⟩
      exact ⟨⟨hn, hu, hw.trans_le hwv⟩, hw⟩
  have hr : (band d N u v).filter (fun n ↦ ¬d n < w) = band d N w v := by
    ext n
    simp only [Finset.mem_filter, mem_band, not_lt]
    constructor
    · rintro ⟨⟨hn, _, hv⟩, hw⟩
      exact ⟨hn, hw, hv⟩
    · rintro ⟨hn, hw, hv⟩
      exact ⟨⟨hn, huw.trans hw, hv⟩, hw⟩
  have h := Finset.sum_filter_add_sum_filter_not (band d N u v) (fun n ↦ d n < w) f
  rw [hl, hr] at h
  exact h.symm

/-- The full original complex sum is the exact sum of all near-resonant
and nonresonant bands, with every cutoff and endpoint retained. -/
theorem sum_eq_bands (d : ℕ → ℝ) (N : ℕ) (f : ℕ → ℂ) {η : ℝ}
    (hη : 0 ≤ η) (hηπ : η ≤ Real.pi) (hd : MonotoneOn d (Set.Iio N)) :
    (∑ n ∈ Finset.range N, f n) =
      ∑ m ∈ cells d N η,
        ((∑ n ∈ band d N ((m : ℝ) * (2 * Real.pi) - η)
          ((m : ℝ) * (2 * Real.pi) + η), f n) +
            ∑ n ∈ band d N ((m : ℝ) * (2 * Real.pi) + η)
              ((m : ℝ) * (2 * Real.pi) + 2 * Real.pi - η), f n) := by
  have hmap : ∀ n ∈ Finset.range N, cellIndex η (d n) ∈ cells d N η :=
    fun _ hn ↦ cellIndex_mem_cells hd η (Finset.mem_range.mp hn)
  rw [← Finset.sum_fiberwise_of_maps_to hmap f]
  apply Finset.sum_congr rfl
  intro m _
  rw [← cell_eq_filter]
  exact band_sum_split d N f (by linarith) (by linarith)

/-- The number of cells is bounded by the original increment spread
divided by a full period, with both endpoint cells paid for explicitly. -/
theorem cells_card_le {d : ℕ → ℝ} {N : ℕ} (η : ℝ) (hd : MonotoneOn d (Set.Iio N)) :
    ((cells d N η).card : ℝ) ≤ (d (N - 1) - d 0) / (2 * Real.pi) + 2 := by
  by_cases hN : N = 0
  · subst N
    simp [cells]
  have hlohi : cellIndex η (d 0) ≤ cellIndex η (d (N - 1)) :=
    cellIndex_mono η (hd (show 0 < N by omega)
      (show N - 1 < N by omega) (Nat.zero_le _))
  have hc : ((cells d N η).card : ℝ) =
      (cellIndex η (d (N - 1)) : ℝ) + 1 - (cellIndex η (d 0) : ℝ) := by
    exact_mod_cast Int.card_Icc_of_le (cellIndex η (d 0)) (cellIndex η (d (N - 1)))
      (by omega)
  rw [hc]
  have hi := Int.floor_le ((d (N - 1) + η) / (2 * Real.pi))
  have hl := Int.lt_floor_add_one ((d 0 + η) / (2 * Real.pi))
  change (cellIndex η (d (N - 1)) : ℝ) ≤ _ at hi
  change _ < (cellIndex η (d 0) : ℝ) + 1 at hl
  have he : (d (N - 1) - d 0) / (2 * Real.pi) =
      (d (N - 1) + η) / (2 * Real.pi) - (d 0 + η) / (2 * Real.pi) := by ring
  rw [he]
  linarith

end
end RiemannGaussian.FiniteResonancePartition
