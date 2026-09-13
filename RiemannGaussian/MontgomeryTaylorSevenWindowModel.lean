/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorSevenWindowParameters
import RiemannGaussian.MontgomeryTaylorNumericalKernel

/-!
# The six-gap numerical model and its exact window transfer

The model keeps every weighted pair separation. Small gaps are settled by
the analytic kernel bound; on the remaining domain the complete model error
is paid before passing to the actual seven-point correlation floor.
-/

namespace RiemannGaussian.MontgomeryTaylorSevenWindowModel
noncomputable section
open MontgomeryTaylorSevenWindowParameters MontgomeryTaylorNumericalKernel
open MontgomeryTaylorWindowEnergy
open scoped BigOperators

/-- A pair separation as the sum of all intervening consecutive gaps. -/
def separation (g : ℕ → ℝ) (s i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (s + 1), g (i + j)

/-- The exact six-gap objective for any squared-correlation function. -/
def energy (w : ℝ → ℝ) (g : ℕ → ℝ) : ℝ :=
  (∑ s ∈ Finset.range 6, ∑ i ∈ Finset.range (6 - s),
    pairWeight s i * w (separation g s i)) +
      ∑ i ∈ Finset.range 6, pressureWeight i * g i

/-- The rational-coefficient numerical kernel model. -/
def model (g : ℕ → ℝ) : ℝ := energy (fun t => kernel t ^ 2) g

/-- The actual Montgomery--Taylor correlation objective in cycle units. -/
def actual (g : ℕ → ℝ) : ℝ :=
  energy (fun t => montgomeryTaylorKernel (2 * Real.pi * t) ^ 2) g

/-- The same numerical objective on its six relevant real coordinates. -/
def finiteModel (g : Fin 6 → ℝ) : ℝ :=
  model (fun j => if hj : j < 6 then g ⟨j, hj⟩ else 0)

/-- The objective depends only on the six consecutive gaps. -/
theorem energy_congr (w : ℝ → ℝ) {g h : ℕ → ℝ}
    (heq : ∀ j < 6, g j = h j) : energy w g = energy w h := by
  unfold energy
  congr 1
  · apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    apply Finset.sum_congr rfl
    intro j hj
    exact heq (i + j) (by
      have := Finset.mem_range.mp hs
      have := Finset.mem_range.mp hi
      have := Finset.mem_range.mp hj
      omega)
  · exact Finset.sum_congr rfl fun j hj => by rw [heq j (Finset.mem_range.mp hj)]

/-- Restriction to the first six gaps preserves the entire objective. -/
theorem finiteModel_restrict (g : ℕ → ℝ) :
    finiteModel (fun j => g j) = model g := by
  unfold finiteModel model
  apply energy_congr (fun t => kernel t ^ 2)
  intro j hj
  simp [hj]

/-- Consecutive differences recover each pair separation exactly. -/
theorem separation_of_differences (x : ℕ → ℝ) (s i : ℕ) :
    separation (fun j => x (j + 1) - x j) s i = x (i + s + 1) - x i := by
  simpa only [separation, Nat.add_assoc, Nat.add_zero] using
    sum_gaps (fun j => x (i + j)) (s + 1)

/-- The gap objective is the literal window objective, without loss of
any pair correlation or pressure coefficient. -/
theorem energy_of_differences (w : ℝ → ℝ) (x : ℕ → ℝ) :
    energy w (fun j => x (j + 1) - x j) =
      windowEnergy w pairWeight x 6 0 + windowPressure pressureWeight x 6 0 := by
  simp only [energy, windowEnergy, windowPressure, separation_of_differences, Nat.zero_add]

/-- Nonnegative intervening gaps retain at least the first gap. -/
theorem first_gap_le_separation {g : ℕ → ℝ} (hg : ∀ j < 6, 0 ≤ g j)
    {s i : ℕ} (hs : s < 6) (hi : i < 6 - s) : g i ≤ separation g s i := by
  have h := Finset.single_le_sum (s := Finset.range (s + 1)) (f := fun j => g (i + j))
    (fun j hj => hg (i + j) (by have := Finset.mem_range.mp hj; omega))
    (by simp : 0 ∈ Finset.range (s + 1))
  simpa only [separation, Nat.add_zero] using h

/-- One pair's nonnegative contribution is retained in the full energy. -/
theorem pair_le_energy {w : ℝ → ℝ} (hw : ∀ t, 0 ≤ w t) {g : ℕ → ℝ}
    (hg : ∀ j < 6, 0 ≤ g j) {s i : ℕ} (hs : s < 6) (hi : i < 6 - s) :
    pairWeight s i * w (separation g s i) ≤ energy w g := by
  have hpair := Finset.single_le_sum (s := Finset.range (6 - s))
    (f := fun j => pairWeight s j * w (separation g s j))
    (fun j _ => mul_nonneg (pairWeight_nonneg s j) (hw _)) (Finset.mem_range.mpr hi)
  have hrow := Finset.single_le_sum (s := Finset.range 6)
    (f := fun t => ∑ j ∈ Finset.range (6 - t), pairWeight t j * w (separation g t j))
    (fun t _ => Finset.sum_nonneg fun j _ => mul_nonneg (pairWeight_nonneg t j) (hw _))
    (Finset.mem_range.mpr hs)
  have hp : 0 ≤ ∑ j ∈ Finset.range 6, pressureWeight j * g j :=
    Finset.sum_nonneg fun j hj => mul_nonneg (pressureWeight_nonneg j) (hg j (Finset.mem_range.mp hj))
  exact (hpair.trans hrow).trans (le_add_of_nonneg_right hp)

/-- Every configuration with a gap at most one third already exceeds
the required actual-kernel floor. -/
theorem target_le_actual_of_small_gap {g : ℕ → ℝ} (hg : ∀ j < 6, 0 ≤ g j)
    {i : ℕ} (hi : i < 6) (hsmall : g i ≤ 1 / 3) : targetFloor ≤ actual g := by
  have hk := MontgomeryTaylorKernelFormula.small_cycles_lower (hg i hi) hsmall
  have hk2 : (1 : ℝ) / 9 ≤ montgomeryTaylorKernel (2 * Real.pi * g i) ^ 2 := by nlinarith
  have hweight := mul_le_mul (nearestWeight_lower hi) hk2
    (by norm_num : (0 : ℝ) ≤ 1 / 9) (pairWeight_nonneg 0 i)
  have hsingle := pair_le_energy
    (fun t => sq_nonneg (montgomeryTaylorKernel (2 * Real.pi * t))) hg
    (s := 0) (by norm_num) (by simpa using hi)
  simp only [separation, Nat.zero_add, Finset.sum_range_one, Nat.add_zero] at hsingle
  unfold actual
  have htar : targetFloor ≤ (1 / 5 : ℝ) * (1 / 9) := by norm_num [targetFloor]
  exact htar.trans (hweight.trans hsingle)

/-- The exact twelve-unit pair budget pays the complete model error on
the remaining domain. The pressure term is unchanged. -/
theorem model_le_actual_add_error {g : ℕ → ℝ} (hg : ∀ j < 6, 1 / 3 ≤ g j) :
    model g ≤ actual g + 12 / 1000000000 := by
  have hpos : ∀ j < 6, 0 ≤ g j := fun j hj => le_trans (by norm_num) (hg j hj)
  have hterm (s : ℕ) (hs : s < 6) (i : ℕ) (hi : i < 6 - s) :
      pairWeight s i * kernel (separation g s i) ^ 2 ≤
        pairWeight s i * montgomeryTaylorKernel (2 * Real.pi * separation g s i) ^ 2 +
          pairWeight s i * (1 / 1000000000) := by
    have hi6 : i < 6 := by omega
    have hsep := (hg i hi6).trans (first_gap_le_separation hpos hs hi)
    have he := mul_le_mul_of_nonneg_left (abs_le.mp (squared_kernel_error hsep)).2
      (pairWeight_nonneg s i)
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.range 6) fun s hs =>
    Finset.sum_le_sum (s := Finset.range (6 - s)) fun i hi =>
      hterm s (Finset.mem_range.mp hs) i (Finset.mem_range.mp hi)
  simp only [Finset.sum_add_distrib] at hsum
  have hbudget : (∑ s ∈ Finset.range 6, ∑ i ∈ Finset.range (6 - s),
      pairWeight s i * (1 / 1000000000 : ℝ)) = 12 / 1000000000 := by
    simp_rw [← Finset.sum_mul]
    rw [total_pairWeight]
    ring
  rw [hbudget] at hsum
  unfold model actual energy
  linarith

/-- A proved numerical-model floor on the surviving gap domain supplies
the exact actual-kernel window floor required by the counting theorem. -/
theorem window_floor_of_model_floor
    (hfloor : ∀ g : ℕ → ℝ, (∀ j < 6, 1 / 3 ≤ g j) → modelFloor ≤ model g)
    (x : ℕ → ℝ) (hx : Monotone x) :
    targetFloor ≤ windowEnergy (fun t => montgomeryTaylorKernel (2 * Real.pi * t) ^ 2)
      pairWeight x 6 0 + windowPressure pressureWeight x 6 0 := by
  let g : ℕ → ℝ := fun j => x (j + 1) - x j
  have hg : ∀ j < 6, 0 ≤ g j := fun j _ => sub_nonneg.mpr (hx (by omega))
  have heq : actual g = windowEnergy (fun t => montgomeryTaylorKernel (2 * Real.pi * t) ^ 2)
      pairWeight x 6 0 + windowPressure pressureWeight x 6 0 := energy_of_differences _ x
  rw [← heq]
  by_cases hlarge : ∀ j < 6, 1 / 3 ≤ g j
  · have hl := hfloor g hlarge
    have he := model_le_actual_add_error hlarge
    linarith [modelFloor_pays_error]
  · push Not at hlarge
    obtain ⟨i, hi, hsmall⟩ := hlarge
    exact target_le_actual_of_small_gap hg hi hsmall.le

/-- A single gap pressure remains available without discarding its
nonnegative pair correlations. -/
theorem pressure_le_energy {w : ℝ → ℝ} (hw : ∀ t, 0 ≤ w t) {g : ℕ → ℝ}
    (hg : ∀ j < 6, 0 ≤ g j) {i : ℕ} (hi : i < 6) :
    pressureWeight i * g i ≤ energy w g := by
  have hp := Finset.single_le_sum (s := Finset.range 6)
    (f := fun j => pressureWeight j * g j)
    (fun j hj => mul_nonneg (pressureWeight_nonneg j) (hg j (Finset.mem_range.mp hj)))
    (Finset.mem_range.mpr hi)
  have he : 0 ≤ ∑ s ∈ Finset.range 6, ∑ j ∈ Finset.range (6 - s),
      pairWeight s j * w (separation g s j) :=
    Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (pairWeight_nonneg s j) (hw _)
  exact hp.trans (le_add_of_nonneg_left he)

/-- The positive pressure settles every configuration with a gap of
at least twenty cycles. -/
theorem modelFloor_le_of_large_gap {g : ℕ → ℝ} (hg : ∀ j < 6, 0 ≤ g j)
    {i : ℕ} (hi : i < 6) (hlarge : 20 ≤ g i) : modelFloor ≤ model g := by
  have hp := mul_le_mul (pressureWeight_lower hi) hlarge
    (by norm_num : (0 : ℝ) ≤ 20) (pressureWeight_nonneg i)
  have he := pressure_le_energy (fun t => sq_nonneg (kernel t)) hg hi
  have ht : modelFloor ≤ (1 / 5000 : ℝ) * 20 := by norm_num [modelFloor]
  exact ht.trans (hp.trans he)

/-- The entire unbounded numerical problem reduces to a closed compact
box in the six gap coordinates. -/
theorem model_floor_of_compact_floor
    (hfloor : ∀ g : Fin 6 → ℝ, (∀ j, g j ∈ Set.Icc (1 / 3) 20) →
      modelFloor ≤ finiteModel g)
    (g : ℕ → ℝ) (hg : ∀ j < 6, 1 / 3 ≤ g j) : modelFloor ≤ model g := by
  by_cases hbounded : ∀ j < 6, g j ≤ 20
  · have h := hfloor (fun j => g j) (fun j => ⟨hg j j.isLt, hbounded j j.isLt⟩)
    rwa [finiteModel_restrict] at h
  · push Not at hbounded
    obtain ⟨i, hi, hlarge⟩ := hbounded
    exact modelFloor_le_of_large_gap
      (fun j hj => le_trans (by norm_num) (hg j hj)) hi hlarge.le

/-- The sole remaining numerical input can be stated on the explicit
six-dimensional compact box, with every other gap configuration settled. -/
theorem window_floor_of_compact_model_floor
    (hfloor : ∀ g : Fin 6 → ℝ, (∀ j, g j ∈ Set.Icc (1 / 3) 20) →
      modelFloor ≤ finiteModel g)
    (x : ℕ → ℝ) (hx : Monotone x) :
    targetFloor ≤ windowEnergy (fun t => montgomeryTaylorKernel (2 * Real.pi * t) ^ 2)
      pairWeight x 6 0 + windowPressure pressureWeight x 6 0 :=
  window_floor_of_model_floor (model_floor_of_compact_floor hfloor) x hx

end
end RiemannGaussian.MontgomeryTaylorSevenWindowModel
