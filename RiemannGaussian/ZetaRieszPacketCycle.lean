/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszArithmeticCycles

/-!
# Exact cancellation of complete signed packets

The complete complex filter, arithmetic support and signed responses remain
explicit. These finite identities and bounds do not prove sufficient
aggregate control at source scale or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszPacketCycle
noncomputable section
open scoped BigOperators Classical
open ZetaRieszCycleCore ZetaRieszCycleIteration ZetaRieszCycleCorrelation
open ZetaRieszMassTransport ZetaRieszRetainedFraction ZetaRieszConditionedEnergy

/-- The signed determinant remains additive on a complete left packet. -/
theorem area_sum_left (A : Finset ℕ) (f : ℕ → ℂ) (z : ℂ) :
    area (∑ n ∈ A, f n) z = ∑ n ∈ A, area (f n) z := by
  simp only [area, Complex.re_sum, Complex.im_sum, Finset.sum_mul, Finset.sum_sub_distrib]

/-- The signed determinant remains additive on a complete right packet. -/
theorem area_sum_right (A : Finset ℕ) (f : ℕ → ℂ) (z : ℂ) :
    area z (∑ n ∈ A, f n) = ∑ n ∈ A, area z (f n) := by
  simp only [area, Complex.re_sum, Complex.im_sum, Finset.mul_sum, Finset.sum_sub_distrib]

/-- Packet orientation retains the entire signed two-packet correlation. -/
theorem area_packet_expansion (A B : Finset ℕ) (f : ℕ → ℂ) :
    area (∑ i ∈ A, f i) (∑ j ∈ B, f j) =
      ∑ i ∈ A, ∑ j ∈ B, area (f i) (f j) := by
  rw [area_sum_left]
  exact Finset.sum_congr rfl (fun _ _ => area_sum_right _ _ _)

/-- An oriented projection is no larger than the full complex norm. -/
theorem abs_area_le_norm_mul (z w : ℂ) : |area z w| ≤ ‖z‖ * ‖w‖ := by
  rw [area_eq_im_conj_mul]
  simpa only [norm_mul, Complex.norm_conj] using Complex.abs_im_le_norm (starRingEnd ℂ z * w)

/-- A complete signed projection lower bound controls packet mass. -/
theorem projection_sum_le_norm (A : Finset ℕ) (f : ℕ → ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∑ n ∈ A, area z (f n)) ≤ ‖∑ n ∈ A, f n‖ := by
  rw [← area_sum_right]
  exact (le_abs_self _).trans ((abs_area_le_norm_mul _ _).trans
    (by nlinarith [norm_nonneg (∑ n ∈ A, f n)]))

/-- Uniform fractions remove whole packets while retaining their original atoms. -/
def packetFraction (f : ℕ → ℂ) (A B C : Finset ℕ) (n : ℕ) : ℝ :=
  let z := ∑ i ∈ A, f i
  let w := ∑ i ∈ B, f i
  let v := ∑ i ∈ C, f i
  let q := cycleScale z w v
  if n ∈ A then q * area w v
  else if n ∈ B then q * area v z
  else if n ∈ C then q * area z w
  else 0

/-- Every packet removal is supported, even when its area test fails. -/
theorem packetFraction_bounds (f : ℕ → ℂ) (A B C : Finset ℕ) (n : ℕ) :
    0 ≤ packetFraction f A B C n ∧ packetFraction f A B C n ≤ 1 := by
  obtain ⟨ha, ha1, hb, hb1, hc, hc1⟩ := cycleScale_bounds
    (∑ i ∈ A, f i) (∑ i ∈ B, f i) (∑ i ∈ C, f i)
  unfold packetFraction
  split_ifs
  · exact ⟨ha, ha1⟩
  · exact ⟨hb, hb1⟩
  · exact ⟨hc, hc1⟩
  · norm_num

/-- Three disjoint original packets split the removal mask exactly. -/
theorem packetFraction_eq_add (f : ℕ → ℂ) {A B C : Finset ℕ}
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (n : ℕ) :
    packetFraction f A B C n =
      (if n ∈ A then cycleScale (∑ i ∈ A, f i) (∑ i ∈ B, f i) (∑ i ∈ C, f i) *
        area (∑ i ∈ B, f i) (∑ i ∈ C, f i) else 0) +
      (if n ∈ B then cycleScale (∑ i ∈ A, f i) (∑ i ∈ B, f i) (∑ i ∈ C, f i) *
        area (∑ i ∈ C, f i) (∑ i ∈ A, f i) else 0) +
      (if n ∈ C then cycleScale (∑ i ∈ A, f i) (∑ i ∈ B, f i) (∑ i ∈ C, f i) *
        area (∑ i ∈ A, f i) (∑ i ∈ B, f i) else 0) := by
  by_cases ha : n ∈ A
  · have hb := Finset.disjoint_left.mp hAB ha
    have hc := Finset.disjoint_left.mp hAC ha
    simp [packetFraction, ha, hb, hc]
  · by_cases hb : n ∈ B
    · have hc := Finset.disjoint_left.mp hBC hb
      simp [packetFraction, ha, hb, hc]
    · simp [packetFraction, ha, hb]

/-- A supported constant mask sums to its literal original packet. -/
theorem sum_packet_mask (S A : Finset ℕ) (hA : A ⊆ S) (c : ℝ) (f : ℕ → ℂ) :
    (∑ n ∈ S, if n ∈ A then c • f n else 0) = c • ∑ n ∈ A, f n := by
  have hs := Finset.sum_subset hA
    (f := fun n => if n ∈ A then c • f n else 0) (fun n _ hn => by simp [hn])
  rw [← hs]
  simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.smul_sum]

/-- Complete packet removals cancel exactly, with all inner phases retained. -/
theorem sum_packet_removed_zero (S : Finset ℕ) (f : ℕ → ℂ) {A B C : Finset ℕ}
    (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (∑ n ∈ S, packetFraction f A B C n • f n) = 0 := by
  simp_rw [packetFraction_eq_add f hAB hAC hBC]
  simp only [add_smul, ite_smul, zero_smul, Finset.sum_add_distrib]
  rw [sum_packet_mask S A hA, sum_packet_mask S B hB, sum_packet_mask S C hC]
  exact sent_cycle_eq_zero _ _ _

/-- The remaining original atom after one complete packet cancellation. -/
def packetStep (f : ℕ → ℂ) (A B C : Finset ℕ) (n : ℕ) : ℂ :=
  (1 - packetFraction f A B C n) • f n

/-- Every original atom keeps its direction and loses exactly its spent mass. -/
theorem norm_packetStep_eq (f : ℕ → ℂ) (A B C : Finset ℕ) (n : ℕ) :
    ‖packetStep f A B C n‖ = ‖f n‖ - packetFraction f A B C n * ‖f n‖ := by
  rw [packetStep, norm_smul,
    Real.norm_of_nonneg (sub_nonneg.mpr (packetFraction_bounds f A B C n).2)]
  ring

/-- Grouping original terms before cancellation retains the whole signed sum. -/
theorem sum_packetStep (S : Finset ℕ) (f : ℕ → ℂ) {A B C : Finset ℕ}
    (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    (∑ n ∈ S, packetStep f A B C n) = ∑ n ∈ S, f n := by
  simp only [packetStep, sub_smul, one_smul, Finset.sum_sub_distrib,
    sum_packet_removed_zero S f hA hB hC hAB hAC hBC, sub_zero]

/-- The exact mass saving of a complete packet cycle. -/
def packetSaving (S : Finset ℕ) (f : ℕ → ℂ) (A B C : Finset ℕ) : ℝ :=
  ∑ n ∈ S, packetFraction f A B C n * ‖f n‖

/-- The full mass saving is nonnegative without any aggregate sign premise. -/
theorem packetSaving_nonneg (S : Finset ℕ) (f : ℕ → ℂ) (A B C : Finset ℕ) :
    0 ≤ packetSaving S f A B C := by
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg (packetFraction_bounds f A B C n).1 (norm_nonneg _)

/-- The original absolute mass pays exactly for the grouped cancellation. -/
theorem mass_packetStep (S : Finset ℕ) (f : ℕ → ℂ) (A B C : Finset ℕ) :
    (∑ n ∈ S, ‖packetStep f A B C n‖) =
      (∑ n ∈ S, ‖f n‖) - packetSaving S f A B C := by
  simp only [norm_packetStep_eq, packetSaving, Finset.sum_sub_distrib]

/-- The complete original carrier receives the exact grouped saving. -/
theorem norm_sum_le_packet_saving (S : Finset ℕ) (f : ℕ → ℂ) {A B C : Finset ℕ}
    (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    ‖∑ n ∈ S, f n‖ ≤ (∑ n ∈ S, ‖f n‖) - packetSaving S f A B C := by
  rw [← mass_packetStep, ← sum_packetStep S f hA hB hC hAB hAC hBC]
  exact norm_sum_le _ _

/-- Full filter phases and all signed cross terms control actual packet orientation. -/
theorem area_actual_packets (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (A B : Finset ℕ) :
    area (∑ i ∈ A, bandWeight L P N t i) (∑ j ∈ B, bandWeight L P N t j) =
      ∑ i ∈ A, ∑ j ∈ B,
        (((starRingEnd ℂ (bandWeight L P N 0 i)) * bandWeight L P N 0 j).re *
          Real.sin (t * (Real.log i - Real.log j)) +
         ((starRingEnd ℂ (bandWeight L P N 0 i)) * bandWeight L P N 0 j).im *
          Real.cos (t * (Real.log i - Real.log j))) := by
  rw [area_packet_expansion]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => area_actual_full ..))

/-- A real supported mask pays exactly its complete original packet mass. -/
theorem sum_packet_real_mask (S A : Finset ℕ) (hA : A ⊆ S) (c : ℝ) (f : ℕ → ℝ) :
    (∑ n ∈ S, if n ∈ A then c * f n else 0) = c * ∑ n ∈ A, f n := by
  have hs := Finset.sum_subset hA
    (f := fun n => if n ∈ A then c * f n else 0) (fun n _ hn => by simp [hn])
  rw [← hs]
  simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.mul_sum]

/-- Packet saving uses the sum of every original mass, not merely the
norm of each compressed complex sum. -/
theorem packetSaving_eq (S : Finset ℕ) (f : ℕ → ℂ) {A B C : Finset ℕ}
    (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    let z := ∑ i ∈ A, f i
    let w := ∑ i ∈ B, f i
    let v := ∑ i ∈ C, f i
    packetSaving S f A B C =
      cycleScale z w v * area w v * (∑ i ∈ A, ‖f i‖) +
      cycleScale z w v * area v z * (∑ i ∈ B, ‖f i‖) +
      cycleScale z w v * area z w * (∑ i ∈ C, ‖f i‖) := by
  dsimp only
  unfold packetSaving
  simp_rw [packetFraction_eq_add f hAB hAC hBC]
  simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
  rw [sum_packet_real_mask S A hA, sum_packet_real_mask S B hB, sum_packet_real_mask S C hC]

/-- The original mass saving dominates the exact saving of the three
compressed sums; no internal packet cancellation is charged as an error. -/
theorem cycleSaving_le_packetSaving (S : Finset ℕ) (f : ℕ → ℂ) {A B C : Finset ℕ}
    (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    cycleSaving (∑ i ∈ A, f i) (∑ i ∈ B, f i) (∑ i ∈ C, f i) ≤
      packetSaving S f A B C := by
  obtain ⟨ha, _, hb, _, hc, _⟩ := cycleScale_bounds
    (∑ i ∈ A, f i) (∑ i ∈ B, f i) (∑ i ∈ C, f i)
  rw [packetSaving_eq S f hA hB hC hAB hAC hBC]
  unfold cycleSaving
  calc
    _ = _ := mul_add _ _ _
    _ ≤ _ := by
      rw [mul_add]
      simpa only [mul_assoc] using add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left (norm_sum_le A f) ha)
          (mul_le_mul_of_nonneg_left (norm_sum_le B f) hb))
        (mul_le_mul_of_nonneg_left (norm_sum_le C f) hc)

/-- Three aggregate masses support the exact cancellation independently
of how many original terms supply each packet. -/
theorem twice_min_packet_mass_le_saving (S : Finset ℕ) (f : ℕ → ℂ) {A B C : Finset ℕ}
    (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hp : positiveCycle (∑ i ∈ A, f i) (∑ i ∈ B, f i) (∑ i ∈ C, f i)) :
    2 * min ‖∑ i ∈ A, f i‖ (min ‖∑ i ∈ B, f i‖ ‖∑ i ∈ C, f i‖) ≤
      packetSaving S f A B C := by
  exact (ZetaRieszCycleSaving.twice_min_norm_le_cycleSaving hp).trans
    (cycleSaving_le_packetSaving S f hA hB hC hAB hAC hBC)

end
end RiemannGaussian.ZetaRieszPacketCycle
