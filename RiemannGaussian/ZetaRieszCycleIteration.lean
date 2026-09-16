/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCycleCore
import RiemannGaussian.ZetaRieszTransportSource

/-!
# Exact cancellations across the whole original band

Exact zero cycles remove supported portions of original amplitudes and
retain every remainder. Nearby opposite phases have quadratic extra mass
cost, but sufficient aggregate arithmetic capacity at source scale remains
unproved. This is not a new zero-free region or an RH proof.
-/

namespace RiemannGaussian.ZetaRieszCycleIteration
noncomputable section
open scoped BigOperators Classical
open ZetaRieszCycleCore

/-- Distinct original labels in one cancellation cycle. -/
def distinctTriple (e : ℕ × ℕ × ℕ) : Prop :=
  e.1 ≠ e.2.1 ∧ e.1 ≠ e.2.2 ∧ e.2.1 ≠ e.2.2

/-- The supported fraction removed from each original label. -/
def removedFraction (f : ℕ → ℂ) (e : ℕ × ℕ × ℕ) (n : ℕ) : ℝ :=
  let z := f e.1
  let w := f e.2.1
  let v := f e.2.2
  let q := cycleScale z w v
  if n = e.1 then q * area w v
  else if n = e.2.1 then q * area v z
  else if n = e.2.2 then q * area z w
  else 0

/-- The actual removal fraction is always supported by the available mass. -/
theorem removedFraction_bounds (f : ℕ → ℂ) (e : ℕ × ℕ × ℕ) (n : ℕ) :
    0 ≤ removedFraction f e n ∧ removedFraction f e n ≤ 1 := by
  obtain ⟨ha, ha1, hb, hb1, hc, hc1⟩ := cycleScale_bounds (f e.1) (f e.2.1) (f e.2.2)
  unfold removedFraction
  split_ifs
  · exact ⟨ha, ha1⟩
  · exact ⟨hb, hb1⟩
  · exact ⟨hc, hc1⟩
  · norm_num

/-- One exact cycle preserves each unused amplitude's original direction. -/
def cycleStep (f : ℕ → ℂ) (e : ℕ × ℕ × ℕ) (n : ℕ) : ℂ :=
  (1 - removedFraction f e n) • f n

/-- No original amplitude grows during an exact zero-cycle step. -/
theorem norm_cycleStep_le (f : ℕ → ℂ) (e : ℕ × ℕ × ℕ) (n : ℕ) :
    ‖cycleStep f e n‖ ≤ ‖f n‖ := by
  obtain ⟨h0, h1⟩ := removedFraction_bounds f e n
  rw [cycleStep, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr h1)]
  nlinarith [norm_nonneg (f n)]

/-- The retained norm is exactly the unsent fraction of the old norm. -/
theorem norm_cycleStep_eq (f : ℕ → ℂ) (e : ℕ × ℕ × ℕ) (n : ℕ) :
    ‖cycleStep f e n‖ = ‖f n‖ - removedFraction f e n * ‖f n‖ := by
  rw [cycleStep, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr (removedFraction_bounds f e n).2)]
  ring

/-- Distinct labels turn the finite mask into three exact additive fibres. -/
theorem removedFraction_eq_add (f : ℕ → ℂ) {e : ℕ × ℕ × ℕ} (he : distinctTriple e) (n : ℕ) :
    removedFraction f e n =
      (if n = e.1 then cycleScale (f e.1) (f e.2.1) (f e.2.2) * area (f e.2.1) (f e.2.2) else 0) +
      (if n = e.2.1 then cycleScale (f e.1) (f e.2.1) (f e.2.2) * area (f e.2.2) (f e.1) else 0) +
      (if n = e.2.2 then cycleScale (f e.1) (f e.2.1) (f e.2.2) * area (f e.1) (f e.2.1) else 0) := by
  obtain ⟨hij, hik, hjk⟩ := he
  by_cases hi : n = e.1
  · subst n
    simp [removedFraction, hij, hik]
  · by_cases hj : n = e.2.1
    · subst n
      simp [removedFraction, hi, hjk]
    · simp [removedFraction, hi, hj]

/-- The complete amount removed from the original complex sum is zero. -/
theorem sum_removed_eq_zero (S : Finset ℕ) (f : ℕ → ℂ) {e : ℕ × ℕ × ℕ}
    (hi : e.1 ∈ S) (hj : e.2.1 ∈ S) (hk : e.2.2 ∈ S) (he : distinctTriple e) :
    (∑ n ∈ S, removedFraction f e n • f n) = 0 := by
  simp_rw [removedFraction_eq_add f he]
  simp only [add_smul, ite_smul, zero_smul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', if_pos hi, if_pos hj, if_pos hk]
  exact sent_cycle_eq_zero _ _ _

/-- Every original summand is accounted for after the exact cycle. -/
theorem sum_cycleStep (S : Finset ℕ) (f : ℕ → ℂ) {e : ℕ × ℕ × ℕ}
    (hi : e.1 ∈ S) (hj : e.2.1 ∈ S) (hk : e.2.2 ∈ S) (he : distinctTriple e) :
    (∑ n ∈ S, cycleStep f e n) = ∑ n ∈ S, f n := by
  simp only [cycleStep, sub_smul, one_smul, Finset.sum_sub_distrib,
    sum_removed_eq_zero S f hi hj hk he, sub_zero]

/-- The entire original absolute budget loses the exact cycle saving. -/
theorem mass_cycleStep (S : Finset ℕ) (f : ℕ → ℂ) {e : ℕ × ℕ × ℕ}
    (hi : e.1 ∈ S) (hj : e.2.1 ∈ S) (hk : e.2.2 ∈ S) (he : distinctTriple e) :
    (∑ n ∈ S, ‖cycleStep f e n‖) = (∑ n ∈ S, ‖f n‖) -
      cycleSaving (f e.1) (f e.2.1) (f e.2.2) := by
  simp_rw [norm_cycleStep_eq]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp_rw [removedFraction_eq_add f he]
  simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', if_pos hi, if_pos hj, if_pos hk]
  unfold cycleSaving
  ring

/-- An exact three-direction cancellation improves the bound on the
whole original support, including every unselected term. -/
theorem norm_sum_le_cycle_saving (S : Finset ℕ) (f : ℕ → ℂ) {e : ℕ × ℕ × ℕ}
    (hi : e.1 ∈ S) (hj : e.2.1 ∈ S) (hk : e.2.2 ∈ S) (he : distinctTriple e) :
    ‖∑ n ∈ S, f n‖ ≤ (∑ n ∈ S, ‖f n‖) - cycleSaving (f e.1) (f e.2.1) (f e.2.2) := by
  rw [← mass_cycleStep S f hi hj hk he, ← sum_cycleStep S f hi hj hk he]
  exact norm_sum_le _ _

/-- The remaining original amplitudes after a sequence of exact cycles. -/
def cycleResidual (f : ℕ → ℂ) : List (ℕ × ℕ × ℕ) → ℕ → ℂ
  | [] => f
  | e :: es => cycleResidual (cycleStep f e) es

/-- The complete mass cancelled exactly by all successive cycles. -/
def totalSaving (f : ℕ → ℂ) : List (ℕ × ℕ × ℕ) → ℝ
  | [] => 0
  | e :: es => cycleSaving (f e.1) (f e.2.1) (f e.2.2) + totalSaving (cycleStep f e) es

/-- The full cycle budget is nonnegative for every actual complex input. -/
theorem totalSaving_nonneg (f : ℕ → ℂ) (es : List (ℕ × ℕ × ℕ)) :
    0 ≤ totalSaving f es := by
  induction es generalizing f with
  | nil => exact le_refl _
  | cons e es ih => exact add_nonneg (cycleSaving_nonneg _ _ _) (ih _)

/-- Every residual original label remains dominated by its initial amplitude. -/
theorem norm_cycleResidual_le (f : ℕ → ℂ) (es : List (ℕ × ℕ × ℕ)) (n : ℕ) :
    ‖cycleResidual f es n‖ ≤ ‖f n‖ := by
  induction es generalizing f with
  | nil => exact le_refl _
  | cons e es ih => exact (ih _).trans (norm_cycleStep_le f e n)

/-- Every complex term in the original carrier survives the exact-cycle
bookkeeping, even when different cycles share original indices. -/
theorem sum_cycleResidual (S : Finset ℕ) (f : ℕ → ℂ) (es : List (ℕ × ℕ × ℕ))
    (he : ∀ e ∈ es, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.2.2 ∈ S ∧ distinctTriple e) :
    (∑ n ∈ S, cycleResidual f es n) = ∑ n ∈ S, f n := by
  induction es generalizing f with
  | nil => rfl
  | cons e es ih =>
    have h := he e (List.mem_cons_self ..)
    exact (ih _ (fun a ha => he a (List.mem_cons_of_mem _ ha))).trans
      (sum_cycleStep S f h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- All exact removals accumulate without any approximation-cost term. -/
theorem mass_cycleResidual (S : Finset ℕ) (f : ℕ → ℂ) (es : List (ℕ × ℕ × ℕ))
    (he : ∀ e ∈ es, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.2.2 ∈ S ∧ distinctTriple e) :
    (∑ n ∈ S, ‖cycleResidual f es n‖) = (∑ n ∈ S, ‖f n‖) - totalSaving f es := by
  induction es generalizing f with
  | nil => simp [cycleResidual, totalSaving]
  | cons e es ih =>
    have h := he e (List.mem_cons_self ..)
    change (∑ n ∈ S, ‖cycleResidual (cycleStep f e) es n‖) = _
    rw [ih _ (fun a ha => he a (List.mem_cons_of_mem _ ha)),
      mass_cycleStep S f h.1 h.2.1 h.2.2.1 h.2.2.2]
    simp only [totalSaving]
    ring

/-- The whole original sum is bounded by its initial mass minus the
complete exact-cycle saving, with no independent cancellation assumption. -/
theorem norm_sum_le_total_saving (S : Finset ℕ) (f : ℕ → ℂ) (es : List (ℕ × ℕ × ℕ))
    (he : ∀ e ∈ es, e.1 ∈ S ∧ e.2.1 ∈ S ∧ e.2.2 ∈ S ∧ distinctTriple e) :
    ‖∑ n ∈ S, f n‖ ≤ (∑ n ∈ S, ‖f n‖) - totalSaving f es := by
  rw [← mass_cycleResidual S f es he, ← sum_cycleResidual S f es he]
  exact norm_sum_le _ _

/-- Every ordered distinct triple of original band labels is available;
its positive-area test is evaluated inside the proved cycle scale. -/
@[irreducible] def actualCycles (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (zetaPrimeLogBand N ×ˢ (zetaPrimeLogBand N ×ˢ zetaPrimeLogBand N)).filter distinctTriple

/-- The literal candidate construction discharges all support obligations. -/
theorem actualCycles_valid {N : ℕ} {e : ℕ × ℕ × ℕ} (he : e ∈ actualCycles N) :
    e.1 ∈ zetaPrimeLogBand N ∧ e.2.1 ∈ zetaPrimeLogBand N ∧
      e.2.2 ∈ zetaPrimeLogBand N ∧ distinctTriple e := by
  simp only [actualCycles, Finset.mem_filter, Finset.mem_product] at he
  exact ⟨he.1.1, he.1.2.1, he.1.2.2, he.2⟩

/-- The fully specified exact-cycle construction bounds the entire
original Riesz carrier, retaining its full polynomial and every remainder.
The amount of saving at source scale remains an arithmetic obligation. -/
theorem norm_actual_band_le_exact_cycles (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ) :
    ‖zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t‖ ≤
      (∑ n ∈ zetaPrimeLogBand N, ‖ZetaRieszConditionedEnergy.bandWeight L P N t n‖) -
        totalSaving (ZetaRieszConditionedEnergy.bandWeight L P N t) (actualCycles N).toList := by
  have hs : (∑ n ∈ zetaPrimeLogBand N, ZetaRieszConditionedEnergy.bandWeight L P N t n) =
      zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N t := by
    unfold ZetaRieszConditionedEnergy.bandWeight zetaArithmeticBand
    exact Finset.sum_congr rfl (fun n hn => by rw [if_pos hn])
  rw [← hs]
  exact norm_sum_le_total_saving _ _ _ (fun _ he => actualCycles_valid (Finset.mem_toList.mp he))
end
end RiemannGaussian.ZetaRieszCycleIteration
