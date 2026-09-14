/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovGaussianSpacing

/-!
# Explicit interval resonance for every actual shift set

The entire tuple-difference support lies in a proved monomial box. A
canonical selection includes all degrees with nonzero spacing whose whole
phase interval stays within half a period. The closed finite allowance
uses the Gaussian width where it improves the support count and pays every
other degree at full cost. This bound alone need not give a net saving.
-/

namespace RiemannGaussian.VinogradovIntervalResonance
noncomputable section
open scoped BigOperators
open VinogradovGaussianBounds VinogradovGaussianKernel
open VinogradovGaussianSpacing

/-- A symmetric integer box has its exact real cardinality. -/
theorem symmetric_box_card (H : ℕ) :
    ((Finset.Icc (-(H : ℤ)) (H : ℤ)).card : ℝ) = 2 * (H : ℝ) + 1 := by
  have h := Int.card_Icc_of_le (a := -(H : ℤ)) (b := H) (by omega)
  have hreal : ((Finset.Icc (-(H : ℤ)) (H : ℤ)).card : ℝ) = (H : ℝ) + 1 - (-(H : ℝ)) := by
    exact_mod_cast h
  linarith only [hreal]

/-- Every original tuple difference lies in its full monomial box, simultaneously in all degrees. -/
theorem actual_difference_in_box (k s Y : ℕ) (B : Finset ℕ)
    (hB : ∀ b ∈ B, b ≤ Y)
    {h : Fin k → ℤ} (hh : h ∈ VinogradovGaussianResonance.differenceSupport
      (VinogradovShiftedMoment.tupleFrequency s
        (fun b : B => VinogradovMeanValue.monomialFrequency k b.val))) :
    ∀ j, h j ∈ Finset.Icc (-((s * Y ^ (j.val + 1) : ℕ) : ℤ))
      ((s * Y ^ (j.val + 1) : ℕ) : ℤ) := by
  classical
  let : DecidableEq (Fin k → ℤ) := Classical.decEq _
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hh
  intro j
  have hbnd (f : Fin s → B) :
      0 ≤ ∑ i : Fin s, (f i).val ^ (j.val + 1) ∧
      (∑ i : Fin s, (f i).val ^ (j.val + 1)) ≤ s * Y ^ (j.val + 1) := by
    constructor
    · exact Nat.zero_le _
    · calc
        _ ≤ ∑ _i : Fin s, Y ^ (j.val + 1) :=
          Finset.sum_le_sum (fun i _ => Nat.pow_le_pow_left (hB (f i).val (f i).property) _)
        _ = _ := by simp
  have hf := hbnd p.1
  have hg := hbnd p.2
  have hf' : (∑ i : Fin s, ((p.1 i).val : ℤ) ^ (j.val + 1)) ≤ (s : ℤ) * (Y : ℤ) ^ (j.val + 1) := by
    exact_mod_cast hf.2
  have hg' : (∑ i : Fin s, ((p.2 i).val : ℤ) ^ (j.val + 1)) ≤ (s : ℤ) * (Y : ℤ) ^ (j.val + 1) := by
    exact_mod_cast hg.2
  have hf0 : 0 ≤ (∑ i : Fin s, ((p.1 i).val : ℤ) ^ (j.val + 1)) := by positivity
  have hg0 : 0 ≤ (∑ i : Fin s, ((p.2 i).val : ℤ) ^ (j.val + 1)) := by positivity
  simp only [Finset.mem_Icc, Pi.sub_apply, VinogradovShiftedMoment.tupleFrequency,
    Finset.sum_apply, VinogradovMeanValue.monomialFrequency, Nat.cast_mul, Nat.cast_pow]
  constructor <;> linarith only [hf', hg', hf0, hg0]

/-- The original positive shift set has an explicit resonance bound using any eligible selection of phase coordinates. -/
theorem actual_resonance_le_selected_widths (k s Y : ℕ) (B : Finset ℕ)
    (hB : ∀ b ∈ B, b ≤ Y) {a : Fin k → ℝ} (ha : ∀ j, 0 < a j)
    (gamma : Fin k → ℝ) (R : Finset (Fin k))
    (hgamma : ∀ j ∈ R, gamma j ≠ 0)
    (hphase : ∀ j ∈ R, |gamma j| * ((s : ℝ) * (Y : ℝ) ^ (j.val + 1)) ≤ 1 / 2) :
    resonanceEnvelope s a gamma (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) ≤
      ∏ j, (2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j)))) *
        if j ∈ R then min (2 * (s : ℝ) * (Y : ℝ) ^ (j.val + 1) + 1)
          (1 + Real.sqrt (a j) / |gamma j|)
        else (2 * (s : ℝ) * (Y : ℝ) ^ (j.val + 1) + 1) := by
  classical
  let S (j : Fin k) := Finset.Icc (-((s * Y ^ (j.val + 1) : ℕ) : ℤ))
    ((s * Y ^ (j.val + 1) : ℕ) : ℤ)
  have hsupp := fun h hh => actual_difference_in_box k s Y B hB (h := h) hh
  have hnowrap : ∀ j ∈ R, ∀ n ∈ S j, |gamma j * (n : ℝ)| ≤ 1 / 2 := by
    intro j hj n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    have hcast : |(n : ℝ)| ≤ (s : ℝ) * (Y : ℝ) ^ (j.val + 1) := by
      apply abs_le.mpr
      constructor
      · exact_mod_cast hlo
      · exact_mod_cast hhi
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hcast (abs_nonneg _)).trans (hphase j hj)
  have h := resonanceEnvelope_le_selected_widths s ha gamma
    (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) S R hsupp hgamma hnowrap
  have hcard (j : Fin k) : ((S j).card : ℝ) = 2 * (s : ℝ) * (Y : ℝ) ^ (j.val + 1) + 1 := by
    change ((Finset.Icc (-((s * Y ^ (j.val + 1) : ℕ) : ℤ))
      ((s * Y ^ (j.val + 1) : ℕ) : ℤ)).card : ℝ) = _
    rw [symmetric_box_card]
    push_cast
    ring
  simpa only [hcard] using h


/-- The full set of coordinates whose actual phase spacing is nonzero and whose whole difference interval stays within half a period. -/
def eligibleCoordinates {k : ℕ} (s Y : ℕ) (gamma : Fin k → ℝ) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun j => gamma j ≠ 0 ∧
    |gamma j| * ((s : ℝ) * (Y : ℝ) ^ (j.val + 1)) ≤ 1 / 2)

/-- A closed finite expression pays the better Gaussian width at every eligible actual coordinate, with all other coordinates included at full cost. -/
def intervalResonanceAllowance {k : ℕ} (s Y : ℕ) (a gamma : Fin k → ℝ) : ℝ := by
  classical
  exact ∏ j, (2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j)))) *
    if j ∈ eligibleCoordinates s Y gamma then
      min (2 * (s : ℝ) * (Y : ℝ) ^ (j.val + 1) + 1) (1 + Real.sqrt (a j) / |gamma j|)
    else (2 * (s : ℝ) * (Y : ℝ) ^ (j.val + 1) + 1)

/-- The actual attainable resonance sum has an explicit upper bound with no spacing hypothesis left to assume. -/
theorem actual_resonance_le_allowance (k s Y : ℕ) (B : Finset ℕ)
    (hB : ∀ b ∈ B, b ≤ Y) {a : Fin k → ℝ} (ha : ∀ j, 0 < a j) (gamma : Fin k → ℝ) :
    resonanceEnvelope s a gamma (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) ≤
      intervalResonanceAllowance s Y a gamma := by
  classical
  apply actual_resonance_le_selected_widths k s Y B hB ha gamma (eligibleCoordinates s Y gamma)
  · intro j hj
    exact (Finset.mem_filter.mp hj).2.1
  · intro j hj
    exact (Finset.mem_filter.mp hj).2.2

/-- Every interval allowance is nonnegative at positive Gaussian scales. -/
theorem intervalResonanceAllowance_nonneg {k : ℕ} (s Y : ℕ) {a : Fin k → ℝ}
    (ha : ∀ j, 0 < a j) (gamma : Fin k → ℝ) :
    0 ≤ intervalResonanceAllowance s Y a gamma := by
  classical
  apply Finset.prod_nonneg
  intro j _
  have hp : 0 ≤ 2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j))) :=
    div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (ha j).le _)
      (tail_denominator_pos (ha j)).le)
  apply mul_nonneg hp
  split_ifs <;> positivity

end
end RiemannGaussian.VinogradovIntervalResonance
