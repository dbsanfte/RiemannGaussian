/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDegreeWindow

/-!
# The full actual Gaussian resonance uses every eligible degree

The actual full difference support is bounded through every unwrapped degree
simultaneously. All other coordinates and every translated Gaussian tail
retain their full costs. The upstream signed fibre identities are unchanged.
-/

namespace RiemannGaussian.VinogradovFullResonance
noncomputable section
open scoped BigOperators
open VinogradovDegreeWindow
open VinogradovGaussianBounds VinogradovGaussianKernel VinogradovIntervalResonance
open VinogradovResonanceScaling VinogradovResonanceWindow VinogradovResonancePower

/-- The complete actual resonance product receives the quadratic gain of every eligible degree simultaneously. -/
theorem exists_full_resonance_power_saving (k r s : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → s ≤ M → ∀ B : Finset ℕ,
      (∀ b ∈ B, b ≤ M) →
      resonanceEnvelope s (fun j => reciprocalScale r M (j.val + 1))
        (VinogradovKorobovMoment.phaseCoefficients k ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4))
        (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) ≤
      C * (M : ℝ) ^ (k * (k + 1) - windowSaving k) := by
  classical
  let G := 2 * (r : ℝ) / (1 - Real.exp (-Real.pi))
  let F := 2 * (s : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ)
  let W := G * F
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    simpa using tail_denominator_pos (a := 1) zero_lt_one
  have hG : 0 < G := by dsimp only [G]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  have hW : 0 < W := mul_pos hG hF
  refine ⟨W ^ k, pow_pos hW _, ?_⟩
  intro M hM hsM B hB
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := zero_lt_one.trans_le hMr
  let R : Finset (Fin k) := Finset.univ.filter (fun j => 2 * k < 3 * (j.val + 1))
  let e (j : Fin k) := if 2 * k < 3 * (j.val + 1) then 4 * (j.val + 1) - 2 * k else 2 * (j.val + 1)
  have he (j : Fin k) : e j + (if 2 * k < 3 * (j.val + 1) then 2 * (k - (j.val + 1)) else 0) =
      2 * (j.val + 1) := by
    by_cases hj : 2 * k < 3 * (j.val + 1)
    · simp only [e, if_pos hj]
      have hq := j.isLt
      omega
    · simp only [e, if_neg hj, add_zero]
  have hEsum : (∑ j : Fin k, e j) + windowSaving k = k * (k + 1) := by
    calc
      _ = ∑ j : Fin k, (e j + (if 2 * k < 3 * (j.val + 1) then 2 * (k - (j.val + 1)) else 0)) := by
        rw [Finset.sum_add_distrib]
        rfl
      _ = ∑ j : Fin k, 2 * (j.val + 1) := Finset.sum_congr rfl (fun j _ => he j)
      _ = _ := doubled_degree_sum k
  have hE : (∑ j : Fin k, e j) = k * (k + 1) - windowSaving k := by omega
  let a (j : Fin k) := reciprocalScale r (M : ℝ) (j.val + 1)
  let gamma := VinogradovKorobovMoment.phaseCoefficients k ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4)
  have ha (j : Fin k) : 0 < a j := reciprocalScale_pos hr hMpos _
  have hbound := actual_resonance_le_selected_widths k s M B hB ha gamma R
    (fun j _ => power_phase_nonzero k hMpos j)
    (by
      intro j hj
      exact power_phase_unwrapped k s hMr (by exact_mod_cast hsM) j (Finset.mem_filter.mp hj).2)
  apply hbound.trans
  calc
    _ ≤ ∏ j : Fin k, W * (M : ℝ) ^ (e j) := by
      apply Finset.prod_le_prod
      · intro j _
        have hp : 0 ≤ 2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j))) :=
          div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (ha j).le _)
            (tail_denominator_pos (ha j)).le)
        apply mul_nonneg hp
        split_ifs <;> positivity
      · intro j _
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        have hq : ((j.val : ℝ) + 1) ≤ k := by exact_mod_cast j.isLt
        have hsmall : 1 + 2 * Real.pi * (j.val + 1) / (r : ℝ) ≤ F := by
          have hmul := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 2 * Real.pi))
            (Nat.cast_nonneg r)
          dsimp only [F]
          linarith only [hmul, Nat.cast_nonneg (α := ℝ) s]
        have hfull : 2 * (s : ℝ) + 1 ≤ F := by
          have hpos : 0 ≤ 2 * Real.pi * (k : ℝ) / (r : ℝ) := by positivity
          dsimp only [F]
          linarith only [hpos]
        by_cases hj : 2 * k < 3 * (j.val + 1)
        · rw [if_pos hj]
          have hp : 0 ≤ 2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j))) :=
            div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (ha j).le _)
              (tail_denominator_pos (ha j)).le)
          apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hp).trans
          apply (selected_coordinate_power_le k r hr hMr j hj.le).trans
          dsimp only [e, W]
          rw [if_pos hj]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hG.le) (by positivity)
        · rw [if_neg hj]
          apply (full_coordinate_power_le r s hr hMr (j.val + 1)).trans
          dsimp only [e, W]
          rw [if_neg hj]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfull hG.le) (by positivity)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum, hE]

end
end RiemannGaussian.VinogradovFullResonance
