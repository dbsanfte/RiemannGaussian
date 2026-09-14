/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovResonanceWindow

/-!
# A power saving in the complete actual resonance product

For every k>=4 and all finite B contained in [0,M], the degree k-1 saves
two powers at t=M^(2k),z=M^4. All remaining degrees, translated tails and
moment-order constants are paid. The general all-eligible-degree bound
remains available; this theorem uses one degree to establish a net saving.
-/

namespace RiemannGaussian.VinogradovResonancePower
noncomputable section
open scoped BigOperators
open VinogradovGaussianBounds VinogradovGaussianKernel
open VinogradovIntervalResonance VinogradovResonanceScaling VinogradovResonanceWindow

/-- The full degree sum is exactly the two-family critical moment dimension. -/
theorem doubled_degree_sum (k : ℕ) : (∑ j : Fin k, 2 * (j.val + 1)) = k * (k + 1) := by
  change (∑ j : Fin k, (fun n : ℕ => 2 * (n + 1)) j.val) = _
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => 2 * (n + 1)) k]
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- The full coordinate support has its exact power cost before any eligible-degree saving. -/
theorem full_coordinate_power_le (r s : ℕ) (hr : 0 < r) {M : ℝ} (hM : 1 ≤ M) (q : ℕ) :
    (2 / ((reciprocalScale r M q) ^ (1 / 2 : ℝ) *
      (1 - Real.exp (-Real.pi / reciprocalScale r M q)))) *
      (2 * (s : ℝ) * M ^ q + 1) ≤
      ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) * (2 * (s : ℝ) + 1)) * M ^ (2 * q) := by
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    simpa using tail_denominator_pos (a := 1) zero_lt_one
  have hcard : 2 * (s : ℝ) * M ^ q + 1 ≤ (2 * (s : ℝ) + 1) * M ^ q := by
    nlinarith only [one_le_pow₀ (n := q) hM]
  calc
    _ ≤ ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) * M ^ q) *
        ((2 * (s : ℝ) + 1) * M ^ q) :=
      mul_le_mul (reciprocal_prefactor_le hr hM q) hcard (by positivity) (by positivity)
    _ = _ := by rw [show 2 * q = q + q by omega, pow_add]; ring

/-- At every degree at least four, the actual joint resonance saves two powers on all finite shift subsets at these power-related endpoints. -/
theorem exists_actual_resonance_power_saving (k r s : ℕ) (hk : 4 ≤ k) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → s ≤ M → ∀ B : Finset ℕ,
      (∀ b ∈ B, b ≤ M) →
      resonanceEnvelope s (fun j => reciprocalScale r M (j.val + 1))
        (VinogradovKorobovMoment.phaseCoefficients k ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4))
        (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) ≤
      C * (M : ℝ) ^ (k * (k + 1) - 2) := by
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
  let j₀ : Fin k := ⟨k - 2, by omega⟩
  have hwin : 2 * k < 3 * (j₀.val + 1) := by dsimp only [j₀]; omega
  let e (j : Fin k) := if j = j₀ then 4 * (j.val + 1) - 2 * k else 2 * (j.val + 1)
  have he (j : Fin k) : e j + (if j = j₀ then 2 else 0) = 2 * (j.val + 1) := by
    by_cases hj : j = j₀
    · subst j
      simp only [e, ite_true, j₀]
      omega
    · simp only [e, if_neg hj, add_zero]
  have hEsum : (∑ j : Fin k, e j) + 2 = k * (k + 1) := by
    calc
      _ = ∑ j : Fin k, (e j + (if j = j₀ then 2 else 0)) := by simp [Finset.sum_add_distrib]
      _ = ∑ j : Fin k, 2 * (j.val + 1) := Finset.sum_congr rfl (fun j _ => he j)
      _ = _ := doubled_degree_sum k
  have hE : (∑ j : Fin k, e j) = k * (k + 1) - 2 := by omega
  let a (j : Fin k) := reciprocalScale r (M : ℝ) (j.val + 1)
  let gamma := VinogradovKorobovMoment.phaseCoefficients k ((M : ℝ) ^ (2 * k)) ((M : ℝ) ^ 4)
  have ha (j : Fin k) : 0 < a j := reciprocalScale_pos hr hMpos _
  have hbound := actual_resonance_le_selected_widths k s M B hB ha gamma {j₀}
    (fun j _ => power_phase_nonzero k hMpos j)
    (by
      intro j hj
      have hj' : j = j₀ := Finset.mem_singleton.mp hj
      subst j
      exact power_phase_unwrapped k s hMr (by exact_mod_cast hsM) j₀ hwin)
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
        simp only [Finset.mem_singleton]
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
        by_cases hj : j = j₀
        · subst j
          rw [if_pos rfl]
          have hp : 0 ≤ 2 / ((a j₀) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j₀))) :=
            div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (ha j₀).le _)
              (tail_denominator_pos (ha j₀)).le)
          apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hp).trans
          apply (selected_coordinate_power_le k r hr hMr j₀ hwin.le).trans
          dsimp only [e, W]
          rw [if_pos rfl]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hG.le) (by positivity)
        · rw [if_neg hj]
          apply (full_coordinate_power_le r s hr hMr (j.val + 1)).trans
          dsimp only [e, W]
          rw [if_neg hj]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfull hG.le) (by positivity)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum, hE]

end
end RiemannGaussian.VinogradovResonancePower
