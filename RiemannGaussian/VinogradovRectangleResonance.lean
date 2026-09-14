/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDegreeWindow
import RiemannGaussian.VinogradovPhaseRectangle

/-!
# Full Gaussian resonance savings throughout a continuous height rectangle

The complete actual difference resonance is bounded uniformly for
M^(2k-2) <= t <= M^(2k) and M^4 <= z <= 4*M^4. The exact selected-degree
gain is quadratic. Every reciprocal-scale prefactor is explicitly paid.
-/

namespace RiemannGaussian.VinogradovRectangleResonance
noncomputable section
open scoped BigOperators
open VinogradovDegreeWindow VinogradovPhaseRectangle
open VinogradovGaussianBounds VinogradovGaussianKernel VinogradovIntervalResonance
open VinogradovResonanceScaling VinogradovResonanceWindow VinogradovResonancePower

/-- Each useful degree keeps its power saving across a full height-exponent interval and a fourfold continuous base interval. -/
theorem rectangle_coordinate_power_le (k r : ℕ) (hr : 0 < r) {M t z : ℝ}
    (hM : 1 ≤ M) (htlo : M ^ (2 * k - 2) ≤ t) (hthi : t ≤ M ^ (2 * k))
    (hzlo : M ^ 4 ≤ z) (hzhi : z ≤ 4 * M ^ 4)
    (j : Fin k) (hwindow : 2 * k ≤ 3 * (j.val + 1)) :
    (2 / ((reciprocalScale r M (j.val + 1)) ^ (1 / 2 : ℝ) *
      (1 - Real.exp (-Real.pi / reciprocalScale r M (j.val + 1))))) *
      (1 + Real.sqrt (reciprocalScale r M (j.val + 1)) /
        |VinogradovKorobovMoment.phaseCoefficients k t z j|) ≤
    ((4 : ℝ) ^ (j.val + 1) * ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
      (1 + 2 * Real.pi * (j.val + 1) / (r : ℝ)))) * M ^ (4 * (j.val + 1) - 2 * k + 2) := by
  have hMpos := zero_lt_one.trans_le hM
  let a := reciprocalScale r M (j.val + 1)
  have ha : 0 < a := reciprocalScale_pos hr hMpos _
  have hP : 0 ≤ 2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a))) :=
    div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg ha.le _) (tail_denominator_pos ha).le)
  have hwidth := power_rectangle_width_le k (a := a) hMpos (by norm_num : (0 : ℝ) < 4)
    htlo hthi hzlo hzhi j
  have hfactor : 1 ≤ (4 : ℝ) ^ (j.val + 1) * M ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hM)
  have hsmall : 1 + Real.sqrt a / |VinogradovKorobovMoment.phaseCoefficients k t z j| ≤
      ((4 : ℝ) ^ (j.val + 1) * M ^ 2) *
        (1 + Real.sqrt a / |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j|) := by
    nlinarith only [hwidth, hfactor]
  calc
    _ ≤ (2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
        (((4 : ℝ) ^ (j.val + 1) * M ^ 2) *
          (1 + Real.sqrt a / |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j|)) :=
      mul_le_mul_of_nonneg_left hsmall hP
    _ = ((4 : ℝ) ^ (j.val + 1) * M ^ 2) *
        ((2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
          (1 + Real.sqrt a / |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j|)) := by ring
    _ ≤ ((4 : ℝ) ^ (j.val + 1) * M ^ 2) *
        (((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
          (1 + 2 * Real.pi * (j.val + 1) / (r : ℝ))) * M ^ (4 * (j.val + 1) - 2 * k)) :=
      mul_le_mul_of_nonneg_left (selected_coordinate_power_le k r hr hM j hwindow) (by positivity)
    _ = _ := by rw [pow_add]; ring

/-- The complete retained gain after the full height interval costs two powers in each selected degree. -/
def rectangleSaving (k : ℕ) : ℕ :=
  ∑ j : Fin k, if 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k then
    2 * (k - (j.val + 1 + 1)) else 0

/-- The continuous rectangle still has an exact quadratic full-window gain. -/
theorem rectangleSaving_eq (k : ℕ) :
    rectangleSaving k = (k - 2 * k / 3 - 1) * (k - 2 * k / 3 - 2) := by
  classical
  unfold rectangleSaving
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if 2 * k < 3 * (j + 1) ∧ j + 1 < k then 2 * (k - (j + 1 + 1)) else 0) k,
    ← Finset.sum_filter]
  have hset : (Finset.range k).filter (fun j => 2 * k < 3 * (j + 1) ∧ j + 1 < k) =
      Finset.Ico (2 * k / 3) (k - 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  have he (j : ℕ) : 2 * (k - (2 * k / 3 + j + 1 + 1)) =
      2 * ((k - 1 - 2 * k / 3) - (j + 1)) := by omega
  simp_rw [he]
  rw [descending_gain_sum]
  congr 1 <;> omega

/-- The full rectangle window saves a quadratic number of powers at every degree at least twelve. -/
theorem square_le_twentyfour_rectangleSaving (k : ℕ) (hk : 12 ≤ k) :
    k ^ 2 ≤ 24 * rectangleSaving k := by
  rw [rectangleSaving_eq]
  have h4 : k ≤ 4 * (k - 2 * k / 3 - 1) := by omega
  have h6 : k ≤ 6 * (k - 2 * k / 3 - 2) := by omega
  have h := Nat.mul_le_mul h4 h6
  nlinarith only [h]

/-- Paying both half-epsilon moments preserves a quadratic rectangle saving. -/
theorem square_le_thirtytwo_net_rectangleSaving (k : ℕ) (hk : 12 ≤ k) :
    k ^ 2 ≤ 32 * (rectangleSaving k - 1) := by
  have hquad := square_le_twentyfour_rectangleSaving k hk
  have hm : 3 ≤ k - 2 * k / 3 - 1 := by omega
  have hsmall : 4 ≤ rectangleSaving k := by
    rw [rectangleSaving_eq]
    have hprod := Nat.mul_le_mul hm (show 2 ≤ k - 2 * k / 3 - 2 by omega)
    omega
  omega

/-- The complete actual resonance product receives the quadratic gain of every eligible degree simultaneously. -/
theorem actual_resonance_le_explicit (k r s : ℕ) (hr : 0 < r) :
    ∀ M : ℕ, 1 ≤ M → s ≤ M → ∀ t z : ℝ,
      (M : ℝ) ^ (2 * k - 2) ≤ t → t ≤ (M : ℝ) ^ (2 * k) →
      (M : ℝ) ^ 4 ≤ z → z ≤ 4 * (M : ℝ) ^ 4 → ∀ B : Finset ℕ,
      (∀ b ∈ B, b ≤ M) →
      resonanceEnvelope s (fun j => reciprocalScale r M (j.val + 1))
        (VinogradovKorobovMoment.phaseCoefficients k t z)
        (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) ≤
      ((4 : ℝ) ^ k * ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
        (2 * (s : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ)))) ^ k *
        (M : ℝ) ^ (k * (k + 1) - rectangleSaving k) := by
  classical
  let G := 2 * (r : ℝ) / (1 - Real.exp (-Real.pi))
  let F := 2 * (s : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ)
  let W := (4 : ℝ) ^ k * (G * F)
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    simpa using tail_denominator_pos (a := 1) zero_lt_one
  have hG : 0 < G := by dsimp only [G]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  intro M hM hsM t z htlo hthi hzlo hzhi B hB
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := zero_lt_one.trans_le hMr
  let R : Finset (Fin k) := Finset.univ.filter (fun j => 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k)
  let e (j : Fin k) := if 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k then 4 * (j.val + 1) - 2 * k + 2 else 2 * (j.val + 1)
  have he (j : Fin k) : e j + (if 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k then 2 * (k - (j.val + 1 + 1)) else 0) =
      2 * (j.val + 1) := by
    by_cases hj : 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k
    · simp only [e, if_pos hj]
      have hq := j.isLt
      omega
    · simp only [e, if_neg hj, add_zero]
  have hEsum : (∑ j : Fin k, e j) + rectangleSaving k = k * (k + 1) := by
    calc
      _ = ∑ j : Fin k, (e j + (if 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k then 2 * (k - (j.val + 1 + 1)) else 0)) := by
        rw [Finset.sum_add_distrib]
        rfl
      _ = ∑ j : Fin k, 2 * (j.val + 1) := Finset.sum_congr rfl (fun j _ => he j)
      _ = _ := doubled_degree_sum k
  have hE : (∑ j : Fin k, e j) = k * (k + 1) - rectangleSaving k := by omega
  let a (j : Fin k) := reciprocalScale r (M : ℝ) (j.val + 1)
  let gamma := VinogradovKorobovMoment.phaseCoefficients k t z
  have ha (j : Fin k) : 0 < a j := reciprocalScale_pos hr hMpos _
  have hbound := actual_resonance_le_selected_widths k s M B hB ha gamma R
    (fun j _ => coefficient_band_nonzero k (pow_pos hMpos _) (pow_pos hMpos _) htlo hzlo j)
    (by
      intro j hj
      exact power_rectangle_unwrapped k s hMr (by norm_num : (0 : ℝ) < 4)
        (by exact_mod_cast hsM) htlo hthi hzlo hzhi j (Finset.mem_filter.mp hj).2.1)
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
        by_cases hj : 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k
        · rw [if_pos hj]
          have hp : 0 ≤ 2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j))) :=
            div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg (ha j).le _)
              (tail_denominator_pos (ha j)).le)
          apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hp).trans
          apply (rectangle_coordinate_power_le k r hr hMr htlo hthi hzlo hzhi j hj.1.le).trans
          dsimp only [e, W]
          rw [if_pos hj]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hfour : (4 : ℝ) ^ (j.val + 1) ≤ (4 : ℝ) ^ k :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          exact mul_le_mul hfour (mul_le_mul_of_nonneg_left hsmall hG.le)
            (by positivity) (by positivity)
        · rw [if_neg hj]
          apply (full_coordinate_power_le r s hr hMr (j.val + 1)).trans
          dsimp only [e, W]
          rw [if_neg hj]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc
            _ ≤ G * F := mul_le_mul_of_nonneg_left hfull hG.le
            _ ≤ (4 : ℝ) ^ k * (G * F) := le_mul_of_one_le_left
              (mul_pos hG hF).le (one_le_pow₀ (by norm_num))
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.prod_pow_eq_pow_sum, hE]
      rfl

/-- The complete actual resonance product receives the quadratic gain of every eligible degree simultaneously. -/
theorem exists_rectangle_resonance_power_saving (k r s : ℕ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → s ≤ M → ∀ t z : ℝ,
      (M : ℝ) ^ (2 * k - 2) ≤ t → t ≤ (M : ℝ) ^ (2 * k) →
      (M : ℝ) ^ 4 ≤ z → z ≤ 4 * (M : ℝ) ^ 4 → ∀ B : Finset ℕ,
      (∀ b ∈ B, b ≤ M) →
      resonanceEnvelope s (fun j => reciprocalScale r M (j.val + 1))
        (VinogradovKorobovMoment.phaseCoefficients k t z)
        (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) ≤
      C * (M : ℝ) ^ (k * (k + 1) - rectangleSaving k) := by
  let W : ℝ := (4 : ℝ) ^ k * ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
    (2 * (s : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ)))
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    simpa using tail_denominator_pos (a := 1) zero_lt_one
  refine ⟨W ^ k, by dsimp only [W]; positivity, ?_⟩
  exact actual_resonance_le_explicit k r s hr

end
end RiemannGaussian.VinogradovRectangleResonance
