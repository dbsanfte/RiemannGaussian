/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovWrappedGaussian
import RiemannGaussian.VinogradovRectangleResonance

/-!
# Recovering the wrapped middle-degree resonance window

The degrees between k/2 and 2k/3 can cross several periods, but their spacing
still saves powers. All crossed periods and all translated Gaussian tails are
paid explicitly. The existing unwrapped high-degree gain is retained.
-/

namespace RiemannGaussian.VinogradovWrappedResonance
noncomputable section
open scoped BigOperators
open VinogradovGaussianBounds VinogradovGaussianSpacing VinogradovWrappedGaussian
open VinogradovResonanceScaling VinogradovResonanceWindow VinogradovPhaseRectangle
open VinogradovRectangleResonance VinogradovIntervalResonance

/-- Each middle degree pays its actual number of periods and still saves powers. -/
theorem middle_coordinate_le (k r s : ℕ) (hr : 0 < r) {M t z : ℝ}
    (hM : 1 ≤ M) (htlo : M ^ (2 * k - 2) ≤ t) (hthi : t ≤ M ^ (2 * k))
    (hzlo : M ^ 4 ≤ z) (hzhi : z ≤ 4 * M ^ 4)
    (j : Fin k) (hj : 3 * (j.val + 1) ≤ 2 * k)
    (S : Finset ℤ) (hs : ∀ n ∈ S, |(n : ℝ)| ≤ (s : ℝ) * M ^ (j.val + 1)) :
    (∑ n ∈ S, tailEnvelope (reciprocalScale r M (j.val + 1))
      (VinogradovKorobovMoment.phaseCoefficients k t z j * (n : ℝ))) ≤
      ((4 : ℝ) ^ (j.val + 1) * (2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
        (4 * (s : ℝ) + 8) * (1 + 2 * Real.pi * (j.val + 1) / (r : ℝ))) *
        M ^ (2 * k - 2 * (j.val + 1) + 2) := by
  have hMpos := zero_lt_one.trans_le hM
  let a := reciprocalScale r M (j.val + 1)
  let gamma := VinogradovKorobovMoment.phaseCoefficients k t z j
  let H := (s : ℝ) * M ^ (j.val + 1)
  let G := 2 * (r : ℝ) / (1 - Real.exp (-Real.pi))
  let W := 1 + 2 * Real.pi * (j.val + 1) / (r : ℝ)
  have ha : 0 < a := reciprocalScale_pos hr hMpos _
  have hg : gamma ≠ 0 := coefficient_band_nonzero k (pow_pos hMpos _)
    (pow_pos hMpos _) htlo hzlo j
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    simpa using tail_denominator_pos (a := 1) zero_lt_one
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hrange : |gamma| * H ≤ (s : ℝ) * M ^ (2 * k - 3 * (j.val + 1)) := by
    have hcoeff := (power_rectangle_coefficient_bounds k hMpos
      (by norm_num : (0 : ℝ) < 4) htlo hthi hzlo hzhi j).2
    have hq : (1 : ℝ) ≤ (j.val : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j.val]
    have hd : 1 ≤ 2 * Real.pi * ((j.val : ℝ) + 1) := by
      have hp := one_le_mul_of_one_le_of_one_le
        (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ 2 * Real.pi) hq
      exact hp
    calc
      _ ≤ |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j| * H :=
        mul_le_mul_of_nonneg_right hcoeff (by dsimp only [H]; positivity)
      _ = ((s : ℝ) / (2 * Real.pi * (j.val + 1))) *
          M ^ (2 * k - 3 * (j.val + 1)) := by
        rw [power_phase_range_identity k s hMpos j]
        simp_rw [div_eq_mul_inv]
        rw [← pow_sub₀ M hMpos.ne' hj]
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_self (Nat.cast_nonneg s) hd) (by positivity)
  have hwrap : 4 * |gamma| * H + 8 ≤
      (4 * (s : ℝ) + 8) * M ^ (2 * k - 3 * (j.val + 1)) := by
    have hp := one_le_pow₀ (n := 2 * k - 3 * (j.val + 1)) hM
    nlinarith only [hrange, hp]
  have hwidth : 1 + Real.sqrt a / |gamma| ≤
      ((4 : ℝ) ^ (j.val + 1) * W) * M ^ 2 := by
    have hrect := power_rectangle_width_le k (a := a) hMpos
      (by norm_num : (0 : ℝ) < 4) htlo hthi hzlo hzhi j
    have hbase : Real.sqrt a /
        |VinogradovKorobovMoment.phaseCoefficients k (M ^ (2 * k)) (M ^ 4) j| ≤
        2 * Real.pi * (j.val + 1) / (r : ℝ) := by
      rw [power_phase_width_identity k r hr hMpos j]
      apply mul_le_of_le_one_right (by positivity)
      exact (div_le_one (pow_pos hMpos _)).mpr (pow_le_pow_right₀ hM hj)
    have hfour : 1 ≤ (4 : ℝ) ^ (j.val + 1) * M ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hM)
    have hb := mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ (4 : ℝ) ^ (j.val + 1) * M ^ 2 by positivity)
    dsimp only [W]
    dsimp only [gamma] at *
    nlinarith only [hrect, hb, hfour]
  apply (finite_envelope_le_wrapped ha hg (by positivity) S hs).trans
  calc
    _ ≤ (G * M ^ (j.val + 1)) *
        ((4 * (s : ℝ) + 8) * M ^ (2 * k - 3 * (j.val + 1))) *
        (((4 : ℝ) ^ (j.val + 1) * W) * M ^ 2) := by
      apply mul_le_mul _ hwidth (by positivity) (by positivity)
      exact mul_le_mul (reciprocal_prefactor_le hr hM (j.val + 1)) hwrap
        (by positivity) (by positivity)
    _ = _ := by
      have he : j.val + 1 + (2 * k - 3 * (j.val + 1)) + 2 =
          2 * k - 2 * (j.val + 1) + 2 := by omega
      calc
        _ = ((4 : ℝ) ^ (j.val + 1) * G * (4 * (s : ℝ) + 8) * W) *
            (M ^ (j.val + 1) * M ^ (2 * k - 3 * (j.val + 1)) * M ^ 2) := by ring
        _ = _ := by rw [← pow_add, ← pow_add, he]

/-- The additional gain recovered from degrees whose phases may wrap. -/
def middleSaving (k : ℕ) : ℕ :=
  ∑ j : Fin k, if k + 1 ≤ 2 * (j.val + 1) ∧ 3 * (j.val + 1) ≤ 2 * k then
    4 * (j.val + 1) - 2 * k - 2 else 0

/-- The old unwrapped gain and the disjoint wrapped middle gain are both retained. -/
def wrappedSaving (k : ℕ) : ℕ := rectangleSaving k + middleSaving k

/-- The power paid in each degree, after selecting the two disjoint useful windows. -/
def coordinateExponent (k : ℕ) (j : Fin k) : ℕ :=
  if 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k then 4 * (j.val + 1) - 2 * k + 2
  else if k + 1 ≤ 2 * (j.val + 1) ∧ 3 * (j.val + 1) ≤ 2 * k then
    2 * k - 2 * (j.val + 1) + 2 else 2 * (j.val + 1)

/-- The saved and paid powers exactly exhaust the original two-family dimension. -/
theorem dimension_balance (k : ℕ) :
    (∑ j : Fin k, coordinateExponent k j) + wrappedSaving k = k * (k + 1) := by
  have hp (j : Fin k) : coordinateExponent k j +
      (if 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k then 2 * (k - (j.val + 1 + 1)) else 0) +
      (if k + 1 ≤ 2 * (j.val + 1) ∧ 3 * (j.val + 1) ≤ 2 * k then
        4 * (j.val + 1) - 2 * k - 2 else 0) = 2 * (j.val + 1) := by
    dsimp only [coordinateExponent]
    split_ifs <;> have hj := j.isLt <;> omega
  calc
    _ = ∑ j : Fin k, (coordinateExponent k j +
        (if 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k then 2 * (k - (j.val + 1 + 1)) else 0) +
        (if k + 1 ≤ 2 * (j.val + 1) ∧ 3 * (j.val + 1) ≤ 2 * k then
          4 * (j.val + 1) - 2 * k - 2 else 0)) := by
      simp only [Finset.sum_add_distrib, wrappedSaving, rectangleSaving, middleSaving, add_assoc]
    _ = ∑ j : Fin k, 2 * (j.val + 1) := Finset.sum_congr rfl (fun j _ => hp j)
    _ = _ := VinogradovResonancePower.doubled_degree_sum k

/-- The combined gain never exceeds the complete original frequency dimension. -/
theorem wrappedSaving_le_dimension (k : ℕ) : wrappedSaving k ≤ k * (k + 1) := by
  have h := dimension_balance k
  omega

/-- The literal full resonance retains both Gaussian windows, with every period cost explicit. -/
theorem actual_resonance_le (k r s : ℕ) (hr : 0 < r)
    (M : ℕ) (hM : 1 ≤ M) (hsM : s ≤ M) (t z : ℝ)
    (htlo : (M : ℝ) ^ (2 * k - 2) ≤ t) (hthi : t ≤ (M : ℝ) ^ (2 * k))
    (hzlo : (M : ℝ) ^ 4 ≤ z) (hzhi : z ≤ 4 * (M : ℝ) ^ 4)
    (B : Finset ℕ) (hB : ∀ b ∈ B, b ≤ M) :
    resonanceEnvelope s (fun j => reciprocalScale r M (j.val + 1))
      (VinogradovKorobovMoment.phaseCoefficients k t z)
      (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) ≤
      (((4 : ℝ) ^ k * ((2 * (r : ℝ) / (1 - Real.exp (-Real.pi))) *
        (2 * (s : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ)))) *
        (4 * (s : ℝ) + 8)) ^ k *
      (M : ℝ) ^ (k * (k + 1) - wrappedSaving k) := by
  classical
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos := zero_lt_one.trans_le hMr
  let G := 2 * (r : ℝ) / (1 - Real.exp (-Real.pi))
  let F := 2 * (s : ℝ) + 2 + 2 * Real.pi * (k : ℝ) / (r : ℝ)
  let W := ((4 : ℝ) ^ k * (G * F)) * (4 * (s : ℝ) + 8)
  have hden : 0 < 1 - Real.exp (-Real.pi) := by
    simpa using tail_denominator_pos (a := 1) zero_lt_one
  have hG : 0 < G := by dsimp only [G]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  let a (j : Fin k) := reciprocalScale r M (j.val + 1)
  let gamma := VinogradovKorobovMoment.phaseCoefficients k t z
  let S (j : Fin k) := Finset.Icc (-((s * M ^ (j.val + 1) : ℕ) : ℤ))
    ((s * M ^ (j.val + 1) : ℕ) : ℤ)
  have ha (j : Fin k) : 0 < a j := reciprocalScale_pos hr hMpos _
  have hs (j : Fin k) (n : ℤ) (hn : n ∈ S j) :
      |(n : ℝ)| ≤ (s : ℝ) * (M : ℝ) ^ (j.val + 1) := by
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    apply abs_le.mpr
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi
  have hcoord (j : Fin k) : (∑ n ∈ S j, tailEnvelope (a j) (gamma j * (n : ℝ))) ≤
      W * (M : ℝ) ^ coordinateExponent k j := by
    have hq : (j.val : ℝ) + 1 ≤ k := by exact_mod_cast j.isLt
    have hfour : (4 : ℝ) ^ (j.val + 1) ≤ (4 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hw : 1 + 2 * Real.pi * (j.val + 1) / (r : ℝ) ≤ F := by
      have hmul := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 2 * Real.pi)) (Nat.cast_nonneg r)
      dsimp only [F]
      linarith only [hmul, Nat.cast_nonneg (α := ℝ) s]
    have hGF : 0 ≤ G * F := (mul_pos hG hF).le
    have hW : (4 : ℝ) ^ k * (G * F) ≤ W :=
      le_mul_of_one_le_right (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) s])
    by_cases hhigh : 2 * k < 3 * (j.val + 1) ∧ j.val + 1 < k
    · have hnowrap := power_rectangle_unwrapped k s hMr (by norm_num : (0 : ℝ) < 4)
        (by exact_mod_cast hsM) htlo hthi hzlo hzhi j hhigh.1
      have hg : gamma j ≠ 0 := coefficient_band_nonzero k (pow_pos hMpos _)
        (pow_pos hMpos _) htlo hzlo j
      have hbound := finite_envelope_le_width (ha j) hg (S j) (by
        intro n hn
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hs j n hn) (abs_nonneg _)).trans hnowrap)
      apply hbound.trans
      apply (rectangle_coordinate_power_le k r hr hMr htlo hthi hzlo hzhi j hhigh.1.le).trans
      simp only [coordinateExponent, if_pos hhigh]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (mul_le_mul hfour (mul_le_mul_of_nonneg_left hw hG.le)
        (by positivity) (by positivity)).trans hW
    · by_cases hmid : k + 1 ≤ 2 * (j.val + 1) ∧ 3 * (j.val + 1) ≤ 2 * k
      · apply (middle_coordinate_le k r s hr hMr htlo hthi hzlo hzhi j hmid.2 (S j) (hs j)).trans
        simp only [coordinateExponent, if_neg hhigh, if_pos hmid]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hb := mul_le_mul hfour (mul_le_mul_of_nonneg_left hw hG.le)
          (by positivity : 0 ≤ G * (1 + 2 * Real.pi * (j.val + 1) / (r : ℝ)))
          (by positivity : 0 ≤ (4 : ℝ) ^ k)
        have hc := mul_le_mul_of_nonneg_right hb
          (by positivity : 0 ≤ 4 * (s : ℝ) + 8)
        dsimp only [W]
        nlinarith only [hc]
      · have hraw : (∑ n ∈ S j, tailEnvelope (a j) (gamma j * (n : ℝ))) ≤
          (2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j)))) *
            (2 * (s : ℝ) * (M : ℝ) ^ (j.val + 1) + 1) := by
          calc
            _ ≤ ∑ _n ∈ S j, 2 / ((a j) ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a j))) :=
              Finset.sum_le_sum (fun _ _ => tailEnvelope_le_prefactor (ha j) _)
            _ = _ := by
              simp only [Finset.sum_const, nsmul_eq_mul, S, symmetric_box_card]
              push_cast
              ring
        apply hraw.trans
        apply (VinogradovResonancePower.full_coordinate_power_le r s hr hMr (j.val + 1)).trans
        simp only [coordinateExponent, if_neg hhigh, if_neg hmid]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hfull : 2 * (s : ℝ) + 1 ≤ F := by
          have hh : 0 ≤ 2 * Real.pi * (k : ℝ) / (r : ℝ) := by positivity
          dsimp only [F]
          linarith only [hh]
        exact (mul_le_mul_of_nonneg_left hfull hG.le).trans
          ((le_mul_of_one_le_left hGF (one_le_pow₀ (by norm_num))).trans hW)
  apply (resonanceEnvelope_le_coordinate_sums s ha gamma
    (fun b : B => VinogradovMeanValue.monomialFrequency k b.val) S
    (fun h hh => actual_difference_in_box k s M B hB hh)).trans
  calc
    _ ≤ ∏ j : Fin k, W * (M : ℝ) ^ coordinateExponent k j :=
      Finset.prod_le_prod (fun j _ => Finset.sum_nonneg (fun _ _ => (tailEnvelope_pos (ha j) _).le))
        (fun j _ => hcoord j)
    _ = _ := by
      have he : (∑ j : Fin k, coordinateExponent k j) = k * (k + 1) - wrappedSaving k := by
        have h := dimension_balance k
        omega
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_pow_eq_pow_sum, he]
      rfl

end
end RiemannGaussian.VinogradovWrappedResonance
