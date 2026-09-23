/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovGaussianSpacing
import RiemannGaussian.VinogradovIntervalResonance

/-!
# Gaussian spacing across multiple periods

Crossing an integer period does not erase Gaussian spacing. We partition the
literal finite sample by its nearest integer, pay a uniform translated Gaussian
sum on each fibre, and count only the periods actually reachable by that sample.
-/

namespace RiemannGaussian.VinogradovWrappedGaussian
noncomputable section
open scoped BigOperators
open VinogradovGaussianBounds VinogradovGaussianSpacing

/-- A finite translated Gaussian costs at most two complete centred Gaussian sums. -/
theorem finite_shifted_gaussian_le {c : ℝ} (hc : 0 < c) (b : ℝ) (S : Finset ℤ) :
    (∑ n ∈ S, Real.exp (-c * ((n : ℝ) - b) ^ 2)) ≤
      2 * (1 + Real.sqrt (Real.pi / c)) := by
  classical
  let m : ℤ := ⌊b⌋
  have hlo : (m : ℝ) ≤ b := Int.floor_le b
  have hhi : b ≤ (m : ℝ) + 1 := (Int.lt_floor_add_one b).le
  have hpoint (n : ℤ) :
      Real.exp (-c * ((n : ℝ) - b) ^ 2) ≤
        Real.exp (-c * ((n - m : ℤ) : ℝ) ^ 2) +
        Real.exp (-c * ((n - (m + 1) : ℤ) : ℝ) ^ 2) := by
    by_cases hn : n ≤ m
    · have hn' : (n : ℝ) ≤ m := by exact_mod_cast hn
      have hsq : ((n - m : ℤ) : ℝ) ^ 2 ≤ ((n : ℝ) - b) ^ 2 := by
        push_cast
        nlinarith [sq_nonneg (b - (m : ℝ))]
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hc.le))
      exact he.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · have hn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
      have hsq : ((n - (m + 1) : ℤ) : ℝ) ^ 2 ≤ ((n : ℝ) - b) ^ 2 := by
        push_cast
        nlinarith [sq_nonneg ((m : ℝ) + 1 - b)]
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hc.le))
      exact he.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hshift (z : ℤ) :
      (∑ n ∈ S, Real.exp (-c * ((n - z : ℤ) : ℝ) ^ 2)) ≤
        1 + Real.sqrt (Real.pi / c) := by
    have himage : (∑ n ∈ S, Real.exp (-c * ((n - z : ℤ) : ℝ) ^ 2)) =
        ∑ n ∈ S.image (fun n => n - z), Real.exp (-c * (n : ℝ) ^ 2) := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      change a - z = b - z at hab
      omega
    rw [himage]
    exact ((summable_gaussian_int hc).sum_le_tsum _
      (fun _ _ => (Real.exp_pos _).le)).trans (int_gaussian_sum_le hc)
  calc
    _ ≤ ∑ n ∈ S, (Real.exp (-c * ((n - m : ℤ) : ℝ) ^ 2) +
        Real.exp (-c * ((n - (m + 1) : ℤ) : ℝ) ^ 2)) :=
      Finset.sum_le_sum (fun n _ => hpoint n)
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith [hshift m, hshift (m + 1)]

/-- Integer translation preserves the nearest-period distance. -/
theorem integerDistance_sub_int (x : ℝ) (m : ℤ) :
    integerDistance (x - m) = integerDistance x := by
  unfold integerDistance
  rw [neg_sub, sub_eq_add_neg, Int.fract_intCast_add]

/-- The nearest integer gives a centred representative in a closed half-period. -/
theorem nearest_representative (x : ℝ) : |x - (⌊x + 1 / 2⌋ : ℤ)| ≤ 1 / 2 := by
  have hlo := Int.floor_le (x + 1 / 2)
  have hhi := Int.lt_floor_add_one (x + 1 / 2)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Each actual nearest-period fibre pays a translated Gaussian width. -/
theorem fibre_envelope_le {a gamma : ℝ} (ha : 0 < a) (hg : gamma ≠ 0)
    (m : ℤ) (S : Finset ℤ)
    (hfibre : ∀ n ∈ S, ⌊gamma * (n : ℝ) + 1 / 2⌋ = m) :
    ∑ n ∈ S, tailEnvelope a (gamma * (n : ℝ)) ≤
      (2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
        (2 * (1 + Real.sqrt a / |gamma|)) := by
  let c := Real.pi * gamma ^ 2 / a
  have hc : 0 < c := div_pos (mul_pos Real.pi_pos (sq_pos_of_ne_zero hg)) ha
  let P := 2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))
  have hP : 0 ≤ P := by
    dsimp only [P]
    exact div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg ha.le _)
      (tail_denominator_pos ha).le)
  have hp (n : ℤ) (hn : n ∈ S) :
      tailEnvelope a (gamma * (n : ℝ)) ≤
        P * Real.exp (-c * ((n : ℝ) - (m : ℝ) / gamma) ^ 2) := by
    have h := tailEnvelope_le_distance ha (gamma * (n : ℝ))
    have hrep := nearest_representative (gamma * (n : ℝ))
    rw [hfibre n hn] at hrep
    rw [← integerDistance_sub_int _ m, integerDistance_eq_abs hrep, sq_abs] at h
    convert h using 1
    dsimp only [P, c]
    congr 2
    field_simp
  have he : Real.pi / c = a / gamma ^ 2 := by dsimp only [c]; field_simp
  calc
    _ ≤ ∑ n ∈ S, P * Real.exp (-c * ((n : ℝ) - (m : ℝ) / gamma) ^ 2) :=
      Finset.sum_le_sum hp
    _ = P * ∑ n ∈ S, Real.exp (-c * ((n : ℝ) - (m : ℝ) / gamma) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ P * (2 * (1 + Real.sqrt (Real.pi / c))) :=
      mul_le_mul_of_nonneg_left (finite_shifted_gaussian_le hc _ S) hP
    _ = _ := by rw [he, Real.sqrt_div ha.le, Real.sqrt_sq_eq_abs]

/-- Wrapped samples pay the number of reachable periods, not their full support cardinality. -/
theorem finite_envelope_le_wrapped {a gamma H : ℝ} (ha : 0 < a) (hg : gamma ≠ 0)
    (hH : 0 ≤ H) (S : Finset ℤ) (hs : ∀ n ∈ S, |(n : ℝ)| ≤ H) :
    ∑ n ∈ S, tailEnvelope a (gamma * (n : ℝ)) ≤
      (2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))) *
        (4 * |gamma| * H + 8) * (1 + Real.sqrt a / |gamma|) := by
  classical
  let q (n : ℤ) : ℤ := ⌊gamma * (n : ℝ) + 1 / 2⌋
  let K : ℕ := ⌈|gamma| * H + 1 / 2⌉₊
  let periods : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  have hq (n : ℤ) (hn : n ∈ S) : q n ∈ periods := by
    have hx : |gamma * (n : ℝ)| ≤ |gamma| * H := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hs n hn) (abs_nonneg _)
    have hnear := nearest_representative (gamma * (n : ℝ))
    have hK : |gamma| * H + 1 / 2 ≤ (K : ℝ) := Nat.le_ceil _
    have habs : |(q n : ℝ)| ≤ K := by
      have he : (q n : ℝ) = gamma * (n : ℝ) -
          (gamma * (n : ℝ) - (q n : ℝ)) := by ring
      rw [he]
      exact (abs_sub _ _).trans (by dsimp only [q] at *; linarith)
    have hh := abs_le.mp habs
    apply Finset.mem_Icc.mpr
    constructor
    · exact_mod_cast hh.1
    · exact_mod_cast hh.2
  have hcard : (periods.card : ℝ) ≤ 2 * |gamma| * H + 4 := by
    have hk : (K : ℝ) ≤ |gamma| * H + 1 / 2 + 1 :=
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ |gamma| * H + 1 / 2)).le
    have hc := VinogradovIntervalResonance.symmetric_box_card K
    change (((Finset.Icc (-(K : ℤ)) K).card : ℕ) : ℝ) ≤ _
    rw [hc]
    linarith
  let P := 2 / (a ^ (1 / 2 : ℝ) * (1 - Real.exp (-Real.pi / a)))
  have hP : 0 ≤ P := by
    dsimp only [P]
    exact div_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg ha.le _)
      (tail_denominator_pos ha).le)
  have hw : 0 ≤ 1 + Real.sqrt a / |gamma| := by positivity
  calc
    _ = ∑ m ∈ periods, ∑ n ∈ S with q n = m, tailEnvelope a (gamma * (n : ℝ)) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hq _
    _ ≤ ∑ _m ∈ periods, P * (2 * (1 + Real.sqrt a / |gamma|)) := by
      apply Finset.sum_le_sum
      intro m _
      exact fibre_envelope_le ha hg m _ (fun n hn => (Finset.mem_filter.mp hn).2)
    _ = (periods.card : ℝ) * (P * (2 * (1 + Real.sqrt a / |gamma|))) := by
      simp
    _ ≤ (2 * |gamma| * H + 4) * (P * (2 * (1 + Real.sqrt a / |gamma|))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end
end RiemannGaussian.VinogradovWrappedGaussian
