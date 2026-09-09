/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLegendreDivisorDual
import RiemannGaussian.SuzukiActualCutoff

/-!
# Subpolynomial allowances for the exact Suzuki arithmetic

The general subexponential compensator permits a one-sided allowance
`O_ε(N^ε)` for every positive `ε`, with constants and starting cutoffs
depending on `ε`. This is applied to the complete canonical gaps, the exact
mass--moment potential, and the literal prime logarithmic average.

No coefficients are selected. The potential is already the attained
optimum over all finite divisor minorants. These theorems relax the open
arithmetic target; they do not prove its subpolynomial lower bound.
-/

namespace RiemannGaussian
noncomputable section
open Filter Set
open scoped Topology

/-- A power allowance at each exact canonical cutoff transports to the
same exponential allowance in log time, without a cutoff-shift loss. -/
theorem suzuki_signal_lower_bound_of_canonical_gap_power_lower_bound
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hg : ∀ count : ℕ, -(C * ((count + 2 : ℕ) : ℝ) ^ ε) ≤
      suzukiFirstTailCanonicalGap count)
    {t : ℝ} (ht : 0 < t) :
    -(C * Real.exp (ε * t)) ≤ suzukiChebyshevLogAverageLaplaceSignal t := by
  rw [suzukiChebyshevLogAverageLaplaceSignal_eq_main_sub_prime ht.le]
  by_cases htail : Real.log 2 ≤ t
  · have h := suzukiPsi_lower_bound_of_canonical_gap_monotone_lower_bound
      (fun s => C * Real.exp (ε * s)) (by
        intro x _ y _ hxy
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy hε)) hC)
      (by intro s _; positivity) (by
        intro count
        have he : Real.exp (ε * Real.log ((count + 2 : ℕ) : ℝ)) =
            ((count + 2 : ℕ) : ℝ) ^ ε := by
          rw [Real.rpow_def_of_pos (by positivity)]
          congr 1
          ring
        rw [he]
        exact hg count) htail
    unfold riemannXiSuzukiPsiNonnegative at h
    linarith [suzukiPointwiseArchimedean_lt_four_mul_exp_half ht.le]
  · rw [suzukiPointwisePrimeContribution_eq_zero_of_lt_log_two ht.le
      (lt_of_not_ge htail)]
    have hp : 0 ≤ C * Real.exp (ε * t) := by positivity
    have he : 0 < 4 * Real.exp (t / 2) := by positivity
    linarith

/-- A one-sided bound by every positive cutoff power suffices for RH.
The constants may depend on the power, and no two-sided estimate is used. -/
theorem riemannHypothesis_of_suzukiCanonicalGap_subpolynomial_lower_bound
    (hg : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ count : ℕ,
      -(C * ((count + 2 : ℕ) : ℝ) ^ ε) ≤ suzukiFirstTailCanonicalGap count) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signal_scaled_subexponential_lower_bound
    (a := 1) (by norm_num)
  intro ε hε
  obtain ⟨C, hC, hg⟩ := hg ε hε
  refine ⟨C, hC, fun t ht => ?_⟩
  simpa only [one_mul] using
    suzuki_signal_lower_bound_of_canonical_gap_power_lower_bound hC hε.le hg ht

/-- The exact optimum over all divisor minorants needs only an eventual
subpolynomial lower allowance. The finite head and the complete signed
Legendre-to-gap error are absorbed into each exponent's constant.
The displayed arithmetic estimate remains an unproved premise. -/
theorem riemannHypothesis_of_suzukiMassLegendrePotential_eventually_subpolynomial_lower_bound
    (hb : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ count : ℕ in atTop,
      -(C * ((count + 2 : ℕ) : ℝ) ^ ε) ≤ suzukiMassLegendrePotential count) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzukiCanonicalGap_subpolynomial_lower_bound
  intro ε hε
  obtain ⟨C, hb⟩ := hb ε hε
  obtain ⟨start, hs⟩ := eventually_atTop.mp hb
  let E := ∑ j ∈ Finset.range start, |suzukiFirstTailCanonicalGap j|
  let D := suzukiMassLegendrePotential 0 - suzukiFirstTailCanonicalGap 0
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨|C| + |D| + E, by positivity, fun count => ?_⟩
  have hp : 1 ≤ ((count + 2 : ℕ) : ℝ) ^ ε :=
    Real.one_le_rpow (by norm_cast; omega) hε.le
  have hCp := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity :
    0 ≤ ((count + 2 : ℕ) : ℝ) ^ ε)
  have hDp := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ |D| + E)
  by_cases hc : start ≤ count
  · have hd : suzukiMassLegendrePotential count - suzukiFirstTailCanonicalGap count ≤ D :=
      antitone_suzukiMassLegendrePotential_sub_gap (Nat.zero_le count)
    nlinarith [hs count hc, le_abs_self D]
  · have he : |suzukiFirstTailCanonicalGap count| ≤ E :=
      Finset.single_le_sum (f := fun j => |suzukiFirstTailCanonicalGap j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (lt_of_not_ge hc))
    have hCp0 : 0 ≤ |C| * ((count + 2 : ℕ) : ℝ) ^ ε := by positivity
    nlinarith [neg_abs_le (suzukiFirstTailCanonicalGap count), abs_nonneg D]

/-- A right-half zero would force negative excursions of some positive
power size in the exact all-weight optimum. In particular, merely
unbounded subpolynomial losses cannot be its required obstruction. -/
theorem suzukiMassLegendrePotential_power_excursions_of_right_half_zero
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, ∃ᶠ count : ℕ in atTop,
      suzukiMassLegendrePotential count < -(C * ((count + 2 : ℕ) : ℝ) ^ ε) := by
  by_contra hn
  push Not at hn
  have hb : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ count : ℕ in atTop,
      -(C * ((count + 2 : ℕ) : ℝ) ^ ε) ≤ suzukiMassLegendrePotential count := by
    intro ε hε
    obtain ⟨C, hC⟩ := hn ε hε
    exact ⟨C, by simpa only [not_frequently, not_lt] using hC⟩
  have hRH :=
    riemannHypothesis_of_suzukiMassLegendrePotential_eventually_subpolynomial_lower_bound hb
  have hre := hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  linarith

/-- Integer endpoint power bounds control the actual real cutoff, including
the complete interpolation error. The exponent is unchanged. -/
theorem suzukiLogAverage_real_upper_of_nat_power_upper {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (h : ∀ N : ℕ, 1 ≤ N → suzukiChebyshevLogAverageError (N : ℝ) ≤ C * (N : ℝ) ^ ε)
    {x : ℝ} (hx : 1 ≤ x) :
    suzukiChebyshevLogAverageError x ≤ (C + 12) * x ^ ε := by
  have hx0 := zero_le_one.trans hx
  have hN : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by exact_mod_cast hx)
  have hNr : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have hs : (1 : ℝ) ≤ Real.sqrt (⌊x⌋₊ : ℝ) := Real.one_le_sqrt.mpr hNr
  have hd : 12 / Real.sqrt (⌊x⌋₊ : ℝ) ≤ (12 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (⌊x⌋₊ : ℝ))).mpr
    linarith
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg ⌊x⌋₊) (Nat.floor_le hx0) hε
  have hCp := mul_le_mul_of_nonneg_left hp hC
  have hxpow := Real.one_le_rpow hx hε
  have he := suzukiChebyshevLogAverageError_le_floor_add_inv_sqrt hx
  nlinarith [h ⌊x⌋₊ hN]

/-- The literal prime logarithmic-average error needs only an eventual
one-sided `O_ε(N^ε)` upper bound for every positive `ε`. Finite heads and
real-cutoff interpolation are discharged, with no entropy hypothesis. -/
theorem riemannHypothesis_of_suzuki_logAverage_eventually_subpolynomial_upper
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      suzukiChebyshevLogAverageError (N : ℝ) ≤ C * (N : ℝ) ^ ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signal_scaled_subexponential_lower_bound
    (a := 1) (by norm_num)
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  obtain ⟨start, hs⟩ := eventually_atTop.mp hC
  let E := ∑ n ∈ Finset.range start, |suzukiChebyshevLogAverageError (n : ℝ)|
  let B := |C| + E
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hall : ∀ N : ℕ, 1 ≤ N →
      suzukiChebyshevLogAverageError (N : ℝ) ≤ B * (N : ℝ) ^ ε := by
    intro N hN
    have hp : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast hN) hε.le
    have hEp := mul_le_mul_of_nonneg_left hp hE
    by_cases hlate : start ≤ N
    · have hCp := mul_le_mul_of_nonneg_right (le_abs_self C)
        (Real.rpow_nonneg (Nat.cast_nonneg N) ε)
      dsimp [B]
      nlinarith [hs N hlate]
    · have he : |suzukiChebyshevLogAverageError (N : ℝ)| ≤ E :=
        Finset.single_le_sum (f := fun n : ℕ => |suzukiChebyshevLogAverageError (n : ℝ)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (lt_of_not_ge hlate))
      have hCp : 0 ≤ |C| * (N : ℝ) ^ ε := by positivity
      dsimp [B]
      nlinarith [le_abs_self (suzukiChebyshevLogAverageError (N : ℝ))]
  refine ⟨B + 12, by positivity, fun t ht => ?_⟩
  have he := suzukiLogAverage_real_upper_of_nat_power_upper hB hε.le hall
    (Real.one_le_exp_iff.mpr ht.le)
  rw [← Real.exp_mul, mul_comm t ε] at he
  simp only [one_mul, suzukiChebyshevLogAverageLaplaceSignal]
  linarith

end
end RiemannGaussian
