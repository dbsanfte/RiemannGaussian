/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSignedFrequency
import Mathlib.Analysis.MeanInequalities
import RiemannGaussian.ZetaRieszFrequencyDecay

/-!
# Prime-count information inside the frequency product

The arithmetic and geometric mean inequality keeps the cardinality cost
that is lost by bounding every prime logarithm by the whole logarithm.
-/

namespace RiemannGaussian.ZetaRieszPrimeCountFrequency
noncomputable section
open scoped BigOperators Classical
open Filter Topology
open ZetaRieszPrimeFourier ZetaRieszSignedFrequency

/-- Nonnegative factors with fixed total mass retain a full cardinality
denominator in their product bound. -/
theorem prod_le_mean_pow {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hS : 0 < S.card) (hx : ∀ i ∈ S, 0 ≤ x i) :
    (∏ i ∈ S, x i) ≤ ((∑ i ∈ S, x i) / (S.card : ℝ)) ^ S.card := by
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS
  have h := Real.geom_mean_le_arith_mean S (fun _ => 1) x (by simp)
    (by simpa using hc) hx
  simp only [Real.rpow_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hp : 0 ≤ ∏ i ∈ S, x i := Finset.prod_nonneg hx
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hp _) h hc.le
  rw [← Real.rpow_mul hp, inv_mul_cancel₀ hc.ne', Real.rpow_one, Real.rpow_natCast] at hh
  exact hh

/-- Prime logarithms share a fixed total. Keeping the actual count
saves its full cardinality power, before any frequency is bounded. -/
theorem prime_log_product_le_mean {n : ℕ} (hn : Squarefree n)
    (hk : 0 < n.primeFactors.card) :
    (∏ p ∈ n.primeFactors, Real.log p) ≤
      (Real.log n / (n.primeFactors.card : ℝ)) ^ n.primeFactors.card := by
  have h := prod_le_mean_pow n.primeFactors (fun p => Real.log p) hk
    (fun p _ => Real.log_natCast_nonneg p)
  rwa [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn] at h

/-- The complete signed prime product is bounded by the mean prime
logarithm, rather than by the full logarithm once per prime. -/
theorem norm_primeProduct_le_mean {n : ℕ} (hn : Squarefree n)
    (hk : 0 < n.primeFactors.card) (xi : ℝ) :
    ‖primeProduct n xi‖ ≤
      (|xi| * (Real.log n / (n.primeFactors.card : ℝ))) ^ n.primeFactors.card := by
  apply (norm_primeProduct_le_prime_count n xi).trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left (prime_log_product_le_mean hn hk) (by positivity)

/-- Both opposite frequencies preserve the cardinality saving. This
estimate is downstream of the exact coupled product. -/
theorem norm_primePair_le_mean {n : ℕ} (hn : Squarefree n)
    (hk : 0 < n.primeFactors.card) (L xi : ℝ) :
    ‖primePair n L xi‖ ≤
      2 * (|xi| * (Real.log n / (n.primeFactors.card : ℝ))) ^ n.primeFactors.card := by
  unfold primePair
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hp := norm_primeProduct_le_mean hn hk xi
  have hm := norm_primeProduct_le_mean hn hk (-xi)
  rw [abs_neg] at hm
  linarith

/-- The complete higher-prime quotient retains every extra vanishing
factor beyond the first four, together with the mean-logarithm denominator. -/
theorem norm_higher_quotient_le_full_count {n : ℕ} (hn : Squarefree n)
    (hk : 4 ≤ n.primeFactors.card) (L xi : ℝ) :
    ‖primePair n L xi / (xi : ℂ) ^ 2‖ ≤
      2 * |xi| ^ 2 * (Real.log n / (n.primeFactors.card : ℝ)) ^ 4 *
        (|xi| * (Real.log n / (n.primeFactors.card : ℝ))) ^ (n.primeFactors.card - 4) := by
  by_cases hxi : xi = 0
  · simp [hxi]
  have h := norm_primePair_le_mean hn (by omega) L xi
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  apply (div_le_iff₀ (sq_pos_of_ne_zero (abs_ne_zero.mpr hxi))).mpr
  apply h.trans_eq
  have hpow (a : ℝ) : a ^ n.primeFactors.card = a ^ 4 * a ^ (n.primeFactors.card - 4) := by
    rw [← pow_add, show 4 + (n.primeFactors.card - 4) = n.primeFactors.card by omega]
  rw [hpow, mul_pow]
  ring

/-- The count-sensitive natural window is k times wider than the old
one and saves k^4 in the coefficient of the quadratic quotient bound. -/
theorem norm_higher_quotient_le_wider_window {n : ℕ} (hn : Squarefree n)
    (hk : 4 ≤ n.primeFactors.card) (L xi : ℝ)
    (hxi : |xi| * Real.log n ≤ (n.primeFactors.card : ℝ)) :
    ‖primePair n L xi / (xi : ℂ) ^ 2‖ ≤
      2 * |xi| ^ 2 * (Real.log n / (n.primeFactors.card : ℝ)) ^ 4 := by
  have hkp : (0 : ℝ) < n.primeFactors.card := by exact_mod_cast (show 0 < n.primeFactors.card by omega)
  have hx0 : 0 ≤ |xi| * (Real.log n / (n.primeFactors.card : ℝ)) := by positivity
  have hx1 : |xi| * (Real.log n / (n.primeFactors.card : ℝ)) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_one hkp).mpr hxi
  exact (norm_higher_quotient_le_full_count hn hk L xi).trans
    ((mul_le_mul_of_nonneg_left (pow_le_one₀ hx0 hx1) (by positivity)).trans_eq (mul_one _))

/-- The arithmetic allowance with each actual prime-count denominator
retained, rather than replaced by the smallest possible count. -/
def meanFrequencyCost (S : Finset ℕ) (f : ℕ → ℂ) (L : ℝ) : ℝ :=
  ∑ n ∈ S.filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬n.Prime),
    (Real.log n / L * ‖f n‖) * (Real.log n / (n.primeFactors.card : ℝ)) ^ 4

/-- The actual count-sensitive cost is nonnegative at positive length. -/
theorem meanFrequencyCost_nonneg (S : Finset ℕ) (f : ℕ → ℂ) {L : ℝ} (hL : 0 < L) :
    0 ≤ meanFrequencyCost S f L := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
    (norm_nonneg _)) (by positivity)

/-- The full higher-prime signed sum retains its larger, count-dependent
frequency window before the complex observations are bounded. -/
theorem norm_bandPrimePair_le_mean (S : Finset ℕ) (f : ℕ → ℂ) {L : ℝ} (hL : 0 < L)
    (hk : ∀ n ∈ S, 4 ≤ n.primeFactors.card) (xi : ℝ)
    (hxi : ∀ n ∈ S, |xi| * Real.log n ≤ (n.primeFactors.card : ℝ)) :
    ‖bandPrimePair S f L xi‖ ≤ 2 * |xi| ^ 2 * meanFrequencyCost S f L := by
  unfold bandPrimePair
  apply (norm_sum_le _ _).trans
  rw [meanFrequencyCost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hm := Finset.mem_filter.mp hn
  rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_natCast_nonneg n), Real.norm_of_nonneg hL.le]
  exact (mul_le_mul_of_nonneg_left
    (norm_higher_quotient_le_wider_window hm.2.1 (hk n hm.1) L xi (hxi n hm.1))
      (by positivity : 0 ≤ Real.log n / L * ‖f n‖)).trans_eq (by ring)

/-- At every prime-count threshold K>=4, the complete arithmetic cost
saves K^4 over the earlier undifferentiated higher-degree allowance. -/
theorem meanFrequencyCost_le_div_count (S : Finset ℕ) (f : ℕ → ℂ)
    {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 0 < K)
    (hk : ∀ n ∈ S, K ≤ n.primeFactors.card) :
    meanFrequencyCost S f L ≤ higherFrequencyCost S f L / (K : ℝ) ^ 4 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold meanFrequencyCost higherFrequencyCost
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  have hkn : (K : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hk n (Finset.mem_filter.mp hn).1
  have h := div_le_div_of_nonneg_left (Real.log_natCast_nonneg n) hKr hkn
  calc
    _ ≤ (Real.log n / L * ‖f n‖) * (Real.log n / (K : ℝ)) ^ 4 := by gcongr
    _ = _ := by rw [div_pow]; ring

/-- The complete finite signed integral has a cubic allowance throughout
each integer's own count-dependent frequency window. -/
theorem norm_integral_bandPrimePair_le_mean (S : Finset ℕ) (f : ℕ → ℂ)
    {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d)
    (hk : ∀ n ∈ S, 4 ≤ n.primeFactors.card)
    (hwindow : ∀ n ∈ S, d * Real.log n ≤ (n.primeFactors.card : ℝ)) :
    ‖∫ xi : ℝ in 0..d, bandPrimePair S f L xi‖ ≤
      (2 / 3 : ℝ) * d ^ 3 * meanFrequencyCost S f L := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (f := bandPrimePair S f L)
    (g := fun xi : ℝ => 2 * xi ^ 2 * meanFrequencyCost S f L) hd
    (Filter.Eventually.of_forall fun xi hxi => by
      have hw (n : ℕ) (hn : n ∈ S) : |xi| * Real.log n ≤ (n.primeFactors.card : ℝ) := by
        rw [abs_of_pos hxi.1]
        exact (mul_le_mul_of_nonneg_right hxi.2 (Real.log_natCast_nonneg n)).trans (hwindow n hn)
      simpa only [sq_abs] using norm_bandPrimePair_le_mean S f hL hk xi hw)
    (((continuous_const.mul (continuous_id.pow 2)).mul continuous_const).intervalIntegrable 0 d)
  apply h.trans_eq
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_pow]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, zero_pow (by decide : 3 ≠ 0), sub_zero]
  ring

/-- On the actual higher-prime support, the frequency window is four
times wider and the cubic allowance's coefficient is smaller by 4^4.
All original masks, observations and source factors remain. -/
theorem norm_actual_higher_low_frequency_le_count (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u d : ℝ} (hu : 0 ≤ u) (hd : 0 ≤ d) (hwindow : d * ((8 / 3 : ℝ) * N) ≤ 4) :
    ‖(u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
      ∫ xi : ℝ in 0..d,
        bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
          (fun n => 4 ≤ n.primeFactors.card))
          (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
          (SquarefreeVaughanLogSource.length u N) xi)‖ ≤
      u ^ (N + 1) * d ^ 3 / (768 * Real.pi) *
        higherFrequencyCost ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
          (fun n => 4 ≤ n.primeFactors.card))
          (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
          (SquarefreeVaughanLogSource.length u N) := by
  let S := (ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => 4 ≤ n.primeFactors.card)
  let f : ℕ → ℂ := fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n
  let L := SquarefreeVaughanLogSource.length u N
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hk : ∀ n ∈ S, 4 ≤ n.primeFactors.card := fun _ hn => (Finset.mem_filter.mp hn).2
  have hb := norm_integral_bandPrimePair_le_mean S f hL hd hk (fun n hn => by
    have hlog : Real.log n ≤ (8 / 3 : ℝ) * N :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2
    have hcard : (4 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hk n hn
    exact ((mul_le_mul_of_nonneg_left hlog hd).trans hwindow).trans hcard)
  have hm := meanFrequencyCost_le_div_count S f hL (by decide : 0 < 4) hk
  norm_num only [Nat.cast_ofNat, show (4 : ℝ) ^ 4 = 256 by norm_num] at hm
  have hc : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu, hc,
    ← mul_assoc]
  calc
    _ ≤ (u ^ (N + 1) * (1 / (2 * Real.pi))) *
        ((2 / 3 : ℝ) * d ^ 3 * meanFrequencyCost S f L) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (u ^ (N + 1) * (1 / (2 * Real.pi))) *
        ((2 / 3 : ℝ) * d ^ 3 * (higherFrequencyCost S f L / 256)) := by gcongr
    _ = _ := by dsimp [S, f, L]; ring

/-- On the natural frequency window, all prime factors contribute their
cardinality denominators, giving the full k^k rather than only k^4. -/
theorem norm_higher_quotient_le_count_power {n : ℕ} (hn : Squarefree n)
    (hk : 4 ≤ n.primeFactors.card) (L xi : ℝ)
    (hxi : |xi| * Real.log n ≤ 1) :
    ‖primePair n L xi / (xi : ℂ) ^ 2‖ ≤
      2 * |xi| ^ 2 * Real.log n ^ 4 /
        (n.primeFactors.card : ℝ) ^ n.primeFactors.card := by
  have hc : (0 : ℝ) < n.primeFactors.card := by exact_mod_cast (show 0 < n.primeFactors.card by omega)
  have hdiv : |xi| * (Real.log n / (n.primeFactors.card : ℝ)) ≤
      1 / (n.primeFactors.card : ℝ) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hxi hc.le
  have hpow : (n.primeFactors.card : ℝ) ^ n.primeFactors.card =
      (n.primeFactors.card : ℝ) ^ 4 * (n.primeFactors.card : ℝ) ^ (n.primeFactors.card - 4) := by
    rw [← pow_add, show 4 + (n.primeFactors.card - 4) = n.primeFactors.card by omega]
  calc
    _ ≤ 2 * |xi| ^ 2 * (Real.log n / (n.primeFactors.card : ℝ)) ^ 4 *
        (|xi| * (Real.log n / (n.primeFactors.card : ℝ))) ^ (n.primeFactors.card - 4) :=
      norm_higher_quotient_le_full_count hn hk L xi
    _ ≤ 2 * |xi| ^ 2 * (Real.log n / (n.primeFactors.card : ℝ)) ^ 4 *
        (1 / (n.primeFactors.card : ℝ)) ^ (n.primeFactors.card - 4) := by gcongr
    _ = _ := by rw [hpow, div_pow, div_pow, one_pow]; ring

/-- The cost retaining every prime-count denominator on the natural
frequency window. The original finite support and observation remain. -/
def countFrequencyCost (S : Finset ℕ) (f : ℕ → ℂ) (L : ℝ) : ℝ :=
  ∑ n ∈ S.filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬n.Prime),
    (Real.log n / L * ‖f n‖) * Real.log n ^ 4 /
      (n.primeFactors.card : ℝ) ^ n.primeFactors.card

/-- The complete count-power cost is nonnegative at positive length. -/
theorem countFrequencyCost_nonneg (S : Finset ℕ) (f : ℕ → ℂ) {L : ℝ} (hL : 0 < L) :
    0 ≤ countFrequencyCost S f L := by
  apply Finset.sum_nonneg
  intro n _
  exact div_nonneg (mul_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
    (norm_nonneg _)) (by positivity)) (by positivity)

/-- The complete signed finite frequency sum retains the full prime-count
power before its phase-bearing observations are bounded. -/
theorem norm_bandPrimePair_le_count_power (S : Finset ℕ) (f : ℕ → ℂ) {L : ℝ} (hL : 0 < L)
    (hk : ∀ n ∈ S, 4 ≤ n.primeFactors.card) (xi : ℝ)
    (hxi : ∀ n ∈ S, |xi| * Real.log n ≤ 1) :
    ‖bandPrimePair S f L xi‖ ≤ 2 * |xi| ^ 2 * countFrequencyCost S f L := by
  unfold bandPrimePair
  apply (norm_sum_le _ _).trans
  rw [countFrequencyCost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hm := Finset.mem_filter.mp hn
  rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_natCast_nonneg n), Real.norm_of_nonneg hL.le]
  exact (mul_le_mul_of_nonneg_left
    (norm_higher_quotient_le_count_power hm.2.1 (hk n hm.1) L xi (hxi n hm.1))
      (by positivity : 0 ≤ Real.log n / L * ‖f n‖)).trans_eq (by ring)

/-- Any count threshold saves its full cardinality power in the actual
finite arithmetic cost. -/
theorem countFrequencyCost_le_div_power (S : Finset ℕ) (f : ℕ → ℂ)
    {L : ℝ} (hL : 0 < L) {K : ℕ} (hK : 0 < K)
    (hk : ∀ n ∈ S, K ≤ n.primeFactors.card) :
    countFrequencyCost S f L ≤ higherFrequencyCost S f L / (K : ℝ) ^ K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold countFrequencyCost higherFrequencyCost
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  have hkn := hk n (Finset.mem_filter.mp hn).1
  have hknr : (K : ℝ) ≤ n.primeFactors.card := by exact_mod_cast hkn
  have hc1 : (1 : ℝ) ≤ n.primeFactors.card := by exact_mod_cast (show 1 ≤ n.primeFactors.card by omega)
  have hpow : (K : ℝ) ^ K ≤ (n.primeFactors.card : ℝ) ^ n.primeFactors.card :=
    (pow_le_pow_left₀ hKr.le hknr K).trans (pow_le_pow_right₀ hc1 hkn)
  exact div_le_div_of_nonneg_left (by positivity) (pow_pos hKr K) hpow

/-- The natural low-frequency integral keeps the full prime-count power
in its cubic allowance; its interval integrability is genuine. -/
theorem norm_integral_bandPrimePair_le_count_power (S : Finset ℕ) (f : ℕ → ℂ)
    {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d)
    (hk : ∀ n ∈ S, 4 ≤ n.primeFactors.card)
    (hwindow : ∀ n ∈ S, d * Real.log n ≤ 1) :
    ‖∫ xi : ℝ in 0..d, bandPrimePair S f L xi‖ ≤
      (2 / 3 : ℝ) * d ^ 3 * countFrequencyCost S f L := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (f := bandPrimePair S f L)
    (g := fun xi : ℝ => 2 * xi ^ 2 * countFrequencyCost S f L) hd
    (Filter.Eventually.of_forall fun xi hxi => by
      have hw (n : ℕ) (hn : n ∈ S) : |xi| * Real.log n ≤ 1 := by
        rw [abs_of_pos hxi.1]
        exact (mul_le_mul_of_nonneg_right hxi.2 (Real.log_natCast_nonneg n)).trans (hwindow n hn)
      simpa only [sq_abs] using norm_bandPrimePair_le_count_power S f hL hk xi hw)
    (((continuous_const.mul (continuous_id.pow 2)).mul continuous_const).intervalIntegrable 0 d)
  apply h.trans_eq
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_pow]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, zero_pow (by decide : 3 ≠ 0), sub_zero]
  ring

/-- The original central frequency sum restricted only by the retained
number of distinct prime factors. -/
def manyPrimeFrequency (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) (xi : ℝ) : ℂ :=
  bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => K ≤ n.primeFactors.card))
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (SquarefreeVaughanLogSource.length u N) xi

/-- The full source-normalized low response on the natural 1/N frequency
window, with only its prime-count selection made explicit. -/
def manyPrimeLowResponse (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) : ℂ :=
  (u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
    ∫ xi : ℝ in 0..(3 / (8 * ((N : ℝ) + 1))), manyPrimeFrequency P u y N K xi)

/-- Every count threshold receives its full K^K saving after the entire
growing arithmetic cost is paid by a genuinely summable tilt. This keeps
the natural frequency window and is uniform in the height and radius. -/
theorem norm_manyPrimeLowResponse_le (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u U q : ℝ} (hu : 0 ≤ u) (huU : u ≤ U) (hq : 0 < q) (hqhalf : q < 1 / 2)
    {K : ℕ} (hK : 4 ≤ K) :
    ‖manyPrimeLowResponse P u y N K‖ ≤
      (18 * U / Real.pi * ZetaRieszFrequencyDecay.frequencyTiltMass P q) *
        (((N : ℝ) + 1) ^ 2 * (U / q) ^ N) / (K : ℝ) ^ K := by
  let S := (ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => K ≤ n.primeFactors.card)
  let f : ℕ → ℂ := fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n
  let L := SquarefreeVaughanLogSource.length u N
  let d : ℝ := 3 / (8 * ((N : ℝ) + 1))
  have hL1 : 1 ≤ L := ZetaRieszHeadOrders.one_le_length u N
  have hL : 0 < L := by linarith
  have hd := natural_frequency_window N
  have hk : ∀ n ∈ S, K ≤ n.primeFactors.card := fun _ hn => (Finset.mem_filter.mp hn).2
  have hlog : ∀ n ∈ S, Real.log n ≤ (8 / 3 : ℝ) * N :=
    fun _ hn => (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2
  have hb := norm_integral_bandPrimePair_le_count_power S f hL hd.1.le
    (fun n hn => hK.trans (hk n hn)) (fun n hn =>
      (mul_le_mul_of_nonneg_left (hlog n hn) hd.1.le).trans hd.2)
  have hm := countFrequencyCost_le_div_power S f hL (by omega : 0 < K) hk
  have ht := ZetaRieszFrequencyDecay.higherFrequencyCost_le_tilt S P N y
    hL1 (show 0 ≤ (8 / 3 : ℝ) * N by positivity) hq hqhalf hlog
  have hp : (1 + (8 / 3 : ℝ) * N) ^ 5 ≤ 1024 * ((N : ℝ) + 1) ^ 5 := by
    calc
      _ ≤ (4 * ((N : ℝ) + 1)) ^ 5 := by gcongr; have := Nat.cast_nonneg (α := ℝ) N; linarith
      _ = _ := by ring
  have hmass := ZetaRieszFrequencyDecay.frequencyTiltMass_nonneg P hq
  have hcost : countFrequencyCost S f L ≤
      (1024 * ((N : ℝ) + 1) ^ 5 *
        (q⁻¹ ^ N * ZetaRieszFrequencyDecay.frequencyTiltMass P q)) / (K : ℝ) ^ K := by
    apply hm.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply ht.trans
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  have hU : 0 ≤ U := hu.trans huU
  have hcount := countFrequencyCost_nonneg S f hL
  have hd0 : 0 ≤ d := hd.1.le
  have hn : (N : ℝ) + 1 ≠ 0 := by positivity
  have hc : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  change ‖(u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
    ∫ xi : ℝ in 0..d, bandPrimePair S f L xi)‖ ≤ _
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu, hc,
    ← mul_assoc]
  calc
    _ ≤ (u ^ (N + 1) * (1 / (2 * Real.pi))) *
        ((2 / 3 : ℝ) * d ^ 3 * countFrequencyCost S f L) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (U ^ (N + 1) * (1 / (2 * Real.pi))) *
        ((2 / 3 : ℝ) * d ^ 3 * ((1024 * ((N : ℝ) + 1) ^ 5 *
          (q⁻¹ ^ N * ZetaRieszFrequencyDecay.frequencyTiltMass P q)) / (K : ℝ) ^ K)) := by
      gcongr
    _ = _ := by
      dsimp [d]
      simp only [div_pow, inv_pow, pow_succ U N]
      field_simp
      ring

/-- A count subsequence of logarithmic-density scale. -/
def dyadicPrimeCount (j : ℕ) : ℕ := 2 ^ (j + 3)

/-- A cofinal moment subsequence for which the count-power saving can
be checked by rational arithmetic without a logarithmic threshold estimate. -/
def dyadicMomentOrder (j : ℕ) : ℕ := 8 * (j + 4) * dyadicPrimeCount j

/-- The cardinality-power denominator buys a definite exponential saving
in the original moment order, on an explicit unbounded subsequence. -/
theorem dyadic_count_power_saving (j : ℕ) :
    (17 / 16 : ℝ) ^ dyadicMomentOrder j ≤
      (dyadicPrimeCount j : ℝ) ^ dyadicPrimeCount j := by
  have h (j : ℕ) : (17 / 16 : ℝ) ^ (8 * (j + 4)) ≤ (2 : ℝ) ^ (j + 3) := by
    induction j with
    | zero => norm_num
    | succ j ih =>
      rw [show 8 * (j + 1 + 4) = 8 * (j + 4) + 8 by omega, pow_add,
        show j + 1 + 3 = (j + 3) + 1 by omega, pow_succ (2 : ℝ) (j + 3)]
      exact mul_le_mul ih (by norm_num : (17 / 16 : ℝ) ^ 8 ≤ 2) (by positivity) (by positivity)
  have he := pow_le_pow_left₀ (by positivity) (h j) (dyadicPrimeCount j)
  simpa only [← pow_mul, dyadicMomentOrder, dyadicPrimeCount, Nat.cast_pow, Nat.cast_ofNat] using he

/-- Every selected count lies in the genuine higher-prime class. -/
theorem four_le_dyadicPrimeCount (j : ℕ) : 4 ≤ dyadicPrimeCount j := by
  dsimp [dyadicPrimeCount]
  have hp : 0 < (2 : ℕ) ^ j := by positivity
  rw [pow_add]
  norm_num
  omega

/-- The selected moment orders tend to infinity, so every existing
source limit remains valid on this subsequence. -/
theorem tendsto_dyadicMomentOrder : Tendsto dyadicMomentOrder atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro j
  have hp := four_le_dyadicPrimeCount j
  dsimp [dyadicMomentOrder]
  nlinarith

/-- The full arithmetic cost of the many-prime sector is bounded on its
natural frequency scale, with a strict geometric improvement from the
retained prime count. No zero or source hypothesis enters this inequality. -/
theorem norm_manyPrimeLowResponse_dyadic_le (P : Polynomial ℂ) (y : ℝ) (j : ℕ)
    {u U q : ℝ} (hu : 0 ≤ u) (huU : u ≤ U) (hq : 0 < q) (hqhalf : q < 1 / 2) :
    ‖manyPrimeLowResponse P u y (dyadicMomentOrder j) (dyadicPrimeCount j)‖ ≤
      (18 * U / Real.pi * ZetaRieszFrequencyDecay.frequencyTiltMass P q) *
        (((dyadicMomentOrder j : ℝ) + 1) ^ 2 * (16 * U / (17 * q)) ^ dyadicMomentOrder j) := by
  have hU := hu.trans huU
  have hm := ZetaRieszFrequencyDecay.frequencyTiltMass_nonneg P hq
  apply (norm_manyPrimeLowResponse_le P y (dyadicMomentOrder j) hu huU hq hqhalf
    (four_le_dyadicPrimeCount j)).trans
  calc
    _ ≤ (18 * U / Real.pi * ZetaRieszFrequencyDecay.frequencyTiltMass P q) *
        (((dyadicMomentOrder j : ℝ) + 1) ^ 2 * (U / q) ^ dyadicMomentOrder j) /
          (17 / 16 : ℝ) ^ dyadicMomentOrder j :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (dyadic_count_power_saving j)
    _ = _ := by
      simp only [mul_div_assoc, ← div_pow]
      congr 3
      field_simp

/-- A genuinely summable tilt exists for the whole radius interval
0<U<17/32 on the natural-window, many-prime sector. -/
theorem exists_many_prime_tilt {U : ℝ} (hU : 0 < U) (hU1 : U < 17 / 32) :
    ∃ q : ℝ, 0 < q ∧ q < 1 / 2 ∧ 16 * U < 17 * q := by
  refine ⟨(16 * U / 17 + 1 / 2) / 2, ?_, ?_, ?_⟩ <;> linarith

/-- Uniform source-normalized decay on the natural frequency window for
the complete selected many-prime class. Both height and radius may move
arbitrarily. Low prime counts and other frequencies remain outside it. -/
theorem tendsto_manyPrimeLowResponse_dyadic_moving (P : Polynomial ℂ)
    (u y : ℕ → ℝ) {U : ℝ} (hu : ∀ j, 0 ≤ u j) (huU : ∀ j, u j ≤ U)
    (hU : 0 < U) (hU1 : U < 17 / 32) :
    Tendsto (fun j => manyPrimeLowResponse P (u j) (y j)
      (dyadicMomentOrder j) (dyadicPrimeCount j)) atTop (𝓝 0) := by
  obtain ⟨q, hq, hqhalf, hrate⟩ := exists_many_prime_tilt hU hU1
  have ht := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 2
    (show 0 < 16 * U / (17 * q) by positivity)
    ((div_lt_one (by positivity : 0 < 17 * q)).mpr hrate)).comp tendsto_dyadicMomentOrder
  apply squeeze_zero_norm (fun j => norm_manyPrimeLowResponse_dyadic_le P (y j) j
    (hu j) (huU j) hq hqhalf)
  simpa only [Function.comp_apply, mul_zero] using
    ht.const_mul (18 * U / Real.pi * ZetaRieszFrequencyDecay.frequencyTiltMass P q)

/-- The original annular source range fits strictly inside the interval
where the many-prime natural-window decay has been independently proved. -/
theorem exp_neg_two_thirds_lt_many_prime_radius :
    Real.exp (-(2 / 3 : ℝ)) < 17 / 32 := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos (2 / 3 : ℝ))).mpr
  have h := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3)
  nlinarith

/-- Every remaining low prime count, including exactly three, kept with
the original mask, phase and filter. -/
def fewPrimeFrequency (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) (xi : ℝ) : ℂ :=
  bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => 3 ≤ n.primeFactors.card ∧ n.primeFactors.card < K))
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (SquarefreeVaughanLogSource.length u N) xi

/-- An exact partition of the full nonlinear carrier. The count split
retains every cross-frequency and cross-integer phase before any estimate. -/
theorem nonlinearFrequency_eq_few_add_many (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    {K : ℕ} (hK : 4 ≤ K) (xi : ℝ) :
    nonlinearFrequency P u y N xi =
      fewPrimeFrequency P u y N K xi + manyPrimeFrequency P u y N K xi := by
  simp only [nonlinearFrequency, fewPrimeFrequency, manyPrimeFrequency,
    bandPrimePair, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp_all <;> omega

/-- All count-restricted frequency integrals are genuinely integrable. -/
theorem integrable_few_many_frequency (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) :
    MeasureTheory.IntegrableOn (fewPrimeFrequency P u y N K) (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn (manyPrimeFrequency P u y N K) (Set.Ioi 0) :=
  ⟨integrable_bandPrimePair _ _ _, integrable_bandPrimePair _ _ _⟩

/-- Deleting the paid low-frequency many-prime component leaves exactly
all frequencies of the few-prime class and the complementary frequencies
of the many-prime class. No boundary or arithmetic term is dropped. -/
theorem nonlinearResponse_sub_many_low_eq (P : Polynomial ℂ) (u y : ℝ) (N : ℕ)
    {K : ℕ} (hK : 4 ≤ K) :
    (u : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPrimeLayers.centralThreePrimeResponse P u y N +
        ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse P u y N) -
          manyPrimeLowResponse P u y N K =
      (u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
        ((∫ xi : ℝ in Set.Ioi 0, fewPrimeFrequency P u y N K xi) +
         (∫ xi : ℝ in Set.Ioi (3 / (8 * ((N : ℝ) + 1))), manyPrimeFrequency P u y N K xi))) := by
  obtain ⟨hf, hm⟩ := integrable_few_many_frequency P u y N K
  rw [nonlinearResponse_eq_integral]
  have he : nonlinearFrequency P u y N =
      fun xi => fewPrimeFrequency P u y N K xi + manyPrimeFrequency P u y N K xi :=
    funext (nonlinearFrequency_eq_few_add_many P u y N hK)
  rw [he, MeasureTheory.integral_add hf hm]
  unfold manyPrimeLowResponse
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hm (natural_frequency_window N).1.le]
  ring

/-- The actual exposed-zero source survives the independent natural-window
many-prime deletion. Its three unpaid pieces are now explicit: all few-prime
frequencies, the remaining many-prime frequencies, and the tapered wing.
Multiplicity is unrestricted, and the original annular range is retained. -/
theorem tendsto_count_reduced_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun j : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (dyadicMomentOrder j + 1) *
      ((1 / (2 * (Real.pi : ℂ))) *
        ((∫ xi : ℝ in Set.Ioi 0,
            fewPrimeFrequency 1 (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j) xi) +
         (∫ xi : ℝ in Set.Ioi (3 / (8 * ((dyadicMomentOrder j : ℝ) + 1))),
            manyPrimeFrequency 1 (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j) xi)) +
        ZetaRieszCompletedCarrier.taperedWing (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder j)))
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hd := tendsto_manyPrimeLowResponse_dyadic_moving 1
    (fun _ => 3 / 2 - rho.1.re) (fun _ => rho.1.im) (fun _ => hu.le) (fun _ => le_rfl)
    hu (huh.trans exp_neg_two_thirds_lt_many_prime_radius)
  have hs := (ZetaRieszCentralHarmonicCost.tendsto_three_unpaid_exact_source
    rho hrho hexposed huh).comp tendsto_dyadicMomentOrder
  have h := hs.sub hd
  simp only [Function.comp_apply, sub_zero] at h
  apply h.congr'
  filter_upwards [] with j
  have he := nonlinearResponse_sub_many_low_eq 1 (3 / 2 - rho.1.re) rho.1.im
    (dyadicMomentOrder j) (four_le_dyadicPrimeCount j)
  linear_combination he

end
end RiemannGaussian.ZetaRieszPrimeCountFrequency
