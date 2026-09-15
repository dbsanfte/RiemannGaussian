/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPrimeFourier
import RiemannGaussian.ZetaRieszCentralPrimeLayers
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Prime-count cancellation inside the retained signed divisor sum

Every prime contributes a vanishing signed Fourier factor. Odd prime count
also cancels the two opposite frequencies at the exact reflection center.
These are bounds on a frequency component, not on the whole arithmetic sum.
-/

namespace RiemannGaussian.ZetaRieszSignedFrequency
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeFourier

/-- The signed sine product retains every distinct prime logarithm. -/
def sineProduct (n : ℕ) (xi : ℝ) : ℝ :=
  ∏ p ∈ n.primeFactors, Real.sin (xi * Real.log p / 2)

/-- The centered complex factor retains the prime-count colour and
all signs of the individual prime sines. -/
def centeredFactor (n : ℕ) (xi : ℝ) : ℂ :=
  (2 * Complex.I) ^ n.primeFactors.card * (sineProduct n xi : ℂ)

/-- The true prime product is exactly its centered factor times the
full logarithmic phase; no prime coordinate or sign is discarded. -/
theorem primeProduct_eq_centeredFactor {n : ℕ} (hn : Squarefree n) (xi : ℝ) :
    primeProduct n xi = centeredFactor n xi *
      Complex.exp (-((xi * Real.log n / 2 : ℝ) : ℂ) * Complex.I) := by
  rw [primeProduct_eq_centered_sine hn]
  unfold centeredFactor sineProduct
  ring

/-- Reflection changes the sine product by precisely the full
prime-count parity, before any absolute value is taken. -/
theorem sineProduct_neg (n : ℕ) (xi : ℝ) :
    sineProduct n (-xi) = (-1 : ℝ) ^ n.primeFactors.card * sineProduct n xi := by
  simp only [sineProduct, neg_mul, neg_div, Real.sin_neg, Finset.prod_neg]

/-- Odd prime count reverses the entire centered factor. -/
theorem centeredFactor_neg_of_odd {n : ℕ} (hodd : Odd n.primeFactors.card) (xi : ℝ) :
    centeredFactor n (-xi) = -centeredFactor n xi := by
  rw [centeredFactor, sineProduct_neg, hodd.neg_one_pow]
  unfold centeredFactor
  push_cast
  ring

/-- The paired Fourier response retains both phases about the actual
reflection center, together with their complete signed prime products. -/
theorem primePair_eq_centered {n : ℕ} (hn : Squarefree n) (L xi : ℝ) :
    primePair n L xi =
      centeredFactor n xi * Complex.exp (((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) +
      centeredFactor n (-xi) * Complex.exp (-((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) := by
  have hp : Complex.exp (((xi * L : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-((xi * Real.log n / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : Complex.exp (((-xi * L : ℝ) : ℂ) * Complex.I) *
      Complex.exp (-((-xi * Real.log n / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [primePair, primeProduct_eq_centeredFactor hn, primeProduct_eq_centeredFactor hn]
  calc
    _ = centeredFactor n xi *
        (Complex.exp (((xi * L : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-((xi * Real.log n / 2 : ℝ) : ℂ) * Complex.I)) +
      centeredFactor n (-xi) *
        (Complex.exp (((-xi * L : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-((-xi * Real.log n / 2 : ℝ) : ℂ) * Complex.I)) := by ring
    _ = _ := by rw [hp, hm]

/-- Every distinct prime gives one genuine vanishing frequency factor.
This uses the signed product before applying its absolute majorant. -/
theorem norm_primeProduct_le_prime_count (n : ℕ) (xi : ℝ) :
    ‖primeProduct n xi‖ ≤ |xi| ^ n.primeFactors.card *
      ∏ p ∈ n.primeFactors, Real.log p := by
  rw [norm_primeProduct_eq_sine_product]
  calc
    _ = ∏ p ∈ n.primeFactors, 2 * |Real.sin (xi * Real.log p / 2)| := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ ∏ p ∈ n.primeFactors, |xi| * Real.log p := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p _
      have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := xi * Real.log p / 2))
        (by norm_num : (0 : ℝ) ≤ 2)
      have he : 2 * |xi * Real.log p / 2| = |xi| * Real.log p := by
        rw [abs_div, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg p)]
        norm_num
        ring
      exact h.trans_eq he
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- Centering changes only a unit-modulus phase, so the full
prime-count cancellation remains in its amplitude. -/
theorem norm_centeredFactor_le {n : ℕ} (hn : Squarefree n) (xi : ℝ) :
    ‖centeredFactor n xi‖ ≤ |xi| ^ n.primeFactors.card *
      ∏ p ∈ n.primeFactors, Real.log p := by
  have h := norm_primeProduct_le_prime_count n xi
  rw [primeProduct_eq_centeredFactor hn, norm_mul] at h
  have he : ‖Complex.exp (-((xi * Real.log n / 2 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [show -((xi * Real.log n / 2 : ℝ) : ℂ) = ((-(xi * Real.log n / 2) : ℝ) : ℂ) by norm_cast]
    exact Complex.norm_exp_ofReal_mul_I _
  simpa only [he, mul_one] using h

/-- Opposite phases are bounded through their signed difference,
retaining its zero at the common reflection center. -/
theorem norm_opposite_exp_sub_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp (-(x : ℂ) * Complex.I)‖ ≤ 2 * |x| := by
  have hp : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
    simpa only [mul_comm, Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x))
  have hm : ‖Complex.exp (-(x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
    simpa only [Complex.ofReal_neg, mul_comm, Real.norm_eq_abs, abs_neg] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := -x))
  have ht := norm_sub_le (Complex.exp ((x : ℂ) * Complex.I) - 1)
    (Complex.exp (-(x : ℂ) * Complex.I) - 1)
  simp only [sub_sub_sub_cancel_right] at ht
  linarith

/-- Odd prime count gives one EXTRA vanishing frequency power in the
full paired response, with the exact reflection gap and all prime logs.
This is actual cancellation of the signed opposite-frequency terms. -/
theorem norm_primePair_le_of_odd {n : ℕ} (hn : Squarefree n)
    (hodd : Odd n.primeFactors.card) (L xi : ℝ) :
    ‖primePair n L xi‖ ≤ 2 * |xi| ^ (n.primeFactors.card + 1) *
      |L - Real.log n / 2| * ∏ p ∈ n.primeFactors, Real.log p := by
  rw [primePair_eq_centered hn, centeredFactor_neg_of_odd hodd]
  have he : centeredFactor n xi *
      Complex.exp (((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) +
      -centeredFactor n xi * Complex.exp (-((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) =
      centeredFactor n xi *
        (Complex.exp (((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (-((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I)) := by ring
  rw [he, norm_mul]
  apply (mul_le_mul (norm_centeredFactor_le hn xi)
    (norm_opposite_exp_sub_le (xi * (L - Real.log n / 2))) (norm_nonneg _)
    (mul_nonneg (pow_nonneg (abs_nonneg _) _) (Finset.prod_nonneg fun p _ => Real.log_natCast_nonneg p))).trans_eq
  rw [abs_mul, pow_succ]
  ring

/-- The genuine three-prime paired quotient is quadratically small
at zero frequency. The reflection gap and all three prime logs remain,
so its low-frequency integral has a cubic cutoff allowance. -/
theorem norm_three_prime_quotient_le {n : ℕ} (hn : Squarefree n)
    (hcard : n.primeFactors.card = 3) (L xi : ℝ) :
    ‖primePair n L xi / (xi : ℂ) ^ 2‖ ≤
      2 * |xi| ^ 2 * |L - Real.log n / 2| * ∏ p ∈ n.primeFactors, Real.log p := by
  by_cases hx : xi = 0
  · simp [hx]
  · have hodd : Odd n.primeFactors.card := by rw [hcard]; decide
    have h := norm_primePair_le_of_odd hn hodd L xi
    rw [hcard] at h
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ (sq_pos_of_ne_zero (abs_ne_zero.mpr hx))).mpr
    exact h.trans_eq (by ring)

/-- The complete finite cost of the three-prime frequency sector.
Every original observation, cutoff gap and prime logarithm remains. -/
def threeFrequencyCost (S : Finset ℕ) (f : ℕ → ℂ) (L : ℝ) : ℝ :=
  ∑ n ∈ S.filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime),
    (Real.log n / L * ‖f n‖) * |L - Real.log n / 2| *
      ∏ p ∈ n.primeFactors, Real.log p

/-- The finite frequency cost is nonnegative on the genuine cutoff domain. -/
theorem threeFrequencyCost_nonneg (S : Finset ℕ) (f : ℕ → ℂ) {L : ℝ} (hL : 0 < L) :
    0 ≤ threeFrequencyCost S f L := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (div_nonneg (Real.log_natCast_nonneg n) hL.le) (norm_nonneg _)) (abs_nonneg _))
    (Finset.prod_nonneg fun p _ => Real.log_natCast_nonneg p)

/-- Both opposite frequencies stay coupled through the actual finite
three-prime sum before it is bounded. Its complete quotient has an
independent quadratic frequency allowance with the original observations. -/
theorem norm_three_bandPrimePair_le (S : Finset ℕ) (f : ℕ → ℂ) {L : ℝ} (hL : 0 < L)
    (hcard : ∀ n ∈ S, n.primeFactors.card = 3) (xi : ℝ) :
    ‖bandPrimePair S f L xi‖ ≤ 2 * |xi| ^ 2 * threeFrequencyCost S f L := by
  unfold bandPrimePair
  apply (norm_sum_le _ _).trans
  rw [threeFrequencyCost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hs := (Finset.mem_filter.mp hn).2.1
  have hc := hcard n (Finset.mem_filter.mp hn).1
  rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n), abs_of_pos hL]
  apply (mul_le_mul_of_nonneg_left (norm_three_prime_quotient_le hs hc L xi)
    (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (norm_nonneg _))).trans_eq
  ring

/-- The actual frequency sector is integrable, using the established
full prime-product integral rather than a totalized singular expression. -/
theorem intervalIntegrable_bandPrimePair (S : Finset ℕ) (f : ℕ → ℂ) (L : ℝ)
    {d : ℝ} (hd : 0 ≤ d) :
    IntervalIntegrable (bandPrimePair S f L) MeasureTheory.volume 0 d := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hd).mpr
  exact (integrable_bandPrimePair S f L).mono_set (fun _ hx => hx.1)

/-- The entire low-frequency three-prime sector has a cubic cutoff
allowance. It sums the genuine finite response after the signed
prime-count and opposite-frequency cancellations have both been used. -/
theorem norm_integral_three_bandPrimePair_le (S : Finset ℕ) (f : ℕ → ℂ)
    {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d)
    (hcard : ∀ n ∈ S, n.primeFactors.card = 3) :
    ‖∫ xi : ℝ in 0..d, bandPrimePair S f L xi‖ ≤
      (2 / 3 : ℝ) * d ^ 3 * threeFrequencyCost S f L := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (f := bandPrimePair S f L)
    (g := fun xi : ℝ => 2 * xi ^ 2 * threeFrequencyCost S f L) hd
    (Filter.Eventually.of_forall fun xi _ => by
      simpa only [sq_abs] using norm_three_bandPrimePair_le S f hL hcard xi)
    (((continuous_const.mul (continuous_id.pow 2)).mul continuous_const).intervalIntegrable 0 d)
  apply h.trans_eq
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    integral_pow]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, zero_pow (by decide : 3 ≠ 0), sub_zero]
  ring

/-- The actual retained three-prime response is the complete signed
prime-product integral with all integer masks and factorial weights kept. -/
theorem centralThreePrimeResponse_eq_integral (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    ZetaRieszCentralPrimeLayers.centralThreePrimeResponse P u y N =
      (1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Set.Ioi 0,
        bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
          (fun n => n.primeFactors.card = 3))
          (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
          (SquarefreeVaughanLogSource.length u N) xi := by
  exact sum_original_eq_primePair_integral _ _ _

/-- The independently bounded low-frequency part belongs to the ACTUAL
retained three-prime sum, with its original source factor and normalization.
The complementary frequency integral and the finite cost are not asserted
to have a vanishing source-scale bound. -/
theorem norm_actual_three_low_frequency_le (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u d : ℝ} (hu : 0 ≤ u) (hd : 0 ≤ d) :
    ‖(u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
      ∫ xi : ℝ in 0..d,
        bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
          (fun n => n.primeFactors.card = 3))
          (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
          (SquarefreeVaughanLogSource.length u N) xi)‖ ≤
      u ^ (N + 1) * d ^ 3 / (3 * Real.pi) *
        threeFrequencyCost ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
          (fun n => n.primeFactors.card = 3))
          (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
          (SquarefreeVaughanLogSource.length u N) := by
  have h := norm_integral_three_bandPrimePair_le
    ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
      (fun n => n.primeFactors.card = 3))
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (SquarefreeVaughanLogSource.length_pos u N) hd
    (fun _ hn => (Finset.mem_filter.mp hn).2)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  have hc : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [hc, ← mul_assoc]
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ u ^ (N + 1) * (1 / (2 * Real.pi)))).trans_eq
  ring

/-- The three-prime paired character is exactly a signed product of four
sines. Its reflection gap remains coupled to all three prime logarithms;
there is no absolute value in this identity. -/
theorem primePair_three_eq_sine_product {n : ℕ} (hn : Squarefree n)
    (hcard : n.primeFactors.card = 3) (L xi : ℝ) :
    primePair n L xi = ((16 * Real.sin (xi * (L - Real.log n / 2)) *
      sineProduct n xi : ℝ) : ℂ) := by
  have hodd : Odd n.primeFactors.card := by rw [hcard]; decide
  rw [primePair_eq_centered hn, centeredFactor_neg_of_odd hodd]
  have hs := Complex.two_sin (((xi * (L - Real.log n / 2)) : ℝ) : ℂ)
  rw [← Complex.ofReal_sin] at hs
  have hi : Complex.exp (((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) -
      Complex.exp (-((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) =
      2 * Complex.I * (Real.sin (xi * (L - Real.log n / 2)) : ℂ) := by
    rw [show 2 * Complex.I * (Real.sin (xi * (L - Real.log n / 2)) : ℂ) =
      (2 * (Real.sin (xi * (L - Real.log n / 2)) : ℂ)) * Complex.I by ring, hs]
    simp only [mul_assoc, Complex.I_mul_I, mul_neg_one]
    ring
  have he : centeredFactor n xi *
      Complex.exp (((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) +
      -centeredFactor n xi * Complex.exp (-((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) =
      centeredFactor n xi *
        (Complex.exp (((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I) -
          Complex.exp (-((xi * (L - Real.log n / 2) : ℝ) : ℂ) * Complex.I)) := by ring
  rw [he, hi, centeredFactor, hcard]
  push_cast
  ring_nf
  norm_num [pow_succ, Complex.I_mul_I]

/-- The original response partitions into genuinely integrable low and
complementary frequencies. No completion of the integer mask is used. -/
theorem centralThreePrimeResponse_eq_low_add_high (P : Polynomial ℂ) (u y : ℝ)
    (N : ℕ) {d : ℝ} (hd : 0 ≤ d) :
    ZetaRieszCentralPrimeLayers.centralThreePrimeResponse P u y N =
      (1 / (2 * (Real.pi : ℂ))) *
        ((∫ xi : ℝ in 0..d,
          bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
            (fun n => n.primeFactors.card = 3))
            (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
            (SquarefreeVaughanLogSource.length u N) xi) +
        ∫ xi : ℝ in Set.Ioi d,
          bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
            (fun n => n.primeFactors.card = 3))
            (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
            (SquarefreeVaughanLogSource.length u N) xi) := by
  rw [centralThreePrimeResponse_eq_integral]
  congr 1
  exact (intervalIntegral.integral_interval_add_Ioi (integrable_bandPrimePair _ _ _)
    ((integrable_bandPrimePair _ _ _).mono_set (Set.Ioi_subset_Ioi hd))).symm

/-- Discarding only the low-frequency part of the actual retained
three-prime response has the explicit cubic error, with its full source
factor and finite arithmetic cost. The high-frequency remainder is kept. -/
theorem norm_actual_three_sub_high_frequency_le (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u d : ℝ} (hu : 0 ≤ u) (hd : 0 ≤ d) :
    ‖(u : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPrimeLayers.centralThreePrimeResponse P u y N -
        (1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Set.Ioi d,
          bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
            (fun n => n.primeFactors.card = 3))
            (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
            (SquarefreeVaughanLogSource.length u N) xi)‖ ≤
      u ^ (N + 1) * d ^ 3 / (3 * Real.pi) *
        threeFrequencyCost ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
          (fun n => n.primeFactors.card = 3))
          (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
          (SquarefreeVaughanLogSource.length u N) := by
  rw [centralThreePrimeResponse_eq_low_add_high P u y N hd, mul_add, add_sub_cancel_right]
  exact norm_actual_three_low_frequency_le P y N hu hd

/-- Every distinct prime logarithm is at most the complete physical
logarithm. This bound is downstream of the signed prime product. -/
theorem prime_log_product_le {n : ℕ} (hn : Squarefree n) :
    (∏ p ∈ n.primeFactors, Real.log p) ≤ (Real.log n) ^ n.primeFactors.card := by
  calc
    _ ≤ ∏ _p ∈ n.primeFactors, Real.log n := by
      apply Finset.prod_le_prod (fun p _ => Real.log_natCast_nonneg p)
      intro p hp
      apply Real.log_le_log (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos)
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero) (Nat.dvd_of_mem_primeFactors hp)
    _ = _ := by rw [Finset.prod_const]

/-- Four or more distinct primes give the same quadratic quotient
saving as the paired three-prime channel throughout the natural frequency
window. All higher degrees are covered, with no bound on their count. -/
theorem norm_higher_prime_quotient_le {n : ℕ} (hn : Squarefree n)
    (hcard : 4 ≤ n.primeFactors.card) (L xi : ℝ)
    (hxi : |xi| * Real.log n ≤ 1) :
    ‖primePair n L xi / (xi : ℂ) ^ 2‖ ≤ 2 * |xi| ^ 2 * (Real.log n) ^ 4 := by
  by_cases hx : xi = 0
  · simp [hx]
  have hp (t : ℝ) : ‖primeProduct n t‖ ≤ (|t| * Real.log n) ^ n.primeFactors.card := by
    apply (norm_primeProduct_le_prime_count n t).trans
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (prime_log_product_le hn) (by positivity)
  have hpair : ‖primePair n L xi‖ ≤ 2 * (|xi| * Real.log n) ^ n.primeFactors.card := by
    unfold primePair
    apply (norm_add_le _ _).trans
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hm := hp (-xi)
    rw [abs_neg] at hm
    linarith [hp xi]
  have ht := pow_le_pow_of_le_one
    (mul_nonneg (abs_nonneg xi) (Real.log_natCast_nonneg n)) hxi hcard
  have hb := hpair.trans (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2))
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  apply (div_le_iff₀ (sq_pos_of_ne_zero (abs_ne_zero.mpr hx))).mpr
  exact hb.trans_eq (by ring)

/-- The explicit finite higher-degree cost retains the observation,
physical logarithm and original inverse-length factor. -/
def higherFrequencyCost (S : Finset ℕ) (f : ℕ → ℂ) (L : ℝ) : ℝ :=
  ∑ n ∈ S.filter (fun n => Squarefree n ∧ n ≠ 1 ∧ ¬ n.Prime),
    (Real.log n / L * ‖f n‖) * (Real.log n) ^ 4

/-- Every higher-degree frequency cost is nonnegative at positive length. -/
theorem higherFrequencyCost_nonneg (S : Finset ℕ) (f : ℕ → ℂ) {L : ℝ} (hL : 0 < L) :
    0 ≤ higherFrequencyCost S f L := by
  apply Finset.sum_nonneg
  intro n _
  exact mul_nonneg (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le)
    (norm_nonneg _)) (by positivity)

/-- The complete signed sum over every higher prime count is bounded
after the within-integer Fourier cancellation has been used. -/
theorem norm_higher_bandPrimePair_le (S : Finset ℕ) (f : ℕ → ℂ) {L : ℝ} (hL : 0 < L)
    (hcard : ∀ n ∈ S, 4 ≤ n.primeFactors.card) (xi : ℝ)
    (hxi : ∀ n ∈ S, |xi| * Real.log n ≤ 1) :
    ‖bandPrimePair S f L xi‖ ≤ 2 * |xi| ^ 2 * higherFrequencyCost S f L := by
  unfold bandPrimePair
  apply (norm_sum_le _ _).trans
  rw [higherFrequencyCost, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hs := (Finset.mem_filter.mp hn).2.1
  have hmem := (Finset.mem_filter.mp hn).1
  rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n), abs_of_pos hL]
  apply (mul_le_mul_of_nonneg_left
    (norm_higher_prime_quotient_le hs (hcard n hmem) L xi (hxi n hmem))
    (mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hL.le) (norm_nonneg _))).trans_eq
  ring

/-- One cubic low-frequency allowance covers the entire class of four
or more prime factors, for every observation and finite support. -/
theorem norm_integral_higher_bandPrimePair_le (S : Finset ℕ) (f : ℕ → ℂ)
    {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d)
    (hcard : ∀ n ∈ S, 4 ≤ n.primeFactors.card)
    (hwindow : ∀ n ∈ S, d * Real.log n ≤ 1) :
    ‖∫ xi : ℝ in 0..d, bandPrimePair S f L xi‖ ≤
      (2 / 3 : ℝ) * d ^ 3 * higherFrequencyCost S f L := by
  have h := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume)
    (f := bandPrimePair S f L)
    (g := fun xi : ℝ => 2 * xi ^ 2 * higherFrequencyCost S f L) hd
    (Filter.Eventually.of_forall fun xi hxi => by
      have hw (n : ℕ) (hn : n ∈ S) : |xi| * Real.log n ≤ 1 := by
        rw [abs_of_pos hxi.1]
        exact (mul_le_mul_of_nonneg_right hxi.2 (Real.log_natCast_nonneg n)).trans (hwindow n hn)
      simpa only [sq_abs] using norm_higher_bandPrimePair_le S f hL hcard xi hw)
    (((continuous_const.mul (continuous_id.pow 2)).mul continuous_const).intervalIntegrable 0 d)
  apply h.trans_eq
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_pow]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, zero_pow (by decide : 3 ≠ 0), sub_zero]
  ring

/-- The full retained higher-degree arithmetic response is exactly its
prime-product integral with all integer masks and factorial shifts intact. -/
theorem centralHigherPrimeResponse_eq_integral (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse P u y N =
      (1 / (2 * (Real.pi : ℂ))) * ∫ xi : ℝ in Set.Ioi 0,
        bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
          (fun n => 4 ≤ n.primeFactors.card))
          (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
          (SquarefreeVaughanLogSource.length u N) xi := by
  exact sum_original_eq_primePair_integral _ _ _

/-- The natural frequency window is valid on the actual retained
higher-degree support. Its original central logarithmic mask is used,
so no hypothesis on the source radius or height is needed. -/
theorem actual_frequency_window {u d : ℝ} {N : ℕ} (hd : 0 ≤ d)
    (hwindow : d * ((8 / 3 : ℝ) * N) ≤ 1)
    {n : ℕ} (hn : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N) :
    d * Real.log n ≤ 1 := by
  have hlog : Real.log n ≤ (8 / 3 : ℝ) * N := (Finset.mem_filter.mp hn).2.2
  exact (mul_le_mul_of_nonneg_left hlog hd).trans hwindow

/-- The complete higher-degree low-frequency piece has an independent
cubic allowance on the natural window, with the original source scale,
fixed filter, physical length and finite cost all retained. -/
theorem norm_actual_higher_low_frequency_le (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u d : ℝ} (hu : 0 ≤ u) (hd : 0 ≤ d) (hwindow : d * ((8 / 3 : ℝ) * N) ≤ 1) :
    ‖(u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
      ∫ xi : ℝ in 0..d,
        bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
          (fun n => 4 ≤ n.primeFactors.card))
          (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
          (SquarefreeVaughanLogSource.length u N) xi)‖ ≤
      u ^ (N + 1) * d ^ 3 / (3 * Real.pi) *
        higherFrequencyCost ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
          (fun n => 4 ≤ n.primeFactors.card))
          (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
          (SquarefreeVaughanLogSource.length u N) := by
  have h := norm_integral_higher_bandPrimePair_le
    ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
      (fun n => 4 ≤ n.primeFactors.card))
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (SquarefreeVaughanLogSource.length_pos u N) hd
    (fun _ hn => (Finset.mem_filter.mp hn).2)
    (fun _ hn => actual_frequency_window hd hwindow (Finset.mem_filter.mp hn).1)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
  have hc : ‖(1 : ℂ) / (2 * (Real.pi : ℂ))‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [hc, ← mul_assoc]
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ u ^ (N + 1) * (1 / (2 * Real.pi)))).trans_eq
  ring

/-- The complete frequency carrier of the two actual nonlinear prime
classes. Their signs, integer masks and complex observations stay coupled. -/
def nonlinearFrequency (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) (xi : ℝ) : ℂ :=
  bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => n.primeFactors.card = 3))
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (SquarefreeVaughanLogSource.length u N) xi +
  bandPrimePair ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => 4 ≤ n.primeFactors.card))
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (SquarefreeVaughanLogSource.length u N) xi

/-- The explicit finite allowance for the coupled nonlinear frequency
carrier. Its growth is retained as an arithmetic obligation. -/
def nonlinearFrequencyCost (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℝ :=
  threeFrequencyCost ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => n.primeFactors.card = 3))
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (SquarefreeVaughanLogSource.length u N) +
  higherFrequencyCost ((ZetaRieszCentralPrimeLayers.centralUnpairedBand u N).filter
    (fun n => 4 ≤ n.primeFactors.card))
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (SquarefreeVaughanLogSource.length u N)

/-- The combined carrier has an ordinary convergent frequency integral. -/
theorem integrable_nonlinearFrequency (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    MeasureTheory.IntegrableOn (nonlinearFrequency P u y N) (Set.Ioi 0) :=
  (integrable_bandPrimePair _ _ _).add (integrable_bandPrimePair _ _ _)

/-- The two entire retained nonlinear arithmetic classes are recovered
from their coupled frequency integral, with no omitted prime degree. -/
theorem nonlinearResponse_eq_integral (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    ZetaRieszCentralPrimeLayers.centralThreePrimeResponse P u y N +
      ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse P u y N =
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ xi : ℝ in Set.Ioi 0, nonlinearFrequency P u y N xi := by
  rw [centralThreePrimeResponse_eq_integral, centralHigherPrimeResponse_eq_integral]
  unfold nonlinearFrequency
  rw [MeasureTheory.integral_add (integrable_bandPrimePair _ _ _)
    (integrable_bandPrimePair _ _ _), mul_add]

/-- Both actual nonlinear prime classes have a common cubic allowance
for their low-frequency sector. The finite arithmetic cost and the
original source normalization remain explicit; no source-scale decay
of this allowance is assumed. -/
theorem norm_nonlinear_low_frequency_le (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u d : ℝ} (hu : 0 ≤ u) (hd : 0 ≤ d) (hwindow : d * ((8 / 3 : ℝ) * N) ≤ 1) :
    ‖(u : ℂ) ^ (N + 1) * ((1 / (2 * (Real.pi : ℂ))) *
      ∫ xi : ℝ in 0..d, nonlinearFrequency P u y N xi)‖ ≤
        u ^ (N + 1) * d ^ 3 / (3 * Real.pi) * nonlinearFrequencyCost P u y N := by
  unfold nonlinearFrequency
  rw [intervalIntegral.integral_add
    (intervalIntegrable_bandPrimePair _ _ _ hd) (intervalIntegrable_bandPrimePair _ _ _ hd),
    mul_add, mul_add]
  apply (norm_add_le _ _).trans
  have h3 := norm_actual_three_low_frequency_le P y N hu hd
  have h4 := norm_actual_higher_low_frequency_le P y N hu hd hwindow
  exact (add_le_add h3 h4).trans_eq (by unfold nonlinearFrequencyCost; ring)

/-- The actual three-prime plus higher-prime sum differs from its
retained high-frequency integral by precisely the bounded low-frequency
sector. This keeps the full complementary signed sum in the theorem. -/
theorem norm_nonlinear_sub_high_frequency_le (P : Polynomial ℂ) (y : ℝ) (N : ℕ)
    {u d : ℝ} (hu : 0 ≤ u) (hd : 0 ≤ d) (hwindow : d * ((8 / 3 : ℝ) * N) ≤ 1) :
    ‖(u : ℂ) ^ (N + 1) *
      (ZetaRieszCentralPrimeLayers.centralThreePrimeResponse P u y N +
        ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse P u y N -
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ xi : ℝ in Set.Ioi d, nonlinearFrequency P u y N xi)‖ ≤
        u ^ (N + 1) * d ^ 3 / (3 * Real.pi) * nonlinearFrequencyCost P u y N := by
  rw [nonlinearResponse_eq_integral, ← mul_sub,
    intervalIntegral.integral_Ioi_sub_Ioi (integrable_nonlinearFrequency P u y N) hd]
  exact norm_nonlinear_low_frequency_le P y N hu hd hwindow

/-- A positive concrete frequency window works at every moment order,
including zero, throughout the actual retained central support. -/
theorem natural_frequency_window (N : ℕ) :
    0 < (3 : ℝ) / (8 * (N + 1)) ∧
      ((3 : ℝ) / (8 * (N + 1))) * ((8 / 3 : ℝ) * N) ≤ 1 := by
  constructor
  · positivity
  · calc
      _ = (N : ℝ) / (N + 1) := by field_simp
      _ ≤ 1 := (div_le_one (by positivity : (0 : ℝ) < N + 1)).mpr (by linarith)

end
end RiemannGaussian.ZetaRieszSignedFrequency
