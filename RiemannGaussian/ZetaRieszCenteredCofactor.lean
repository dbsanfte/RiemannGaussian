/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReplacementPhase
import RiemannGaussian.ZetaRieszPrimeFourier

/-!
# Center the complete nonunit Mobius cofactor

Preserve the full complex filter, original support and unmatched remainder.
Centering halves a proved pair allowance; a source-scale saving for the
whole carrier and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszCenteredCofactor
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaArithmeticBandCorrelation

/-- A zero-mass signed sum pays only half the range of its observable. -/
theorem abs_sum_mul_le_half_range {ι : Type*} (S : Finset ι) (w f : ι → ℝ)
    (hm : ∑ i ∈ S, w i = 0) {a b : ℝ}
    (hf : ∀ i ∈ S, a ≤ f i ∧ f i ≤ b) :
    |∑ i ∈ S, w i * f i| ≤ (b - a) / 2 * ∑ i ∈ S, |w i| := by
  have he : (∑ i ∈ S, w i * f i) =
      ∑ i ∈ S, w i * (f i - (a + b) / 2) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hm, zero_mul, sub_zero]
  rw [he, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul, mul_comm ((b - a) / 2)]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply abs_le.mpr
  have := hf i hi
  constructor <;> linarith

/-- The oriented cutoff increment lies in an interval of length K-L,
not an interval of length twice that amount. -/
theorem hinge_increment_range {L K : ℝ} (hLK : L ≤ K) (v : ℝ) :
    0 ≤ max 0 (K - v) - max 0 (L - v) ∧
      max 0 (K - v) - max 0 (L - v) ≤ K - L := by
  constructor
  · exact sub_nonneg.mpr (max_le_max_left 0 (sub_le_sub_right hLK v))
  · simp only [max_def]
    split_ifs <;> linarith

/-- Centering uses the complete, actually vanishing nonunit Mobius mass.
This is uniform over every real cutoff, including clipped endpoints. -/
theorem riesz_cutoff_lipschitz_centered (L K : ℝ) {n : ℕ} (hn : n ≠ 1) :
    |VaughanLogAverage.riesz L n - VaughanLogAverage.riesz K n| ≤
      |L - K| / 2 * ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  have hm : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero hn
  have hordered (x y : ℝ) (hxy : x ≤ y) :
      |VaughanLogAverage.riesz y n - VaughanLogAverage.riesz x n| ≤
        (y - x) / 2 * ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
    have h := abs_sum_mul_le_half_range n.divisors
      (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      (fun d => max 0 (y - Real.log d) - max 0 (x - Real.log d)) hm
      (fun d _ => hinge_increment_range hxy (Real.log d))
    simpa only [sub_zero, mul_sub, Finset.sum_sub_distrib, VaughanLogAverage.riesz] using h
  rcases le_total K L with hKL | hLK
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hKL)] using hordered K L hKL
  · rw [abs_sub_comm L K, abs_of_nonneg (sub_nonneg.mpr hLK), abs_sub_comm]
    exact hordered L K hLK

/-- The prime-insertion difference inherits the centered cofactor gain. -/
theorem abs_riesz_prime_difference_centered (L : ℝ) {p q n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hn : n ≠ 1) :
    |VaughanLogAverage.riesz L (p * n) - VaughanLogAverage.riesz L (q * n)| ≤
      |Real.log p - Real.log q| / 2 *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [riesz_prime_mul L hp hpn, riesz_prime_mul L hq hqn, sub_sub_sub_cancel_left]
  have h := riesz_cutoff_lipschitz_centered (L - Real.log q) (L - Real.log p) hn
  simpa only [sub_sub_sub_cancel_left] using h

/-- The full inserted-prime profile also saves the same factor of two.
The common cofactor is nonunit; no primality of that cofactor is needed. -/
theorem abs_riesz_prime_mul_centered (L : ℝ) {p n : ℕ}
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hn : n ≠ 1) :
    |VaughanLogAverage.riesz L (p * n)| ≤ Real.log p / 2 *
      ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [riesz_prime_mul L hp hpn]
  simpa only [sub_sub_cancel, abs_of_nonneg (Real.log_natCast_nonneg p)] using
    riesz_cutoff_lipschitz_centered L (L - Real.log p) hn

/-- The complete opposite-phase pair pays half the former profile cost.
This retains the actual complex amplitude sum for all nonunit cofactors. -/
theorem norm_bandWeight_prime_pair_centered (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    (hn : n ≠ 1) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P N t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P N t (q * n)‖ ≤
      (‖bandAmplitude L P N t (p * n)‖ * |Real.log p - Real.log q| +
        ‖bandAmplitude L P N t (p * n) + bandAmplitude L P N t (q * n)‖ * Real.log q) *
        (∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) / 2 := by
  rw [bandWeight_eq_amplitude_mul_riesz, bandWeight_eq_amplitude_mul_riesz]
  have he (A B : ℂ) (R S : ℝ) : A * (R : ℂ) + B * (S : ℂ) =
      A * ((R - S : ℝ) : ℂ) + (A + B) * (S : ℂ) := by push_cast; ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := mul_le_mul_of_nonneg_left (abs_riesz_prime_difference_centered L hp hq hpn hqn hn)
    (norm_nonneg (bandAmplitude L P N t (p * n)))
  have h2 := mul_le_mul_of_nonneg_left (abs_riesz_prime_mul_centered L hq hqn hn)
    (norm_nonneg (bandAmplitude L P N t (p * n) + bandAmplitude L P N t (q * n)))
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- The compact two-prime tent is nonnegative, so centering its range
also halves the full cost for every nonunit common cofactor. -/
theorem abs_riesz_two_primes_centered (L : ℝ) {a b n : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (han : ¬ a ∣ n) (hbn : ¬ b ∣ n) (hn : n ≠ 1) :
    |VaughanLogAverage.riesz L (a * (b * n))| ≤
      min (Real.log a) (Real.log b) / 2 *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [riesz_two_primes_eq_tent L ha hb hab han hbn]
  have hm : (∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 0 := by
    exact_mod_cast ZetaRieszPrimeFourier.sum_moebius_eq_zero hn
  have h := abs_sum_mul_le_half_range n.divisors
    (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
    (fun d => primePairTent (Real.log a) (Real.log b) (L - Real.log d)) hm
    (fun d _ => primePairTent_bounds (Real.log_natCast_nonneg a)
      (Real.log_natCast_nonneg b) (L - Real.log d))
  simpa only [sub_zero] using h

/-- Prime-to-product cancellation gets the same centered improvement.
Both saturated smaller profiles and the complete amplitude mismatch stay
explicit; no prime-gap or density hypothesis is added. -/
theorem norm_bandWeight_replacement_pair_centered (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {a b q n : ℕ} (ha : a.Prime) (hb : b.Prime) (hq : q.Prime) (hab : a ≠ b)
    (han : ¬ a ∣ n) (hbn : ¬ b ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1)
    (haL : Real.log (a * n : ℕ) ≤ L) (hbL : Real.log (b * n : ℕ) ≤ L) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P N t (q * n) +
      ZetaRieszConditionedEnergy.bandWeight L P N t (a * (b * n))‖ ≤
      (‖bandAmplitude L P N t (q * n)‖ * |Real.log q - Real.log (a * b : ℕ)| +
        ‖bandAmplitude L P N t (a * (b * n)) - bandAmplitude L P N t (q * n)‖ *
          min (Real.log a) (Real.log b)) *
        (∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) / 2 := by
  have hpair := ZetaRieszPrimeReplacement.riesz_prime_replacement_pair L ha hb hq hab han hbn hqn
    hn hn1 haL hbL
  have hgap : |VaughanLogAverage.riesz L (q * n) +
      VaughanLogAverage.riesz L (a * (b * n))| ≤
      |Real.log q - Real.log (a * b : ℕ)| / 2 *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
    rw [hpair]
    have hh := riesz_cutoff_lipschitz_centered (L - Real.log a - Real.log b) (L - Real.log q) hn1
    have he : (L - Real.log a - Real.log b) - (L - Real.log q) =
        Real.log q - Real.log (a * b : ℕ) := by
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne_zero) (by exact_mod_cast hb.ne_zero)]
      ring
    rwa [he] at hh
  rw [bandWeight_eq_amplitude_mul_riesz, bandWeight_eq_amplitude_mul_riesz]
  have he (A B : ℂ) (R S : ℝ) : A * (R : ℂ) + B * (S : ℂ) =
      A * ((R + S : ℝ) : ℂ) + (B - A) * (S : ℂ) := by push_cast; ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := mul_le_mul_of_nonneg_left hgap (norm_nonneg (bandAmplitude L P N t (q * n)))
  have h2 := mul_le_mul_of_nonneg_left (abs_riesz_two_primes_centered L ha hb hab han hbn hn1)
    (norm_nonneg (bandAmplitude L P N t (a * (b * n)) - bandAmplitude L P N t (q * n)))
  exact (add_le_add h1 h2).trans_eq (by ring)

end
end RiemannGaussian.ZetaRieszCenteredCofactor
