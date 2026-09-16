/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCenteredPhase
import RiemannGaussian.ZetaRieszSperner

/-!
# Retain the coupled slopes of the two-prime tent

Keep the actual cutoff, full polynomial, local pair interval and phase.
The resulting pair costs are independently proved; aggregate cancellation
at source scale and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszTentSlope
noncomputable section
open scoped BigOperators Classical
open ZetaSquarefreeRieszWindows ZetaArithmeticBandCorrelation
open ZetaRieszPrimeReplacement ZetaRieszReplacementPhase ZetaRieszOppositePrimes

/-- The original four-hinge kernel is a clipped minimum of four
one-Lipschitz affine profiles. Both moving edges and the plateau remain. -/
theorem primePairTent_eq_clipped_min {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (v : ℝ) :
    primePairTent a b v = max 0 (min (min a b) (min v (a + b - v))) := by
  rw [primePairTent_eq_overlap ha hb]
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- The whole two-prime kernel has slope at most one, independently
of the two logarithmic widths. Bounding its four hinges separately loses
this factor of four. -/
theorem primePairTent_lipschitz {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (v w : ℝ) :
    |primePairTent a b v - primePairTent a b w| ≤ |v - w| := by
  rw [primePairTent_eq_clipped_min ha hb, primePairTent_eq_clipped_min ha hb]
  have h1 := abs_min_sub_min_le_max v (a + b - v) w (a + b - w)
  have he : (a + b - v) - (a + b - w) = -(v - w) := by ring
  rw [he, abs_neg, max_self] at h1
  have h2 := abs_min_sub_min_le_max (min a b) (min v (a + b - v))
    (min a b) (min w (a + b - w))
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h2
  have h3 := abs_max_sub_max_le_abs (min (min a b) (min v (a + b - v)))
    (min (min a b) (min w (a + b - w))) 0
  rw [max_comm _ 0, max_comm _ 0] at h3
  exact h3.trans (h2.trans h1)

/-- The full cutoff difference pays only the remaining cofactor mass,
with both prime insertions canceled before the absolute sum is taken. -/
theorem riesz_two_prime_cutoff_lipschitz (L K : ℝ) {a b m : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (ham : ¬ a ∣ m) (hbm : ¬ b ∣ m) :
    |VaughanLogAverage.riesz L (a * (b * m)) -
      VaughanLogAverage.riesz K (a * (b * m))| ≤
      |L - K| * ∑ d ∈ m.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [riesz_two_primes_eq_tent L ha hb hab ham hbm,
    riesz_two_primes_eq_tent K ha hb hab ham hbm, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [← mul_sub, abs_mul]
  have h := primePairTent_lipschitz (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg b)
    (L - Real.log d) (K - Real.log d)
  rw [sub_sub_sub_cancel_right] at h
  exact (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans_eq (mul_comm _ _)

/-- On squarefree support every divisor has unit absolute Mobius weight. -/
theorem absolute_divisor_mass_eq_card {n : ℕ} (hn : Squarefree n) :
    (∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) =
      (n.divisors.card : ℝ) := by
  calc
    _ = ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = _ := by simp

/-- A new prime exactly doubles the squarefree divisor mass. -/
theorem absolute_divisor_mass_prime_mul {p n : ℕ} (hp : p.Prime) (hn : Squarefree n)
    (hpn : ¬ p ∣ n) :
    (∑ d ∈ (p * n).divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) =
      2 * ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  have hcop := hp.coprime_iff_not_dvd.mpr hpn
  have hs := (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hn⟩
  rw [absolute_divisor_mass_eq_card hs, absolute_divisor_mass_eq_card hn,
    hcop.card_divisors_mul, Nat.cast_mul]
  have hpC : (p.divisors.card : ℝ) = 2 := by
    have h := hp.sum_divisors (f := fun _ : ℕ => (1 : ℝ))
    norm_num at h
    exact h
  rw [hpC]

/-- Every squarefree cofactor with at least two primes saves a factor
of four in its complete cutoff Lipschitz allowance. The two primes are
selected from the actual factorization; no small-prime premise remains. -/
theorem riesz_cutoff_lipschitz_quarter (L K : ℝ) {n : ℕ} (hn : Squarefree n)
    (hcard : 2 ≤ n.primeFactors.card) :
    |VaughanLogAverage.riesz L n - VaughanLogAverage.riesz K n| ≤
      |L - K| / 4 * ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  obtain ⟨a, b, m, ha, hb, hab, he, hm, ham, hbm, _, _, _⟩ :=
    ZetaRieszSperner.exists_two_smallest_factorization hn hcard
  have hbmS := (Nat.squarefree_mul (hb.coprime_iff_not_dvd.mpr hbm)).mpr ⟨hb.squarefree, hm⟩
  have habm : ¬ a ∣ b * m := ZetaRieszPrimeReplacement.not_dvd_prime_mul ha hb hab ham
  rw [he, absolute_divisor_mass_prime_mul ha hbmS habm,
    absolute_divisor_mass_prime_mul hb hm hbm]
  exact (riesz_two_prime_cutoff_lipschitz L K ha hb hab ham hbm).trans_eq (by ring)

/-- The prime-insertion difference inherits the coupled two-prime slope gain. -/
theorem abs_riesz_prime_difference_quarter (L : ℝ) {p q n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card) :
    |VaughanLogAverage.riesz L (p * n) - VaughanLogAverage.riesz L (q * n)| ≤
      |Real.log p - Real.log q| / 4 *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [riesz_prime_mul L hp hpn, riesz_prime_mul L hq hqn, sub_sub_sub_cancel_left]
  have h := riesz_cutoff_lipschitz_quarter (L - Real.log q) (L - Real.log p) hn hcard
  simpa only [sub_sub_sub_cancel_left] using h

/-- The full inserted-prime profile also saves the factor of four.
The common cofactor contains at least two distinct prime factors. -/
theorem abs_riesz_prime_mul_quarter (L : ℝ) {p n : ℕ}
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card) :
    |VaughanLogAverage.riesz L (p * n)| ≤ Real.log p / 4 *
      ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [riesz_prime_mul L hp hpn]
  simpa only [sub_sub_cancel, abs_of_nonneg (Real.log_natCast_nonneg p)] using
    riesz_cutoff_lipschitz_quarter L (L - Real.log p) hn hcard

/-- The complete opposite-phase pair pays a quarter of the original divisor-mass cost.
This retains the actual complex amplitude sum for every squarefree cofactor
with at least two prime factors. -/
theorem norm_bandWeight_prime_pair_quarter (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P N t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P N t (q * n)‖ ≤
      (‖bandAmplitude L P N t (p * n)‖ * |Real.log p - Real.log q| +
        ‖bandAmplitude L P N t (p * n) + bandAmplitude L P N t (q * n)‖ * Real.log q) *
        (∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) / 4 := by
  rw [bandWeight_eq_amplitude_mul_riesz, bandWeight_eq_amplitude_mul_riesz]
  have he (A B : ℂ) (R S : ℝ) : A * (R : ℂ) + B * (S : ℂ) =
      A * ((R - S : ℝ) : ℂ) + (A + B) * (S : ℂ) := by push_cast; ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := mul_le_mul_of_nonneg_left (abs_riesz_prime_difference_quarter L hp hq hpn hqn hn hcard)
    (norm_nonneg (bandAmplitude L P N t (p * n)))
  have h2 := mul_le_mul_of_nonneg_left (abs_riesz_prime_mul_quarter L hq hqn hn hcard)
    (norm_nonneg (bandAmplitude L P N t (p * n) + bandAmplitude L P N t (q * n)))
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- Retaining both prime slopes quarters the original full opposite-phase
cost whenever the common squarefree cofactor has at least two prime factors. The full polynomial, physical support, smooth allowance and exact
cosine phase are retained. -/
theorem norm_bandWeight_prime_pair_le_quarter_phaseCost (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hcard : 2 ≤ n.primeFactors.card)
    (hBandP : p * n ∈ zetaPrimeLogBand (N + 1)) (hBandQ : q * n ∈ zetaPrimeLogBand (N + 1)) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (q * n)‖ ≤
      oppositePrimeCost L P N t r p q n / 4 := by
  have hn1 : n ≠ 1 := by intro h; subst n; norm_num at hcard
  let A := min (Real.log (q * n : ℕ)) (Real.log (p * n : ℕ))
  let B := max (Real.log (q * n : ℕ)) (Real.log (p * n : ℕ))
  let E := B / L * logKernelEnvelope P (N + 1) (3 / 2 : ℂ) r A
  let D := logAmplitudeAllowance L P N (3 / 2 : ℂ) r A B
  let gap := |Real.log p - Real.log q|
  let chord := 2 * |Real.cos (t * (Real.log p - Real.log q) / 2)|
  have hA : 0 ≤ A := le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hx : Real.log (q * n : ℕ) ∈ Set.Icc A B := ⟨min_le_left _ _, le_max_left _ _⟩
  have hy : Real.log (p * n : ℕ) ∈ Set.Icc A B := ⟨min_le_right _ _, le_max_right _ _⟩
  have hrs : r ≤ (3 / 2 : ℂ).re := by norm_num; exact hr3
  have hsuqq := prime_mul_composite_support hq hn hn1 hqn
  have hsupp := prime_mul_composite_support hp hn hn1 hpn
  have hqeq := bandAmplitude_eq_logAmplitude L P (N + 1) t ⟨hBandQ, hsuqq⟩
  have hpeq := bandAmplitude_eq_logAmplitude L P (N + 1) t ⟨hBandP, hsupp⟩
  have hamp : ‖bandAmplitude L P (N + 1) t (p * n)‖ ≤ E := by
    rw [hpeq]
    have he := norm_logAmplitude_add_imag L P (N + 1) (3 / 2) t (Real.log (p * n : ℕ))
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
    rw [he]
    exact norm_logAmplitude_le P (N + 1) (3 / 2 : ℂ)
      (L := L) (r := r) (A := A) (B := B) (v := Real.log (p * n : ℕ))
      hL hr hrs (Real.log_natCast_nonneg (p * n)) hy.1 hy.2
  have hsum : ‖bandAmplitude L P (N + 1) t (p * n) + bandAmplitude L P (N + 1) t (q * n)‖ ≤
      D * gap + E * chord := by
    rw [hpeq, hqeq]
    have hh := norm_logAmplitude_add_le_phase P N (3 / 2) t hL hr hr3 hA hx hy
    rw [prime_insertion_log_difference hp.pos hq.pos (Nat.pos_of_ne_zero hn.ne_zero)] at hh
    simpa only [D, E, gap, chord, Complex.ofReal_div, Complex.ofReal_ofNat] using hh
  apply (norm_bandWeight_prime_pair_quarter L P (N + 1) t hp hq hpn hqn hn hcard).trans
  change _ ≤ (E * gap + (D * gap + E * chord) * Real.log q) * _ / 4
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (by intros; positivity))
  exact add_le_add (mul_le_mul_of_nonneg_right hamp (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hsum (Real.log_natCast_nonneg _))

end
end RiemannGaussian.ZetaRieszTentSlope
