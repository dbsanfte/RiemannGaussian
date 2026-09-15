/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReplacementPhase

/-!
# Opposite-phase prime insertions

Preserve the full complex filter, original support and unmatched remainder.
Centering halves a proved pair allowance; a source-scale saving for the
whole carrier and a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszOppositePrimes
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open ZetaArithmeticBandCorrelation ZetaSquarefreeRieszWindows
open ZetaRieszPrimeReplacement ZetaRieszReplacementPhase

/-- A half-turn negates the exact unit phase. -/
theorem unitPhase_add_pi (x : ℝ) : unitPhase (x + Real.pi) = -unitPhase x := by
  unfold unitPhase
  rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have he : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [mul_comm]
    exact Complex.exp_pi_mul_I
  rw [he, mul_neg_one]

/-- The sum of two original phases retains the cosine of their
half-angle difference, so opposite-phase cancellation stays visible. -/
theorem norm_unitPhase_add_eq (x y : ℝ) :
    ‖unitPhase x + unitPhase y‖ = 2 * |Real.cos ((x - y) / 2)| := by
  have h := norm_unitPhase_sub_eq x (y + Real.pi)
  rw [unitPhase_add_pi, sub_neg_eq_add] at h
  have he : (x - (y + Real.pi)) / 2 = (x - y) / 2 - Real.pi / 2 := by ring
  rw [he, Real.sin_sub_pi_div_two, abs_neg] at h
  exact h

/-- Replacing one prime by another leaves the exact cutoff difference
of the common cofactor. No smaller-profile deletion is needed. -/
theorem riesz_prime_difference (L : ℝ) {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) :
    VaughanLogAverage.riesz L (p * n) - VaughanLogAverage.riesz L (q * n) =
      VaughanLogAverage.riesz (L - Real.log q) n -
        VaughanLogAverage.riesz (L - Real.log p) n := by
  rw [riesz_prime_mul L hp hpn, riesz_prime_mul L hq hqn]
  ring

/-- The full prime-to-prime profile mismatch pays the prime-log gap
with no physical-cutoff growth and no zero hypothesis. -/
theorem abs_riesz_prime_difference_le (L : ℝ) {p q n : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) :
    |VaughanLogAverage.riesz L (p * n) - VaughanLogAverage.riesz L (q * n)| ≤
      |Real.log p - Real.log q| *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [riesz_prime_difference L hp hq hpn hqn]
  have h := riesz_cutoff_lipschitz (L - Real.log q) (L - Real.log p) n
  simpa only [sub_sub_sub_cancel_left] using h

/-- Opposite-phase pairing uses the sum of the full complex amplitudes,
while the actual Riesz profile difference is independently bounded. -/
theorem norm_bandWeight_prime_pair_le (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P N t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P N t (q * n)‖ ≤
      (‖bandAmplitude L P N t (p * n)‖ * |Real.log p - Real.log q| +
        ‖bandAmplitude L P N t (p * n) + bandAmplitude L P N t (q * n)‖ * Real.log q) *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [bandWeight_eq_amplitude_mul_riesz, bandWeight_eq_amplitude_mul_riesz]
  have he (A B : ℂ) (R S : ℝ) : A * (R : ℂ) + B * (S : ℂ) =
      A * ((R - S : ℝ) : ℂ) + (A + B) * (S : ℂ) := by push_cast; ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := mul_le_mul_of_nonneg_left (abs_riesz_prime_difference_le L hp hq hpn hqn)
    (norm_nonneg (bandAmplitude L P N t (p * n)))
  have h2 := mul_le_mul_of_nonneg_left (abs_riesz_prime_mul_le L hq hqn)
    (norm_nonneg (bandAmplitude L P N t (p * n) + bandAmplitude L P N t (q * n)))
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- The complete amplitude sum has an explicit cosine-phase bound.
The full complex polynomial stays coupled; only the spectral rotation is
separated, and every smooth allowance is proved on the same interval. -/
theorem norm_logAmplitude_add_le_phase (P : Polynomial ℂ) (N : ℕ) (sigma t : ℝ)
    {L r A B x y : ℝ} (hL : 0 < L) (hr : 0 < r) (hrs : r ≤ sigma) (hA : 0 ≤ A)
    (hx : x ∈ Set.Icc A B) (hy : y ∈ Set.Icc A B) :
    ‖logAmplitude L P (N + 1) (sigma + Complex.I * t) y +
      logAmplitude L P (N + 1) (sigma + Complex.I * t) x‖ ≤
      logAmplitudeAllowance L P N (sigma : ℂ) r A B * |y - x| +
        (B / L * logKernelEnvelope P (N + 1) (sigma : ℂ) r A) *
          (2 * |Real.cos (t * (y - x) / 2)|) := by
  rw [logAmplitude_add_imag, logAmplitude_add_imag]
  have he (a b u v : ℂ) : a * u + b * v = (a - b) * u + b * (u + v) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, norm_unitPhase, mul_one, norm_unitPhase_add_eq]
  have hang : (-t * y - -t * x) / 2 = -(t * (y - x) / 2) := by ring
  rw [hang, Real.cos_neg]
  exact add_le_add (norm_logAmplitude_sub_le P N (sigma : ℂ) hL hr hrs hA hx hy)
    (mul_le_mul_of_nonneg_right
      (norm_logAmplitude_le P (N + 1) (sigma : ℂ) hL hr hrs (hA.trans hx.1) hx.1 hx.2)
      (by positivity))

/-- The common cofactor cancels exactly from the signed logarithmic
distance of two original prime insertions. -/
theorem prime_insertion_log_difference {p q n : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hn : 0 < n) :
    Real.log (p * n : ℕ) - Real.log (q * n : ℕ) = Real.log p - Real.log q := by
  simp only [Nat.cast_mul]
  rw [Real.log_mul (by exact_mod_cast hp.ne') (by exact_mod_cast hn.ne'),
    Real.log_mul (by exact_mod_cast hq.ne') (by exact_mod_cast hn.ne'), add_sub_add_right_eq_sub]

/-- The independent cost for two prime insertions retains the exact
opposite-phase cosine, both original endpoints and full cofactor mass. -/
def oppositePrimeCost (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ) (p q n : ℕ) : ℝ :=
  let A := min (Real.log (q * n : ℕ)) (Real.log (p * n : ℕ))
  let B := max (Real.log (q * n : ℕ)) (Real.log (p * n : ℕ))
  let E := B / L * logKernelEnvelope P (N + 1) (3 / 2 : ℂ) r A
  let D := logAmplitudeAllowance L P N (3 / 2 : ℂ) r A B
  let gap := |Real.log p - Real.log q|
  (E * gap + (D * gap + E * (2 * |Real.cos (t * (Real.log p - Real.log q) / 2)|)) *
    Real.log q) * ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|

/-- Actual original pairs of equal prime count have a fully proved
opposite-phase bound. It applies to semiprimes as well as larger squarefree
integers and requires no saturated smaller terms. Existence of enough
useful pairs and their source-scale aggregate saving remain open. -/
theorem norm_bandWeight_prime_pair_le_phase (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1)
    (hBandP : p * n ∈ zetaPrimeLogBand (N + 1)) (hBandQ : q * n ∈ zetaPrimeLogBand (N + 1)) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (q * n)‖ ≤
      oppositePrimeCost L P N t r p q n := by
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
  apply (norm_bandWeight_prime_pair_le L P (N + 1) t hp hq hpn hqn).trans
  change _ ≤ (E * gap + (D * gap + E * chord) * Real.log q) * _
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (by intros; positivity))
  exact add_le_add (mul_le_mul_of_nonneg_right hamp (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hsum (Real.log_natCast_nonneg _))

/-- The full prime Riesz profile is exactly a clipped ramp, with
both cutoff edges retained even for negative cutoff values. -/
theorem riesz_prime_clipped (L : ℝ) {p : ℕ} (hp : p.Prime) :
    VaughanLogAverage.riesz L p = min (max L 0) (Real.log p) := by
  rw [VaughanLogAverage.riesz, hp.sum_divisors]
  simp only [ArithmeticFunction.moebius_apply_one, ArithmeticFunction.moebius_apply_prime hp,
    Int.cast_one, Int.cast_neg, one_mul, neg_mul, Nat.cast_one, Real.log_one, sub_zero]
  have hp0 := Real.log_natCast_nonneg p
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- A prime cofactor's profile has Lipschitz constant one, improving
the generic sum of two absolute divisor weights. -/
theorem prime_profile_lipschitz (L K : ℝ) {p : ℕ} (hp : p.Prime) :
    |VaughanLogAverage.riesz L p - VaughanLogAverage.riesz K p| ≤ |L - K| := by
  rw [riesz_prime_clipped L hp, riesz_prime_clipped K hp]
  have h := abs_min_sub_min_le_max (max L 0) (Real.log p) (max K 0) (Real.log p)
  simp only [sub_self, abs_zero] at h
  rw [max_eq_left (abs_nonneg (max L 0 - max K 0))] at h
  exact h.trans (abs_max_sub_max_le_abs L K 0)

/-- On semiprimes, the actual profile mismatch pays just the prime-log
gap, with no leftover divisor-count factor. -/
theorem abs_semiprime_profile_difference_le (L : ℝ) {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpr : p ≠ r) (hqr : q ≠ r) :
    |VaughanLogAverage.riesz L (p * r) - VaughanLogAverage.riesz L (q * r)| ≤
      |Real.log p - Real.log q| := by
  have hpn : ¬ p ∣ r := by intro h; exact hpr ((Nat.dvd_prime_two_le hr hp.two_le).mp h)
  have hqn : ¬ q ∣ r := by intro h; exact hqr ((Nat.dvd_prime_two_le hr hq.two_le).mp h)
  rw [riesz_prime_difference L hp hq hpn hqn]
  simpa only [sub_sub_sub_cancel_left] using prime_profile_lipschitz (L - Real.log q) (L - Real.log p) hr

/-- A complete semiprime coefficient is exactly the two-prime tent,
so its bound is the smaller prime logarithm without a divisor-count cost. -/
theorem abs_semiprime_profile_le (L : ℝ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    |VaughanLogAverage.riesz L (p * q)| ≤ min (Real.log p) (Real.log q) := by
  have h := riesz_two_primes_eq_tent L (m := 1) hp hq hpq
    (by simpa using hp.ne_one) (by simpa using hq.ne_one)
  simp only [mul_one, Nat.divisors_one, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one,
    Int.cast_one, one_mul, Nat.cast_one, Real.log_one, sub_zero] at h
  rw [h, abs_of_nonneg (primePairTent_bounds (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _) _).1]
  exact (primePairTent_bounds (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _) _).2

/-- The original semiprime pair has a sharper full-amplitude bound:
the profile difference costs one gap, and its retained profile costs the
smaller prime logarithm. No two-divisor triangle factor remains. -/
theorem norm_bandWeight_semiprime_pair_le (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hn : n.Prime) (hpn : p ≠ n) (hqn : q ≠ n) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P N t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P N t (q * n)‖ ≤
      ‖bandAmplitude L P N t (p * n)‖ * |Real.log p - Real.log q| +
        ‖bandAmplitude L P N t (p * n) + bandAmplitude L P N t (q * n)‖ *
          min (Real.log q) (Real.log n) := by
  rw [bandWeight_eq_amplitude_mul_riesz, bandWeight_eq_amplitude_mul_riesz]
  have he (A B : ℂ) (R S : ℝ) : A * (R : ℂ) + B * (S : ℂ) =
      A * ((R - S : ℝ) : ℂ) + (A + B) * (S : ℂ) := by push_cast; ring
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (abs_semiprime_profile_difference_le L hp hq hn hpn hqn) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (abs_semiprime_profile_le L hq hn hqn) (norm_nonneg _))

/-- The exact two-divisor Mobius mass explains the factor removed by
the prime-specific profile estimate. -/
theorem prime_absolute_divisor_mass {p : ℕ} (hp : p.Prime) :
    (∑ d ∈ p.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) = 2 := by
  rw [hp.sum_divisors]
  norm_num [ArithmeticFunction.moebius_apply_prime hp]

/-- For every actual semiprime pair, the complete independent cosine
allowance improves by a factor of two. All band, phase and full-polynomial
conditions are retained. No pair-density or source-scale conclusion follows. -/
theorem norm_bandWeight_semiprime_pair_le_half_phaseCost (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n)
    (hn : n.Prime)
    (hBandP : p * n ∈ zetaPrimeLogBand (N + 1)) (hBandQ : q * n ∈ zetaPrimeLogBand (N + 1)) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (q * n)‖ ≤
      oppositePrimeCost L P N t r p q n / 2 := by
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
  have hsuqq := prime_mul_composite_support hq hn.squarefree hn.ne_one hqn
  have hsupp := prime_mul_composite_support hp hn.squarefree hn.ne_one hpn
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
    rw [prime_insertion_log_difference hp.pos hq.pos hn.pos] at hh
    simpa only [D, E, gap, chord, Complex.ofReal_div, Complex.ofReal_ofNat] using hh
  have hpn' : p ≠ n := by intro h; exact hpn (h ▸ dvd_refl n)
  have hqn' : q ≠ n := by intro h; exact hqn (h ▸ dvd_refl n)
  have hD : 0 ≤ D := logAmplitudeAllowance_nonneg P N (3 / 2 : ℂ) hL.le hr.le
    ((Real.log_natCast_nonneg _).trans (le_max_left _ _))
  have hE : 0 ≤ E := by unfold E logKernelEnvelope; positivity
  have hC : 0 ≤ D * gap + E * chord := by unfold gap chord; positivity
  have hbound : ‖ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (p * n) +
      ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (q * n)‖ ≤
      E * gap + (D * gap + E * chord) * Real.log q := by
    apply (norm_bandWeight_semiprime_pair_le L P (N + 1) t hp hq hn hpn' hqn').trans
    apply add_le_add (mul_le_mul_of_nonneg_right hamp (abs_nonneg _))
    exact (mul_le_mul_of_nonneg_right hsum
      (le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
  have he : oppositePrimeCost L P N t r p q n / 2 =
      E * gap + (D * gap + E * chord) * Real.log q := by
    unfold oppositePrimeCost
    rw [prime_absolute_divisor_mass hn]
    dsimp only [E, D, gap, chord, A, B]
    ring
  rw [he]
  exact hbound

end
end RiemannGaussian.ZetaRieszOppositePrimes
