/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWindowUnitDeletion
import RiemannGaussian.ZetaPrimeKernelSecondDifference

/-!
# Quantitative prime-to-product cancellation

Retain the actual prime support, cutoff and full complex amplitudes.
Quantitative pair bounds do not establish source-scale saving of the
whole signed carrier or a new zero-free region.
-/

namespace RiemannGaussian.ZetaRieszPrimeReplacement
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open ZetaSquarefreeRieszWindows ZetaArithmeticBandCorrelation

/-- The two inserted primes remain coprime to the opposite factor
and to the common original cofactor. -/
theorem not_dvd_prime_mul {a b n : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hab : a ≠ b) (han : ¬ a ∣ n) : ¬ a ∣ b * n := by
  intro h
  rcases ha.dvd_mul.mp h with h | h
  · exact hab ((Nat.dvd_prime_two_le hb ha.two_le).mp h)
  · exact han h

/-- Prime replacement has an exact four-integer cutoff identity.
The two smaller original integers are present explicitly; no cutoff
completion or phase averaging has taken place. -/
theorem riesz_prime_replacement_identity (L : ℝ) {a b q n : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hq : q.Prime) (hab : a ≠ b)
    (han : ¬ a ∣ n) (hbn : ¬ b ∣ n) (hqn : ¬ q ∣ n) :
    VaughanLogAverage.riesz L (q * n) + VaughanLogAverage.riesz L (a * (b * n)) -
      VaughanLogAverage.riesz L (a * n) - VaughanLogAverage.riesz L (b * n) =
      VaughanLogAverage.riesz (L - Real.log a - Real.log b) n -
        VaughanLogAverage.riesz (L - Real.log q) n := by
  rw [riesz_prime_mul L hq hqn, riesz_prime_mul L ha (not_dvd_prime_mul ha hb hab han),
    riesz_prime_mul L ha han, riesz_prime_mul L hb hbn,
    riesz_prime_mul (L - Real.log a) hb hbn]
  ring

/-- Cancellation between four actual integers pays only the prime-to-
product logarithmic gap times the common cofactor's divisor mass. -/
theorem abs_riesz_prime_replacement_le (L : ℝ) {a b q n : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hq : q.Prime) (hab : a ≠ b)
    (han : ¬ a ∣ n) (hbn : ¬ b ∣ n) (hqn : ¬ q ∣ n) :
    |VaughanLogAverage.riesz L (q * n) + VaughanLogAverage.riesz L (a * (b * n)) -
      VaughanLogAverage.riesz L (a * n) - VaughanLogAverage.riesz L (b * n)| ≤
      |Real.log q - Real.log (a * b : ℕ)| *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  rw [riesz_prime_replacement_identity L ha hb hq hab han hbn hqn]
  have hh := riesz_cutoff_lipschitz (L - Real.log a - Real.log b) (L - Real.log q) n
  have he : (L - Real.log a - Real.log b) - (L - Real.log q) =
      Real.log q - Real.log (a * b : ℕ) := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast ha.ne_zero) (by exact_mod_cast hb.ne_zero)]
    ring
  rwa [he] at hh

/-- The multiplicative replacement gap is bounded by its literal
integer gap divided by the smaller positive integer. -/
theorem abs_log_nat_sub_log_nat_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    |Real.log a - Real.log b| ≤ |(a : ℝ) - b| / min (a : ℝ) b := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  apply abs_sub_le_iff.mpr
  constructor
  · exact log_sub_le_gap_div haR hbR (lt_min haR hbR) (min_le_right _ _)
  · simpa only [abs_sub_comm] using
      log_sub_le_gap_div hbR haR (lt_min haR hbR) (min_le_left _ _)

/-- Saturation of the two smaller profiles leaves a genuinely
oppositely signed pair. Their deletion is an explicit proved condition. -/
theorem riesz_prime_replacement_pair (L : ℝ) {a b q n : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hq : q.Prime) (hab : a ≠ b)
    (han : ¬ a ∣ n) (hbn : ¬ b ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1)
    (haL : Real.log (a * n : ℕ) ≤ L) (hbL : Real.log (b * n : ℕ) ≤ L) :
    VaughanLogAverage.riesz L (q * n) + VaughanLogAverage.riesz L (a * (b * n)) =
      VaughanLogAverage.riesz (L - Real.log a - Real.log b) n -
        VaughanLogAverage.riesz (L - Real.log q) n := by
  have hsa : Squarefree (a * n) := (Nat.squarefree_mul (ha.coprime_iff_not_dvd.mpr han)).mpr ⟨ha.squarefree, hn⟩
  have hsb : Squarefree (b * n) := (Nat.squarefree_mul (hb.coprime_iff_not_dvd.mpr hbn)).mpr ⟨hb.squarefree, hn⟩
  have ha1 : a * n ≠ 1 := by intro he; exact ha.ne_one (mul_eq_one.mp he).1
  have hb1 : b * n ≠ 1 := by intro he; exact hb.ne_one (mul_eq_one.mp he).1
  have hna : ¬ (a * n).Prime := by
    intro hp
    have hh := (Nat.dvd_prime hp).mp (dvd_mul_right a n)
    rcases hh with hh | hh
    · exact ha.ne_one hh
    · have hcan : a * 1 = a * n := by simpa using hh
      exact hn1 ((Nat.eq_of_mul_eq_mul_left ha.pos hcan).symm)
  have hnb : ¬ (b * n).Prime := by
    intro hp
    have hh := (Nat.dvd_prime hp).mp (dvd_mul_right b n)
    rcases hh with hh | hh
    · exact hb.ne_one hh
    · have hcan : b * 1 = b * n := by simpa using hh
      exact hn1 ((Nat.eq_of_mul_eq_mul_left hb.pos hcan).symm)
  have he := riesz_prime_replacement_identity L ha hb hq hab han hbn hqn
  rw [ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hsa ha1 hna haL,
    ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated hsb hb1 hnb hbL,
    sub_zero, sub_zero] at he
  exact he

/-- The two-prime Riesz profile is bounded by the smaller prime log
times the original cofactor mass; its full signed profile stays upstream. -/
theorem abs_riesz_two_primes_le (L : ℝ) {a b n : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (han : ¬ a ∣ n) (hbn : ¬ b ∣ n) :
    |VaughanLogAverage.riesz L (a * (b * n))| ≤
      min (Real.log a) (Real.log b) *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  exact (abs_riesz_two_primes_boundary_le L ha hb hab han hbn).trans
    (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; positivity))
      (le_min (Real.log_natCast_nonneg a) (Real.log_natCast_nonneg b)))

/-- The literal pair of original band weights has a quantitative
cancellation bound. The exact original amplitudes, including their complex
phases, are compared before a norm is taken; no common-phase assumption is used. -/
theorem norm_bandWeight_replacement_pair_le (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {a b q n : ℕ} (ha : a.Prime) (hb : b.Prime) (hq : q.Prime) (hab : a ≠ b)
    (han : ¬ a ∣ n) (hbn : ¬ b ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1)
    (haL : Real.log (a * n : ℕ) ≤ L) (hbL : Real.log (b * n : ℕ) ≤ L) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P N t (q * n) +
      ZetaRieszConditionedEnergy.bandWeight L P N t (a * (b * n))‖ ≤
      (‖bandAmplitude L P N t (q * n)‖ * |Real.log q - Real.log (a * b : ℕ)| +
        ‖bandAmplitude L P N t (a * (b * n)) - bandAmplitude L P N t (q * n)‖ *
          min (Real.log a) (Real.log b)) *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
  have hpair := riesz_prime_replacement_pair L ha hb hq hab han hbn hqn hn hn1 haL hbL
  have hgap : |VaughanLogAverage.riesz L (q * n) +
      VaughanLogAverage.riesz L (a * (b * n))| ≤
      |Real.log q - Real.log (a * b : ℕ)| *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
    rw [hpair]
    have hh := riesz_cutoff_lipschitz (L - Real.log a - Real.log b) (L - Real.log q) n
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
  calc
    _ ≤ ‖bandAmplitude L P N t (q * n)‖ *
          (|Real.log q - Real.log (a * b : ℕ)| *
            ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) +
        ‖bandAmplitude L P N t (a * (b * n)) - bandAmplitude L P N t (q * n)‖ *
          (min (Real.log a) (Real.log b) *
            ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|) :=
      add_le_add (mul_le_mul_of_nonneg_left hgap (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (abs_riesz_two_primes_le L ha hb hab han hbn) (norm_nonneg _))
    _ = _ := by ring

/-- The full smooth amplitude in logarithmic coordinates, with the
original factorial filter and complex spectral parameter retained. -/
def logAmplitude (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (v : ℝ) : ℂ :=
  ((-v / L : ℝ) : ℂ) * zetaPrimeFilterKernel P N s (Real.exp v)

/-- The smooth logarithmic amplitude equals the literal band amplitude
on its original support. There is no extension across a discrete cutoff. -/
theorem bandAmplitude_eq_logAmplitude (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {n : ℕ} (hn : n ∈ zetaPrimeLogBand N ∧ Squarefree n ∧ ¬ n.Prime) :
    bandAmplitude L P N t n = logAmplitude L P N (3 / 2 + Complex.I * t) (Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn.2.1.ne_zero
  simp only [bandAmplitude, if_pos hn, logAmplitude, Real.exp_log hn0]

/-- The derivative of the full factorial kernel in logarithmic
coordinates keeps both adjacent orders and the exact complex rotation. -/
theorem hasDerivAt_logKernel (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (v : ℝ) :
    HasDerivAt (fun x : ℝ => zetaPrimeFilterKernel P (N + 1) s (Real.exp x))
      (zetaPrimeFilterKernel P N s (Real.exp v) -
        s * zetaPrimeFilterKernel P (N + 1) s (Real.exp v)) v := by
  have h := (hasDerivAt_zetaPrimeFilterKernel P N s (Real.exp_pos v)).scomp v
    (Real.hasDerivAt_exp v)
  apply h.congr_deriv
  simp only [Complex.real_smul]
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v))

/-- Differentiation preserves the full arithmetic amplitude, including
its extra logarithm, normalization and imaginary phase coefficient. -/
theorem hasDerivAt_logAmplitude (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (v : ℝ) :
    HasDerivAt (logAmplitude L P (N + 1) s)
      (((-1 / L : ℝ) : ℂ) *
        (zetaPrimeFilterKernel P (N + 1) s (Real.exp v) + (v : ℂ) *
          (zetaPrimeFilterKernel P N s (Real.exp v) -
            s * zetaPrimeFilterKernel P (N + 1) s (Real.exp v)))) v := by
  have h := (((hasDerivAt_id v).neg.div_const L).ofReal_comp).mul (hasDerivAt_logKernel P N s v)
  apply h.congr_deriv
  simp only [Pi.neg_apply, id_eq, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one]
  ring

/-- An explicit envelope for the complete kernel on a logarithmic
interval, retaining every coefficient of the fixed polynomial filter. -/
def logKernelEnvelope (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (r A : ℝ) : ℝ :=
  r⁻¹ ^ N * Real.exp (-(s.re - r) * A) *
    ∑ k ∈ P.support, ‖P.coeff k‖ * r⁻¹ ^ k

/-- The explicit logarithmic derivative allowance includes the full
ordinate-dependent rotation cost, rather than bounding only the phase. -/
def logAmplitudeAllowance (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (r A B : ℝ) : ℝ :=
  logKernelEnvelope P N s r A / L * (r⁻¹ + B * (1 + ‖s‖ * r⁻¹))

/-- A positive tilt and a lower logarithmic endpoint give a uniform
bound on the full kernel throughout the actual comparison interval. -/
theorem norm_logKernel_le (P : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {r A v : ℝ} (hr : 0 < r) (hrs : r ≤ s.re) (hv : 0 ≤ v) (hAv : A ≤ v) :
    ‖zetaPrimeFilterKernel P N s (Real.exp v)‖ ≤ logKernelEnvelope P N s r A := by
  have h := norm_zetaPrimeFilterKernel_le_tilt P N s (Real.one_le_exp_iff.mpr hv) hr
  rw [Real.log_exp] at h
  apply h.trans
  unfold logKernelEnvelope
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hAv (neg_nonpos.mpr (sub_nonneg.mpr hrs))))
      (by positivity)) (Finset.sum_nonneg (by intros; positivity))

/-- The adjacent-order envelope has its exact extra reciprocal tilt. -/
theorem logKernelEnvelope_succ (P : Polynomial ℂ) (N : ℕ) (s : ℂ) (r A : ℝ) :
    logKernelEnvelope P (N + 1) s r A = r⁻¹ * logKernelEnvelope P N s r A := by
  unfold logKernelEnvelope
  rw [pow_succ]
  ring

/-- Every genuine logarithmic derivative is bounded explicitly on the
whole interval. No derivative, smoothness or cancellation premise remains. -/
theorem norm_logAmplitude_derivative_le (P : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {L r A B v : ℝ} (hL : 0 < L) (hr : 0 < r) (hrs : r ≤ s.re)
    (hv : 0 ≤ v) (hAv : A ≤ v) (hvB : v ≤ B) :
    ‖((-1 / L : ℝ) : ℂ) *
        (zetaPrimeFilterKernel P (N + 1) s (Real.exp v) + (v : ℂ) *
          (zetaPrimeFilterKernel P N s (Real.exp v) -
            s * zetaPrimeFilterKernel P (N + 1) s (Real.exp v)))‖ ≤
      logAmplitudeAllowance L P N s r A B := by
  let E := logKernelEnvelope P N s r A
  have hE : 0 ≤ E := by unfold E logKernelEnvelope; positivity
  have h0 := norm_logKernel_le P N s hr hrs hv hAv
  have h1 := norm_logKernel_le P (N + 1) s hr hrs hv hAv
  rw [logKernelEnvelope_succ] at h1
  have hminus : ‖zetaPrimeFilterKernel P N s (Real.exp v) -
      s * zetaPrimeFilterKernel P (N + 1) s (Real.exp v)‖ ≤ E + ‖s‖ * (r⁻¹ * E) := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    exact add_le_add h0 (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
  have hinner : ‖zetaPrimeFilterKernel P (N + 1) s (Real.exp v) + (v : ℂ) *
      (zetaPrimeFilterKernel P N s (Real.exp v) -
        s * zetaPrimeFilterKernel P (N + 1) s (Real.exp v))‖ ≤
      r⁻¹ * E + B * (E + ‖s‖ * (r⁻¹ * E)) := by
    apply (norm_add_le _ _).trans
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hv]
    exact add_le_add h1 (mul_le_mul hvB hminus (norm_nonneg _) (hv.trans hvB))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_one,
    abs_of_pos hL]
  exact (mul_le_mul_of_nonneg_left hinner (by positivity)).trans_eq (by
    unfold logAmplitudeAllowance E
    ring)

/-- Full complex amplitudes at any two points of a positive logarithmic
interval differ by at most the explicit allowance times their logarithmic
distance. The height and all factorial orders are accounted for. -/
theorem norm_logAmplitude_sub_le (P : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {L r A B x y : ℝ} (hL : 0 < L) (hr : 0 < r) (hrs : r ≤ s.re) (hA : 0 ≤ A)
    (hx : x ∈ Set.Icc A B) (hy : y ∈ Set.Icc A B) :
    ‖logAmplitude L P (N + 1) s y - logAmplitude L P (N + 1) s x‖ ≤
      logAmplitudeAllowance L P N s r A B * |y - x| := by
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v (_hv : v ∈ Set.Icc A B) => (hasDerivAt_logAmplitude L P N s v).hasDerivWithinAt)
    (fun v (hv : v ∈ Set.Icc A B) =>
      norm_logAmplitude_derivative_le P N s hL hr hrs (hA.trans hv.1) hv.1 hv.2)
    (convex_Icc A B) hx hy

/-- The full smooth amplitude has a uniform size bound on the same
interval used for its derivative, with positive normalization explicit. -/
theorem norm_logAmplitude_le (P : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {L r A B v : ℝ} (hL : 0 < L) (hr : 0 < r) (hrs : r ≤ s.re)
    (hv : 0 ≤ v) (hAv : A ≤ v) (hvB : v ≤ B) :
    ‖logAmplitude L P N s v‖ ≤ B / L * logKernelEnvelope P N s r A := by
  rw [logAmplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_neg, abs_of_nonneg hv, abs_of_pos hL]
  exact mul_le_mul (div_le_div_of_nonneg_right hvB hL.le)
    (norm_logKernel_le P N s hr hrs hv hAv) (norm_nonneg _)
    (div_nonneg (hv.trans hvB) hL.le)

/-- A new prime times a squarefree nonunit gives the exact composite
support needed by the original amplitude, with squarefreeness discharged. -/
theorem prime_mul_composite_support {p n : ℕ} (hp : p.Prime) (hn : Squarefree n)
    (hn1 : n ≠ 1) (hpn : ¬ p ∣ n) : Squarefree (p * n) ∧ ¬ (p * n).Prime := by
  exact ⟨(Nat.squarefree_mul (hp.coprime_iff_not_dvd.mpr hpn)).mpr ⟨hp.squarefree, hn⟩,
    Nat.not_prime_mul hp.ne_one hn1⟩

/-- The same cofactor cancels exactly from the logarithmic amplitude
separation; the remaining distance is the prime-to-product gap. -/
theorem replacement_log_distance {a b q n : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) (hn : 0 < n) :
    |Real.log (a * (b * n) : ℕ) - Real.log (q * n : ℕ)| =
      |Real.log q - Real.log (a * b : ℕ)| := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have habR : ((a * b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos ha hb).ne'
  rw [← Nat.mul_assoc a b n]
  simp only [Nat.cast_mul]
  rw [Real.log_mul (by simpa using habR) hnR, Real.log_mul hqR hnR,
    add_sub_add_right_eq_sub, abs_sub_comm]

/-- Every factor in the explicit derivative allowance is nonnegative
on the logarithmic comparison interval. -/
theorem logAmplitudeAllowance_nonneg (P : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {L r A B : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (hB : 0 ≤ B) :
    0 ≤ logAmplitudeAllowance L P N s r A B := by
  unfold logAmplitudeAllowance logKernelEnvelope
  positivity

/-- The complete quantitative cost of a prime-to-product match. Both
actual integer endpoints determine the envelope; all polynomial coefficients,
the ordinate, and the common cofactor divisor mass remain explicit. -/
def replacementAllowance (L : ℝ) (P : Polynomial ℂ) (N : ℕ) (t r : ℝ)
    (a b q n : ℕ) : ℝ :=
  let A := min (Real.log (q * n : ℕ)) (Real.log (a * (b * n) : ℕ))
  let B := max (Real.log (q * n : ℕ)) (Real.log (a * (b * n) : ℕ))
  let s : ℂ := 3 / 2 + Complex.I * t
  (B / L * logKernelEnvelope P (N + 1) s r A +
    logAmplitudeAllowance L P N s r A B * min (Real.log a) (Real.log b)) *
      ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)|

/-- The literal two-integer cancellation has a fully explicit error.
No amplitude comparison, phase bound, smoothness or zero-location premise
is left unpaid. The two smaller saturated profiles are genuinely zero. -/
theorem norm_bandWeight_replacement_pair_le_gap (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {a b q n : ℕ} (ha : a.Prime) (hb : b.Prime) (hq : q.Prime) (hab : a ≠ b)
    (han : ¬ a ∣ n) (hbn : ¬ b ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1)
    (haL : Real.log (a * n : ℕ) ≤ L) (hbL : Real.log (b * n : ℕ) ≤ L)
    (hBandQ : q * n ∈ zetaPrimeLogBand (N + 1))
    (hBandAB : a * (b * n) ∈ zetaPrimeLogBand (N + 1)) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (q * n) +
      ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (a * (b * n))‖ ≤
      replacementAllowance L P N t r a b q n * |Real.log q - Real.log (a * b : ℕ)| := by
  let A := min (Real.log (q * n : ℕ)) (Real.log (a * (b * n) : ℕ))
  let B := max (Real.log (q * n : ℕ)) (Real.log (a * (b * n) : ℕ))
  let s : ℂ := 3 / 2 + Complex.I * t
  have hA : 0 ≤ A := le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hx : Real.log (q * n : ℕ) ∈ Set.Icc A B := ⟨min_le_left _ _, le_max_left _ _⟩
  have hy : Real.log (a * (b * n) : ℕ) ∈ Set.Icc A B := ⟨min_le_right _ _, le_max_right _ _⟩
  have hrs : r ≤ s.re := by simpa [s] using hr3
  have hsupq := prime_mul_composite_support hq hn hn1 hqn
  have hbn' := prime_mul_composite_support hb hn hn1 hbn
  have hb1 : b * n ≠ 1 := by intro he; exact hb.ne_one (mul_eq_one.mp he).1
  have hsupab := prime_mul_composite_support ha hbn'.1 hb1 (not_dvd_prime_mul ha hb hab han)
  have hqeq := bandAmplitude_eq_logAmplitude L P (N + 1) t ⟨hBandQ, hsupq⟩
  have habeq := bandAmplitude_eq_logAmplitude L P (N + 1) t ⟨hBandAB, hsupab⟩
  have hamp : ‖bandAmplitude L P (N + 1) t (q * n)‖ ≤
      B / L * logKernelEnvelope P (N + 1) s r A := by
    rw [hqeq]
    exact norm_logAmplitude_le P (N + 1) s hL hr hrs (Real.log_natCast_nonneg _) hx.1 hx.2
  have hdiff : ‖bandAmplitude L P (N + 1) t (a * (b * n)) -
      bandAmplitude L P (N + 1) t (q * n)‖ ≤
      logAmplitudeAllowance L P N s r A B * |Real.log q - Real.log (a * b : ℕ)| := by
    rw [hqeq, habeq]
    have hh := norm_logAmplitude_sub_le P N s hL hr hrs hA hx hy
    rwa [replacement_log_distance ha.pos hb.pos hq.pos (Nat.pos_of_ne_zero hn.ne_zero)] at hh
  apply (norm_bandWeight_replacement_pair_le L P (N + 1) t
    ha hb hq hab han hbn hqn hn hn1 haL hbL).trans
  calc
    _ ≤ (B / L * logKernelEnvelope P (N + 1) s r A * |Real.log q - Real.log (a * b : ℕ)| +
        (logAmplitudeAllowance L P N s r A B * |Real.log q - Real.log (a * b : ℕ)|) *
          min (Real.log a) (Real.log b)) *
        ∑ d ∈ n.divisors, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (by intros; positivity))
      exact add_le_add (mul_le_mul_of_nonneg_right hamp (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hdiff (le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)))
    _ = _ := by unfold replacementAllowance; dsimp [A, B, s] at *; ring

/-- The explicit replacement allowance is nonnegative for every
integer family and positive normalization and tilt. -/
theorem replacementAllowance_nonneg (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (a b q n : ℕ) :
    0 ≤ replacementAllowance L P N t r a b q n := by
  have hB : 0 ≤ max (Real.log (q * n : ℕ)) (Real.log (a * (b * n) : ℕ)) :=
    (Real.log_natCast_nonneg _).trans (le_max_left _ _)
  have hallow := logAmplitudeAllowance_nonneg P N (3 / 2 + Complex.I * t)
    (A := min (Real.log (q * n : ℕ)) (Real.log (a * (b * n) : ℕ))) hL hr hB
  unfold replacementAllowance
  dsimp only
  apply mul_nonneg _ (Finset.sum_nonneg (by intros; positivity))
  apply add_nonneg
  · apply mul_nonneg (div_nonneg hB hL)
    unfold logKernelEnvelope
    positivity
  · exact mul_nonneg hallow (le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))

/-- A fully explicit cancellation bound for literal original band
weights in terms of the integer gap |q-ab|/min(q,ab). This does not posit
the existence, coverage or aggregate saving of a family of such matches. -/
theorem norm_bandWeight_replacement_pair_le_integer_gap (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr3 : r ≤ 3 / 2)
    {a b q n : ℕ} (ha : a.Prime) (hb : b.Prime) (hq : q.Prime) (hab : a ≠ b)
    (han : ¬ a ∣ n) (hbn : ¬ b ∣ n) (hqn : ¬ q ∣ n)
    (hn : Squarefree n) (hn1 : n ≠ 1)
    (haL : Real.log (a * n : ℕ) ≤ L) (hbL : Real.log (b * n : ℕ) ≤ L)
    (hBandQ : q * n ∈ zetaPrimeLogBand (N + 1))
    (hBandAB : a * (b * n) ∈ zetaPrimeLogBand (N + 1)) :
    ‖ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (q * n) +
      ZetaRieszConditionedEnergy.bandWeight L P (N + 1) t (a * (b * n))‖ ≤
      replacementAllowance L P N t r a b q n *
        (|(q : ℝ) - (a * b : ℕ)| / min (q : ℝ) (a * b : ℕ)) := by
  exact (norm_bandWeight_replacement_pair_le_gap P N t hL hr hr3 ha hb hq hab
    han hbn hqn hn hn1 haL hbL hBandQ hBandAB).trans
    (mul_le_mul_of_nonneg_left (abs_log_nat_sub_log_nat_le hq.pos (Nat.mul_pos ha.pos hb.pos))
      (replacementAllowance_nonneg P N t hL.le hr.le a b q n))

end
end RiemannGaussian.ZetaRieszPrimeReplacement
