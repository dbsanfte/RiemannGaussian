/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerQuotient

/-!
# Even and odd bounds for the complete Euler correction

Every interaction order of the finite correction product is retained.
Weighted Cauchy--Schwarz pays its logarithmic square by prime-square mass,
then the complete paired correction has an integrable frequency quotient
and the odd correction has integrable energy. Both arithmetic allowances
tend uniformly to zero on each fixed closed half-plane right of one half.

The exact weighted pairing identity retains both channels. These bounds do
not pay the leading Euler quotient, its coupling with the correction, the
original factorial filter or the signed completion boundary. The full
independent signed floor and RH remain open.
-/

namespace RiemannGaussian.ZetaRieszEulerCorrectionEnergy
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory Set
open ZetaRieszEulerQuotient

/-- The local correction retains a first-order character difference,
with a square-amplitude coefficient and a separated denominator. -/
theorem norm_localCorrection_le_phase (q : ℂ) (hq : ‖q‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖localCorrection q z‖ ≤ 2 * ‖q‖ ^ 2 * ‖1 - z‖ := by
  have hd := local_denominator_bound hq hz
  unfold localCorrection
  rw [norm_div, norm_mul, norm_pow, norm_sub_rev z 1]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 - q * z‖)).mpr
  calc
    _ = (2 * ‖q‖ ^ 2 * ‖1 - z‖) * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (show 1 / 2 ≤ ‖1 - q * z‖ by linarith) (by positivity)

/-- Every local correction itself lies in the quarter disk. -/
theorem norm_localCorrection_le_quarter (q : ℂ) (hq : ‖q‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖localCorrection q z‖ ≤ 1 / 4 := by
  have hb : ‖1 - z‖ ≤ 2 := (norm_sub_le (1 : ℂ) z).trans (by rw [norm_one]; linarith)
  have h := (norm_localCorrection_le_phase q hq z hz).trans
    (mul_le_mul_of_nonneg_left hb (by positivity))
  nlinarith [norm_nonneg q]

/-- Each correction logarithm retains its linear phase factor while
its prime amplitude is already square-summable. -/
theorem norm_localCorrection_log_le_phase (q : ℂ) (hq : ‖q‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.log (1 + localCorrection q z)‖ ≤ 4 * ‖q‖ ^ 2 * ‖1 - z‖ := by
  have hw := norm_localCorrection_le_quarter q hq z hz
  have hl := Complex.norm_log_one_add_half_le_self (show ‖localCorrection q z‖ ≤ 1 / 2 by linarith)
  have hp := norm_localCorrection_le_phase q hq z hz
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 3 / 2)
  nlinarith [norm_nonneg (localCorrection q z)]

/-- The full local-log correction keeps all primes before exponentiation. -/
def correctionLogSum {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) (xi : ℝ) : ℂ :=
  ∑ p ∈ Q, Complex.log (1 + localCorrection (q p)
    (Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)))

/-- The complete correction product retains every interaction order. -/
def correctionProduct {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) (xi : ℝ) : ℂ :=
  ∏ p ∈ Q, (1 + localCorrection (q p)
    (Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)))

/-- The full product is the exponential of its local logs, with every
local nonvanishing condition discharged from the amplitude bound. -/
theorem correctionProduct_eq_exp {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (xi : ℝ) :
    correctionProduct Q q ell xi = Complex.exp (correctionLogSum Q q ell xi) := by
  unfold correctionProduct correctionLogSum
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  have hw := norm_localCorrection_le_quarter (q p) (hq p hp)
    (Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I _).le
  have hn : 1 + localCorrection (q p)
      (Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)) ≠ 0 := by
    intro he
    have hh : localCorrection (q p)
        (Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)) = -1 := by linear_combination he
    rw [hh, norm_neg, norm_one] at hw
    norm_num at hw
  rw [Complex.exp_log hn]

/-- The full log keeps a weighted sum of character differences rather
than replacing each of them by a constant near frequency zero. -/
theorem norm_correctionLogSum_le_phase {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (xi : ℝ) :
    ‖correctionLogSum Q q ell xi‖ ≤
      4 * ∑ p ∈ Q, ‖q p‖ ^ 2 *
        ‖1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)‖ := by
  unfold correctionLogSum
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun p hp => by
    simpa only [mul_assoc] using norm_localCorrection_log_le_phase (q p) (hq p hp)
      (Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)) (Complex.norm_exp_ofReal_mul_I _).le)

/-- Weighted Cauchy--Schwarz keeps the prime-square mass, avoiding an
unbounded count of primes in the full logarithm's squared allowance. -/
theorem norm_correctionLogSum_sq_le {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (xi : ℝ) :
    ‖correctionLogSum Q q ell xi‖ ^ 2 ≤
      16 * (∑ p ∈ Q, ‖q p‖ ^ 2) *
        ∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
  have h := norm_correctionLogSum_le_phase Q q ell hq xi
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Q (fun p => ‖q p‖)
    (fun p => ‖q p‖ * ‖1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)‖)
  simp only [mul_pow, ← mul_assoc, ← pow_two] at hc
  have hs : 0 ≤ ∑ p ∈ Q, ‖q p‖ ^ 2 *
      ‖1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)‖ := Finset.sum_nonneg fun _ _ => by positivity
  nlinarith [norm_nonneg (correctionLogSum Q q ell xi)]

/-- A frequency-independent ceiling for the exponent uses only the
finite prime-square mass, not the number of participating primes. -/
theorem norm_correctionLogSum_le_mass {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (xi : ℝ) :
    ‖correctionLogSum Q q ell xi‖ ≤ 8 * ∑ p ∈ Q, ‖q p‖ ^ 2 := by
  apply (norm_correctionLogSum_le_phase Q q ell hq xi).trans
  have hb : (∑ p ∈ Q, ‖q p‖ ^ 2 *
      ‖1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)‖) ≤ 2 * ∑ p ∈ Q, ‖q p‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p _hp
    have hz : ‖1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)‖ ≤ 2 := by
      have h := norm_sub_le (1 : ℂ) (Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I))
      simpa only [norm_one, Complex.norm_exp_ofReal_mul_I, one_add_one_eq_two] using h
    nlinarith [mul_le_mul_of_nonneg_left hz (sq_nonneg ‖q p‖)]
  linarith

/-- A bounded complex exponent has a quadratic remainder globally.
This leaves its first-order term explicit for reciprocal-frequency pairing. -/
theorem norm_exp_sub_one_sub_le_quadratic {z : ℂ} {M : ℝ} (hz : ‖z‖ ≤ M) :
    ‖Complex.exp z - 1 - z‖ ≤ (2 + Real.exp M) * ‖z‖ ^ 2 := by
  by_cases h : ‖z‖ ≤ 1
  · apply (Complex.norm_exp_sub_one_sub_id_le h).trans
    have he := Real.exp_pos M
    nlinarith [sq_nonneg ‖z‖]
  · have h1 : 1 ≤ ‖z‖ := le_of_lt (lt_of_not_ge h)
    have he : ‖Complex.exp z‖ ≤ Real.exp M := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr (Complex.re_le_norm z |>.trans hz)
    have hn := norm_sub_le (Complex.exp z - 1) z
    have hn1 := norm_sub_le (Complex.exp z) (1 : ℂ)
    rw [norm_one] at hn1
    have hm : (1 + Real.exp M) * 1 ≤ (1 + Real.exp M) * ‖z‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    nlinarith


/-- The real cosine-energy majorant keeps every logarithmic frequency. -/
def phaseEnergy {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) (xi : ℝ) : ℝ :=
  ∑ p ∈ Q, ‖q p‖ ^ 2 * ((1 - Real.cos (ell p * xi)) / xi ^ 2)

/-- The retained cosine-energy majorant is nonnegative at every frequency. -/
theorem phaseEnergy_nonneg {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) (xi : ℝ) :
    0 ≤ phaseEnergy Q q ell xi := by
  apply Finset.sum_nonneg
  intro p _hp
  exact mul_nonneg (sq_nonneg _) (div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (sq_nonneg _))

/-- The energy majorant has an ordinary integrable frequency kernel. -/
theorem integrable_phaseEnergy {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) :
    IntegrableOn (phaseEnergy Q q ell) (Ioi 0) := by
  exact integrable_finsetSum _ (fun p _hp =>
    (CosineHinge.integrable_one_sub_cos_div_sq (ell p)).const_mul (‖q p‖ ^ 2))

/-- The exact energy integral is a prime-square logarithmic mass. -/
theorem integral_phaseEnergy {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) :
    (∫ xi : ℝ in Ioi 0, phaseEnergy Q q ell xi) =
      (Real.pi / 2) * ∑ p ∈ Q, ‖q p‖ ^ 2 * |ell p| := by
  unfold phaseEnergy
  rw [integral_finsetSum Q (fun p _hp =>
    (CosineHinge.integrable_one_sub_cos_div_sq (ell p)).const_mul (‖q p‖ ^ 2)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [integral_const_mul, CosineHinge.integral_one_sub_cos_div_sq]
  ring

/-- The local logarithm's second-order error keeps a quadratic phase
factor and is bounded by a square-amplitude weight. -/
theorem norm_localCorrection_log_error_le_phase (q : ℂ) (hq : ‖q‖ ≤ 1 / 4)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.log (1 + localCorrection q z) - localCorrection q z‖ ≤
      4 * ‖q‖ ^ 2 * ‖1 - z‖ ^ 2 := by
  have hw := norm_localCorrection_le_quarter q hq z hz
  have he : ‖Complex.log (1 + localCorrection q z) - localCorrection q z‖ ≤
      ‖localCorrection q z‖ ^ 2 := by
    simpa using ZetaPrimeCharacterRemainder.norm_local_log_error_le_phase
      (localCorrection q z) 0 hw (by norm_num)
  have hb := pow_le_pow_left₀ (norm_nonneg (localCorrection q z))
    (norm_localCorrection_le_phase q hq z hz) 2
  have hq2 : ‖q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg q]
  have hq4 : ‖q‖ ^ 4 ≤ ‖q‖ ^ 2 := by nlinarith [sq_nonneg ‖q‖]
  calc
    _ ≤ ‖localCorrection q z‖ ^ 2 := he
    _ ≤ (2 * ‖q‖ ^ 2 * ‖1 - z‖) ^ 2 := hb
    _ = 4 * ‖q‖ ^ 4 * ‖1 - z‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hq4 (by norm_num)) (sq_nonneg _)

/-- Pairing the actual logarithms cancels their first-order frequency
terms before the log remainders are bounded. -/
theorem norm_paired_local_log_le (q : ℂ) (hq : ‖q‖ ≤ 1 / 4) (x : ℝ) :
    ‖Complex.log (1 + localCorrection q (Complex.exp ((x : ℂ) * Complex.I))) +
      Complex.log (1 + localCorrection q (Complex.exp (((-x : ℝ) : ℂ) * Complex.I)))‖ ≤
        32 * ‖q‖ ^ 2 * (1 - Real.cos x) := by
  let z := Complex.exp ((x : ℂ) * Complex.I)
  let w := Complex.exp (((-x : ℝ) : ℂ) * Complex.I)
  have hz := norm_localCorrection_log_error_le_phase q hq z (Complex.norm_exp_ofReal_mul_I x).le
  have hw := norm_localCorrection_log_error_le_phase q hq w (Complex.norm_exp_ofReal_mul_I (-x)).le
  rw [show ‖1 - z‖ ^ 2 = 2 * (1 - Real.cos x) from
    ZetaPrimeCharacterRemainder.norm_character_difference_sq x] at hz
  rw [show ‖1 - w‖ ^ 2 = 2 * (1 - Real.cos x) by
    simpa only [Real.cos_neg] using ZetaPrimeCharacterRemainder.norm_character_difference_sq (-x)] at hw
  have hp := norm_paired_local_le q hq x
  have he : Complex.log (1 + localCorrection q z) + Complex.log (1 + localCorrection q w) =
      (localCorrection q z + localCorrection q w) +
        ((Complex.log (1 + localCorrection q z) - localCorrection q z) +
          (Complex.log (1 + localCorrection q w) - localCorrection q w)) := by ring
  change ‖Complex.log (1 + localCorrection q z) + Complex.log (1 + localCorrection q w)‖ ≤ _
  rw [he]
  exact (norm_add_le_of_le hp (norm_add_le_of_le hz hw)).trans_eq (by ring)


/-- The majorant retains reciprocal-frequency symmetry exactly. -/
theorem phaseEnergy_neg {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) (xi : ℝ) :
    phaseEnergy Q q ell (-xi) = phaseEnergy Q q ell xi := by
  simp only [phaseEnergy, mul_neg, Real.cos_neg, neg_sq]

/-- The full logarithm squared is paid by the integrable cosine energy,
with the finite square-amplitude mass retained as its only set-size cost. -/
theorem norm_correctionLogSum_sq_div_le_energy {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (xi : ℝ) :
    ‖correctionLogSum Q q ell xi‖ ^ 2 / xi ^ 2 ≤
      32 * (∑ p ∈ Q, ‖q p‖ ^ 2) * phaseEnergy Q q ell xi := by
  have he : (∑ p ∈ Q, ‖q p‖ ^ 2 *
      ‖1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)‖ ^ 2) / xi ^ 2 =
        2 * phaseEnergy Q q ell xi := by
    rw [Finset.sum_div, phaseEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [ZetaPrimeCharacterRemainder.norm_character_difference_sq]
    ring
  calc
    _ ≤ (16 * (∑ p ∈ Q, ‖q p‖ ^ 2) *
        ∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)‖ ^ 2) /
          xi ^ 2 := div_le_div_of_nonneg_right (norm_correctionLogSum_sq_le Q q ell hq xi) (sq_nonneg xi)
    _ = _ := by rw [mul_div_assoc, he]; ring

/-- The entire paired logarithm has a quadratic frequency allowance,
without a separate integrability assertion for either unpaired channel. -/
theorem norm_paired_correctionLogSum_div_le_energy {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (xi : ℝ) :
    ‖(correctionLogSum Q q ell xi + correctionLogSum Q q ell (-xi)) / (xi : ℂ) ^ 2‖ ≤
      32 * phaseEnergy Q q ell xi := by
  have hp : ‖correctionLogSum Q q ell xi + correctionLogSum Q q ell (-xi)‖ ≤
      32 * ∑ p ∈ Q, ‖q p‖ ^ 2 * (1 - Real.cos (ell p * xi)) := by
    unfold correctionLogSum
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    simpa only [mul_neg, mul_assoc] using norm_paired_local_log_le (q p) (hq p hp) (ell p * xi)
  have he : (∑ p ∈ Q, ‖q p‖ ^ 2 * (1 - Real.cos (ell p * xi))) / xi ^ 2 =
      phaseEnergy Q q ell xi := by
    rw [Finset.sum_div, phaseEnergy]
    apply Finset.sum_congr rfl
    intro p _hp
    ring
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (32 * ∑ p ∈ Q, ‖q p‖ ^ 2 * (1 - Real.cos (ell p * xi))) / xi ^ 2 :=
      div_le_div_of_nonneg_right hp (sq_nonneg xi)
    _ = _ := by rw [mul_div_assoc, he]

/-- Pairing full complex exponentials leaves only their paired linear
term and two quadratic remainders; no product interaction is truncated. -/
theorem norm_exp_pair_sub_two_le {z w : ℂ} {M : ℝ} (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ‖Complex.exp z + Complex.exp w - 2‖ ≤
      ‖z + w‖ + (2 + Real.exp M) * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  have he : Complex.exp z + Complex.exp w - 2 =
      (z + w) + ((Complex.exp z - 1 - z) + (Complex.exp w - 1 - w)) := by ring
  rw [he]
  exact (norm_add_le_of_le le_rfl (norm_add_le_of_le
    (norm_exp_sub_one_sub_le_quadratic hz) (norm_exp_sub_one_sub_le_quadratic hw))).trans_eq (by ring)

/-- The complete correction product has a paired cosine-energy bound,
including every higher interaction and all complex local phases. -/
theorem norm_paired_correctionProduct_div_le_energy {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (xi : ℝ) :
    ‖(correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2) / (xi : ℂ) ^ 2‖ ≤
      (32 + 64 * (∑ p ∈ Q, ‖q p‖ ^ 2) *
        (2 + Real.exp (8 * ∑ p ∈ Q, ‖q p‖ ^ 2))) * phaseEnergy Q q ell xi := by
  let M : ℝ := ∑ p ∈ Q, ‖q p‖ ^ 2
  let C : ℝ := 2 + Real.exp (8 * M)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp := norm_exp_pair_sub_two_le (norm_correctionLogSum_le_mass Q q ell hq xi)
    (norm_correctionLogSum_le_mass Q q ell hq (-xi))
  have hs1 := norm_correctionLogSum_sq_div_le_energy Q q ell hq xi
  have hs2 := norm_correctionLogSum_sq_div_le_energy Q q ell hq (-xi)
  rw [neg_sq, phaseEnergy_neg] at hs2
  have hl := norm_paired_correctionLogSum_div_le_energy Q q ell hq xi
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hl ⊢
  rw [correctionProduct_eq_exp Q q ell hq xi, correctionProduct_eq_exp Q q ell hq (-xi)]
  calc
    _ ≤ (‖correctionLogSum Q q ell xi + correctionLogSum Q q ell (-xi)‖ +
        C * (‖correctionLogSum Q q ell xi‖ ^ 2 + ‖correctionLogSum Q q ell (-xi)‖ ^ 2)) /
          xi ^ 2 := div_le_div_of_nonneg_right hp (sq_nonneg xi)
    _ = ‖correctionLogSum Q q ell xi + correctionLogSum Q q ell (-xi)‖ / xi ^ 2 +
        C * (‖correctionLogSum Q q ell xi‖ ^ 2 / xi ^ 2 +
          ‖correctionLogSum Q q ell (-xi)‖ ^ 2 / xi ^ 2) := by ring
    _ ≤ 32 * phaseEnergy Q q ell xi + C *
        (32 * M * phaseEnergy Q q ell xi + 32 * M * phaseEnergy Q q ell xi) :=
      add_le_add hl (mul_le_mul_of_nonneg_left (add_le_add hs1 hs2) hC)
    _ = _ := by dsimp [C, M]; ring


/-- The full finite correction product is continuous at every frequency. -/
theorem continuous_correctionProduct {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) :
    Continuous (correctionProduct Q q ell) := by
  unfold correctionProduct
  apply continuous_finsetProd
  intro p hp
  exact continuous_const.add ((continuous_localCorrection_phase (q p) (hq p hp)).comp
    (show Continuous (fun xi : ℝ => ell p * xi) by fun_prop))

/-- The entire paired correction product has a genuinely integrable
cutoff quotient. This retains all interactions, not just the local sum. -/
theorem integrable_paired_correctionProduct_div {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) :
    IntegrableOn (fun xi : ℝ =>
      (correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2) / (xi : ℂ) ^ 2)
      (Ioi 0) := by
  apply ((integrable_phaseEnergy Q q ell).const_mul
    (32 + 64 * (∑ p ∈ Q, ‖q p‖ ^ 2) * (2 + Real.exp (8 * ∑ p ∈ Q, ‖q p‖ ^ 2)))).mono'
  · have hp := continuous_correctionProduct Q q ell hq
    have hm := hp.comp (show Continuous (fun xi : ℝ => -xi) by fun_prop)
    have hc : ContinuousOn (fun xi : ℝ =>
        (correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2) / (xi : ℂ) ^ 2)
        (Ioi 0) := by
      apply ((hp.add hm).sub continuous_const).continuousOn.div (by fun_prop)
      intro xi hxi
      exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hxi))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [] with xi
    exact norm_paired_correctionProduct_div_le_energy Q q ell hq xi

/-- All interaction orders of the reciprocal-frequency correction
product have one integrated square-amplitude logarithmic allowance. -/
theorem integral_norm_paired_correctionProduct_div_le {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) :
    (∫ xi : ℝ in Ioi 0,
      ‖(correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2) / (xi : ℂ) ^ 2‖) ≤
      (32 + 64 * (∑ p ∈ Q, ‖q p‖ ^ 2) * (2 + Real.exp (8 * ∑ p ∈ Q, ‖q p‖ ^ 2))) *
        (Real.pi / 2 * ∑ p ∈ Q, ‖q p‖ ^ 2 * |ell p|) := by
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0,
        (32 + 64 * (∑ p ∈ Q, ‖q p‖ ^ 2) * (2 + Real.exp (8 * ∑ p ∈ Q, ‖q p‖ ^ 2))) *
          phaseEnergy Q q ell xi := integral_mono_ae
      (integrable_paired_correctionProduct_div Q q ell hq).norm
      ((integrable_phaseEnergy Q q ell).const_mul _)
      (Filter.Eventually.of_forall (norm_paired_correctionProduct_div_le_energy Q q ell hq))
    _ = _ := by rw [integral_const_mul, integral_phaseEnergy]


/-- One closed-half-plane ceiling controls the square-amplitude mass
of every finite selection of literal prime features. -/
theorem actual_square_mass_le (Q : Finset ℕ) {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    {s : ℂ} (hs : sigma ≤ s.re) :
    (∑ p ∈ Q, ‖zetaPrimeFeature s p‖ ^ 2) ≤ ∑' n, zetaPrimeExpWeight (2 * sigma) n := by
  have he (p : ℕ) : ‖zetaPrimeFeature s p‖ ^ 2 = zetaPrimeExpWeight (2 * s.re) p := by
    rw [norm_zetaPrimeFeature, pow_two]
    unfold zetaPrimeExpWeight
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  exact (Finset.sum_le_sum (fun p _hp =>
    ZetaPrimeNonlinearHalfplane.expWeight_mono (by linarith) p)).trans
      ((summable_zetaPrimeExpWeight (by linarith : 1 < 2 * sigma)).sum_le_tsum Q
        (fun n _hn => (Real.exp_pos _).le))

/-- The complete paired Euler correction product has a vanishing
prime-square tail allowance uniform over the entire closed half-plane. -/
theorem integral_norm_actual_paired_correctionProduct_le_tail (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    {s : ℂ} (hs : sigma ≤ s.re) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) :
    (∫ xi : ℝ in Ioi 0,
      ‖(correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) xi +
        correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi) - 2) /
          (xi : ℂ) ^ 2‖) ≤
      (32 + 64 * (∑' n, zetaPrimeExpWeight (2 * sigma) n) *
        (2 + Real.exp (8 * ∑' n, zetaPrimeExpWeight (2 * sigma) n))) *
          (Real.pi / 2 * ZetaPrimeNonlinearTail.squareLogTail sigma K) := by
  let M : ℝ := ∑ p ∈ Q, ‖zetaPrimeFeature s p‖ ^ 2
  let A : ℝ := ∑' n, zetaPrimeExpWeight (2 * sigma) n
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMA : M ≤ A := actual_square_mass_le Q hsigma hs
  have hA0 : 0 ≤ A := hM0.trans hMA
  have hJ : (∑ p ∈ Q, ‖zetaPrimeFeature s p‖ ^ 2 * |Real.log p|) ≤
      ZetaPrimeNonlinearTail.squareLogTail sigma K := by
    simp_rw [← ZetaPrimeNonlinearTail.squareLogWeight_eq]
    exact (Finset.sum_le_sum (fun p _hp =>
      ZetaPrimeNonlinearHalfplane.squareLogWeight_mono hs p)).trans
        (ZetaPrimeNonlinearTail.sum_squareLogWeight_le_tail Q hsigma K hK)
  have hC : 32 + 64 * M * (2 + Real.exp (8 * M)) ≤
      32 + 64 * A * (2 + Real.exp (8 * A)) := by
    have he : 2 + Real.exp (8 * M) ≤ 2 + Real.exp (8 * A) :=
      add_le_add le_rfl (Real.exp_le_exp.mpr (by linarith))
    have hm := mul_le_mul hMA he (by positivity) hA0
    nlinarith
  have h := integral_norm_paired_correctionProduct_div_le Q (zetaPrimeFeature s)
    (fun p => Real.log p) (fun p hp => ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter
      (hsigma.trans_le hs).le (h16 p hp))
  apply h.trans
  exact mul_le_mul hC (mul_le_mul_of_nonneg_left hJ (by positivity))
    (by positivity) (by
      change 0 ≤ 32 + 64 * A * (2 + Real.exp (8 * A))
      positivity)

/-- A single prime threshold pays the full paired correction product,
including all higher interactions, uniformly in height and finite selection. -/
theorem exists_uniform_actual_paired_correctionProduct_lt {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) {eps : ℝ} (heps : 0 < eps) :
    ∃ K : ℕ, 16 ≤ K ∧ ∀ (s : ℂ), sigma ≤ s.re → ∀ (Q : Finset ℕ),
      (∀ p ∈ Q, K ≤ p) →
        (∫ xi : ℝ in Ioi 0,
          ‖(correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) xi +
            correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi) - 2) /
              (xi : ℂ) ^ 2‖) < eps := by
  let A : ℝ := ∑' n, zetaPrimeExpWeight (2 * sigma) n
  let C : ℝ := 32 + 64 * A * (2 + Real.exp (8 * A))
  have ht : Filter.Tendsto (fun K => C * (Real.pi / 2 * ZetaPrimeNonlinearTail.squareLogTail sigma K))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((ZetaPrimeNonlinearTail.tendsto_squareLogTail hsigma).const_mul (Real.pi / 2)).const_mul C
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds heps))
  refine ⟨max 16 K, le_max_left _ _, ?_⟩
  intro s hs Q hQ
  have h16 (p : ℕ) (hp : p ∈ Q) : 16 ≤ p := (le_max_left _ _).trans (hQ p hp)
  exact (integral_norm_actual_paired_correctionProduct_le_tail Q h16 hsigma hs (max 16 K) hQ).trans_lt
    (hK (max 16 K) (le_max_right _ _))

/-- The bound applies to the full correction in the literal finite
Euler character, with its leading quotient still explicitly present. -/
theorem actual_character_eq_euler_quotient_correction (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} (hs : 1 / 2 ≤ s.re) (xi : ℝ) :
    (∏ p ∈ Q, (1 + zetaPrimeFeature s p *
      (1 - Complex.exp (((Real.log p * xi : ℝ) : ℂ) * Complex.I)))) =
      ((∏ p ∈ Q, (1 - zetaPrimeFeature s p *
        Complex.exp (((Real.log p * xi : ℝ) : ℂ) * Complex.I))) /
          (∏ p ∈ Q, (1 - zetaPrimeFeature s p))) *
            correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) xi := by
  exact finite_character_eq_quotient_product Q (zetaPrimeFeature s)
    (fun p => Complex.exp (((Real.log p * xi : ℝ) : ℂ) * Complex.I))
    (fun p hp => ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter hs (h16 p hp))
    (fun p _hp => (Complex.norm_exp_ofReal_mul_I _).le)

/-- Multiplication by the two distinct leading responses retains both
the even correction and its odd coupling; the latter cannot be discarded
merely because the unweighted paired correction is small. -/
theorem weighted_correction_pair_split (Vp Vm Hp Hm : ℂ) :
    Vp * (Hp - 1) + Vm * (Hm - 1) =
      ((Vp + Vm) / 2) * (Hp + Hm - 2) + ((Vp - Vm) / 2) * (Hp - Hm) := by ring


/-- The full odd correction has a quadratic energy allowance. The
finite square-amplitude mass replaces a loss proportional to prime count. -/
theorem norm_odd_correctionProduct_sq_div_le_energy {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (xi : ℝ) :
    ‖correctionProduct Q q ell xi - correctionProduct Q q ell (-xi)‖ ^ 2 / xi ^ 2 ≤
      (128 * (2 + Real.exp (8 * ∑ p ∈ Q, ‖q p‖ ^ 2)) ^ 2 *
        (∑ p ∈ Q, ‖q p‖ ^ 2)) * phaseEnergy Q q ell xi := by
  let M : ℝ := ∑ p ∈ Q, ‖q p‖ ^ 2
  let C : ℝ := 2 + Real.exp (8 * M)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp := ZetaPrimeNonlinearFactor.norm_exp_sub_one_le_linear
    (norm_correctionLogSum_le_mass Q q ell hq xi)
  have hm := ZetaPrimeNonlinearFactor.norm_exp_sub_one_le_linear
    (norm_correctionLogSum_le_mass Q q ell hq (-xi))
  have hn : ‖correctionProduct Q q ell xi - correctionProduct Q q ell (-xi)‖ ≤
      C * (‖correctionLogSum Q q ell xi‖ + ‖correctionLogSum Q q ell (-xi)‖) := by
    rw [correctionProduct_eq_exp Q q ell hq xi, correctionProduct_eq_exp Q q ell hq (-xi)]
    have he : Complex.exp (correctionLogSum Q q ell xi) - Complex.exp (correctionLogSum Q q ell (-xi)) =
        (Complex.exp (correctionLogSum Q q ell xi) - 1) -
          (Complex.exp (correctionLogSum Q q ell (-xi)) - 1) := by ring
    rw [he]
    exact (norm_sub_le_of_le hp hm).trans_eq (by dsimp [C, M]; ring)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hs : ‖correctionProduct Q q ell xi - correctionProduct Q q ell (-xi)‖ ^ 2 ≤
      2 * C ^ 2 * (‖correctionLogSum Q q ell xi‖ ^ 2 + ‖correctionLogSum Q q ell (-xi)‖ ^ 2) := by
    have h := mul_nonneg (sq_nonneg C)
      (sq_nonneg (‖correctionLogSum Q q ell xi‖ - ‖correctionLogSum Q q ell (-xi)‖))
    nlinarith
  have hs1 := norm_correctionLogSum_sq_div_le_energy Q q ell hq xi
  have hs2 := norm_correctionLogSum_sq_div_le_energy Q q ell hq (-xi)
  rw [neg_sq, phaseEnergy_neg] at hs2
  calc
    _ ≤ (2 * C ^ 2 * (‖correctionLogSum Q q ell xi‖ ^ 2 +
        ‖correctionLogSum Q q ell (-xi)‖ ^ 2)) / xi ^ 2 :=
      div_le_div_of_nonneg_right hs (sq_nonneg xi)
    _ = 2 * C ^ 2 * (‖correctionLogSum Q q ell xi‖ ^ 2 / xi ^ 2 +
        ‖correctionLogSum Q q ell (-xi)‖ ^ 2 / xi ^ 2) := by ring
    _ ≤ 2 * C ^ 2 * (32 * M * phaseEnergy Q q ell xi + 32 * M * phaseEnergy Q q ell xi) :=
      mul_le_mul_of_nonneg_left (add_le_add hs1 hs2) (by positivity)
    _ = _ := by dsimp [C, M]; ring

/-- The odd correction energy is genuinely integrable, so it can be
paired against a separately controlled odd leading response. -/
theorem integrable_odd_correctionProduct_energy {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) :
    IntegrableOn (fun xi : ℝ =>
      ‖correctionProduct Q q ell xi - correctionProduct Q q ell (-xi)‖ ^ 2 / xi ^ 2) (Ioi 0) := by
  apply ((integrable_phaseEnergy Q q ell).const_mul
    (128 * (2 + Real.exp (8 * ∑ p ∈ Q, ‖q p‖ ^ 2)) ^ 2 * (∑ p ∈ Q, ‖q p‖ ^ 2))).mono'
  · have hp := continuous_correctionProduct Q q ell hq
    have hm := hp.comp (show Continuous (fun xi : ℝ => -xi) by fun_prop)
    have hc : ContinuousOn (fun xi : ℝ =>
        ‖correctionProduct Q q ell xi - correctionProduct Q q ell (-xi)‖ ^ 2 / xi ^ 2) (Ioi 0) := by
      apply ((hp.sub hm).norm.pow 2).continuousOn.div (by fun_prop)
      intro xi hxi
      exact pow_ne_zero 2 (ne_of_gt hxi)
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [] with xi
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_odd_correctionProduct_sq_div_le_energy Q q ell hq xi

/-- The whole odd correction has a finite integrated energy cost in
terms of its square-amplitude mass and square-logarithmic mass. -/
theorem integral_odd_correctionProduct_energy_le {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) :
    (∫ xi : ℝ in Ioi 0,
      ‖correctionProduct Q q ell xi - correctionProduct Q q ell (-xi)‖ ^ 2 / xi ^ 2) ≤
      (128 * (2 + Real.exp (8 * ∑ p ∈ Q, ‖q p‖ ^ 2)) ^ 2 * (∑ p ∈ Q, ‖q p‖ ^ 2)) *
        (Real.pi / 2 * ∑ p ∈ Q, ‖q p‖ ^ 2 * |ell p|) := by
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0,
        (128 * (2 + Real.exp (8 * ∑ p ∈ Q, ‖q p‖ ^ 2)) ^ 2 * (∑ p ∈ Q, ‖q p‖ ^ 2)) *
          phaseEnergy Q q ell xi := integral_mono_ae
      (integrable_odd_correctionProduct_energy Q q ell hq)
      ((integrable_phaseEnergy Q q ell).const_mul _)
      (Filter.Eventually.of_forall (norm_odd_correctionProduct_sq_div_le_energy Q q ell hq))
    _ = _ := by rw [integral_const_mul, integral_phaseEnergy]


/-- The full odd correction energy has the same vanishing arithmetic
tail support, uniformly on a fixed closed right half-plane. -/
theorem integral_actual_odd_correctionProduct_energy_le_tail (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    {s : ℂ} (hs : sigma ≤ s.re) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) :
    (∫ xi : ℝ in Ioi 0,
      ‖correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) xi -
        correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi)‖ ^ 2 / xi ^ 2) ≤
      (128 * (2 + Real.exp (8 * ∑' n, zetaPrimeExpWeight (2 * sigma) n)) ^ 2 *
        (∑' n, zetaPrimeExpWeight (2 * sigma) n)) *
          (Real.pi / 2 * ZetaPrimeNonlinearTail.squareLogTail sigma K) := by
  let M : ℝ := ∑ p ∈ Q, ‖zetaPrimeFeature s p‖ ^ 2
  let A : ℝ := ∑' n, zetaPrimeExpWeight (2 * sigma) n
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMA : M ≤ A := actual_square_mass_le Q hsigma hs
  have hA0 : 0 ≤ A := hM0.trans hMA
  have hJ : (∑ p ∈ Q, ‖zetaPrimeFeature s p‖ ^ 2 * |Real.log p|) ≤
      ZetaPrimeNonlinearTail.squareLogTail sigma K := by
    simp_rw [← ZetaPrimeNonlinearTail.squareLogWeight_eq]
    exact (Finset.sum_le_sum (fun p _hp =>
      ZetaPrimeNonlinearHalfplane.squareLogWeight_mono hs p)).trans
        (ZetaPrimeNonlinearTail.sum_squareLogWeight_le_tail Q hsigma K hK)
  have hC : 128 * (2 + Real.exp (8 * M)) ^ 2 * M ≤
      128 * (2 + Real.exp (8 * A)) ^ 2 * A := by
    have he : 2 + Real.exp (8 * M) ≤ 2 + Real.exp (8 * A) :=
      add_le_add le_rfl (Real.exp_le_exp.mpr (by linarith))
    have hc := pow_le_pow_left₀ (by positivity : 0 ≤ 2 + Real.exp (8 * M)) he 2
    have hm := mul_le_mul hc hMA hM0 (sq_nonneg _)
    nlinarith
  have h := integral_odd_correctionProduct_energy_le Q (zetaPrimeFeature s)
    (fun p => Real.log p) (fun p hp => ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter
      (hsigma.trans_le hs).le (h16 p hp))
  apply h.trans
  exact mul_le_mul hC (mul_le_mul_of_nonneg_left hJ (by positivity))
    (by positivity) (by
      change 0 ≤ 128 * (2 + Real.exp (8 * A)) ^ 2 * A
      positivity)

/-- The odd energy tends uniformly to zero above a growing prime
threshold, retaining the channel needed by the weighted pairing identity. -/
theorem exists_uniform_actual_odd_correctionProduct_energy_lt {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) {eps : ℝ} (heps : 0 < eps) :
    ∃ K : ℕ, 16 ≤ K ∧ ∀ (s : ℂ), sigma ≤ s.re → ∀ (Q : Finset ℕ),
      (∀ p ∈ Q, K ≤ p) →
        (∫ xi : ℝ in Ioi 0,
          ‖correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) xi -
            correctionProduct Q (zetaPrimeFeature s) (fun p => Real.log p) (-xi)‖ ^ 2 / xi ^ 2) < eps := by
  let A : ℝ := ∑' n, zetaPrimeExpWeight (2 * sigma) n
  let C : ℝ := 128 * (2 + Real.exp (8 * A)) ^ 2 * A
  have ht : Filter.Tendsto (fun K => C * (Real.pi / 2 * ZetaPrimeNonlinearTail.squareLogTail sigma K))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      ((ZetaPrimeNonlinearTail.tendsto_squareLogTail hsigma).const_mul (Real.pi / 2)).const_mul C
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds heps))
  refine ⟨max 16 K, le_max_left _ _, ?_⟩
  intro s hs Q hQ
  have h16 (p : ℕ) (hp : p ∈ Q) : 16 ≤ p := (le_max_left _ _).trans (hQ p hp)
  exact (integral_actual_odd_correctionProduct_energy_le_tail Q h16 hsigma hs (max 16 K) hQ).trans_lt
    (hK (max 16 K) (le_max_right _ _))

end
end RiemannGaussian.ZetaRieszEulerCorrectionEnergy
