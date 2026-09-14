/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszEulerCorrectionEnergy

/-!
# The physical phase of the full Euler correction

The complete correction retains its even and odd channels. Pairing with the
actual reciprocal cutoff phases gives a cosine majorant with integrated cost
linear in the cutoff length. Literal prime-square tails bound that allowance
uniformly in height on each fixed closed half-plane right of one half.
The leading Euler quotient and original signed boundary remain separate.
-/

namespace RiemannGaussian.ZetaRieszEulerCutoff
noncomputable section
open scoped BigOperators
open MeasureTheory Set
open ZetaRieszEulerQuotient ZetaRieszEulerCorrectionEnergy

/-- The actual reciprocal cutoff phase. -/
def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

/-- The phase has unit norm at every real frequency. -/
theorem norm_phase (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I x

/-- Translation is retained as exact multiplication of phases. -/
theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, Complex.ofReal_add, add_mul, Complex.exp_add]

/-- Reciprocal-frequency character differences have identical amplitudes. -/
theorem norm_one_sub_phase_neg (x : ℝ) : ‖1 - phase (-x)‖ = ‖1 - phase x‖ := by
  have he : 1 - phase (-x) = phase (-x) * (phase x - 1) := by
    rw [mul_sub, mul_one, ← phase_add]
    simp [phase]
  rw [he, norm_mul, norm_phase, one_mul, norm_sub_rev]

/-- The full reciprocal cutoff difference has the exact doubled-frequency
cosine square, without replacing the difference by two unit bounds. -/
theorem norm_phase_sub_neg_sq (x : ℝ) :
    ‖phase x - phase (-x)‖ ^ 2 = 2 * (1 - Real.cos (2 * x)) := by
  have he : phase x - phase (-x) = phase (-x) * (phase (2 * x) - 1) := by
    rw [mul_sub, mul_one, ← phase_add]
    congr 1
    congr 1
    ring
  rw [he, norm_mul, norm_phase, one_mul, norm_sub_rev]
  exact ZetaPrimeCharacterRemainder.norm_character_difference_sq (2 * x)

/-- The even cutoff phase has norm at most one. -/
theorem norm_even_phase_le (x : ℝ) : ‖(phase x + phase (-x)) / 2‖ ≤ 1 := by
  have h := norm_add_le (phase x) (phase (-x))
  rw [norm_phase, norm_phase] at h
  norm_num only [norm_div, Complex.norm_ofNat] at ⊢
  linarith

/-- The whole square-amplitude mass, retaining every prime label. -/
def localMass {ι : Type*} (Q : Finset ι) (q : ι → ℂ) : ℝ := ∑ p ∈ Q, ‖q p‖ ^ 2

/-- The complete exponential correction cost. -/
def expCost {ι : Type*} (Q : Finset ι) (q : ι → ℂ) : ℝ := 2 + Real.exp (8 * localMass Q q)

/-- The full even correction cost before the physical phase is restored. -/
def evenCost {ι : Type*} (Q : Finset ι) (q : ι → ℂ) : ℝ :=
  32 + 64 * localMass Q q * expCost Q q

/-- The actual cutoff phase multiplies both full correction channels. -/
def shiftedCorrection {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) (L xi : ℝ) : ℂ :=
  phase (L * xi) * (correctionProduct Q q ell xi - 1) +
    phase (-(L * xi)) * (correctionProduct Q q ell (-xi) - 1)


/-- The exponential correction cost is nonnegative for every finite set. -/
theorem expCost_nonneg {ι : Type*} (Q : Finset ι) (q : ι → ℂ) : 0 ≤ expCost Q q := by
  unfold expCost
  positivity

/-- The full odd product keeps its linear character differences before
it is paired against the odd cutoff phase. -/
theorem norm_odd_product_le_phase {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (xi : ℝ) :
    ‖correctionProduct Q q ell xi - correctionProduct Q q ell (-xi)‖ ≤
      8 * expCost Q q * ∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - phase (ell p * xi)‖ := by
  let S : ℝ := ∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - phase (ell p * xi)‖
  have hC := expCost_nonneg Q q
  have ht := norm_correctionLogSum_le_phase Q q ell hq xi
  have htneg := norm_correctionLogSum_le_phase Q q ell hq (-xi)
  change ‖correctionLogSum Q q ell (-xi)‖ ≤
    4 * ∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - phase (ell p * (-xi))‖ at htneg
  simp only [mul_neg, norm_one_sub_phase_neg] at htneg
  have hp : ‖Complex.exp (correctionLogSum Q q ell xi) - 1‖ ≤ expCost Q q * (4 * S) :=
    (ZetaPrimeNonlinearFactor.norm_exp_sub_one_le_linear
      (norm_correctionLogSum_le_mass Q q ell hq xi)).trans
        (mul_le_mul_of_nonneg_left ht hC)
  have hm : ‖Complex.exp (correctionLogSum Q q ell (-xi)) - 1‖ ≤ expCost Q q * (4 * S) :=
    (ZetaPrimeNonlinearFactor.norm_exp_sub_one_le_linear
      (norm_correctionLogSum_le_mass Q q ell hq (-xi))).trans
        (mul_le_mul_of_nonneg_left htneg hC)
  rw [correctionProduct_eq_exp Q q ell hq xi, correctionProduct_eq_exp Q q ell hq (-xi)]
  have he : Complex.exp (correctionLogSum Q q ell xi) - Complex.exp (correctionLogSum Q q ell (-xi)) =
      (Complex.exp (correctionLogSum Q q ell xi) - 1) -
        (Complex.exp (correctionLogSum Q q ell (-xi)) - 1) := by ring
  rw [he]
  exact (norm_sub_le_of_le hp hm).trans_eq (by dsimp [S]; ring)

/-- Weighted Young inequality keeps the actual amplitudes in every
cross term; no count of the selected primes is introduced. -/
theorem sum_weighted_young {ι : Type*} (Q : Finset ι) (w b : ι → ℝ)
    (hw : ∀ p ∈ Q, 0 ≤ w p) (a : ℝ) :
    2 * a * (∑ p ∈ Q, w p * b p) ≤
      a ^ 2 * (∑ p ∈ Q, w p) + ∑ p ∈ Q, w p * b p ^ 2 := by
  calc
    _ = ∑ p ∈ Q, 2 * a * (w p * b p) := Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ Q, (a ^ 2 * w p + w p * b p ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      nlinarith [mul_nonneg (hw p hp) (sq_nonneg (a - b p))]
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The physical cutoff phase keeps an explicit even correction and
an explicit odd correction coupling before either is bounded. -/
theorem shiftedCorrection_eq_even_odd {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (L xi : ℝ) :
    shiftedCorrection Q q ell L xi =
      ((phase (L * xi) + phase (-(L * xi))) / 2) *
        (correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2) +
      ((phase (L * xi) - phase (-(L * xi))) / 2) *
        (correctionProduct Q q ell xi - correctionProduct Q q ell (-xi)) :=
  weighted_correction_pair_split _ _ _ _


/-- The full physical-phase correction keeps a quadratic cutoff
phase cost and the actual weighted prime-character square sum. -/
theorem norm_shiftedCorrection_le {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (L xi : ℝ) :
    ‖shiftedCorrection Q q ell L xi‖ ≤
      ‖correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2‖ +
      2 * expCost Q q * localMass Q q * ‖phase (L * xi) - phase (-(L * xi))‖ ^ 2 +
      2 * expCost Q q * ∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - phase (ell p * xi)‖ ^ 2 := by
  let S : ℝ := ∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - phase (ell p * xi)‖
  let T : ℝ := ∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - phase (ell p * xi)‖ ^ 2
  let d : ℝ := ‖phase (L * xi) - phase (-(L * xi))‖
  let C : ℝ := expCost Q q
  have hC : 0 ≤ C := expCost_nonneg Q q
  have hodd := norm_odd_product_le_phase Q q ell hq xi
  have hVo : ‖(phase (L * xi) - phase (-(L * xi))) / 2‖ = d / 2 := by
    norm_num only [norm_div, Complex.norm_ofNat]
    rfl
  have hb : ‖shiftedCorrection Q q ell L xi‖ ≤
      ‖correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2‖ + 4 * C * d * S := by
    rw [shiftedCorrection_eq_even_odd]
    have h := norm_add_le
      (((phase (L * xi) + phase (-(L * xi))) / 2) *
        (correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2))
      (((phase (L * xi) - phase (-(L * xi))) / 2) *
        (correctionProduct Q q ell xi - correctionProduct Q q ell (-xi)))
    rw [norm_mul, norm_mul, hVo] at h
    have hfirst := mul_le_mul_of_nonneg_right (norm_even_phase_le (L * xi))
      (norm_nonneg (correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2))
    rw [one_mul] at hfirst
    have hsecond := mul_le_mul_of_nonneg_left hodd (by dsimp [d]; positivity : 0 ≤ d / 2)
    exact (h.trans (add_le_add hfirst hsecond)).trans_eq (by dsimp [S, C]; ring)
  have hy := sum_weighted_young Q (fun p => ‖q p‖ ^ 2)
    (fun p => ‖1 - phase (ell p * xi)‖) (fun _ _ => sq_nonneg _) d
  change 2 * d * S ≤ d ^ 2 * localMass Q q + T at hy
  have hp := mul_le_mul_of_nonneg_left hy (show 0 ≤ 2 * C by positivity)
  change ‖shiftedCorrection Q q ell L xi‖ ≤
    ‖correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2‖ +
      2 * C * localMass Q q * d ^ 2 + 2 * C * T
  nlinarith

/-- Keeping the odd phase before taking norms yields a cosine majorant
whose integrated cutoff cost is linear, rather than quadratic, in its shift. -/
theorem norm_shiftedCorrection_div_le_energy {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (L xi : ℝ) :
    ‖shiftedCorrection Q q ell L xi / (xi : ℂ) ^ 2‖ ≤
      (evenCost Q q + 4 * expCost Q q) * phaseEnergy Q q ell xi +
        4 * expCost Q q * localMass Q q * ((1 - Real.cos ((2 * L) * xi)) / xi ^ 2) := by
  have he : (∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - phase (ell p * xi)‖ ^ 2) / xi ^ 2 =
      2 * phaseEnergy Q q ell xi := by
    rw [Finset.sum_div, phaseEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [phase, ZetaPrimeCharacterRemainder.norm_character_difference_sq]
    ring
  have hp := norm_paired_correctionProduct_div_le_energy Q q ell hq xi
  change ‖(correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2) /
    (xi : ℂ) ^ 2‖ ≤ evenCost Q q * phaseEnergy Q q ell xi at hp
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hp ⊢
  calc
    _ ≤ (‖correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2‖ +
        2 * expCost Q q * localMass Q q * ‖phase (L * xi) - phase (-(L * xi))‖ ^ 2 +
        2 * expCost Q q * ∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - phase (ell p * xi)‖ ^ 2) / xi ^ 2 :=
      div_le_div_of_nonneg_right (norm_shiftedCorrection_le Q q ell hq L xi) (sq_nonneg xi)
    _ = ‖correctionProduct Q q ell xi + correctionProduct Q q ell (-xi) - 2‖ / xi ^ 2 +
        4 * expCost Q q * localMass Q q * ((1 - Real.cos ((2 * L) * xi)) / xi ^ 2) +
        2 * expCost Q q * ((∑ p ∈ Q, ‖q p‖ ^ 2 * ‖1 - phase (ell p * xi)‖ ^ 2) /
          xi ^ 2) := by
      rw [norm_phase_sub_neg_sq]
      have hangle : 2 * (L * xi) = (2 * L) * xi := by ring
      rw [hangle]
      ring
    _ ≤ evenCost Q q * phaseEnergy Q q ell xi +
        4 * expCost Q q * localMass Q q * ((1 - Real.cos ((2 * L) * xi)) / xi ^ 2) +
        2 * expCost Q q * (2 * phaseEnergy Q q ell xi) := by
      rw [he]
      exact add_le_add (add_le_add hp le_rfl) le_rfl
    _ = _ := by ring

/-- Restoring the physical phase preserves continuity of the complete
paired correction, including at zero frequency. -/
theorem continuous_shiftedCorrection {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (L : ℝ) :
    Continuous (shiftedCorrection Q q ell L) := by
  have hp := continuous_correctionProduct Q q ell hq
  have hm := hp.comp (show Continuous (fun xi : ℝ => -xi) by fun_prop)
  have hvp : Continuous (fun xi : ℝ => phase (L * xi)) := by unfold phase; fun_prop
  have hvm : Continuous (fun xi : ℝ => phase (-(L * xi))) := by unfold phase; fun_prop
  exact (hvp.mul (hp.sub continuous_const)).add (hvm.mul (hm.sub continuous_const))

/-- The physical-phase correction divided by frequency squared is
genuinely integrable on the positive half-line, with no unpaired singular
integral silently totalized. -/
theorem integrable_shiftedCorrection_div {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (L : ℝ) :
    IntegrableOn (fun xi : ℝ => shiftedCorrection Q q ell L xi / (xi : ℂ) ^ 2) (Ioi 0) := by
  apply (((integrable_phaseEnergy Q q ell).const_mul (evenCost Q q + 4 * expCost Q q)).add
    ((CosineHinge.integrable_one_sub_cos_div_sq (2 * L)).const_mul
      (4 * expCost Q q * localMass Q q))).mono'
  · have hc : ContinuousOn (fun xi : ℝ => shiftedCorrection Q q ell L xi / (xi : ℂ) ^ 2)
        (Ioi 0) := by
      apply (continuous_shiftedCorrection Q q ell hq L).continuousOn.div (by fun_prop)
      intro xi hxi
      exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hxi))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [] with xi
    exact norm_shiftedCorrection_div_le_energy Q q ell hq L xi

/-- Every interaction order of the full correction survives the physical
cutoff phase with a linear shift allowance and its original prime weights. -/
theorem integral_norm_shiftedCorrection_div_le {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (L : ℝ) :
    (∫ xi : ℝ in Ioi 0, ‖shiftedCorrection Q q ell L xi / (xi : ℂ) ^ 2‖) ≤
      (evenCost Q q + 4 * expCost Q q) *
        (Real.pi / 2 * ∑ p ∈ Q, ‖q p‖ ^ 2 * |ell p|) +
          4 * Real.pi * expCost Q q * localMass Q q * |L| := by
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0,
        (evenCost Q q + 4 * expCost Q q) * phaseEnergy Q q ell xi +
          4 * expCost Q q * localMass Q q * ((1 - Real.cos ((2 * L) * xi)) / xi ^ 2) :=
      integral_mono_ae (integrable_shiftedCorrection_div Q q ell hq L).norm
        (((integrable_phaseEnergy Q q ell).const_mul _).add
          ((CosineHinge.integrable_one_sub_cos_div_sq (2 * L)).const_mul _))
        (Filter.Eventually.of_forall (norm_shiftedCorrection_div_le_energy Q q ell hq L))
    _ = _ := by
      rw [integral_add ((integrable_phaseEnergy Q q ell).const_mul _)
        ((CosineHinge.integrable_one_sub_cos_div_sq (2 * L)).const_mul _),
        integral_const_mul, integral_const_mul, integral_phaseEnergy,
        CosineHinge.integral_one_sub_cos_div_sq, abs_mul]
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring

/-- Above the fixed small-prime head, the same logarithmic square mass
also pays the unweighted square mass. -/
theorem localMass_le_logMass_div (Q : Finset ℕ) (q : ℕ → ℂ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) :
    localMass Q q ≤ (∑ p ∈ Q, ‖q p‖ ^ 2 * |Real.log p|) / Real.log 16 := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 16))).mpr
  rw [localMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact (Real.log_le_log (by norm_num : (0 : ℝ) < 16)
    (by exact_mod_cast h16 p hp)).trans (le_abs_self _)

/-- The logarithmic square mass of the literal arithmetic labels has
the same tail bound uniformly in height and in the closed half-plane. -/
theorem actual_logMass_le_tail (Q : Finset ℕ) {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    {s : ℂ} (hs : sigma ≤ s.re) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) :
    (∑ p ∈ Q, ‖zetaPrimeFeature s p‖ ^ 2 * |Real.log p|) ≤
      ZetaPrimeNonlinearTail.squareLogTail sigma K := by
  simp_rw [← ZetaPrimeNonlinearTail.squareLogWeight_eq]
  exact (Finset.sum_le_sum (fun p _hp =>
    ZetaPrimeNonlinearHalfplane.squareLogWeight_mono hs p)).trans
      (ZetaPrimeNonlinearTail.sum_squareLogWeight_le_tail Q hsigma K hK)

/-- A half-plane ceiling for every finite square-amplitude selection. -/
def massCeiling (sigma : ℝ) : ℝ := ∑' n, zetaPrimeExpWeight (2 * sigma) n

/-- The full cutoff-phase cost keeps its linear dependence on the actual
shift; it does not suppress growing physical cutoffs. -/
def phaseTailCost (sigma L : ℝ) : ℝ :=
  (32 + 64 * massCeiling sigma * (2 + Real.exp (8 * massCeiling sigma)) +
    4 * (2 + Real.exp (8 * massCeiling sigma))) * (Real.pi / 2) +
      4 * Real.pi * (2 + Real.exp (8 * massCeiling sigma)) * |L| / Real.log 16

/-- The complete physical-phase budget is paid by the actual square-log
arithmetic tail, before any particular frequency integral is substituted. -/
theorem actual_phaseBudget_le_tail (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    {s : ℂ} (hs : sigma ≤ s.re) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) (L : ℝ) :
    (evenCost Q (zetaPrimeFeature s) + 4 * expCost Q (zetaPrimeFeature s)) *
      (Real.pi / 2 * ∑ p ∈ Q, ‖zetaPrimeFeature s p‖ ^ 2 * |Real.log p|) +
        4 * Real.pi * expCost Q (zetaPrimeFeature s) * localMass Q (zetaPrimeFeature s) * |L| ≤
          phaseTailCost sigma L * ZetaPrimeNonlinearTail.squareLogTail sigma K := by
  let M : ℝ := localMass Q (zetaPrimeFeature s)
  let A : ℝ := massCeiling sigma
  let C : ℝ := expCost Q (zetaPrimeFeature s)
  let D : ℝ := 2 + Real.exp (8 * A)
  let J : ℝ := ∑ p ∈ Q, ‖zetaPrimeFeature s p‖ ^ 2 * |Real.log p|
  let T : ℝ := ZetaPrimeNonlinearTail.squareLogTail sigma K
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hMA : M ≤ A := actual_square_mass_le Q hsigma hs
  have hA0 : 0 ≤ A := hM0.trans hMA
  have hC0 : 0 ≤ C := expCost_nonneg Q _
  have hCD : C ≤ D := add_le_add le_rfl (Real.exp_le_exp.mpr (by
    change 8 * M ≤ 8 * A
    linarith))
  have hD0 : 0 ≤ D := hC0.trans hCD
  have hJ0 : 0 ≤ J := Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hJT : J ≤ T := actual_logMass_le_tail Q hsigma hs K hK
  have hT0 : 0 ≤ T := hJ0.trans hJT
  have hlog : 0 < Real.log (16 : ℝ) := Real.log_pos (by norm_num)
  have hMT : M ≤ T / Real.log 16 :=
    (localMass_le_logMass_div Q (zetaPrimeFeature s) h16).trans
      (div_le_div_of_nonneg_right hJT hlog.le)
  have hB : evenCost Q (zetaPrimeFeature s) + 4 * C ≤ 32 + 64 * A * D + 4 * D := by
    have hm := mul_le_mul hMA hCD hC0 hA0
    change 32 + 64 * M * C + 4 * C ≤ _
    nlinarith
  have hfirst := mul_le_mul hB
    (mul_le_mul_of_nonneg_left hJT (by positivity : 0 ≤ Real.pi / 2))
    (by positivity : 0 ≤ Real.pi / 2 * J) (by positivity : 0 ≤ 32 + 64 * A * D + 4 * D)
  have hsecond : 4 * Real.pi * C * M * |L| ≤
      4 * Real.pi * D * (T / Real.log 16) * |L| := by
    have hm := mul_le_mul hCD hMT hM0 hD0
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 * Real.pi by positivity)) (abs_nonneg L)]
  exact (add_le_add hfirst hsecond).trans_eq (by
    dsimp [phaseTailCost, A, D, T]
    ring)

/-- The ordinary integrated correction after restoring the physical phase
has a literal arithmetic tail allowance, with the full shift cost exposed. -/
theorem integral_norm_actual_shiftedCorrection_le_tail (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    {s : ℂ} (hs : sigma ≤ s.re) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) (L : ℝ) :
    (∫ xi : ℝ in Ioi 0,
      ‖shiftedCorrection Q (zetaPrimeFeature s) (fun p => Real.log p) L xi / (xi : ℂ) ^ 2‖) ≤
        phaseTailCost sigma L * ZetaPrimeNonlinearTail.squareLogTail sigma K := by
  exact (integral_norm_shiftedCorrection_div_le Q (zetaPrimeFeature s)
    (fun p => Real.log p) (fun p hp => ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter
      (hsigma.trans_le hs).le (h16 p hp)) L).trans
        (actual_phaseBudget_le_tail Q h16 hsigma hs K hK L)

/-- The cutoff cost is monotone in a supplied absolute shift bound. -/
theorem phaseTailCost_le {sigma L R : ℝ} (hL : |L| ≤ R) :
    phaseTailCost sigma L ≤ phaseTailCost sigma R := by
  have hR : 0 ≤ R := (abs_nonneg L).trans hL
  unfold phaseTailCost
  rw [abs_of_nonneg hR]
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hL (by positivity)) (Real.log_pos (by norm_num)).le

/-- A common prime threshold pays the complete correction for every
bounded physical shift, every finite selection and every height in a fixed
closed half-plane. Growing shifts retain an explicit additional obligation. -/
theorem exists_uniform_actual_shiftedCorrection_lt {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) (R : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∃ K : ℕ, 16 ≤ K ∧ ∀ (s : ℂ), sigma ≤ s.re → ∀ (Q : Finset ℕ),
      (∀ p ∈ Q, K ≤ p) → ∀ (L : ℝ), |L| ≤ R →
        (∫ xi : ℝ in Ioi 0,
          ‖shiftedCorrection Q (zetaPrimeFeature s) (fun p => Real.log p) L xi /
            (xi : ℂ) ^ 2‖) < eps := by
  have ht : Filter.Tendsto (fun K => phaseTailCost sigma R *
      ZetaPrimeNonlinearTail.squareLogTail sigma K) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (ZetaPrimeNonlinearTail.tendsto_squareLogTail hsigma).const_mul (phaseTailCost sigma R)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds heps))
  refine ⟨max 16 K, le_max_left _ _, ?_⟩
  intro s hs Q hQ L hL
  have h16 (p : ℕ) (hp : p ∈ Q) : 16 ≤ p := (le_max_left _ _).trans (hQ p hp)
  apply (integral_norm_actual_shiftedCorrection_le_tail Q h16 hsigma hs (max 16 K) hQ L).trans_lt
  apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (phaseTailCost_le hL)
    (ZetaPrimeNonlinearTail.squareLogTail_nonneg hsigma (max 16 K)))
  exact hK (max 16 K) (le_max_right _ _)

end
end RiemannGaussian.ZetaRieszEulerCutoff
