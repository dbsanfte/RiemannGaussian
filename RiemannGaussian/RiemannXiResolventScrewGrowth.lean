import RiemannGaussian.RiemannXiScrewWickBridge
import RiemannGaussian.GaussianXiInverseSquareSummability

/-!
# A finite resolvent-regularized spectral screw norm

The unregularized positive reflected-pair screw mass can be infinite because
its coefficients carry no decay in the zero ordinate.  Suzuki's screw-line
coefficients, by contrast, contain a spectral denominator.  This file inserts
the canonical first-order resolvent `1 + i * alpha` into the exact screw/Wick
bridge and proves that the resulting object is a genuine `ℓ²` vector for every
real time.

For a spectral coordinate `alpha = gamma + i h`, the scalar mode

`exp (-i * alpha * z) / (1 + i * alpha)`

solves the first-order resolvent identity `u - u' = exp (-i * alpha * z)`.
The critical strip bounds its squared denominator below by a fixed multiple
of `1 + gamma^2`.  The already formalized inverse-square xi-divisor theorem
therefore proves unconditional square summability.

The squared Hilbert norm is a positive, finite reflected-pair screw mass.  It
has an unconditional `O(exp |t|)` bound, vanishes exactly under RH, and is
subexponential exactly under RH.  Its Wick-rotated Gaussian counterpart is an
absolutely convergent real series whose genuine finite zeta windows converge
to the full mass.  This removes the infinite-mass mismatch before comparison
with an arithmetic Suzuki norm; it does not yet prove the arithmetic
subexponential estimate.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The first-order spectral resolvent denominator `1 + i * alpha`. -/
def spectralScrewResolventDenominator
    (alpha : ℂ) : ℂ :=
  1 + Complex.I * alpha

/-- The entire spectral screw exponential divided by its first-order
resolvent denominator. -/
def complexSpectralScrewResolventMode
    (z alpha : ℂ) : ℂ :=
  Complex.exp (-Complex.I * alpha * z) /
    spectralScrewResolventDenominator alpha

/-- The complex derivative of a resolvent-regularized screw mode. -/
theorem hasDerivAt_complexSpectralScrewResolventMode
    (z alpha : ℂ) :
    HasDerivAt (fun w : ℂ ↦
      complexSpectralScrewResolventMode w alpha)
      ((-Complex.I * alpha) *
        complexSpectralScrewResolventMode z alpha) z := by
  have hinner : HasDerivAt
      (fun w : ℂ ↦ -Complex.I * alpha * w)
      (-Complex.I * alpha) z := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id z).const_mul (-Complex.I * alpha)
  have hexp := (Complex.hasDerivAt_exp _).comp z hinner
  simpa only [Function.comp_apply, complexSpectralScrewResolventMode,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hexp.mul_const (spectralScrewResolventDenominator alpha)⁻¹

/-- Away from the resolvent pole, the regularized mode solves the exact
first-order equation `u - u' = exp (-i * alpha * z)`. -/
theorem complexSpectralScrewResolventMode_sub_deriv
    {z alpha : ℂ}
    (hden : spectralScrewResolventDenominator alpha ≠ 0) :
    complexSpectralScrewResolventMode z alpha -
        (-Complex.I * alpha) *
          complexSpectralScrewResolventMode z alpha =
      Complex.exp (-Complex.I * alpha * z) := by
  have hden' : 1 + Complex.I * alpha ≠ 0 := by
    simpa [spectralScrewResolventDenominator] using hden
  unfold complexSpectralScrewResolventMode
    spectralScrewResolventDenominator
  field_simp [hden']
  ring

/-- The squared resolvent denominator separates into radial displacement and
real spectral ordinate. -/
theorem spectralScrewResolventDenominator_normSq
    (alpha : ℂ) :
    Complex.normSq (spectralScrewResolventDenominator alpha) =
      (1 - alpha.im) ^ 2 + alpha.re ^ 2 := by
  simp [spectralScrewResolventDenominator, Complex.normSq_apply]
  ring

/-- The critical strip keeps the resolvent denominator nonzero at every
nontrivial zeta zero. -/
theorem spectralScrewResolventDenominator_normSq_pos
    (rho : NontrivialZetaZero) :
    0 < Complex.normSq
      (spectralScrewResolventDenominator
        (zetaSpectralCoordinate rho.1)) := by
  rw [spectralScrewResolventDenominator_normSq]
  have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have hone : 0 < 1 - (zetaSpectralCoordinate rho.1).im := by
    nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).im]
  positivity

/-- The standard inverse-square ordinate denominator is controlled by four
times the screw-resolvent denominator throughout the critical strip. -/
theorem one_add_spectral_re_sq_le_four_mul_screwResolvent_normSq
    (rho : NontrivialZetaZero) :
    1 + (zetaSpectralCoordinate rho.1).re ^ 2 ≤
      4 * Complex.normSq
        (spectralScrewResolventDenominator
          (zetaSpectralCoordinate rho.1)) := by
  rw [spectralScrewResolventDenominator_normSq]
  have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have hlow : 0 ≤ 1 / 2 - (zetaSpectralCoordinate rho.1).im := by
    nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).im]
  have hhigh : 0 ≤ 3 / 2 - (zetaSpectralCoordinate rho.1).im := by
    nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).im]
  nlinarith [mul_nonneg hlow hhigh,
    sq_nonneg (zetaSpectralCoordinate rho.1).re]

/-- The positive upper-height coefficient divided by the squared screw
resolvent denominator. -/
def zetaUpperResolventScrewWeight
    (rho : NontrivialZetaZero) : ℝ :=
  zetaUpperSpectralHeightSummand rho /
    Complex.normSq
      (spectralScrewResolventDenominator
        (zetaSpectralCoordinate rho.1))

/-- Every resolvent-weighted upper-height coefficient is nonnegative. -/
theorem zetaUpperResolventScrewWeight_nonneg
    (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperResolventScrewWeight rho := by
  exact div_nonneg (zetaUpperSpectralHeightSummand_nonneg rho)
    (spectralScrewResolventDenominator_normSq_pos rho).le

/-- A resolvent-weighted upper-height coefficient is bounded by twice the
unconditionally summable inverse-square xi-divisor coefficient. -/
theorem zetaUpperResolventScrewWeight_le_inverseSquare
    (rho : NontrivialZetaZero) :
    zetaUpperResolventScrewWeight rho ≤
      2 * ((analyticZetaZeroMultiplicity rho : ℝ) /
        (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by
  let h : ℝ := (zetaSpectralCoordinate rho.1).im
  let gamma : ℝ := (zetaSpectralCoordinate rho.1).re
  let m : ℝ := analyticZetaZeroMultiplicity rho
  let D : ℝ := Complex.normSq
    (spectralScrewResolventDenominator
      (zetaSpectralCoordinate rho.1))
  let Q : ℝ := 1 + gamma ^ 2
  have hD : 0 < D := spectralScrewResolventDenominator_normSq_pos rho
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hden : Q ≤ 4 * D := by
    exact one_add_spectral_re_sq_le_four_mul_screwResolvent_normSq rho
  have hrecip : 1 / D ≤ 4 / Q := by
    rw [div_le_div_iff₀ hD hQ]
    simpa only [one_mul] using hden
  have hheight : zetaUpperSpectralHeightSummand rho ≤ m / 2 := by
    by_cases hupper : 0 < h
    · rw [zetaUpperSpectralHeightSummand, if_pos hupper]
      have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
      have hm : 0 ≤ m := Nat.cast_nonneg _
      have hhalf : h ≤ 1 / 2 := by
        exact (le_abs_self h).trans habs.le
      dsimp [h, m] at hm hhalf ⊢
      nlinarith
    · rw [zetaUpperSpectralHeightSummand, if_neg hupper]
      dsimp [m]
      positivity
  have hm : 0 ≤ m := Nat.cast_nonneg _
  change zetaUpperSpectralHeightSummand rho / D ≤ 2 * (m / Q)
  calc
    zetaUpperSpectralHeightSummand rho / D =
        zetaUpperSpectralHeightSummand rho * (1 / D) := by ring
    _ ≤ (m / 2) * (4 / Q) :=
      mul_le_mul hheight hrecip (by positivity) (by positivity)
    _ = 2 * (m / Q) := by ring

/-- The complete resolvent-weighted upper-height series is unconditionally
summable. -/
theorem summable_zetaUpperResolventScrewWeight :
    Summable zetaUpperResolventScrewWeight := by
  apply
    (summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left 2).of_nonneg_of_le
      zetaUpperResolventScrewWeight_nonneg
  exact zetaUpperResolventScrewWeight_le_inverseSquare

/-- The unregularized spectral screw exponential on real time. -/
def spectralScrewExponential (t : ℝ) (alpha : ℂ) : ℂ :=
  Complex.exp (-Complex.I * alpha * (t : ℂ))

/-- The squared modulus of a spectral screw exponential is
`exp (2 * im alpha * t)`. -/
theorem normSq_spectralScrewExponential
    (t : ℝ) (alpha : ℂ) :
    Complex.normSq (spectralScrewExponential t alpha) =
      Real.exp (2 * alpha.im * t) := by
  rw [← Complex.sq_norm, spectralScrewExponential, Complex.norm_exp,
    pow_two, ← Real.exp_add]
  congr 1
  simp
  ring

/-- One height-weighted, resolvent-regularized spectral screw coordinate. -/
def zetaUpperResolventScrewFeature
    (t : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  ((Real.sqrt (zetaUpperSpectralHeightSummand rho) : ℂ) /
      spectralScrewResolventDenominator
        (zetaSpectralCoordinate rho.1)) *
    spectralScrewExponential t (zetaSpectralCoordinate rho.1)

/-- Each zeta screw coordinate is exactly a height amplitude times the
first-order resolvent mode. -/
theorem zetaUpperResolventScrewFeature_eq_resolventMode
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaUpperResolventScrewFeature t rho =
      (Real.sqrt (zetaUpperSpectralHeightSummand rho) : ℂ) *
        complexSpectralScrewResolventMode (t : ℂ)
          (zetaSpectralCoordinate rho.1) := by
  unfold zetaUpperResolventScrewFeature
    complexSpectralScrewResolventMode spectralScrewExponential
  ring

/-- The positive squared-norm contribution of one upper spectral zero at real
screw time. -/
def zetaUpperResolventScrewGrowthSummand
    (t : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  zetaUpperResolventScrewWeight rho *
    Real.exp (2 * (zetaSpectralCoordinate rho.1).im * t)

/-- The squared modulus of one resolvent screw coordinate is its positive
growth summand. -/
theorem normSq_zetaUpperResolventScrewFeature
    (t : ℝ) (rho : NontrivialZetaZero) :
    Complex.normSq (zetaUpperResolventScrewFeature t rho) =
      zetaUpperResolventScrewGrowthSummand t rho := by
  rw [zetaUpperResolventScrewFeature, Complex.normSq_mul,
    Complex.normSq_div, Complex.normSq_ofReal,
    Real.mul_self_sqrt (zetaUpperSpectralHeightSummand_nonneg rho),
    normSq_spectralScrewExponential]
  rfl

/-- The positive resolvent growth summand is exactly the real reflected-pair
screw kernel divided by its squared resolvent denominator. -/
theorem zetaUpperResolventScrewGrowthSummand_eq_reflectedPair
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaUpperResolventScrewGrowthSummand t rho =
      ((zetaUpperReflectedScrewGrowthSummand t rho).re / 2) /
        Complex.normSq
          (spectralScrewResolventDenominator
            (zetaSpectralCoordinate rho.1)) := by
  rw [zetaUpperReflectedScrewGrowthSummand_re_div_two]
  unfold zetaUpperResolventScrewGrowthSummand
    zetaUpperResolventScrewWeight
  ring

/-- Every real-time resolvent screw growth summand is nonnegative. -/
theorem zetaUpperResolventScrewGrowthSummand_nonneg
    (t : ℝ) (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperResolventScrewGrowthSummand t rho := by
  exact mul_nonneg (zetaUpperResolventScrewWeight_nonneg rho)
    (Real.exp_pos _).le

/-- Critical-strip height bounds control every upper-mode exponent by
absolute real time. -/
theorem two_mul_upperSpectral_im_mul_le_abs
    (t : ℝ) (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    2 * (zetaSpectralCoordinate rho.1).im * t ≤ |t| := by
  have habs := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  have htwo : 2 * (zetaSpectralCoordinate rho.1).im ≤ 1 := by
    nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).im]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    exact mul_le_of_le_one_left ht htwo
  · have ht' : t ≤ 0 := le_of_not_ge ht
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) ht').trans
      (abs_nonneg t)

/-- Each real-time growth summand is dominated by an explicit fixed-time
multiple of the inverse-square xi-divisor coefficient. -/
theorem zetaUpperResolventScrewGrowthSummand_le_inverseSquare
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaUpperResolventScrewGrowthSummand t rho ≤
      (2 * Real.exp |t|) *
        ((analyticZetaZeroMultiplicity rho : ℝ) /
          (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hexp : Real.exp
        (2 * (zetaSpectralCoordinate rho.1).im * t) ≤
        Real.exp |t| :=
      Real.exp_le_exp.mpr
        (two_mul_upperSpectral_im_mul_le_abs t rho hupper)
    calc
      zetaUpperResolventScrewGrowthSummand t rho =
          zetaUpperResolventScrewWeight rho *
            Real.exp (2 * (zetaSpectralCoordinate rho.1).im * t) := rfl
      _ ≤ zetaUpperResolventScrewWeight rho * Real.exp |t| :=
        mul_le_mul_of_nonneg_left hexp
          (zetaUpperResolventScrewWeight_nonneg rho)
      _ ≤
          (2 * ((analyticZetaZeroMultiplicity rho : ℝ) /
            (1 + (zetaSpectralCoordinate rho.1).re ^ 2))) *
              Real.exp |t| :=
        mul_le_mul_of_nonneg_right
          (zetaUpperResolventScrewWeight_le_inverseSquare rho)
          (Real.exp_pos _).le
      _ = (2 * Real.exp |t|) *
          ((analyticZetaZeroMultiplicity rho : ℝ) /
            (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by ring
  · rw [zetaUpperResolventScrewGrowthSummand,
      zetaUpperResolventScrewWeight,
      zetaUpperSpectralHeightSummand, if_neg hupper, zero_div, zero_mul]
    positivity

/-- The positive resolvent screw growth series is summable at every real
time. -/
theorem summable_zetaUpperResolventScrewGrowthSummand (t : ℝ) :
    Summable (zetaUpperResolventScrewGrowthSummand t) := by
  apply
    (summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left
      (2 * Real.exp |t|)).of_nonneg_of_le
      (zetaUpperResolventScrewGrowthSummand_nonneg t)
  exact zetaUpperResolventScrewGrowthSummand_le_inverseSquare t

/-- The zeta-indexed resolvent screw coordinates are square-summable at every
real time. -/
theorem summable_norm_sq_zetaUpperResolventScrewFeature (t : ℝ) :
    Summable (fun rho : NontrivialZetaZero ↦
      ‖zetaUpperResolventScrewFeature t rho‖ ^ 2) := by
  simpa only [Complex.sq_norm,
    normSq_zetaUpperResolventScrewFeature] using
      summable_zetaUpperResolventScrewGrowthSummand t

/-- The complete resolvent-regularized spectral screw line as a literal
Hilbert vector. -/
def riemannXiUpperResolventScrewFeatureVector (t : ℝ) :
    ℓ²(NontrivialZetaZero, ℂ) :=
  ⟨zetaUpperResolventScrewFeature t, by
    apply memℓp_gen
    simpa using summable_norm_sq_zetaUpperResolventScrewFeature t⟩

/-- The finite positive squared-norm mass of the complete resolvent screw
line. -/
def riemannXiUpperResolventScrewGrowthMass (t : ℝ) : ℝ :=
  ∑' rho : NontrivialZetaZero,
    zetaUpperResolventScrewGrowthSummand t rho

/-- The complete positive growth mass is exactly the squared Hilbert norm of
the resolvent screw feature vector. -/
theorem norm_sq_riemannXiUpperResolventScrewFeatureVector (t : ℝ) :
    ‖riemannXiUpperResolventScrewFeatureVector t‖ ^ 2 =
      riemannXiUpperResolventScrewGrowthMass t := by
  calc
    ‖riemannXiUpperResolventScrewFeatureVector t‖ ^ 2 =
        ∑' rho : NontrivialZetaZero,
          ‖riemannXiUpperResolventScrewFeatureVector t rho‖ ^ 2 := by
      simpa using
        (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
          (riemannXiUpperResolventScrewFeatureVector t))
    _ = ∑' rho : NontrivialZetaZero,
          zetaUpperResolventScrewGrowthSummand t rho := by
      apply tsum_congr
      intro rho
      change ‖zetaUpperResolventScrewFeature t rho‖ ^ 2 = _
      rw [Complex.sq_norm,
        normSq_zetaUpperResolventScrewFeature]
    _ = riemannXiUpperResolventScrewGrowthMass t := rfl

/-- The complete finite resolvent screw growth mass is nonnegative. -/
theorem riemannXiUpperResolventScrewGrowthMass_nonneg (t : ℝ) :
    0 ≤ riemannXiUpperResolventScrewGrowthMass t := by
  exact tsum_nonneg (zetaUpperResolventScrewGrowthSummand_nonneg t)

/-- Unconditionally, the finite resolvent screw mass has exponential type at
most one. -/
theorem riemannXiUpperResolventScrewGrowthMass_le_exponential (t : ℝ) :
    riemannXiUpperResolventScrewGrowthMass t ≤
      (2 * Real.exp |t|) *
        ∑' rho : NontrivialZetaZero,
          (analyticZetaZeroMultiplicity rho : ℝ) /
            (1 + (zetaSpectralCoordinate rho.1).re ^ 2) := by
  calc
    riemannXiUpperResolventScrewGrowthMass t =
        ∑' rho : NontrivialZetaZero,
          zetaUpperResolventScrewGrowthSummand t rho := rfl
    _ ≤ ∑' rho : NontrivialZetaZero,
          (2 * Real.exp |t|) *
            ((analyticZetaZeroMultiplicity rho : ℝ) /
              (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) :=
      (summable_zetaUpperResolventScrewGrowthSummand t).tsum_le_tsum
        (zetaUpperResolventScrewGrowthSummand_le_inverseSquare t)
        (summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left _)
    _ = (2 * Real.exp |t|) *
        ∑' rho : NontrivialZetaZero,
          (analyticZetaZeroMultiplicity rho : ℝ) /
            (1 + (zetaSpectralCoordinate rho.1).re ^ 2) :=
      summable_distinct_zetaZeroInverseSquareSpectralRe.tsum_mul_left _

/-- Every individual positive screw coordinate is bounded by the complete
squared-norm mass. -/
theorem zetaUpperResolventScrewGrowthSummand_le_mass
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaUpperResolventScrewGrowthSummand t rho ≤
      riemannXiUpperResolventScrewGrowthMass t := by
  rw [← normSq_zetaUpperResolventScrewFeature,
    ← Complex.sq_norm,
    ← norm_sq_riemannXiUpperResolventScrewFeatureVector]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
  exact lp.norm_apply_le_norm (by norm_num)
    (riemannXiUpperResolventScrewFeatureVector t) rho

/-- At real time zero, the growth mass is the total resolvent-weighted upper
height. -/
theorem riemannXiUpperResolventScrewGrowthMass_zero :
    riemannXiUpperResolventScrewGrowthMass 0 =
      ∑' rho : NontrivialZetaZero,
        zetaUpperResolventScrewWeight rho := by
  unfold riemannXiUpperResolventScrewGrowthMass
    zetaUpperResolventScrewGrowthSummand
  congr 1
  funext rho
  norm_num

/-- RH annihilates the finite resolvent screw mass at every real time. -/
theorem riemannXiUpperResolventScrewGrowthMass_eq_zero_of_rh
    (hRH : RiemannHypothesis) (t : ℝ) :
    riemannXiUpperResolventScrewGrowthMass t = 0 := by
  unfold riemannXiUpperResolventScrewGrowthMass
  have hzero : zetaUpperResolventScrewGrowthSummand t = 0 := by
    funext rho
    have him : (zetaSpectralCoordinate rho.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
        rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
    rw [zetaUpperResolventScrewGrowthSummand,
      zetaUpperResolventScrewWeight,
      zetaUpperSpectralHeightSummand, if_neg (by linarith),
      zero_div, zero_mul]
    rfl
  rw [hzero]
  exact tsum_zero

/-- At each real time, vanishing of the finite resolvent screw mass is
equivalent to RH. -/
theorem riemannXiUpperResolventScrewGrowthMass_eq_zero_iff_rh
    (t : ℝ) :
    riemannXiUpperResolventScrewGrowthMass t = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    have hsummand : 0 < zetaUpperSpectralHeightSummand rho := by
      rw [zetaUpperSpectralHeightSummand, if_pos hwupper]
      exact mul_pos
        (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
        hwupper
    have hweight : 0 < zetaUpperResolventScrewWeight rho :=
      div_pos hsummand
        (spectralScrewResolventDenominator_normSq_pos rho)
    have hterm : 0 < zetaUpperResolventScrewGrowthSummand t rho :=
      mul_pos hweight (Real.exp_pos _)
    have hle := zetaUpperResolventScrewGrowthSummand_le_mass t rho
    rw [hzero] at hle
    exact (not_lt_of_ge hle) hterm
  · intro hRH
    exact riemannXiUpperResolventScrewGrowthMass_eq_zero_of_rh hRH t

/-- The complete resolvent screw Hilbert vector vanishes exactly under RH. -/
theorem riemannXiUpperResolventScrewFeatureVector_eq_zero_iff_rh
    (t : ℝ) :
    riemannXiUpperResolventScrewFeatureVector t = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    apply (riemannXiUpperResolventScrewGrowthMass_eq_zero_iff_rh t).mp
    rw [← norm_sq_riemannXiUpperResolventScrewFeatureVector,
      hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · intro hRH
    apply norm_eq_zero.mp
    have hsquare :
        ‖riemannXiUpperResolventScrewFeatureVector t‖ ^ 2 = 0 := by
      rw [norm_sq_riemannXiUpperResolventScrewFeatureVector,
        riemannXiUpperResolventScrewGrowthMass_eq_zero_of_rh hRH]
    nlinarith [norm_nonneg
      (riemannXiUpperResolventScrewFeatureVector t)]

/-- Subexponential growth of the finite resolvent screw mass on nonnegative
real time. -/
def RiemannXiUpperResolventScrewGrowthSubexponential : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      riemannXiUpperResolventScrewGrowthMass t ≤
        C * Real.exp (epsilon * t)

/-- The finite resolvent-regularized positive screw mass is subexponential
exactly under RH.  An upper zero of height `a` otherwise supplies a positive
`exp (2*a*t)` coordinate that defeats an `exp (a*t)` bound. -/
theorem riemannXiUpperResolventScrewGrowthSubexponential_iff_rh :
    RiemannXiUpperResolventScrewGrowthSubexponential ↔
      RiemannHypothesis := by
  constructor
  · intro hsub
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    let a : ℝ := (zetaSpectralCoordinate rho.1).im
    let c : ℝ := zetaUpperResolventScrewWeight rho
    have ha : 0 < a := hwupper
    have hsummand : 0 < zetaUpperSpectralHeightSummand rho := by
      rw [zetaUpperSpectralHeightSummand, if_pos hwupper]
      exact mul_pos
        (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
        hwupper
    have hc : 0 < c := by
      exact div_pos hsummand
        (spectralScrewResolventDenominator_normSq_pos rho)
    obtain ⟨C, hC, hbound⟩ := hsub a ha
    let q : ℝ := C / c + 1
    let t : ℝ := q / a
    have hq : 0 < q := by
      dsimp [q]
      have hdiv : 0 ≤ C / c := div_nonneg hC hc.le
      linarith
    have ht : 0 ≤ t := (div_pos hq ha).le
    have hat : a * t = q := by
      dsimp [t]
      field_simp [ha.ne']
    have hterm : c * Real.exp (2 * a * t) ≤
        riemannXiUpperResolventScrewGrowthMass t := by
      exact zetaUpperResolventScrewGrowthSummand_le_mass t rho
    have hreal : c * Real.exp (2 * a * t) ≤
        C * Real.exp (a * t) :=
      hterm.trans (hbound t ht)
    have hcancel : c * Real.exp (a * t) ≤ C := by
      have hexp : 0 < Real.exp (a * t) := Real.exp_pos _
      apply le_of_mul_le_mul_right _ hexp
      calc
        (c * Real.exp (a * t)) * Real.exp (a * t) =
            c * Real.exp (2 * a * t) := by
              rw [mul_assoc, ← Real.exp_add]
              congr 2
              ring
        _ ≤ C * Real.exp (a * t) := hreal
    rw [hat] at hcancel
    have hexpLower : q + 1 ≤ Real.exp q := Real.add_one_le_exp q
    have hscale : c * (q + 1) ≤ c * Real.exp q :=
      mul_le_mul_of_nonneg_left hexpLower hc.le
    have hstrict : C < c * Real.exp q := by
      calc
        C < C + 2 * c := by linarith
        _ = c * (q + 1) := by
          dsimp [q]
          field_simp [hc.ne']
          ring
        _ ≤ c * Real.exp q := hscale
    exact (not_lt_of_ge hcancel) hstrict
  · intro hRH epsilon _hepsilon
    refine ⟨0, le_rfl, ?_⟩
    intro t _ht
    rw [riemannXiUpperResolventScrewGrowthMass_eq_zero_of_rh hRH]
    positivity

/-- The resolvent-weighted Gaussian average of one Wick-rotated upper screw
mode. -/
def zetaUpperResolventScrewWickSummand
    (tau : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  zetaUpperResolventScrewWeight rho *
    Real.exp (-(tau * (zetaSpectralCoordinate rho.1).im ^ 2))

/-- For positive Gaussian time, a regularized Wick summand is exactly the
reflected-pair Wick average divided by its squared resolvent denominator. -/
theorem zetaUpperResolventScrewWickSummand_eq_reflectedPair
    {tau : ℝ} (htau : 0 < tau) (rho : NontrivialZetaZero) :
    zetaUpperResolventScrewWickSummand tau rho =
      ((zetaUpperReflectedScrewWickSummand tau rho).re / 2) /
        Complex.normSq
          (spectralScrewResolventDenominator
            (zetaSpectralCoordinate rho.1)) := by
  rw [zetaUpperReflectedScrewWickSummand_re_div_two htau]
  unfold zetaUpperSpectralHeightGaussianSummand
    zetaUpperResolventScrewWickSummand
    zetaUpperResolventScrewWeight
  ring

/-- Every resolvent-weighted Wick summand is nonnegative. -/
theorem zetaUpperResolventScrewWickSummand_nonneg
    (tau : ℝ) (rho : NontrivialZetaZero) :
    0 ≤ zetaUpperResolventScrewWickSummand tau rho := by
  exact mul_nonneg (zetaUpperResolventScrewWeight_nonneg rho)
    (Real.exp_pos _).le

/-- At nonnegative Gaussian time, damping bounds every Wick summand by its
zero-time resolvent weight. -/
theorem zetaUpperResolventScrewWickSummand_le_weight
    {tau : ℝ} (htau : 0 ≤ tau) (rho : NontrivialZetaZero) :
    zetaUpperResolventScrewWickSummand tau rho ≤
      zetaUpperResolventScrewWeight rho := by
  unfold zetaUpperResolventScrewWickSummand
  have hexponent :
      -(tau * (zetaSpectralCoordinate rho.1).im ^ 2) ≤ 0 := by
    exact neg_nonpos.mpr (mul_nonneg htau (sq_nonneg _))
  have hexp : Real.exp
      (-(tau * (zetaSpectralCoordinate rho.1).im ^ 2)) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr hexponent
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hexp
      (zetaUpperResolventScrewWeight_nonneg rho)

/-- The complete regularized Wick screw series is summable at every
nonnegative Gaussian time. -/
theorem summable_zetaUpperResolventScrewWickSummand
    {tau : ℝ} (htau : 0 ≤ tau) :
    Summable (zetaUpperResolventScrewWickSummand tau) := by
  exact summable_zetaUpperResolventScrewWeight.of_nonneg_of_le
    (zetaUpperResolventScrewWickSummand_nonneg tau)
    (zetaUpperResolventScrewWickSummand_le_weight htau)

/-- The complete finite resolvent-weighted Wick screw mass. -/
def riemannXiUpperResolventScrewWickMass (tau : ℝ) : ℝ :=
  ∑' rho : NontrivialZetaZero,
    zetaUpperResolventScrewWickSummand tau rho

/-- A genuine finite zeta-window approximation to the resolvent Wick mass. -/
def riemannXiUpperResolventScrewWickMassWindow
    (tau T : ℝ) : ℝ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    zetaUpperResolventScrewWickSummand tau rho

/-- Cofinal genuine zeta windows converge to the complete finite resolvent
Wick mass. -/
theorem tendsto_riemannXiUpperResolventScrewWickMassWindow
    {tau : ℝ} (htau : 0 ≤ tau) :
    Tendsto (riemannXiUpperResolventScrewWickMassWindow tau) atTop
      (nhds (riemannXiUpperResolventScrewWickMass tau)) := by
  unfold riemannXiUpperResolventScrewWickMassWindow
    riemannXiUpperResolventScrewWickMass
  exact (summable_zetaUpperResolventScrewWickSummand htau).hasSum.comp
    tendsto_spectralZetaZeroWindow_atTop

/-- At zero Gaussian time, Wick mass agrees with real screw growth mass at
zero real time. -/
theorem riemannXiUpperResolventScrewWickMass_zero :
    riemannXiUpperResolventScrewWickMass 0 =
      riemannXiUpperResolventScrewGrowthMass 0 := by
  unfold riemannXiUpperResolventScrewWickMass
  rw [riemannXiUpperResolventScrewGrowthMass_zero]
  congr 1
  funext rho
  unfold zetaUpperResolventScrewWickSummand
  norm_num

/-- At every nonnegative Gaussian time, vanishing of the finite resolvent Wick
mass is equivalent to RH. -/
theorem riemannXiUpperResolventScrewWickMass_eq_zero_iff_rh
    {tau : ℝ} (htau : 0 ≤ tau) :
    riemannXiUpperResolventScrewWickMass tau = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    have hsummand : 0 < zetaUpperSpectralHeightSummand rho := by
      rw [zetaUpperSpectralHeightSummand, if_pos hwupper]
      exact mul_pos
        (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
        hwupper
    have hweight : 0 < zetaUpperResolventScrewWeight rho :=
      div_pos hsummand
        (spectralScrewResolventDenominator_normSq_pos rho)
    have hterm : 0 < zetaUpperResolventScrewWickSummand tau rho :=
      mul_pos hweight (Real.exp_pos _)
    have hle : zetaUpperResolventScrewWickSummand tau rho ≤
        riemannXiUpperResolventScrewWickMass tau := by
      unfold riemannXiUpperResolventScrewWickMass
      simpa using
        (summable_zetaUpperResolventScrewWickSummand htau).sum_le_tsum
          {rho} (fun sigma _hsigma ↦
            zetaUpperResolventScrewWickSummand_nonneg tau sigma)
    rw [hzero] at hle
    exact (not_lt_of_ge hle) hterm
  · intro hRH
    unfold riemannXiUpperResolventScrewWickMass
    have hzero : zetaUpperResolventScrewWickSummand tau = 0 := by
      funext rho
      have him : (zetaSpectralCoordinate rho.1).im = 0 :=
        (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
          rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
      rw [zetaUpperResolventScrewWickSummand,
        zetaUpperResolventScrewWeight,
        zetaUpperSpectralHeightSummand, if_neg (by linarith),
        zero_div, zero_mul]
      rfl
    rw [hzero]
    exact tsum_zero

end

end RiemannGaussian
