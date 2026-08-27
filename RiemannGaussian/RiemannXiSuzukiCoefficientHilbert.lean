import RiemannGaussian.RiemannXiSuzukiFiniteExpansion

/-!
# Suzuki's spectral coefficient Hilbert vector

Suzuki's zero expansion has coefficient

`sqrt(pi * m_alpha) * (exp(-i * alpha * t) - 1) / alpha`.

This file proves, unconditionally and for the genuine spectral-xi divisor,
that the coefficient sequence with the universal `sqrt(pi)` removed belongs
to `ℓ²` at every real time.  The proof first represents the continuously
extended coefficient as the interval integral of its raw screw derivative.
It then combines a uniform critical-strip bound with the quotient's large
spectral-ordinate decay to obtain an explicit inverse-square majorant.  The
already formalized inverse-square xi-divisor theorem supplies summability.

The resulting `ℓ²` vector is the exact domain coefficient vector in Suzuki's
finite expansion.  This does not assert that synthesis by the zero-function
family is bounded into `L²(R)` off RH; formalizing and controlling that Gram
operator remains the central analytic frontier.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The norm of the raw coefficient derivative records its transverse
spectral exponential exactly. -/
theorem norm_suzukiSpectralScrewCoefficientDerivative
    (t : ℝ) (alpha : ℂ) :
    ‖suzukiSpectralScrewCoefficientDerivative t alpha‖ =
      Real.exp (alpha.im * t) := by
  unfold suzukiSpectralScrewCoefficientDerivative spectralScrewExponential
  rw [norm_mul, norm_neg, norm_I, one_mul, Complex.norm_exp]
  congr 1
  simp

/-- Suzuki's continuously extended coefficient is the interval integral of
its raw derivative, for either sign of time. -/
theorem integral_suzukiSpectralScrewCoefficientDerivative
    (t : ℝ) (alpha : ℂ) :
    (∫ u : ℝ in 0..t,
      suzukiSpectralScrewCoefficientDerivative u alpha) =
      suzukiSpectralScrewCoefficient t alpha := by
  have hcont : Continuous
      (fun u : ℝ ↦ suzukiSpectralScrewCoefficientDerivative u alpha) := by
    unfold suzukiSpectralScrewCoefficientDerivative
      spectralScrewExponential
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _hu ↦ hasDerivAt_suzukiSpectralScrewCoefficient u alpha)
    (hcont.intervalIntegrable 0 t)]
  simp

/-- On a half-width critical strip, the raw derivative is uniformly bounded
along the interval from zero to `t`. -/
lemma norm_suzukiSpectralScrewCoefficientDerivative_le
    {t u : ℝ} {alpha : ℂ}
    (halpha : |alpha.im| ≤ 1 / 2)
    (hu : u ∈ Set.uIcc 0 t) :
    ‖suzukiSpectralScrewCoefficientDerivative u alpha‖ ≤
      Real.exp (|t| / 2) := by
  rw [norm_suzukiSpectralScrewCoefficientDerivative]
  apply Real.exp_le_exp.mpr
  have huabs : |u| ≤ |t| := by
    rcases mem_uIcc.mp hu with h | h
    · rw [abs_of_nonneg h.1]
      exact (le_abs_self t).trans' h.2
    · rw [abs_of_nonpos h.2]
      have : -u ≤ -t := neg_le_neg h.1
      exact this.trans (neg_le_abs t)
  calc
    alpha.im * u ≤ |alpha.im * u| := le_abs_self _
    _ = |alpha.im| * |u| := abs_mul _ _
    _ ≤ (1 / 2) * |t| :=
      mul_le_mul halpha huabs (abs_nonneg _) (by norm_num)
    _ = |t| / 2 := by ring

/-- The interval representation gives a uniform strip bound for Suzuki's
coefficient, including at the removable frequency zero. -/
theorem norm_suzukiSpectralScrewCoefficient_le_strip
    (t : ℝ) {alpha : ℂ} (halpha : |alpha.im| ≤ 1 / 2) :
    ‖suzukiSpectralScrewCoefficient t alpha‖ ≤
      Real.exp (|t| / 2) * |t| := by
  rw [← integral_suzukiSpectralScrewCoefficientDerivative]
  calc
    ‖∫ u : ℝ in 0..t,
        suzukiSpectralScrewCoefficientDerivative u alpha‖ ≤
        Real.exp (|t| / 2) * |t - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (fun u hu ↦
          norm_suzukiSpectralScrewCoefficientDerivative_le halpha
            (uIoc_subset_uIcc hu))
    _ = Real.exp (|t| / 2) * |t| := by simp

/-- Away from zero frequency, the quotient formula gives spectral decay. -/
theorem norm_suzukiSpectralScrewCoefficient_le_div
    (t : ℝ) {alpha : ℂ} (halpha : alpha ≠ 0) :
    ‖suzukiSpectralScrewCoefficient t alpha‖ ≤
      (Real.exp (alpha.im * t) + 1) / ‖alpha‖ := by
  rw [suzukiSpectralScrewCoefficient_of_ne_zero t halpha, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg alpha)
  calc
    ‖spectralScrewExponential t alpha - 1‖ ≤
        ‖spectralScrewExponential t alpha‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = Real.exp (alpha.im * t) + 1 := by
      rw [show ‖spectralScrewExponential t alpha‖ =
          Real.exp (alpha.im * t) by
        unfold spectralScrewExponential
        rw [Complex.norm_exp]
        congr 1
        simp]
      norm_num

/-- The quotient decay bound made uniform on the half-width strip. -/
theorem norm_suzukiSpectralScrewCoefficient_le_div_strip
    (t : ℝ) {alpha : ℂ} (halpha : alpha ≠ 0)
    (hstrip : |alpha.im| ≤ 1 / 2) :
    ‖suzukiSpectralScrewCoefficient t alpha‖ ≤
      (Real.exp (|t| / 2) + 1) / ‖alpha‖ := by
  refine (norm_suzukiSpectralScrewCoefficient_le_div t halpha).trans ?_
  apply div_le_div_of_nonneg_right _ (norm_nonneg alpha)
  gcongr
  calc
    alpha.im * t ≤ |alpha.im * t| := le_abs_self _
    _ = |alpha.im| * |t| := abs_mul _ _
    _ ≤ (1 / 2) * |t| :=
      mul_le_mul_of_nonneg_right hstrip (abs_nonneg t)
    _ = |t| / 2 := by ring

/-- An explicit uniform constant for inverse-square decay of Suzuki's
coefficient on the critical strip. -/
def suzukiSpectralCoefficientInverseSquareConstant (t : ℝ) : ℝ :=
  4 *
    ((Real.exp (|t| / 2) * |t|) ^ 2 +
      (Real.exp (|t| / 2) + 1) ^ 2)

/-- The inverse-square coefficient constant is nonnegative. -/
theorem suzukiSpectralCoefficientInverseSquareConstant_nonneg (t : ℝ) :
    0 ≤ suzukiSpectralCoefficientInverseSquareConstant t := by
  unfold suzukiSpectralCoefficientInverseSquareConstant
  positivity

/-- The published Suzuki coefficient has uniform inverse-square decay on the
genuine xi divisor. -/
theorem one_add_re_sq_mul_normSq_suzukiSpectralScrewCoefficient_le
    (t : ℝ) (rho : NontrivialZetaZero) :
    (1 + (zetaSpectralCoordinate rho.1).re ^ 2) *
        Complex.normSq
          (suzukiSpectralScrewCoefficient t
            (zetaSpectralCoordinate rho.1)) ≤
      suzukiSpectralCoefficientInverseSquareConstant t := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  let B : ℝ := Real.exp (|t| / 2)
  let A : ℝ := B * |t|
  let D : ℝ := B + 1
  let x : ℝ := ‖suzukiSpectralScrewCoefficient t alpha‖
  let R : ℝ := |alpha.re|
  have hstrip : |alpha.im| ≤ 1 / 2 :=
    (NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho).le
  have hB : 0 ≤ B := by positivity
  have hA : 0 ≤ A := mul_nonneg hB (abs_nonneg t)
  have hD : 0 ≤ D := by positivity
  have hx : 0 ≤ x := norm_nonneg _
  rw [← Complex.sq_norm]
  unfold suzukiSpectralCoefficientInverseSquareConstant
  change (1 + alpha.re ^ 2) * x ^ 2 ≤
    4 * (A ^ 2 + D ^ 2)
  by_cases hsmall : R ≤ 1
  · have hnorm : x ≤ A := by
      exact norm_suzukiSpectralScrewCoefficient_le_strip t hstrip
    have hxsq : x ^ 2 ≤ A ^ 2 :=
      (sq_le_sq₀ hx hA).2 hnorm
    have hRsq : R ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (1 - R), abs_nonneg alpha.re]
    have hreSq : alpha.re ^ 2 = R ^ 2 := by
      simp [R]
    have hQ : 1 + alpha.re ^ 2 ≤ 2 := by
      rw [hreSq]
      linarith
    calc
      (1 + alpha.re ^ 2) * x ^ 2 ≤ 2 * A ^ 2 :=
        mul_le_mul hQ hxsq (sq_nonneg x) (by positivity)
      _ ≤ 4 * (A ^ 2 + D ^ 2) := by
        nlinarith [sq_nonneg A, sq_nonneg D]
  · have hR : 1 < R := lt_of_not_ge hsmall
    have hRpos : 0 < R := lt_trans (by norm_num) hR
    have halpha : alpha ≠ 0 := by
      intro hz
      have hre : alpha.re = 0 := congrArg Complex.re hz
      have hRzero : R = 0 := by simp [R, hre]
      linarith
    have hnormDiv : x ≤ D / ‖alpha‖ := by
      exact norm_suzukiSpectralScrewCoefficient_le_div_strip
        t halpha hstrip
    have hnormR : x ≤ D / R := by
      calc
        x ≤ D / ‖alpha‖ := hnormDiv
        _ ≤ D / R := by
          gcongr
          exact Complex.abs_re_le_norm alpha
    have hmul : x * R ≤ D :=
      (le_div_iff₀ hRpos).mp hnormR
    have hmulNonneg : 0 ≤ x * R :=
      mul_nonneg hx hRpos.le
    have hmulSq : (x * R) ^ 2 ≤ D ^ 2 :=
      (sq_le_sq₀ hmulNonneg hD).2 hmul
    have hprod : x ^ 2 * R ^ 2 ≤ D ^ 2 := by
      simpa [mul_pow] using hmulSq
    have hreSq : alpha.re ^ 2 = R ^ 2 := by
      simp [R]
    have hQ : 1 + alpha.re ^ 2 ≤ 2 * R ^ 2 := by
      rw [hreSq]
      nlinarith [sq_nonneg (R - 1)]
    calc
      (1 + alpha.re ^ 2) * x ^ 2 ≤
          (2 * R ^ 2) * x ^ 2 :=
        mul_le_mul_of_nonneg_right hQ (sq_nonneg x)
      _ = 2 * (x ^ 2 * R ^ 2) := by ring
      _ ≤ 2 * D ^ 2 := by gcongr
      _ ≤ 4 * (A ^ 2 + D ^ 2) := by
        nlinarith [sq_nonneg A, sq_nonneg D]

/-- The multiplicity-weighted squared modulus of one Suzuki coefficient. -/
def zetaSuzukiSpectralCoefficientEnergy
    (t : ℝ) (rho : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity rho : ℝ) *
    Complex.normSq
      (suzukiSpectralScrewCoefficient t
        (zetaSpectralCoordinate rho.1))

/-- Every Suzuki coefficient energy is nonnegative. -/
theorem zetaSuzukiSpectralCoefficientEnergy_nonneg
    (t : ℝ) (rho : NontrivialZetaZero) :
    0 ≤ zetaSuzukiSpectralCoefficientEnergy t rho := by
  unfold zetaSuzukiSpectralCoefficientEnergy
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-- Every multiplicity-weighted coefficient energy is controlled by the
unconditionally summable inverse-square xi-divisor weight. -/
theorem zetaSuzukiSpectralCoefficientEnergy_le_inverseSquare
    (t : ℝ) (rho : NontrivialZetaZero) :
    zetaSuzukiSpectralCoefficientEnergy t rho ≤
      suzukiSpectralCoefficientInverseSquareConstant t *
        ((analyticZetaZeroMultiplicity rho : ℝ) /
          (1 + (zetaSpectralCoordinate rho.1).re ^ 2)) := by
  let m : ℝ := analyticZetaZeroMultiplicity rho
  let q : ℝ := 1 + (zetaSpectralCoordinate rho.1).re ^ 2
  let n : ℝ := Complex.normSq
    (suzukiSpectralScrewCoefficient t
      (zetaSpectralCoordinate rho.1))
  let C : ℝ := suzukiSpectralCoefficientInverseSquareConstant t
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hweighted : q * n ≤ C := by
    exact
      one_add_re_sq_mul_normSq_suzukiSpectralScrewCoefficient_le t rho
  have hdiv : n ≤ C / q := by
    rw [le_div_iff₀ hq]
    simpa [mul_comm] using hweighted
  change m * n ≤ C * (m / q)
  calc
    m * n ≤ m * (C / q) := mul_le_mul_of_nonneg_left hdiv hm
    _ = C * (m / q) := by ring

/-- The complete multiplicity-weighted Suzuki coefficient energy is
unconditionally summable at every real time. -/
theorem summable_zetaSuzukiSpectralCoefficientEnergy (t : ℝ) :
    Summable (zetaSuzukiSpectralCoefficientEnergy t) := by
  apply
    (summable_distinct_zetaZeroInverseSquareSpectralRe.mul_left
      (suzukiSpectralCoefficientInverseSquareConstant t)).of_nonneg_of_le
      (zetaSuzukiSpectralCoefficientEnergy_nonneg t)
  exact zetaSuzukiSpectralCoefficientEnergy_le_inverseSquare t

/-- One square-root-multiplicity-weighted Suzuki coefficient. -/
def zetaSuzukiSpectralCoefficientFeature
    (t : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
    suzukiSpectralScrewCoefficient t
      (zetaSpectralCoordinate rho.1)

/-- The squared modulus of a coefficient feature is its positive energy. -/
theorem normSq_zetaSuzukiSpectralCoefficientFeature
    (t : ℝ) (rho : NontrivialZetaZero) :
    Complex.normSq (zetaSuzukiSpectralCoefficientFeature t rho) =
      zetaSuzukiSpectralCoefficientEnergy t rho := by
  rw [zetaSuzukiSpectralCoefficientFeature, Complex.normSq_mul,
    Complex.normSq_ofReal,
    Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rfl

/-- The genuine-zeta Suzuki coefficient features form an `ℓ²` family at
every real time, without assuming RH. -/
theorem summable_norm_sq_zetaSuzukiSpectralCoefficientFeature (t : ℝ) :
    Summable (fun rho : NontrivialZetaZero ↦
      ‖zetaSuzukiSpectralCoefficientFeature t rho‖ ^ 2) := by
  simpa only [Complex.sq_norm,
    normSq_zetaSuzukiSpectralCoefficientFeature] using
      summable_zetaSuzukiSpectralCoefficientEnergy t

/-- The complete Suzuki coefficient sequence as a literal `ℓ²` vector. -/
def riemannXiSuzukiSpectralCoefficientVector (t : ℝ) :
    ℓ²(NontrivialZetaZero, ℂ) :=
  ⟨zetaSuzukiSpectralCoefficientFeature t, by
    apply memℓp_gen
    simpa using summable_norm_sq_zetaSuzukiSpectralCoefficientFeature t⟩

/-- Suzuki's published coefficient amplitude factors into the universal
`sqrt(pi)` and the square-root multiplicity used by the `ℓ²` vector. -/
theorem suzukiXiZeroCoefficientAmplitude_eq
    (rho : NontrivialZetaZero) :
    suzukiXiZeroCoefficientAmplitude rho =
      Real.sqrt Real.pi *
        Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) := by
  unfold suzukiXiZeroCoefficientAmplitude
  rw [Real.sqrt_mul Real.pi_nonneg]

/-- The coefficient in Suzuki's finite zero expansion is exactly
`sqrt(pi)` times the corresponding coordinate of the complete coefficient
vector. -/
theorem suzukiXiPublishedCoefficient_eq_sqrtPi_mul_feature
    (t : ℝ) (rho : NontrivialZetaZero) :
    (suzukiXiZeroCoefficientAmplitude rho : ℂ) *
        suzukiSpectralScrewCoefficient t
          (zetaSpectralCoordinate rho.1) =
      (Real.sqrt Real.pi : ℂ) *
        zetaSuzukiSpectralCoefficientFeature t rho := by
  rw [suzukiXiZeroCoefficientAmplitude_eq]
  unfold zetaSuzukiSpectralCoefficientFeature
  push_cast
  ring

/-- The total squared coefficient mass. -/
def riemannXiSuzukiSpectralCoefficientEnergy (t : ℝ) : ℝ :=
  ∑' rho : NontrivialZetaZero,
    zetaSuzukiSpectralCoefficientEnergy t rho

/-- The complete coefficient mass is the squared norm of the literal `ℓ²`
coefficient vector. -/
theorem norm_sq_riemannXiSuzukiSpectralCoefficientVector (t : ℝ) :
    ‖riemannXiSuzukiSpectralCoefficientVector t‖ ^ 2 =
      riemannXiSuzukiSpectralCoefficientEnergy t := by
  calc
    ‖riemannXiSuzukiSpectralCoefficientVector t‖ ^ 2 =
        ∑' rho : NontrivialZetaZero,
          ‖riemannXiSuzukiSpectralCoefficientVector t rho‖ ^ 2 := by
      simpa using
        (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
          (riemannXiSuzukiSpectralCoefficientVector t))
    _ = ∑' rho : NontrivialZetaZero,
          zetaSuzukiSpectralCoefficientEnergy t rho := by
      apply tsum_congr
      intro rho
      change ‖zetaSuzukiSpectralCoefficientFeature t rho‖ ^ 2 = _
      rw [Complex.sq_norm,
        normSq_zetaSuzukiSpectralCoefficientFeature]
    _ = riemannXiSuzukiSpectralCoefficientEnergy t := rfl

/-- The complete Suzuki coefficient vector starts at the zero vector. -/
@[simp] theorem riemannXiSuzukiSpectralCoefficientVector_zero_time :
    riemannXiSuzukiSpectralCoefficientVector 0 = 0 := by
  ext rho
  simp [riemannXiSuzukiSpectralCoefficientVector,
    zetaSuzukiSpectralCoefficientFeature]

end

end RiemannGaussian
