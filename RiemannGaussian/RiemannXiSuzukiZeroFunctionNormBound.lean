import RiemannGaussian.RiemannXiSuzukiGramSchur
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Quantitative norms of off-axis Suzuki zero functions

The qualitative boundary `L²` theorem for every normalized xi-zero function
used only the unit carrier bound and an off-axis Cauchy kernel.  Here that
argument is made quantitative.  We first prove the exact translated and
scaled Cauchy-density integral

`∫ x, ((x-a)^2 + b^2)⁻¹ = pi / |b|` for `b != 0`,

then combine it with `|carrier(x)| <= 1`.  The result is the explicit bound

`‖zeroFunction(rho)‖₂² <= multiplicity(rho) / |Im(alpha_rho)|`

for every off-axis spectral zero.  This is unconditional and identifies the
vertical-gap statistic that any absolute-Gram argument must control.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- A translated and scaled real Cauchy density. -/
def suzukiShiftedScaledCauchyDensity (a b x : ℝ) : ℝ :=
  ((x - a) ^ 2 + b ^ 2)⁻¹

/-- Algebraic reduction of a nondegenerate Cauchy density to the normalized
`(1 + x²)⁻¹` density. -/
theorem suzukiShiftedScaledCauchyDensity_eq_normalized
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) (x : ℝ) :
    suzukiShiftedScaledCauchyDensity a b x =
      |b|⁻¹ ^ 2 * (1 + ((x - a) / |b|) ^ 2)⁻¹ := by
  have habs : |b| ≠ 0 := abs_ne_zero.mpr hb
  unfold suzukiShiftedScaledCauchyDensity
  rw [← sq_abs b]
  field_simp [habs]
  ring

/-- The translated and scaled Cauchy density is integrable whenever its
vertical scale is nonzero. -/
theorem integrable_suzukiShiftedScaledCauchyDensity
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    Integrable (suzukiShiftedScaledCauchyDensity a b) := by
  have habs : |b| ≠ 0 := abs_ne_zero.mpr hb
  have hscaled : Integrable (fun x : ℝ ↦
      (1 + (x / |b|) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div habs
  have hshifted : Integrable (fun x : ℝ ↦
      (1 + ((x - a) / |b|) ^ 2)⁻¹) := by
    simpa [sub_eq_add_neg] using hscaled.comp_add_right (-a)
  have hmul := hshifted.const_mul (|b|⁻¹ ^ 2)
  convert hmul using 1
  funext x
  exact suzukiShiftedScaledCauchyDensity_eq_normalized a hb x

/-- Exact integral of a translated and scaled Cauchy density. -/
theorem integral_suzukiShiftedScaledCauchyDensity
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) :
    ∫ x : ℝ, suzukiShiftedScaledCauchyDensity a b x =
      Real.pi / |b| := by
  have habs : |b| ≠ 0 := abs_ne_zero.mpr hb
  have htranslate :
      (∫ x : ℝ, (1 + ((x - a) / |b|) ^ 2)⁻¹) =
        ∫ x : ℝ, (1 + (x / |b|) ^ 2)⁻¹ := by
    simpa [sub_eq_add_neg] using
      (MeasureTheory.integral_add_right_eq_self
        (fun x : ℝ ↦ (1 + (x / |b|) ^ 2)⁻¹) (-a))
  have hscale :
      (∫ x : ℝ, (1 + (x / |b|) ^ 2)⁻¹) =
        |b| * Real.pi := by
    calc
      (∫ x : ℝ, (1 + (x / |b|) ^ 2)⁻¹) =
          ‖|b|‖ • ∫ y : ℝ, (1 + y ^ 2)⁻¹ :=
        MeasureTheory.Measure.integral_comp_div
          (fun y : ℝ ↦ (1 + y ^ 2)⁻¹) |b|
      _ = |b| * Real.pi := by
        rw [integral_univ_inv_one_add_sq]
        simp [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg b)]
  calc
    (∫ x : ℝ, suzukiShiftedScaledCauchyDensity a b x) =
        ∫ x : ℝ,
          |b|⁻¹ ^ 2 * (1 + ((x - a) / |b|) ^ 2)⁻¹ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦
        suzukiShiftedScaledCauchyDensity_eq_normalized a hb x
    _ = |b|⁻¹ ^ 2 *
        ∫ x : ℝ, (1 + ((x - a) / |b|) ^ 2)⁻¹ := by
      rw [integral_const_mul]
    _ = |b|⁻¹ ^ 2 * (|b| * Real.pi) := by rw [htranslate, hscale]
    _ = Real.pi / |b| := by field_simp [habs]

/-- Squared norm of a real boundary displacement from a complex point. -/
theorem norm_sq_ofReal_sub_complex (x : ℝ) (alpha : ℂ) :
    ‖(x : ℂ) - alpha‖ ^ 2 =
      (x - alpha.re) ^ 2 + alpha.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
    Complex.ofReal_im, zero_sub]
  ring

/-- Pointwise squared-norm domination of an off-axis normalized zero function
by its scalar Cauchy density. -/
theorem norm_sq_suzukiRealAxisZeroFunction_le_cauchyDensity_of_im_ne_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0)
    (x : ℝ) :
    ‖suzukiRealAxisZeroFunction rho x‖ ^ 2 ≤
      suzukiXiZeroNormalization rho ^ 2 *
        suzukiShiftedScaledCauchyDensity
          (zetaSpectralCoordinate rho.1).re
          (zetaSpectralCoordinate rho.1).im x := by
  let alpha := zetaSpectralCoordinate rho.1
  let N := suzukiXiZeroNormalization rho
  have hnormalization : 0 ≤ N := suzukiXiZeroNormalization_nonneg rho
  have hdenNe : (x : ℂ) - alpha ≠ 0 := by
    intro hzero
    have him : -alpha.im = 0 := by
      simpa using congrArg Complex.im hzero
    exact hrho (by simpa [alpha] using (neg_eq_zero.mp him))
  have hdenPos : 0 < ‖(x : ℂ) - alpha‖ := norm_pos_iff.mpr hdenNe
  have hnorm : ‖suzukiRealAxisZeroFunction rho x‖ ≤
      N / ‖(x : ℂ) - alpha‖ := by
    change ‖(N : ℂ) * suzukiXiZeroCarrier (x : ℂ) /
        ((x : ℂ) - alpha)‖ ≤ N / ‖(x : ℂ) - alpha‖
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnormalization]
    apply div_le_div_of_nonneg_right _ hdenPos.le
    exact mul_le_of_le_one_right hnormalization
      (norm_suzukiXiZeroCarrier_ofReal_le_one x)
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  change ‖suzukiRealAxisZeroFunction rho x‖ ^ 2 ≤
    N ^ 2 * suzukiShiftedScaledCauchyDensity alpha.re alpha.im x
  calc
    ‖suzukiRealAxisZeroFunction rho x‖ ^ 2 ≤
        (N / ‖(x : ℂ) - alpha‖) ^ 2 := hsquare
    _ = N ^ 2 * suzukiShiftedScaledCauchyDensity alpha.re alpha.im x := by
      unfold suzukiShiftedScaledCauchyDensity
      rw [div_pow, norm_sq_ofReal_sub_complex]
      ring

/-- The normalization square is exactly analytic multiplicity divided by
`pi`. -/
theorem sq_suzukiXiZeroNormalization (rho : NontrivialZetaZero) :
    suzukiXiZeroNormalization rho ^ 2 =
      (analyticZetaZeroMultiplicity rho : ℝ) / Real.pi := by
  unfold suzukiXiZeroNormalization
  exact Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) Real.pi_nonneg)

/-- Exact `L²` norm-square identity for every packaged normalized zero
function. -/
theorem norm_sq_suzukiRealAxisZeroFunctionLp
    (rho : NontrivialZetaZero) :
    ‖suzukiRealAxisZeroFunctionLp rho‖ ^ 2 =
      ∫ x : ℝ, ‖suzukiRealAxisZeroFunction rho x‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)
    (suzukiRealAxisZeroFunctionLp rho)]
  rw [L2.inner_def]
  rw [← integral_re
    (L2.integrable_inner (suzukiRealAxisZeroFunctionLp rho)
      (suzukiRealAxisZeroFunctionLp rho))]
  apply integral_congr_ae
  filter_upwards [suzukiRealAxisZeroFunctionLp_ae rho] with x hx
  rw [hx]
  exact inner_self_eq_norm_sq (𝕜 := ℂ)
    (suzukiRealAxisZeroFunction rho x)

/-- Quantitative integral bound for every off-axis normalized xi-zero
function. -/
theorem integral_norm_sq_suzukiRealAxisZeroFunction_le_of_im_ne_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    (∫ x : ℝ, ‖suzukiRealAxisZeroFunction rho x‖ ^ 2) ≤
      (analyticZetaZeroMultiplicity rho : ℝ) /
        |(zetaSpectralCoordinate rho.1).im| := by
  let alpha := zetaSpectralCoordinate rho.1
  let N := suzukiXiZeroNormalization rho
  have hleft : Integrable
      (fun x : ℝ ↦ ‖suzukiRealAxisZeroFunction rho x‖ ^ 2) := by
    exact (memLp_two_iff_integrable_sq_norm
      (measurable_suzukiRealAxisZeroFunction rho).aestronglyMeasurable).1
        (memLp_two_suzukiRealAxisZeroFunction_of_im_ne_zero rho hrho)
  have hright : Integrable (fun x : ℝ ↦
      N ^ 2 * suzukiShiftedScaledCauchyDensity alpha.re alpha.im x) :=
    (integrable_suzukiShiftedScaledCauchyDensity alpha.re hrho).const_mul
      (N ^ 2)
  calc
    (∫ x : ℝ, ‖suzukiRealAxisZeroFunction rho x‖ ^ 2) ≤
        ∫ x : ℝ,
          N ^ 2 * suzukiShiftedScaledCauchyDensity alpha.re alpha.im x := by
      apply integral_mono hleft hright
      intro x
      exact norm_sq_suzukiRealAxisZeroFunction_le_cauchyDensity_of_im_ne_zero
        rho hrho x
    _ = N ^ 2 * (Real.pi / |alpha.im|) := by
      rw [integral_const_mul,
        integral_suzukiShiftedScaledCauchyDensity alpha.re hrho]
    _ = (analyticZetaZeroMultiplicity rho : ℝ) / |alpha.im| := by
      rw [show N ^ 2 = (analyticZetaZeroMultiplicity rho : ℝ) /
        Real.pi by exact sq_suzukiXiZeroNormalization rho]
      field_simp [Real.pi_ne_zero, abs_ne_zero.mpr hrho]
    _ = (analyticZetaZeroMultiplicity rho : ℝ) /
        |(zetaSpectralCoordinate rho.1).im| := by rfl

/-- Explicit off-axis norm-square bound for the actual boundary Hilbert
vector. -/
theorem norm_sq_suzukiRealAxisZeroFunctionLp_le_of_im_ne_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ‖suzukiRealAxisZeroFunctionLp rho‖ ^ 2 ≤
      (analyticZetaZeroMultiplicity rho : ℝ) /
        |(zetaSpectralCoordinate rho.1).im| := by
  rw [norm_sq_suzukiRealAxisZeroFunctionLp]
  exact integral_norm_sq_suzukiRealAxisZeroFunction_le_of_im_ne_zero rho hrho

/-- Square-root form of the quantitative off-axis boundary norm bound. -/
theorem norm_suzukiRealAxisZeroFunctionLp_le_sqrt_of_im_ne_zero
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ‖suzukiRealAxisZeroFunctionLp rho‖ ≤
      Real.sqrt ((analyticZetaZeroMultiplicity rho : ℝ) /
        |(zetaSpectralCoordinate rho.1).im|) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt]
  · exact norm_sq_suzukiRealAxisZeroFunctionLp_le_of_im_ne_zero rho hrho
  · exact div_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

/-- Explicit two-node Gram majorant for off-axis spectral zeros. -/
theorem norm_suzukiXiZeroFunctionGramEntry_le_verticalGap
    (rho sigma : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0)
    (hsigma : (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    ‖suzukiXiZeroFunctionGramEntry rho sigma‖ ≤
      Real.sqrt ((analyticZetaZeroMultiplicity rho : ℝ) /
          |(zetaSpectralCoordinate rho.1).im|) *
        Real.sqrt ((analyticZetaZeroMultiplicity sigma : ℝ) /
          |(zetaSpectralCoordinate sigma.1).im|) := by
  calc
    ‖suzukiXiZeroFunctionGramEntry rho sigma‖ ≤
        ‖suzukiRealAxisZeroFunctionLp rho‖ *
          ‖suzukiRealAxisZeroFunctionLp sigma‖ :=
      norm_suzukiXiZeroFunctionGramEntry_le rho sigma
    _ ≤ Real.sqrt ((analyticZetaZeroMultiplicity rho : ℝ) /
          |(zetaSpectralCoordinate rho.1).im|) *
        Real.sqrt ((analyticZetaZeroMultiplicity sigma : ℝ) /
          |(zetaSpectralCoordinate sigma.1).im|) := by
      exact mul_le_mul
        (norm_suzukiRealAxisZeroFunctionLp_le_sqrt_of_im_ne_zero rho hrho)
        (norm_suzukiRealAxisZeroFunctionLp_le_sqrt_of_im_ne_zero sigma hsigma)
        (norm_nonneg _) (Real.sqrt_nonneg _)

/-- Finite off-axis Gram rows are bounded by the corresponding explicit sum
of vertical-gap majorants. -/
theorem sum_norm_suzukiXiZeroFunctionGramEntry_le_verticalGap
    (rho : NontrivialZetaZero)
    (hrho : (zetaSpectralCoordinate rho.1).im ≠ 0)
    (S : Finset NontrivialZetaZero)
    (hS : ∀ sigma ∈ S,
      (zetaSpectralCoordinate sigma.1).im ≠ 0) :
    ∑ sigma ∈ S, ‖suzukiXiZeroFunctionGramEntry rho sigma‖ ≤
      Real.sqrt ((analyticZetaZeroMultiplicity rho : ℝ) /
          |(zetaSpectralCoordinate rho.1).im|) *
        ∑ sigma ∈ S,
          Real.sqrt ((analyticZetaZeroMultiplicity sigma : ℝ) /
            |(zetaSpectralCoordinate sigma.1).im|) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro sigma hsigma
  exact norm_suzukiXiZeroFunctionGramEntry_le_verticalGap
    rho sigma hrho (hS sigma hsigma)

end

end RiemannGaussian
