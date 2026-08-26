import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import RiemannGaussian.GaussianXiGrowth

/-!
# Complex Gaussian heat convolution

The real heat identity is insufficient on its own for a Weil zero sum,
because nontrivial zeros need not lie on the real spectral axis.  Here the
same identity is proved for the entire Gaussian at an arbitrary complex
spectral point.
-/

namespace RiemannGaussian

noncomputable section

open MeasureTheory

lemma heatKernel_mul_complexTranslatedGaussian_eq_quadratic
    (a b t s : ℝ) (z : ℂ) :
    (Real.exp (-b * (t - s) ^ 2) : ℂ) *
        complexTranslatedGaussian a s z =
      Complex.exp
        ((-(a + b) : ℂ) * (s : ℂ) ^ 2 +
          (2 * ((b : ℂ) * t + (a : ℂ) * z)) * s +
            (-((b : ℂ) * t ^ 2 + (a : ℂ) * z ^ 2))) := by
  rw [complexTranslatedGaussian, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrable_heatKernel_mul_complexTranslatedGaussian
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) (z : ℂ) :
    Integrable (fun s : ℝ =>
      (Real.exp (-b * (t - s) ^ 2) : ℂ) *
        complexTranslatedGaussian a s z) := by
  have habpos : 0 < a + b := add_pos ha hb
  have hquad := integrable_cexp_quadratic
    (b := ((a + b : ℝ) : ℂ))
    (by simpa using habpos)
    (2 * ((b : ℂ) * t + (a : ℂ) * z))
    (-((b : ℂ) * t ^ 2 + (a : ℂ) * z ^ 2))
  exact hquad.congr (Filter.Eventually.of_forall fun s =>
    (by
      simpa only [Complex.ofReal_add] using
        (heatKernel_mul_complexTranslatedGaussian_eq_quadratic
          a b t s z).symm))

/-- Exact integral of the norm of the complex heat integrand. -/
theorem integral_norm_heatKernel_mul_complexTranslatedGaussian
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) (z : ℂ) :
    (∫ s : ℝ,
        ‖(Real.exp (-b * (t - s) ^ 2) : ℂ) *
          complexTranslatedGaussian a s z‖) =
      Real.sqrt (Real.pi / (a + b)) *
        Real.exp (a * z.im ^ 2 -
          (a * b / (a + b)) * (z.re - t) ^ 2) := by
  have hpoint (s : ℝ) :
      ‖(Real.exp (-b * (t - s) ^ 2) : ℂ) *
          complexTranslatedGaussian a s z‖ =
        Real.exp (a * z.im ^ 2) *
          (Real.exp (-b * (t - s) ^ 2) *
            translatedGaussian a s z.re) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), norm_complexTranslatedGaussian]
    unfold translatedGaussian
    simp only [← Real.exp_add]
    congr 1
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul,
    integral_translatedGaussian_mul_translatedGaussian ha hb]
  rw [show a * z.im ^ 2 - a * b / (a + b) * (z.re - t) ^ 2 =
      a * z.im ^ 2 + (-(a * b / (a + b)) * (z.re - t) ^ 2) by ring,
    Real.exp_add]
  ring

/-- Integral of the product of a real heat kernel with an entire translated
Gaussian. -/
theorem integral_heatKernel_mul_complexTranslatedGaussian
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) (z : ℂ) :
    (∫ s : ℝ,
        (Real.exp (-b * (t - s) ^ 2) : ℂ) *
          complexTranslatedGaussian a s z) =
      (Real.sqrt (Real.pi / (a + b)) : ℂ) *
        complexTranslatedGaussian (a * b / (a + b)) t z := by
  have habpos : 0 < a + b := add_pos ha hb
  have hab : a + b ≠ 0 := habpos.ne'
  have hpoint := fun s : ℝ =>
    heatKernel_mul_complexTranslatedGaussian_eq_quadratic a b t s z
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_cexp_quadratic
    (b := (-(a + b) : ℂ))
    (by simpa using neg_lt_zero.mpr habpos)
    (2 * ((b : ℂ) * t + (a : ℂ) * z))
    (-((b : ℂ) * t ^ 2 + (a : ℂ) * z ^ 2))]
  have hsqrt :
      ((Real.sqrt (Real.pi / (a + b)) : ℝ) : ℂ) =
        ((Real.pi / (a + b) : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa using Complex.ofReal_cpow
      (div_nonneg Real.pi_pos.le habpos.le) (1 / 2 : ℝ)
  have hbase :
      (((Real.pi : ℂ) / -(-(a + b) : ℂ)) : ℂ) ^ (1 / 2 : ℂ) =
        (Real.sqrt (Real.pi / (a + b)) : ℂ) := by
    rw [hsqrt]
    congr 2
    push_cast
    ring
  have hexponent :
      -((b : ℂ) * t ^ 2 + (a : ℂ) * z ^ 2) -
          (2 * ((b : ℂ) * t + (a : ℂ) * z)) ^ 2 /
            (4 * (-(a + b) : ℂ)) =
        -(((a * b / (a + b) : ℝ) : ℂ) * (z - t) ^ 2) := by
    have habc : (a : ℂ) + b ≠ 0 := by
      simpa only [Complex.ofReal_add] using Complex.ofReal_ne_zero.mpr hab
    have hbac : (b : ℂ) + a ≠ 0 := by
      simpa [add_comm] using habc
    push_cast
    field_simp [habc, hbac]
    ring
  rw [hbase, hexponent]
  rfl

/-- Exact positive heat broadening of the entire translated Gaussian. -/
theorem complexTranslatedGaussian_heat_convolution
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) (z : ℂ) :
    complexTranslatedGaussian ε t z =
      (heatNormalization a (heatParameter a ε) : ℂ) *
        ∫ s : ℝ,
          (Real.exp (-heatParameter a ε * (t - s) ^ 2) : ℂ) *
            complexTranslatedGaussian a s z := by
  have ha : 0 < a := hε.trans hεa
  have hb : 0 < heatParameter a ε := heatParameter_pos hε hεa
  have hab : 0 < a + heatParameter a ε := add_pos ha hb
  rw [integral_heatKernel_mul_complexTranslatedGaussian ha hb]
  rw [heatParameter_effective hε hεa]
  unfold heatNormalization
  have hsqrt : Real.sqrt (Real.pi / (a + heatParameter a ε)) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (div_pos Real.pi_pos hab)
  have hsqrtC :
      (Real.sqrt (Real.pi / (a + heatParameter a ε)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrt
  push_cast
  field_simp [hsqrtC]

/-- The even entire Gaussian satisfies the same heat identity. -/
theorem complexSymmetricGaussian_heat_convolution
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) (z : ℂ) :
    complexSymmetricGaussian ε t z =
      (heatNormalization a (heatParameter a ε) : ℂ) *
        ∫ s : ℝ,
          (Real.exp (-heatParameter a ε * (t - s) ^ 2) : ℂ) *
            complexSymmetricGaussian a s z := by
  have ha : 0 < a := hε.trans hεa
  have hb : 0 < heatParameter a ε := heatParameter_pos hε hεa
  let b := heatParameter a ε
  have hfirstInt : Integrable (fun s : ℝ =>
      (Real.exp (-b * (t - s) ^ 2) : ℂ) *
        complexTranslatedGaussian a s z) :=
    integrable_heatKernel_mul_complexTranslatedGaussian ha hb t z
  have hnegativeCenter : Integrable (fun s : ℝ =>
      (Real.exp (-b * (-t - s) ^ 2) : ℂ) *
        complexTranslatedGaussian a s z) :=
    integrable_heatKernel_mul_complexTranslatedGaussian ha hb (-t) z
  have hsecondInt : Integrable (fun s : ℝ =>
      (Real.exp (-b * (t - s) ^ 2) : ℂ) *
        complexTranslatedGaussian a (-s) z) := by
    have hcomp := hnegativeCenter.comp_neg
    refine hcomp.congr (Filter.Eventually.of_forall fun s => ?_)
    dsimp only [Function.comp_apply] at hcomp ⊢
    have hsquare : (-t - -s) ^ 2 = (t - s) ^ 2 := by ring
    rw [hsquare]
  have hsecondIntegral :
      (∫ s : ℝ,
          (Real.exp (-b * (-t - s) ^ 2) : ℂ) *
            complexTranslatedGaussian a s z) =
        ∫ s : ℝ,
          (Real.exp (-b * (t - s) ^ 2) : ℂ) *
            complexTranslatedGaussian a (-s) z := by
    calc
      (∫ s : ℝ,
          (Real.exp (-b * (-t - s) ^ 2) : ℂ) *
            complexTranslatedGaussian a s z) =
          ∫ s : ℝ,
            (Real.exp (-b * (-t - (-s)) ^ 2) : ℂ) *
              complexTranslatedGaussian a (-s) z := by
        exact (integral_neg_eq_self
          (fun s : ℝ =>
            (Real.exp (-b * (-t - s) ^ 2) : ℂ) *
              complexTranslatedGaussian a s z) volume).symm
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun s => by
          dsimp only
          have hsquare : (-t - -s) ^ 2 = (t - s) ^ 2 := by ring
          rw [hsquare]
  have hfirst := complexTranslatedGaussian_heat_convolution hε hεa t z
  have hsecond := complexTranslatedGaussian_heat_convolution hε hεa (-t) z
  unfold complexSymmetricGaussian
  rw [hfirst, hsecond, ← mul_add]
  congr 1
  rw [show
    (∫ s : ℝ,
        (Real.exp (-heatParameter a ε * (-t - s) ^ 2) : ℂ) *
          complexTranslatedGaussian a s z) =
      ∫ s : ℝ,
        (Real.exp (-heatParameter a ε * (t - s) ^ 2) : ℂ) *
          complexTranslatedGaussian a (-s) z by
    simpa only [b] using hsecondIntegral]
  rw [← integral_add]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun s => by
      simp only [mul_add]
  · simpa only [b] using hfirstInt
  · simpa only [b] using hsecondInt

/-! ## Passing heat convolution through the canonical zero sum -/

/-- The `L¹` norms of all zero-summand heat integrands form a summable
family.  This is the quantitative input needed to exchange the zero sum and
the center integral. -/
theorem summable_integral_norm_zetaGaussian_heat
    (hOrdinate : ZetaZeroGaussianOrdinateSummable)
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) :
    Summable (fun occurrence :
        NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
      ∫ s : ℝ,
        ‖(Real.exp (-heatParameter a ε * (t - s) ^ 2) : ℂ) *
          zetaGaussianZeroSummand
            analyticZetaZeroMultiplicity a s occurrence‖) := by
  let b : ℝ := heatParameter a ε
  let root : ℝ := Real.sqrt (Real.pi / (a + b))
  let D : ℝ := root * Real.exp ((a - ε) / 4)
  have ha : 0 < a := hε.trans hεa
  have hb : 0 < b := by
    dsimp [b]
    exact heatParameter_pos hε hεa
  have hroot0 : 0 ≤ root := Real.sqrt_nonneg _
  have hD0 : 0 ≤ D := mul_nonneg hroot0 (Real.exp_nonneg _)
  have hbase :=
    (summable_zetaGaussianZeroSummand_of_ordinateSummable
      hOrdinate ε t hε).norm
  have hdominating : Summable (fun occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
        D * ‖zetaGaussianZeroSummand
          analyticZetaZeroMultiplicity ε t occurrence‖) :=
    hbase.mul_left D
  apply hdominating.of_nonneg_of_le
  · intro occurrence
    exact integral_nonneg fun _ => norm_nonneg _
  · intro occurrence
    let z := zetaSpectralCoordinate occurrence.1.1
    have habs :=
      NontrivialZetaZero.abs_spectralCoordinate_im_lt_half occurrence.1
    have himSq : z.im ^ 2 ≤ 1 / 4 := by
      have hsquare : z.im ^ 2 < (1 / 2 : ℝ) ^ 2 :=
        sq_lt_sq.mpr (by
          simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            using habs)
      norm_num at hsquare ⊢
      exact hsquare.le
    have hgap0 : 0 ≤ a - ε := sub_nonneg.mpr hεa.le
    have hexponent :
        a * z.im ^ 2 - ε * (z.re - t) ^ 2 ≤
          (a - ε) / 4 +
            (ε * z.im ^ 2 - ε * (z.re - t) ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left himSq hgap0]
    rw [show heatParameter a ε = b by rfl]
    unfold zetaGaussianZeroSummand
    rw [integral_norm_heatKernel_mul_complexTranslatedGaussian ha hb]
    rw [show a * b / (a + b) = ε by
      dsimp [b]
      exact heatParameter_effective hε hεa]
    rw [norm_complexTranslatedGaussian]
    calc
      Real.sqrt (Real.pi / (a + b)) *
          Real.exp (a * z.im ^ 2 - ε * (z.re - t) ^ 2) ≤
          root * Real.exp
            ((a - ε) / 4 +
              (ε * z.im ^ 2 - ε * (z.re - t) ^ 2)) := by
        dsimp only [root]
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hexponent) hroot0
      _ = D * Real.exp
          (ε * z.im ^ 2 - ε * (z.re - t) ^ 2) := by
        dsimp only [D]
        rw [Real.exp_add]
        ring

/-- Heat convolution commutes with the complete multiplicity-weighted
translated zero sum. -/
theorem tsum_zetaGaussianZeroSummand_heat_convolution
    (hOrdinate : ZetaZeroGaussianOrdinateSummable)
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) :
    (∑' occurrence :
        NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      zetaGaussianZeroSummand
        analyticZetaZeroMultiplicity ε t occurrence) =
      (heatNormalization a (heatParameter a ε) : ℂ) *
        ∫ s : ℝ,
          (Real.exp (-heatParameter a ε * (t - s) ^ 2) : ℂ) *
            (∑' occurrence :
              NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
              zetaGaussianZeroSummand
                analyticZetaZeroMultiplicity a s occurrence) := by
  let F := fun occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
    fun s : ℝ =>
      (Real.exp (-heatParameter a ε * (t - s) ^ 2) : ℂ) *
        zetaGaussianZeroSummand
          analyticZetaZeroMultiplicity a s occurrence
  have ha : 0 < a := hε.trans hεa
  have hb : 0 < heatParameter a ε := heatParameter_pos hε hεa
  have hFint : ∀ occurrence, Integrable (F occurrence) := by
    intro occurrence
    exact integrable_heatKernel_mul_complexTranslatedGaussian ha hb t
      (zetaSpectralCoordinate occurrence.1.1)
  have hFnorm : Summable (fun occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
        ∫ s : ℝ, ‖F occurrence s‖) := by
    simpa only [F] using
      summable_integral_norm_zetaGaussian_heat hOrdinate hε hεa t
  have hinterchange :
      (∑' occurrence :
          NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        ∫ s : ℝ, F occurrence s) =
        ∫ s : ℝ,
          ∑' occurrence :
            NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
            F occurrence s :=
    integral_tsum_of_summable_integral_norm hFint hFnorm
  calc
    (∑' occurrence :
        NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      zetaGaussianZeroSummand
        analyticZetaZeroMultiplicity ε t occurrence) =
        ∑' occurrence :
          NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
          (heatNormalization a (heatParameter a ε) : ℂ) *
            ∫ s : ℝ, F occurrence s := by
      apply tsum_congr
      intro occurrence
      unfold F zetaGaussianZeroSummand
      exact complexTranslatedGaussian_heat_convolution
        hε hεa t (zetaSpectralCoordinate occurrence.1.1)
    _ = (heatNormalization a (heatParameter a ε) : ℂ) *
        (∑' occurrence :
          NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
          ∫ s : ℝ, F occurrence s) := tsum_mul_left
    _ = (heatNormalization a (heatParameter a ε) : ℂ) *
        ∫ s : ℝ,
          ∑' occurrence :
            NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
            F occurrence s := by rw [hinterchange]
    _ = (heatNormalization a (heatParameter a ε) : ℂ) *
        ∫ s : ℝ,
          (Real.exp (-heatParameter a ε * (t - s) ^ 2) : ℂ) *
            (∑' occurrence :
              NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
              zetaGaussianZeroSummand
                analyticZetaZeroMultiplicity a s occurrence) := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        unfold F
        exact tsum_mul_left

/-- The canonical real translated zero sum obeys exact positive heat
propagation in its center variable. -/
theorem canonicalZetaGaussianZeroSum_heat_convolution
    (hOrdinate : ZetaZeroGaussianOrdinateSummable)
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) :
    canonicalZetaGaussianZeroSum ε t =
      heatConvolution a (heatParameter a ε)
        (canonicalZetaGaussianZeroSum a) t := by
  let F := fun occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
    fun s : ℝ =>
      (Real.exp (-heatParameter a ε * (t - s) ^ 2) : ℂ) *
        zetaGaussianZeroSummand
          analyticZetaZeroMultiplicity a s occurrence
  let R := fun occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
    fun s : ℝ => (F occurrence s).re
  have ha : 0 < a := hε.trans hεa
  have hb : 0 < heatParameter a ε := heatParameter_pos hε hεa
  have hFint : ∀ occurrence, Integrable (F occurrence) := by
    intro occurrence
    exact integrable_heatKernel_mul_complexTranslatedGaussian ha hb t
      (zetaSpectralCoordinate occurrence.1.1)
  have hRint : ∀ occurrence, Integrable (R occurrence) := by
    intro occurrence
    exact (hFint occurrence).re
  have hFnorm : Summable (fun occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
        ∫ s : ℝ, ‖F occurrence s‖) := by
    simpa only [F] using
      summable_integral_norm_zetaGaussian_heat hOrdinate hε hεa t
  have hRnorm : Summable (fun occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
        ∫ s : ℝ, ‖R occurrence s‖) := by
    apply hFnorm.of_nonneg_of_le
    · intro occurrence
      exact integral_nonneg fun _ => norm_nonneg _
    · intro occurrence
      apply integral_mono (hRint occurrence).norm (hFint occurrence).norm
      intro s
      dsimp only [R]
      simpa only [Real.norm_eq_abs] using
        Complex.abs_re_le_norm (F occurrence s)
  have hinterchange :
      (∑' occurrence :
          NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        ∫ s : ℝ, R occurrence s) =
        ∫ s : ℝ,
          ∑' occurrence :
            NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
            R occurrence s :=
    integral_tsum_of_summable_integral_norm hRint hRnorm
  have hterm (occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity) :
      (zetaGaussianZeroSummand
        analyticZetaZeroMultiplicity ε t occurrence).re =
        heatNormalization a (heatParameter a ε) *
          ∫ s : ℝ, R occurrence s := by
    have hcomplex := congrArg Complex.re
      (complexTranslatedGaussian_heat_convolution hε hεa t
        (zetaSpectralCoordinate occurrence.1.1))
    have hreIntegral := integral_re (hFint occurrence)
    rw [RCLike.re_eq_complex_re] at hreIntegral
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hcomplex
    change
      (zetaGaussianZeroSummand
        analyticZetaZeroMultiplicity ε t occurrence).re =
        heatNormalization a (heatParameter a ε) *
          (∫ s : ℝ, F occurrence s).re at hcomplex
    calc
      (zetaGaussianZeroSummand
          analyticZetaZeroMultiplicity ε t occurrence).re =
          heatNormalization a (heatParameter a ε) *
            (∫ s : ℝ, F occurrence s).re := hcomplex
      _ = heatNormalization a (heatParameter a ε) *
          ∫ s : ℝ, R occurrence s := by
        rw [← hreIntegral]
  have hsumε := summable_zetaGaussianZeroSummand_of_ordinateSummable
    hOrdinate ε t hε
  have hreε :
      (∑' occurrence :
          NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        (zetaGaussianZeroSummand
          analyticZetaZeroMultiplicity ε t occurrence).re) =
        (∑' occurrence :
          NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
          zetaGaussianZeroSummand
            analyticZetaZeroMultiplicity ε t occurrence).re :=
    (Complex.hasSum_re hsumε.hasSum).tsum_eq
  have hpoint (s : ℝ) :
      (∑' occurrence :
          NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        R occurrence s) =
        Real.exp (-heatParameter a ε * (t - s) ^ 2) *
          canonicalZetaGaussianZeroSum a s := by
    have hsuma := summable_zetaGaussianZeroSummand_of_ordinateSummable
      hOrdinate a s ha
    have hrea :
        (∑' occurrence :
            NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
          (zetaGaussianZeroSummand
            analyticZetaZeroMultiplicity a s occurrence).re) =
          (∑' occurrence :
            NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
            zetaGaussianZeroSummand
              analyticZetaZeroMultiplicity a s occurrence).re :=
      (Complex.hasSum_re hsuma.hasSum).tsum_eq
    calc
      (∑' occurrence :
          NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        R occurrence s) =
          ∑' occurrence :
            NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
            Real.exp (-heatParameter a ε * (t - s) ^ 2) *
              (zetaGaussianZeroSummand
                analyticZetaZeroMultiplicity a s occurrence).re := by
        apply tsum_congr
        intro occurrence
        simp only [R, F, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero]
      _ = Real.exp (-heatParameter a ε * (t - s) ^ 2) *
          (∑' occurrence :
            NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
            (zetaGaussianZeroSummand
              analyticZetaZeroMultiplicity a s occurrence).re) :=
        tsum_mul_left
      _ = Real.exp (-heatParameter a ε * (t - s) ^ 2) *
          canonicalZetaGaussianZeroSum a s := by
        rw [hrea]
        rfl
  unfold canonicalZetaGaussianZeroSum heatConvolution
  calc
    (∑' occurrence :
        NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      zetaGaussianZeroSummand
        analyticZetaZeroMultiplicity ε t occurrence).re =
        ∑' occurrence :
          NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
          (zetaGaussianZeroSummand
            analyticZetaZeroMultiplicity ε t occurrence).re := hreε.symm
    _ = ∑' occurrence :
        NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        heatNormalization a (heatParameter a ε) *
          ∫ s : ℝ, R occurrence s := by
      apply tsum_congr
      exact hterm
    _ = heatNormalization a (heatParameter a ε) *
        (∑' occurrence :
          NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
          ∫ s : ℝ, R occurrence s) := tsum_mul_left
    _ = heatNormalization a (heatParameter a ε) *
        ∫ s : ℝ,
          ∑' occurrence :
            NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
            R occurrence s := by rw [hinterchange]
    _ = heatNormalization a (heatParameter a ε) *
        ∫ s : ℝ,
          Real.exp (-heatParameter a ε * (t - s) ^ 2) *
            (∑' occurrence :
              NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
              zetaGaussianZeroSummand
                analyticZetaZeroMultiplicity a s occurrence).re := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint

/-- The certificate's symmetric normalization inherits the same exact heat
propagation. -/
theorem canonicalZetaSymmetricGaussianZeroSum_heat_convolution
    (hOrdinate : ZetaZeroGaussianOrdinateSummable)
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) :
    canonicalZetaSymmetricGaussianZeroSum ε t =
      heatConvolution a (heatParameter a ε)
        (canonicalZetaSymmetricGaussianZeroSum a) t := by
  rw [canonicalZetaSymmetricGaussianZeroSum,
    canonicalZetaGaussianZeroSum_heat_convolution hOrdinate hε hεa]
  unfold heatConvolution canonicalZetaSymmetricGaussianZeroSum
  rw [show
    (fun s : ℝ =>
      Real.exp (-heatParameter a ε * (t - s) ^ 2) *
        (2 * canonicalZetaGaussianZeroSum a s)) =
      fun s : ℝ => 2 *
        (Real.exp (-heatParameter a ε * (t - s) ^ 2) *
          canonicalZetaGaussianZeroSum a s) by
    funext s
    ring]
  rw [integral_const_mul]
  ring

/-- The canonical translated zero sum satisfies heat propagation without any
extra convergence hypothesis: Gaussian ordinate summability was established
from the unconditional quadratic growth bound for `riemannXi`. -/
theorem canonicalZetaGaussianZeroSum_heat_convolution_unconditional
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) :
    canonicalZetaGaussianZeroSum ε t =
      heatConvolution a (heatParameter a ε)
        (canonicalZetaGaussianZeroSum a) t :=
  canonicalZetaGaussianZeroSum_heat_convolution
    zetaZeroGaussianOrdinateSummable hε hεa t

/-- The canonical symmetric zero sum satisfies the same unconditional heat
propagation identity. -/
theorem canonicalZetaSymmetricGaussianZeroSum_heat_convolution_unconditional
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a) (t : ℝ) :
    canonicalZetaSymmetricGaussianZeroSum ε t =
      heatConvolution a (heatParameter a ε)
        (canonicalZetaSymmetricGaussianZeroSum a) t :=
  canonicalZetaSymmetricGaussianZeroSum_heat_convolution
    zetaZeroGaussianOrdinateSummable hε hεa t

/-- Nonnegativity of the canonical symmetric zero sum at one Gaussian width
propagates to every smaller positive width. -/
theorem canonicalZetaSymmetricGaussianZeroSum_nonnegative_of_larger_width
    {a ε : ℝ} (hε : 0 < ε) (hεa : ε < a)
    (ha : ∀ s : ℝ, 0 ≤ canonicalZetaSymmetricGaussianZeroSum a s)
    (t : ℝ) :
    0 ≤ canonicalZetaSymmetricGaussianZeroSum ε t := by
  rw [canonicalZetaSymmetricGaussianZeroSum_heat_convolution_unconditional
    hε hεa]
  unfold heatConvolution
  exact mul_nonneg
    (heatNormalization_pos (heatParameter_add_pos hε hεa)).le
    (integral_nonneg fun s =>
      mul_nonneg (Real.exp_nonneg _) (ha s))

end

end RiemannGaussian
