import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaComplementaryTiltRigidity

/-!
# The arithmetic gap transform forced by an off-critical zero

The positive horizontal-defect certificate cannot be excluded by positivity
alone: positive measures may have Fourier zeros.  This module isolates the
arithmetic part of the problem.  It decomposes the positive logarithmic
half-line into the paired-eta support and its omitted gaps.

On the full positive half-line, the horizontal-defect Fourier kernel has the
elementary transform

`2 a^2 / (((1/2+a)+I*y) * ((1/2-a)+I*y))`,

which is nonzero whenever `a != 0` and `|a| < 1/2`.  At an off-critical zeta
zero, the transform over the eta support vanishes by the complementary-tilt
certificate.  Lean therefore proves that the transform over the arithmetic
gaps is exactly this explicit nonzero rational value.

This support-gap identity is unconditional.  It does not yet bound the gap
transform, but it identifies the exact arithmetic equality that a rigidity
estimate must contradict.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The omitted logarithmic gaps inside the positive half-line. -/
def pairedEtaLogGapSupport : Set ℝ :=
  Ioi 0 \ pairedEtaLogSupport

/-- Lebesgue measure restricted to the omitted logarithmic gaps. -/
def pairedEtaLogGapMeasure : Measure ℝ :=
  volume.restrict pairedEtaLogGapSupport

/-- The logarithmic gap support is measurable. -/
theorem measurableSet_pairedEtaLogGapSupport :
    MeasurableSet pairedEtaLogGapSupport := by
  exact measurableSet_Ioi.diff measurableSet_pairedEtaLogSupport

/-- The eta support and its logarithmic gaps are disjoint. -/
theorem disjoint_pairedEtaLogSupport_pairedEtaLogGapSupport :
    Disjoint pairedEtaLogSupport pairedEtaLogGapSupport := by
  apply Set.disjoint_left.mpr
  intro t htSupport htGap
  exact htGap.2 htSupport

/-- The eta support together with its gaps is the entire positive half-line. -/
theorem pairedEtaLogSupport_union_pairedEtaLogGapSupport :
    pairedEtaLogSupport ∪ pairedEtaLogGapSupport = Ioi 0 := by
  apply Set.ext
  intro t
  constructor
  · intro ht
    rcases ht with ht | ht
    · exact pairedEtaLogSupport_subset_Ioi_zero ht
    · exact ht.1
  · intro ht
    by_cases hs : t ∈ pairedEtaLogSupport
    · exact Or.inl hs
    · exact Or.inr ⟨ht, hs⟩

/-- Lebesgue measure on the positive half-line splits exactly into the eta
support measure and its gap measure. -/
theorem volume_restrict_Ioi_zero_eq_pairedEtaLogMeasure_add_gapMeasure :
    volume.restrict (Ioi 0) =
      pairedEtaLogMeasure + pairedEtaLogGapMeasure := by
  calc
    volume.restrict (Ioi 0) = volume.restrict
        (pairedEtaLogSupport ∪ pairedEtaLogGapSupport) := by
      rw [pairedEtaLogSupport_union_pairedEtaLogGapSupport]
    _ = volume.restrict pairedEtaLogSupport +
        volume.restrict pairedEtaLogGapSupport :=
      Measure.restrict_union
        disjoint_pairedEtaLogSupport_pairedEtaLogGapSupport
        measurableSet_pairedEtaLogGapSupport
    _ = pairedEtaLogMeasure + pairedEtaLogGapMeasure := rfl

/-- The complex Fourier kernel of the positive horizontal defect, written as
the difference of its two complementary Laplace kernels. -/
def pairedEtaPositiveHorizontalDefectFourierKernel
    (a y t : ℝ) : ℂ :=
  -(a : ℂ) *
    (Complex.exp (-(((1 / 2 + a : ℝ) : ℂ) +
        (y : ℂ) * Complex.I) * t) -
      Complex.exp (-(((1 / 2 - a : ℝ) : ℂ) +
        (y : ℂ) * Complex.I) * t))

/-- The complex kernel is exactly the positive horizontal-defect density
times the negative-frequency Fourier phase. -/
theorem pairedEtaPositiveHorizontalDefectFourierKernel_eq
    (a y t : ℝ) :
    pairedEtaPositiveHorizontalDefectFourierKernel a y t =
      (pairedEtaPositiveHorizontalDefectDensity a t : ℂ) *
        Complex.exp (-((y * t : ℝ) : ℂ) * Complex.I) := by
  unfold pairedEtaPositiveHorizontalDefectFourierKernel
    pairedEtaPositiveHorizontalDefectDensity pairedEtaHorizontalDefectWeight
  rw [show -(((1 / 2 + a : ℝ) : ℂ) +
        (y : ℂ) * Complex.I) * t =
      ((-(1 / 2 + a) * t : ℝ) : ℂ) +
        -((y * t : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
    show -(((1 / 2 - a : ℝ) : ℂ) +
        (y : ℂ) * Complex.I) * t =
      ((-(1 / 2 - a) * t : ℝ) : ℂ) +
        -((y * t : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
    Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp,
    ← Complex.ofReal_exp]
  push_cast
  ring

/-- A positive-real-part complex exponential is integrable on the positive
half-line. -/
theorem integrableOn_cexp_neg_sigma_add_I_mul_Ioi_zero
    {sigma : ℝ} (hsigma : 0 < sigma) (y : ℝ) :
    IntegrableOn (fun t : ℝ =>
      Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t))
      (Ioi 0) := by
  have hraw := integrableOn_exp_mul_complex_Ioi
    (a := -((sigma : ℂ) + (y : ℂ) * Complex.I)) (by
      norm_num
      linarith) 0
  simpa using hraw

/-- The elementary positive-half-line complex Laplace integral. -/
theorem integral_cexp_neg_sigma_add_I_mul_Ioi_zero
    {sigma : ℝ} (hsigma : 0 < sigma) (y : ℝ) :
    (∫ t : ℝ in Ioi 0,
      Complex.exp (-((sigma : ℂ) + (y : ℂ) * Complex.I) * t)) =
      (((sigma : ℂ) + (y : ℂ) * Complex.I))⁻¹ := by
  have hraw := integral_exp_mul_complex_Ioi
    (a := -((sigma : ℂ) + (y : ℂ) * Complex.I)) (by
      norm_num
      linarith) 0
  simpa only [ofReal_zero, mul_zero, exp_zero, neg_div, inv_neg, neg_neg,
    one_div] using hraw

/-- The positive horizontal-defect Fourier kernel is integrable on the full
positive half-line whenever both complementary tilts are positive. -/
theorem integrableOn_pairedEtaPositiveHorizontalDefectFourierKernel
    {a : ℝ} (ha : |a| < 1 / 2) (y : ℝ) :
    IntegrableOn (pairedEtaPositiveHorizontalDefectFourierKernel a y)
      (Ioi 0) := by
  have habs := abs_lt.mp ha
  have hplus : 0 < 1 / 2 + a := by linarith
  have hminus : 0 < 1 / 2 - a := by linarith
  have hint :=
    (((integrableOn_cexp_neg_sigma_add_I_mul_Ioi_zero hplus y).sub
      (integrableOn_cexp_neg_sigma_add_I_mul_Ioi_zero hminus y)).const_mul
        (-(a : ℂ)))
  apply hint.congr
  filter_upwards with t
  unfold pairedEtaPositiveHorizontalDefectFourierKernel
  rfl

/-- Full positive-half-line transform of the horizontal-defect kernel. -/
def pairedEtaPositiveHorizontalDefectFullTransform (a y : ℝ) : ℂ :=
  ∫ t : ℝ, pairedEtaPositiveHorizontalDefectFourierKernel a y t
    ∂volume.restrict (Ioi 0)

/-- Transform of the horizontal-defect kernel on the paired-eta support. -/
def pairedEtaPositiveHorizontalDefectSupportTransform (a y : ℝ) : ℂ :=
  ∫ t : ℝ, pairedEtaPositiveHorizontalDefectFourierKernel a y t
    ∂pairedEtaLogMeasure

/-- Transform of the horizontal-defect kernel on the omitted eta gaps. -/
def pairedEtaPositiveHorizontalDefectGapTransform (a y : ℝ) : ℂ :=
  ∫ t : ℝ, pairedEtaPositiveHorizontalDefectFourierKernel a y t
    ∂pairedEtaLogGapMeasure

/-- On the eta support, the horizontal-defect transform is the
sign-normalized difference of the two complementary Laplace transforms. -/
theorem pairedEtaPositiveHorizontalDefectSupportTransform_eq_sub
    {a : ℝ} (ha : |a| < 1 / 2) (y : ℝ) :
    pairedEtaPositiveHorizontalDefectSupportTransform a y =
      -(a : ℂ) *
        ((∫ t : ℝ,
          Complex.exp (-(((1 / 2 + a : ℝ) : ℂ) +
            (y : ℂ) * Complex.I) * t) ∂pairedEtaLogMeasure) -
        ∫ t : ℝ,
          Complex.exp (-(((1 / 2 - a : ℝ) : ℂ) +
            (y : ℂ) * Complex.I) * t) ∂pairedEtaLogMeasure) := by
  have habs := abs_lt.mp ha
  have hplus : 0 < 1 / 2 + a := by linarith
  have hminus : 0 < 1 / 2 - a := by linarith
  have hp := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (((1 / 2 + a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) (by
      norm_num
      exact hplus)
  have hm := integrable_exp_neg_mul_pairedEtaLogMeasure
    (s := (((1 / 2 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) (by
      norm_num
      linarith)
  unfold pairedEtaPositiveHorizontalDefectSupportTransform
    pairedEtaPositiveHorizontalDefectFourierKernel
  rw [integral_const_mul, integral_sub hp hm]

/-- The full transform is exactly the elementary rational function. -/
theorem pairedEtaPositiveHorizontalDefectFullTransform_eq
    {a : ℝ} (ha : |a| < 1 / 2) (y : ℝ) :
    pairedEtaPositiveHorizontalDefectFullTransform a y =
      2 * (a : ℂ) ^ 2 /
        ((((1 / 2 + a : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
          (((1 / 2 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := by
  have habs := abs_lt.mp ha
  have hplus : 0 < 1 / 2 + a := by linarith
  have hminus : 0 < 1 / 2 - a := by linarith
  let qplus : ℂ := ((1 / 2 + a : ℝ) : ℂ) + (y : ℂ) * Complex.I
  let qminus : ℂ := ((1 / 2 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I
  have hqplus : qplus ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    dsimp [qplus] at hre
    norm_num at hre
    linarith
  have hqminus : qminus ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    dsimp [qminus] at hre
    norm_num at hre
    linarith
  unfold pairedEtaPositiveHorizontalDefectFullTransform
    pairedEtaPositiveHorizontalDefectFourierKernel
  rw [integral_const_mul]
  rw [integral_sub
    (integrableOn_cexp_neg_sigma_add_I_mul_Ioi_zero hplus y)
    (integrableOn_cexp_neg_sigma_add_I_mul_Ioi_zero hminus y)]
  rw [integral_cexp_neg_sigma_add_I_mul_Ioi_zero hplus,
    integral_cexp_neg_sigma_add_I_mul_Ioi_zero hminus]
  change -(a : ℂ) * (qplus⁻¹ - qminus⁻¹) =
    2 * (a : ℂ) ^ 2 / (qplus * qminus)
  field_simp [hqplus, hqminus]
  dsimp [qplus, qminus]
  push_cast
  ring

/-- The elementary full transform is nonzero away from the critical line. -/
theorem pairedEtaPositiveHorizontalDefectFullTransform_ne_zero
    {a : ℝ} (ha : |a| < 1 / 2) (ha0 : a ≠ 0) (y : ℝ) :
    pairedEtaPositiveHorizontalDefectFullTransform a y ≠ 0 := by
  rw [pairedEtaPositiveHorizontalDefectFullTransform_eq ha]
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ofReal_ne_zero.mpr ha0))
  · apply mul_ne_zero
    · intro hzero
      have hre := congrArg Complex.re hzero
      norm_num at hre
      have habs := abs_lt.mp ha
      linarith
    · intro hzero
      have hre := congrArg Complex.re hzero
      norm_num at hre
      have habs := abs_lt.mp ha
      linarith

/-- The full transform decomposes exactly into its eta-support and arithmetic
gap transforms. -/
theorem pairedEtaPositiveHorizontalDefectFullTransform_eq_support_add_gap
    {a : ℝ} (ha : |a| < 1 / 2) (y : ℝ) :
    pairedEtaPositiveHorizontalDefectFullTransform a y =
      pairedEtaPositiveHorizontalDefectSupportTransform a y +
        pairedEtaPositiveHorizontalDefectGapTransform a y := by
  have hfull :=
    integrableOn_pairedEtaPositiveHorizontalDefectFourierKernel ha y
  have hsupport : Integrable
      (pairedEtaPositiveHorizontalDefectFourierKernel a y)
      pairedEtaLogMeasure :=
    Integrable.mono_measure
      (μ := pairedEtaLogMeasure) (ν := volume.restrict (Ioi 0))
      hfull pairedEtaLogMeasure_le_volume_restrict_Ioi_zero
  have hgapMeasure : pairedEtaLogGapMeasure <=
      volume.restrict (Ioi 0) := by
    unfold pairedEtaLogGapMeasure pairedEtaLogGapSupport
    exact Measure.restrict_mono sdiff_subset le_rfl
  have hgap : Integrable
      (pairedEtaPositiveHorizontalDefectFourierKernel a y)
      pairedEtaLogGapMeasure :=
    Integrable.mono_measure
      (μ := pairedEtaLogGapMeasure) (ν := volume.restrict (Ioi 0))
      hfull hgapMeasure
  unfold pairedEtaPositiveHorizontalDefectFullTransform
    pairedEtaPositiveHorizontalDefectSupportTransform
    pairedEtaPositiveHorizontalDefectGapTransform
  rw [volume_restrict_Ioi_zero_eq_pairedEtaLogMeasure_add_gapMeasure,
    integral_add_measure hsupport hgap]

/-- At every zeta zero, the positive horizontal-defect transform vanishes on
the eta support. -/
theorem pairedEtaPositiveHorizontalDefectSupportTransform_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaPositiveHorizontalDefectSupportTransform
      (rho.1.re - 1 / 2) rho.1.im = 0 := by
  have hrePos := NontrivialZetaZero.zero_lt_re rho
  have hreLt := NontrivialZetaZero.re_lt_one rho
  let a : ℝ := rho.1.re - 1 / 2
  have ha : |a| < 1 / 2 := by
    dsimp [a]
    rw [abs_lt]
    constructor <;> linarith
  let qplus : ℂ := (((1 / 2 + a : ℝ) : ℂ) +
    (rho.1.im : ℂ) * Complex.I)
  let qminus : ℂ := (((1 / 2 - a : ℝ) : ℂ) +
    (rho.1.im : ℂ) * Complex.I)
  have hqplus : qplus = rho.1 := by
    apply Complex.ext <;> simp [qplus, a]
  have hqminus : qminus =
      (NontrivialZetaZero.conjugatePartner rho).1 := by
    apply Complex.ext
    · simp [qminus, a, NontrivialZetaZero.conjugatePartner_coe]
      ring
    · simp [qminus, a, NontrivialZetaZero.conjugatePartner_coe]
  rw [show rho.1.re - 1 / 2 = a by rfl,
    pairedEtaPositiveHorizontalDefectSupportTransform_eq_sub ha]
  change -(a : ℂ) *
    ((∫ t : ℝ, Complex.exp (-qplus * t) ∂pairedEtaLogMeasure) -
      ∫ t : ℝ, Complex.exp (-qminus * t) ∂pairedEtaLogMeasure) = 0
  rw [hqplus, hqminus,
    integral_exp_neg_mul_pairedEtaLogMeasure_eq_zero_of_nontrivialZetaZero,
    integral_exp_neg_mul_pairedEtaLogMeasure_eq_zero_of_nontrivialZetaZero]
  ring

/-- Every zeta zero forces the arithmetic gaps to reproduce the exact full
horizontal-defect transform; away from the critical line this value is
nonzero. -/
theorem nontrivialZetaZero_etaHorizontalDefectGapTransform_eq
    (rho : NontrivialZetaZero) :
    pairedEtaPositiveHorizontalDefectGapTransform
        (rho.1.re - 1 / 2) rho.1.im =
      2 * ((rho.1.re - 1 / 2 : ℝ) : ℂ) ^ 2 /
        ((((rho.1.re : ℝ) : ℂ) + (rho.1.im : ℂ) * Complex.I) *
          (((1 - rho.1.re : ℝ) : ℂ) +
            (rho.1.im : ℂ) * Complex.I)) := by
  have hrePos := NontrivialZetaZero.zero_lt_re rho
  have hreLt := NontrivialZetaZero.re_lt_one rho
  have ha : |rho.1.re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  have hsplit :=
    pairedEtaPositiveHorizontalDefectFullTransform_eq_support_add_gap
      ha rho.1.im
  rw [pairedEtaPositiveHorizontalDefectSupportTransform_eq_zero_of_nontrivialZetaZero,
    zero_add] at hsplit
  rw [← hsplit, pairedEtaPositiveHorizontalDefectFullTransform_eq ha]
  congr 1
  push_cast
  ring

/-- In particular, the forced arithmetic gap transform is nonzero. -/
theorem nontrivialZetaZero_offCritical_etaHorizontalDefectGapTransform_ne_zero
    (rho : NontrivialZetaZero) (hoff : rho.1.re ≠ 1 / 2) :
    pairedEtaPositiveHorizontalDefectGapTransform
      (rho.1.re - 1 / 2) rho.1.im ≠ 0 := by
  have hrePos := NontrivialZetaZero.zero_lt_re rho
  have hreLt := NontrivialZetaZero.re_lt_one rho
  have ha : |rho.1.re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  have hfull := pairedEtaPositiveHorizontalDefectFullTransform_ne_zero
    ha (sub_ne_zero.mpr hoff) rho.1.im
  have hsplit :=
    pairedEtaPositiveHorizontalDefectFullTransform_eq_support_add_gap
      ha rho.1.im
  rw [pairedEtaPositiveHorizontalDefectSupportTransform_eq_zero_of_nontrivialZetaZero,
    zero_add] at hsplit
  exact fun hgap => hfull (hsplit.trans hgap)

/-- The exact arithmetic-gap identity and its nonvanishing, packaged as the
conditional certificate forced by every off-critical zeta zero. -/
theorem nontrivialZetaZero_offCritical_etaHorizontalDefectGap_certificate
    (rho : NontrivialZetaZero) (hoff : rho.1.re ≠ 1 / 2) :
    (pairedEtaPositiveHorizontalDefectGapTransform
        (rho.1.re - 1 / 2) rho.1.im =
      2 * ((rho.1.re - 1 / 2 : ℝ) : ℂ) ^ 2 /
        ((((rho.1.re : ℝ) : ℂ) + (rho.1.im : ℂ) * Complex.I) *
          (((1 - rho.1.re : ℝ) : ℂ) +
            (rho.1.im : ℂ) * Complex.I))) ∧
      pairedEtaPositiveHorizontalDefectGapTransform
        (rho.1.re - 1 / 2) rho.1.im ≠ 0 := by
  exact ⟨nontrivialZetaZero_etaHorizontalDefectGapTransform_eq rho,
    nontrivialZetaZero_offCritical_etaHorizontalDefectGapTransform_ne_zero
      rho hoff⟩

end

end RiemannGaussian
