import RiemannGaussian.GaussianScrewBridge
import RiemannGaussian.GaussianArchimedeanContour
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gauss's digamma difference and the Gaussian--Suzuki transform

This file reduces `GaussianDigammaScrewTransform` to one pointwise special
case of Gauss's integral representation.  The statement isolated here,
`QuarterLineDigammaGaussDifferenceFormula`, says that the real part of
`digamma (1/4 + I*r/2)` relative to its value at zero is the positive
quarter-line integral with density

`exp (-u/2) / (1 - exp (-2u))`.

Everything after that statement is proved here.  In particular:

* the apparent pole at `u = 0` is cancelled by `1 - cos (r*u)` and the
  resulting density is integrable;
* the translated-Gaussian cosine transform is evaluated exactly;
* the nonnegative two-variable kernel is proved integrable, so Fubini applies;
* the pointwise Gauss formula implies the exact Gaussian digamma energy;
* splitting the density into the reflected exponential and Suzuki's missing
  curvature proves `GaussianDigammaScrewTransform`.

At this dependency layer the pointwise formula is an explicit proposition,
not an axiom.  The later module `GaussianDigammaGauss` proves it from
Mathlib's Gamma integral and Euler approximation and thereby closes the seam.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory Topology Set
open scoped BigOperators Topology

/-- Gauss's positive quarter-line density tested against one cosine
oscillation. -/
def gaussianSuzukiDigammaOscillationIntegrand (r u : ℝ) : ℝ :=
  gaussianSuzukiDigammaDensity u * (1 - Real.cos (r * u))

theorem continuousOn_gaussianSuzukiDigammaOscillationIntegrand (r : ℝ) :
    ContinuousOn (gaussianSuzukiDigammaOscillationIntegrand r) (Set.Ioi 0) := by
  intro u hu
  have hden : 1 - Real.exp (-2 * u) ≠ 0 :=
    (one_sub_exp_neg_two_mul_pos hu).ne'
  unfold gaussianSuzukiDigammaOscillationIntegrand gaussianSuzukiDigammaDensity
  fun_prop

lemma norm_gaussianSuzukiDigammaOscillationIntegrand_le_near_zero
    (r : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    ‖gaussianSuzukiDigammaOscillationIntegrand r u‖ ≤ (3 / 2 : ℝ) * |r| := by
  have hdenpos := one_sub_exp_neg_two_mul_pos hu
  have hden := two_thirds_mul_le_one_sub_exp_neg_two_mul hu hu1
  have hnumerator : Real.exp (-u / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hoscNonneg : 0 ≤ 1 - Real.cos (r * u) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hosc : 1 - Real.cos (r * u) ≤ |r| * u := by
    calc
      1 - Real.cos (r * u) = |1 - Real.cos (r * u)| :=
        (abs_of_nonneg hoscNonneg).symm
      _ = |Real.cos (r * u) - Real.cos 0| := by
        rw [Real.cos_zero, abs_sub_comm]
      _ ≤ |r * u - 0| := Real.abs_cos_sub_cos_le _ _
      _ = |r| * u := by rw [sub_zero, abs_mul, abs_of_pos hu]
  unfold gaussianSuzukiDigammaOscillationIntegrand gaussianSuzukiDigammaDensity
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (div_nonneg (Real.exp_pos _).le hdenpos.le) hoscNonneg)]
  calc
    Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) *
        (1 - Real.cos (r * u)) ≤
      (1 / ((2 / 3 : ℝ) * u)) * (|r| * u) := by
        gcongr
    _ = (3 / 2 : ℝ) * |r| := by
      field_simp [hu.ne']

theorem integrableOn_gaussianSuzukiDigammaOscillationIntegrand_Ioc (r : ℝ) :
    IntegrableOn (gaussianSuzukiDigammaOscillationIntegrand r)
      (Set.Ioc (0 : ℝ) 1) := by
  apply IntegrableOn.of_bound measure_Ioc_lt_top
  · exact ((continuousOn_gaussianSuzukiDigammaOscillationIntegrand r).mono
      Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact norm_gaussianSuzukiDigammaOscillationIntegrand_le_near_zero r hu.1 hu.2

lemma norm_gaussianSuzukiDigammaOscillationIntegrand_le_tail
    (r : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    ‖gaussianSuzukiDigammaOscillationIntegrand r u‖ ≤
      (2 / (1 - Real.exp (-2))) * Real.exp (-(1 / 2 : ℝ) * u) := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hdenpos := one_sub_exp_neg_two_mul_pos hu0
  have hfixedDen : 0 < 1 - Real.exp (-2) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hden : 1 - Real.exp (-2) ≤ 1 - Real.exp (-2 * u) := by
    apply sub_le_sub_left
    apply Real.exp_le_exp.mpr
    nlinarith
  have hoscNonneg : 0 ≤ 1 - Real.cos (r * u) :=
    sub_nonneg.mpr (Real.cos_le_one _)
  have hosc : 1 - Real.cos (r * u) ≤ 2 := by
    linarith [Real.neg_one_le_cos (r * u)]
  unfold gaussianSuzukiDigammaOscillationIntegrand gaussianSuzukiDigammaDensity
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (div_nonneg (Real.exp_pos _).le hdenpos.le) hoscNonneg)]
  calc
    Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) *
        (1 - Real.cos (r * u)) ≤
      (Real.exp (-u / 2) / (1 - Real.exp (-2))) * 2 := by
        gcongr
    _ = (2 / (1 - Real.exp (-2))) *
        Real.exp (-(1 / 2 : ℝ) * u) := by
      rw [show Real.exp (-u / 2) = Real.exp (-(1 / 2 : ℝ) * u) by
        congr 1
        ring]
      ring

theorem integrableOn_gaussianSuzukiDigammaOscillationIntegrand_Ioi_one (r : ℝ) :
    IntegrableOn (gaussianSuzukiDigammaOscillationIntegrand r)
      (Set.Ioi (1 : ℝ)) := by
  let C : ℝ := 2 / (1 - Real.exp (-2))
  have hmajor : IntegrableOn
      (fun u : ℝ => C * Real.exp (-(1 / 2 : ℝ) * u))
      (Set.Ioi (1 : ℝ)) := by
    exact (exp_neg_integrableOn_Ioi 1
      (by norm_num : (0 : ℝ) < 1 / 2)).const_mul C
  apply hmajor.mono'
  · exact ((continuousOn_gaussianSuzukiDigammaOscillationIntegrand r).mono (by
      intro u hu
      change 1 < u at hu
      exact zero_lt_one.trans hu)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change 1 < u at hu
    exact norm_gaussianSuzukiDigammaOscillationIntegrand_le_tail r hu.le

theorem integrableOn_gaussianSuzukiDigammaOscillationIntegrand (r : ℝ) :
    IntegrableOn (gaussianSuzukiDigammaOscillationIntegrand r) (Set.Ioi (0 : ℝ)) := by
  have h := (integrableOn_gaussianSuzukiDigammaOscillationIntegrand_Ioc r).union
    (integrableOn_gaussianSuzukiDigammaOscillationIntegrand_Ioi_one r)
  rw [show Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 by
    ext u
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hu | hu)
      · exact hu.1
      · linarith
    · intro hu
      by_cases hu1 : u ≤ 1
      · exact Or.inl ⟨hu, hu1⟩
      · exact Or.inr (lt_of_not_ge hu1)] at h
  exact h

/-- The pointwise identity isolated at this layer: the real quarter-line
digamma difference is Gauss's positive oscillatory integral.  Integrability
of the right side is proved above, so this proposition contains only the
equality.  `GaussianDigammaGauss` supplies its proof. -/
def QuarterLineDigammaGaussDifferenceFormula : Prop :=
  ∀ r : ℝ,
    riemannArchimedeanDensity r - riemannArchimedeanDensity 0 =
      2 * ∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiDigammaOscillationIntegrand r u

/-- Complex Gaussian oscillation used to evaluate the real cosine transform. -/
def complexTranslatedGaussianOscillation
    (ε t u r : ℝ) : ℂ :=
  Complex.exp (((-ε * (r - t) ^ 2 : ℝ) : ℂ) +
    Complex.I * (u * r))

theorem integrable_complexTranslatedGaussianOscillation
    {ε : ℝ} (hε : 0 < ε) (t u : ℝ) :
    Integrable (complexTranslatedGaussianOscillation ε t u) := by
  let b : ℂ := -(ε : ℂ)
  let c : ℂ := ((2 * ε * t : ℝ) : ℂ) + Complex.I * u
  let d : ℂ := ((-ε * t ^ 2 : ℝ) : ℂ)
  have hb : b.re < 0 := by
    dsimp only [b]
    simpa using neg_lt_zero.mpr hε
  have hfun : complexTranslatedGaussianOscillation ε t u =
      fun r : ℝ => Complex.exp (b * (r : ℂ) ^ 2 + c * r + d) := by
    funext r
    unfold complexTranslatedGaussianOscillation
    congr 1
    dsimp only [b, c, d]
    push_cast
    ring
  rw [hfun]
  exact integrable_cexp_quadratic' hb c d

theorem integral_complexTranslatedGaussianOscillation
    {ε : ℝ} (hε : 0 < ε) (t u : ℝ) :
    (∫ r : ℝ, complexTranslatedGaussianOscillation ε t u r) =
      (Real.sqrt (Real.pi / ε) : ℂ) *
        Complex.exp (((-u ^ 2 / (4 * ε) : ℝ) : ℂ) +
          Complex.I * (t * u)) := by
  let b : ℂ := -(ε : ℂ)
  let c : ℂ := ((2 * ε * t : ℝ) : ℂ) + Complex.I * u
  let d : ℂ := ((-ε * t ^ 2 : ℝ) : ℂ)
  have hb : b.re < 0 := by
    dsimp only [b]
    simpa using neg_lt_zero.mpr hε
  have hfun : complexTranslatedGaussianOscillation ε t u =
      fun r : ℝ => Complex.exp (b * (r : ℂ) ^ 2 + c * r + d) := by
    funext r
    unfold complexTranslatedGaussianOscillation
    congr 1
    dsimp only [b, c, d]
    push_cast
    ring
  rw [hfun, integral_cexp_quadratic hb c d]
  have hsqrt :
      (Real.sqrt (Real.pi / ε) : ℂ) =
        (((Real.pi / ε : ℝ) : ℂ) ^ (1 / 2 : ℂ)) := by
    rw [Real.sqrt_eq_rpow]
    simpa using Complex.ofReal_cpow
      (div_nonneg Real.pi_pos.le hε.le) (1 / 2 : ℝ)
  have hbase :
      (((Real.pi : ℂ) / -b) : ℂ) ^ (1 / 2 : ℂ) =
        (Real.sqrt (Real.pi / ε) : ℂ) := by
    rw [hsqrt]
    congr 2
    dsimp only [b]
    push_cast
    field_simp [hε.ne']
  have hexponent :
      d - c ^ 2 / (4 * b) =
        ((-u ^ 2 / (4 * ε) : ℝ) : ℂ) +
          Complex.I * (t * u) := by
    dsimp only [b, c, d]
    have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
    push_cast
    field_simp [hεc]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hbase, hexponent]

theorem complexTranslatedGaussianOscillation_re
    (ε t u r : ℝ) :
    (complexTranslatedGaussianOscillation ε t u r).re =
      translatedGaussian ε t r * Real.cos (u * r) := by
  unfold complexTranslatedGaussianOscillation translatedGaussian
  rw [Complex.exp_add, ← Complex.ofReal_exp]
  rw [mul_comm Complex.I]
  rw [← Complex.ofReal_mul]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    add_zero, sub_zero, mul_one]

theorem integrable_translatedGaussian_mul_cos
    {ε : ℝ} (hε : 0 < ε) (t u : ℝ) :
    Integrable (fun r : ℝ =>
      translatedGaussian ε t r * Real.cos (u * r)) := by
  have hre := (integrable_complexTranslatedGaussianOscillation hε t u).re
  apply hre.congr
  filter_upwards with r
  exact complexTranslatedGaussianOscillation_re ε t u r

theorem integral_translatedGaussian_mul_cos
    {ε : ℝ} (hε : 0 < ε) (t u : ℝ) :
    (∫ r : ℝ, translatedGaussian ε t r * Real.cos (u * r)) =
      Real.sqrt (Real.pi / ε) *
        Real.exp (-u ^ 2 / (4 * ε)) * Real.cos (t * u) := by
  have hre := integral_re
    (integrable_complexTranslatedGaussianOscillation hε t u)
  rw [integral_complexTranslatedGaussianOscillation hε t u] at hre
  change
    (∫ r : ℝ, (complexTranslatedGaussianOscillation ε t u r).re) =
      ((Real.sqrt (Real.pi / ε) : ℂ) *
        Complex.exp (((-u ^ 2 / (4 * ε) : ℝ) : ℂ) +
          Complex.I * (t * u))).re at hre
  rw [integral_congr_ae (Filter.Eventually.of_forall fun r =>
    complexTranslatedGaussianOscillation_re ε t u r)] at hre
  have hresult :
      ((Real.sqrt (Real.pi / ε) : ℂ) *
        Complex.exp (((-u ^ 2 / (4 * ε) : ℝ) : ℂ) +
          Complex.I * (t * u))).re =
        Real.sqrt (Real.pi / ε) *
          Real.exp (-u ^ 2 / (4 * ε)) * Real.cos (t * u) := by
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    rw [mul_comm Complex.I]
    rw [← Complex.ofReal_mul]
    rw [Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      add_zero, sub_zero, mul_one]
    ring
  rw [hresult] at hre
  exact hre

theorem integrable_translatedGaussianOscillation
    {ε : ℝ} (hε : 0 < ε) (t u : ℝ) :
    Integrable (fun r : ℝ =>
      translatedGaussian ε t r * (1 - Real.cos (u * r))) := by
  apply (integrable_translatedGaussian hε t).mul_bdd (c := 2)
  · fun_prop
  · filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _))]
    linarith [Real.neg_one_le_cos (u * r)]

theorem integral_translatedGaussianOscillation
    {ε : ℝ} (hε : 0 < ε) (t u : ℝ) :
    (∫ r : ℝ,
      translatedGaussian ε t r * (1 - Real.cos (u * r))) =
      Real.sqrt (Real.pi / ε) *
        (1 - Real.exp (-u ^ 2 / (4 * ε)) * Real.cos (t * u)) := by
  rw [show (fun r : ℝ =>
      translatedGaussian ε t r * (1 - Real.cos (u * r))) =
      fun r : ℝ => translatedGaussian ε t r -
        translatedGaussian ε t r * Real.cos (u * r) by
    funext r
    ring]
  rw [integral_sub (integrable_translatedGaussian hε t)
      (integrable_translatedGaussian_mul_cos hε t u),
    integral_translatedGaussian hε t,
    integral_translatedGaussian_mul_cos hε t u]
  ring

theorem integrable_symmetricGaussianOscillation
    {ε : ℝ} (hε : 0 < ε) (t u : ℝ) :
    Integrable (fun r : ℝ =>
      symmetricGaussian ε t r * (1 - Real.cos (u * r))) := by
  apply (integrable_symmetricGaussian hε t).mul_bdd (c := 2)
  · fun_prop
  · filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _))]
    linarith [Real.neg_one_le_cos (u * r)]

theorem integral_symmetricGaussianOscillation_Ioi_eq_translated
    {ε : ℝ} (hε : 0 < ε) (t u : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
      symmetricGaussian ε t r * (1 - Real.cos (u * r))) =
      ∫ r : ℝ,
        translatedGaussian ε t r * (1 - Real.cos (u * r)) := by
  let f : ℝ → ℝ := fun r =>
    symmetricGaussian ε t r * (1 - Real.cos (u * r))
  have hf : Integrable f :=
    integrable_symmetricGaussianOscillation hε t u
  have heven : ∀ r : ℝ, f (-r) = f r := by
    intro r
    dsimp only [f]
    rw [symmetricGaussian_even, mul_neg, Real.cos_neg]
  have hhalf := integral_even_eq_two_mul_integral_Ioi hf heven
  have hfull : (∫ r : ℝ, f r) =
      2 * ∫ r : ℝ,
        translatedGaussian ε t r * (1 - Real.cos (u * r)) := by
    let g : ℝ → ℝ := fun r =>
      translatedGaussian ε t r * (1 - Real.cos (u * r))
    have hg : Integrable g :=
      integrable_translatedGaussianOscillation hε t u
    have hdecomp : f = fun r : ℝ => g r + g (-r) := by
      funext r
      unfold f g symmetricGaussian
      rw [mul_neg, Real.cos_neg]
      ring
    have hreflect : (∫ r : ℝ, g (-r)) = ∫ r : ℝ, g r := by
      simpa only [Function.comp_apply] using integral_neg_eq_self g volume
    rw [hdecomp, integral_add hg hg.comp_neg, hreflect]
    ring
  rw [hfull] at hhalf
  linarith

theorem integral_symmetricGaussianOscillation_Ioi
    {ε : ℝ} (hε : 0 < ε) (t u : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
      symmetricGaussian ε t r * (1 - Real.cos (u * r))) =
      Real.sqrt (Real.pi / ε) *
        (1 - Real.exp (-u ^ 2 / (4 * ε)) * Real.cos (t * u)) := by
  rw [integral_symmetricGaussianOscillation_Ioi_eq_translated hε t u,
    integral_translatedGaussianOscillation hε t u]

/-- Nonnegative joint kernel for the Gaussian center and Gauss-density
variables. -/
def gaussianDigammaGaussJointIntegrand (ε t : ℝ) (z : ℝ × ℝ) : ℝ :=
  symmetricGaussian ε t z.1 *
    gaussianSuzukiDigammaOscillationIntegrand z.1 z.2

/-- The pointwise Gauss formula makes the norm integral of the joint kernel a
Gaussian-weighted digamma difference, hence finite. -/
theorem integrable_gaussianDigammaGaussJointIntegrand
    (hgauss : QuarterLineDigammaGaussDifferenceFormula)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (gaussianDigammaGaussJointIntegrand ε t)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.restrict (Set.Ioi (0 : ℝ)))) := by
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  have hmeas : AEStronglyMeasurable (gaussianDigammaGaussJointIntegrand ε t)
      (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    unfold gaussianDigammaGaussJointIntegrand gaussianSuzukiDigammaOscillationIntegrand
      gaussianSuzukiDigammaDensity symmetricGaussian translatedGaussian
    fun_prop
  rw [show volume.restrict (Set.Ioi (0 : ℝ)) = μ by rfl]
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards with r
    exact (integrableOn_gaussianSuzukiDigammaOscillationIntegrand r).const_mul
      (symmetricGaussian ε t r)
  · have houter : IntegrableOn
        (fun r : ℝ =>
          symmetricGaussian ε t r *
            (riemannArchimedeanDensity r -
              riemannArchimedeanDensity 0) / 2)
        (Set.Ioi (0 : ℝ)) := by
      have hdensity : Integrable
          (fun r : ℝ =>
            symmetricGaussian ε t r * riemannArchimedeanDensity r) :=
        by
          have hre :=
            (integrable_symmetricGaussian_mul_digamma_quarter hε t).re
          apply hre.congr
          filter_upwards with r
          unfold riemannArchimedeanDensity
          simp
      have hconstant : Integrable
          (fun r : ℝ =>
            symmetricGaussian ε t r * riemannArchimedeanDensity 0) :=
        (integrable_symmetricGaussian hε t).mul_const _
      have hsub := hdensity.sub hconstant
      have hdiv := hsub.div_const 2
      apply hdiv.integrableOn.congr_fun
      · intro r hr
        change
          (symmetricGaussian ε t r * riemannArchimedeanDensity r -
              symmetricGaussian ε t r * riemannArchimedeanDensity 0) / 2 =
            symmetricGaussian ε t r *
              (riemannArchimedeanDensity r -
                riemannArchimedeanDensity 0) / 2
        ring
      · exact measurableSet_Ioi
    apply houter.congr_fun
    · intro r hr
      symm
      dsimp only [μ, gaussianDigammaGaussJointIntegrand]
      change
        (∫ u in Set.Ioi (0 : ℝ),
          ‖symmetricGaussian ε t r *
            gaussianSuzukiDigammaOscillationIntegrand r u‖) =
          symmetricGaussian ε t r *
            (riemannArchimedeanDensity r -
              riemannArchimedeanDensity 0) / 2
      have hnonneg (u : ℝ) (hu : 0 < u) :
          0 ≤ gaussianSuzukiDigammaOscillationIntegrand r u := by
        unfold gaussianSuzukiDigammaOscillationIntegrand
        exact mul_nonneg
          (div_nonneg (Real.exp_pos _).le
            (one_sub_exp_neg_two_mul_pos hu).le)
          (sub_nonneg.mpr (Real.cos_le_one _))
      have hgaussianNonneg : 0 ≤ symmetricGaussian ε t r := by
        unfold symmetricGaussian translatedGaussian
        positivity
      calc
        (∫ u in Set.Ioi (0 : ℝ),
            ‖symmetricGaussian ε t r *
              gaussianSuzukiDigammaOscillationIntegrand r u‖) =
            ∫ u in Set.Ioi (0 : ℝ),
              symmetricGaussian ε t r *
                gaussianSuzukiDigammaOscillationIntegrand r u := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          rw [Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg hgaussianNonneg (hnonneg u hu))]
        _ = symmetricGaussian ε t r *
            ∫ u in Set.Ioi (0 : ℝ),
              gaussianSuzukiDigammaOscillationIntegrand r u := by
          rw [integral_const_mul]
        _ = symmetricGaussian ε t r *
            (riemannArchimedeanDensity r -
              riemannArchimedeanDensity 0) / 2 := by
          rw [hgauss r]
          ring
    · exact measurableSet_Ioi

/-- Fubini exchange for the Gaussian--Gauss joint kernel. -/
theorem integral_gaussianDigammaGauss_swap
    (hgauss : QuarterLineDigammaGaussDifferenceFormula)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
      symmetricGaussian ε t r *
        ∫ u in Set.Ioi (0 : ℝ),
          gaussianSuzukiDigammaOscillationIntegrand r u) =
      ∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiDigammaDensity u *
          ∫ r in Set.Ioi (0 : ℝ),
            symmetricGaussian ε t r *
              (1 - Real.cos (r * u)) := by
  have hswap := integral_integral_swap
    (f := fun r u => gaussianDigammaGaussJointIntegrand ε t (r, u))
    (integrable_gaussianDigammaGaussJointIntegrand hgauss hε t)
  calc
    _ = ∫ r in Set.Ioi (0 : ℝ),
        ∫ u in Set.Ioi (0 : ℝ),
          gaussianDigammaGaussJointIntegrand ε t (r, u) := by
      apply integral_congr_ae
      filter_upwards with r
      unfold gaussianDigammaGaussJointIntegrand
      change
        symmetricGaussian ε t r *
            (∫ u in Set.Ioi (0 : ℝ),
              gaussianSuzukiDigammaOscillationIntegrand r u) =
          ∫ u in Set.Ioi (0 : ℝ),
            symmetricGaussian ε t r *
              gaussianSuzukiDigammaOscillationIntegrand r u
      rw [integral_const_mul]
    _ = ∫ u in Set.Ioi (0 : ℝ),
        ∫ r in Set.Ioi (0 : ℝ),
          gaussianDigammaGaussJointIntegrand ε t (r, u) := hswap
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      unfold gaussianDigammaGaussJointIntegrand gaussianSuzukiDigammaOscillationIntegrand
      change
        (∫ r in Set.Ioi (0 : ℝ),
          symmetricGaussian ε t r *
            (gaussianSuzukiDigammaDensity u *
              (1 - Real.cos (r * u)))) =
          gaussianSuzukiDigammaDensity u *
            ∫ r in Set.Ioi (0 : ℝ),
              symmetricGaussian ε t r *
                (1 - Real.cos (r * u))
      rw [show (fun r : ℝ =>
          symmetricGaussian ε t r *
            (gaussianSuzukiDigammaDensity u *
              (1 - Real.cos (r * u)))) =
          fun r : ℝ => gaussianSuzukiDigammaDensity u *
            (symmetricGaussian ε t r *
              (1 - Real.cos (r * u))) by
        funext r
        ring]
      rw [integral_const_mul]

theorem integral_symmetricGaussian_mul_archimedeanDensityDifference
    (hgauss : QuarterLineDigammaGaussDifferenceFormula)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
      symmetricGaussian ε t r *
        (riemannArchimedeanDensity r -
          riemannArchimedeanDensity 0)) =
      2 * ∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiDigammaDensity u *
          (Real.sqrt (Real.pi / ε) *
            (1 - Real.exp (-u ^ 2 / (4 * ε)) *
              Real.cos (t * u))) := by
  calc
    (∫ r in Set.Ioi (0 : ℝ),
      symmetricGaussian ε t r *
        (riemannArchimedeanDensity r -
          riemannArchimedeanDensity 0)) =
        ∫ r in Set.Ioi (0 : ℝ),
          2 * (symmetricGaussian ε t r *
            ∫ u in Set.Ioi (0 : ℝ),
              gaussianSuzukiDigammaOscillationIntegrand r u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      change
        symmetricGaussian ε t r *
            (riemannArchimedeanDensity r -
              riemannArchimedeanDensity 0) =
          2 * (symmetricGaussian ε t r *
            ∫ u in Set.Ioi (0 : ℝ),
              gaussianSuzukiDigammaOscillationIntegrand r u)
      rw [hgauss r]
      ring
    _ = 2 * ∫ r in Set.Ioi (0 : ℝ),
          symmetricGaussian ε t r *
            ∫ u in Set.Ioi (0 : ℝ),
              gaussianSuzukiDigammaOscillationIntegrand r u := by
      rw [integral_const_mul]
    _ = 2 * ∫ u in Set.Ioi (0 : ℝ),
          gaussianSuzukiDigammaDensity u *
            ∫ r in Set.Ioi (0 : ℝ),
              symmetricGaussian ε t r *
                (1 - Real.cos (r * u)) := by
      rw [integral_gaussianDigammaGauss_swap hgauss hε t]
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      change
        gaussianSuzukiDigammaDensity u *
            (∫ r in Set.Ioi (0 : ℝ),
              symmetricGaussian ε t r *
                (1 - Real.cos (r * u))) =
          gaussianSuzukiDigammaDensity u *
            (Real.sqrt (Real.pi / ε) *
              (1 - Real.exp (-u ^ 2 / (4 * ε)) *
                Real.cos (t * u)))
      rw [show (∫ r in Set.Ioi (0 : ℝ),
          symmetricGaussian ε t r * (1 - Real.cos (r * u))) =
          ∫ r in Set.Ioi (0 : ℝ),
            symmetricGaussian ε t r * (1 - Real.cos (u * r)) by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        change
          symmetricGaussian ε t r * (1 - Real.cos (r * u)) =
            symmetricGaussian ε t r * (1 - Real.cos (u * r))
        rw [mul_comm r u]]
      rw [integral_symmetricGaussianOscillation_Ioi hε t u]

theorem integral_symmetricGaussian_Ioi
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ), symmetricGaussian ε t r) =
      Real.sqrt (Real.pi / ε) := by
  have hhalf := integral_even_eq_two_mul_integral_Ioi
    (integrable_symmetricGaussian hε t) (symmetricGaussian_even ε t)
  rw [integral_symmetricGaussian hε t] at hhalf
  linarith

theorem integrableOn_symmetricGaussian_mul_archimedeanDensityDifference
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    IntegrableOn
      (fun r : ℝ => symmetricGaussian ε t r *
        (riemannArchimedeanDensity r -
          riemannArchimedeanDensity 0))
      (Set.Ioi (0 : ℝ)) := by
  have hdensity : Integrable
      (fun r : ℝ =>
        symmetricGaussian ε t r * riemannArchimedeanDensity r) := by
    have hre :=
      (integrable_symmetricGaussian_mul_digamma_quarter hε t).re
    apply hre.congr
    filter_upwards with r
    unfold riemannArchimedeanDensity
    simp
  have hconstant : Integrable
      (fun r : ℝ =>
        symmetricGaussian ε t r * riemannArchimedeanDensity 0) :=
    (integrable_symmetricGaussian hε t).mul_const _
  have hsub := hdensity.sub hconstant
  apply hsub.integrableOn.congr_fun
  · intro r hr
    change
      symmetricGaussian ε t r * riemannArchimedeanDensity r -
          symmetricGaussian ε t r * riemannArchimedeanDensity 0 =
        symmetricGaussian ε t r *
          (riemannArchimedeanDensity r -
            riemannArchimedeanDensity 0)
    ring
  · exact measurableSet_Ioi

theorem gaussianDigammaGain_eq_archimedeanDensityDifference
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianDigammaGain ε t =
      (1 / Real.pi) *
        ((∫ r in Set.Ioi (0 : ℝ),
          symmetricGaussian ε t r *
            (riemannArchimedeanDensity r -
              riemannArchimedeanDensity 0)) -
        ∫ r in Set.Ioi (0 : ℝ),
          symmetricGaussian ε 0 r *
            (riemannArchimedeanDensity r -
              riemannArchimedeanDensity 0)) := by
  have hrewrite (s : ℝ) :
      (∫ r in Set.Ioi (0 : ℝ),
        symmetricGaussian ε s r *
          (riemannArchimedeanDensity r -
            riemannArchimedeanDensity 0)) =
        (∫ r in Set.Ioi (0 : ℝ),
          symmetricGaussian ε s r * riemannArchimedeanDensity r) -
        riemannArchimedeanDensity 0 * Real.sqrt (Real.pi / ε) := by
    have hdensity : IntegrableOn
        (fun r : ℝ =>
          symmetricGaussian ε s r * riemannArchimedeanDensity r)
        (Set.Ioi (0 : ℝ)) := by
      have hre :=
        (integrable_symmetricGaussian_mul_digamma_quarter hε s).re
      apply hre.integrableOn.congr_fun
      · intro r hr
        unfold riemannArchimedeanDensity
        simp
      · exact measurableSet_Ioi
    have hconstant : IntegrableOn
        (fun r : ℝ =>
          symmetricGaussian ε s r * riemannArchimedeanDensity 0)
        (Set.Ioi (0 : ℝ)) :=
      (integrable_symmetricGaussian hε s).mul_const _ |>.integrableOn
    rw [show (fun r : ℝ =>
        symmetricGaussian ε s r *
          (riemannArchimedeanDensity r -
            riemannArchimedeanDensity 0)) =
        fun r : ℝ =>
          symmetricGaussian ε s r * riemannArchimedeanDensity r -
            symmetricGaussian ε s r * riemannArchimedeanDensity 0 by
      funext r
      ring]
    rw [integral_sub hdensity hconstant, integral_mul_const,
      integral_symmetricGaussian_Ioi hε s]
    ring
  unfold gaussianDigammaGain gaussianDigammaIntegral
  rw [hrewrite t, hrewrite 0]
  ring

theorem integrableOn_gaussianDigammaGaussOuter
    (hgauss : QuarterLineDigammaGaussDifferenceFormula)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    IntegrableOn
      (fun u : ℝ => gaussianSuzukiDigammaDensity u *
        (Real.sqrt (Real.pi / ε) *
          (1 - Real.exp (-u ^ 2 / (4 * ε)) *
            Real.cos (t * u))))
      (Set.Ioi (0 : ℝ)) := by
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  have hraw :=
    (integrable_gaussianDigammaGaussJointIntegrand hgauss hε t).integral_prod_right
  change Integrable
    (fun u : ℝ => ∫ r : ℝ,
      gaussianDigammaGaussJointIntegrand ε t (r, u) ∂μ) μ at hraw
  apply hraw.congr
  filter_upwards with u
  dsimp only [μ]
  unfold gaussianDigammaGaussJointIntegrand gaussianSuzukiDigammaOscillationIntegrand
  change
    (∫ r in Set.Ioi (0 : ℝ),
      symmetricGaussian ε t r *
        (gaussianSuzukiDigammaDensity u *
          (1 - Real.cos (r * u)))) =
      gaussianSuzukiDigammaDensity u *
        (Real.sqrt (Real.pi / ε) *
          (1 - Real.exp (-u ^ 2 / (4 * ε)) *
            Real.cos (t * u)))
  rw [show (fun r : ℝ =>
      symmetricGaussian ε t r *
        (gaussianSuzukiDigammaDensity u *
          (1 - Real.cos (r * u)))) =
      fun r : ℝ => gaussianSuzukiDigammaDensity u *
        (symmetricGaussian ε t r *
          (1 - Real.cos (u * r))) by
    funext r
    rw [mul_comm r u]
    ring]
  rw [integral_const_mul,
    integral_symmetricGaussianOscillation_Ioi hε t u]

/-- Under the pointwise Gauss formula, the complete digamma gain is the
Gaussian energy of the quarter-line density. -/
theorem gaussianDigammaGain_eq_gaussianSuzukiDigammaEnergy
    (hgauss : QuarterLineDigammaGaussDifferenceFormula)
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    gaussianDigammaGain ε t =
      2 / Real.sqrt (Real.pi * ε) *
        ∫ u in Set.Ioi (0 : ℝ),
          gaussianSuzukiDigammaDensity u *
            Real.exp (-u ^ 2 / (4 * ε)) *
              (1 - Real.cos (t * u)) := by
  let F : ℝ → ℝ := fun u => gaussianSuzukiDigammaDensity u *
    (Real.sqrt (Real.pi / ε) *
      (1 - Real.exp (-u ^ 2 / (4 * ε)) * Real.cos (t * u)))
  let F0 : ℝ → ℝ := fun u => gaussianSuzukiDigammaDensity u *
    (Real.sqrt (Real.pi / ε) *
      (1 - Real.exp (-u ^ 2 / (4 * ε)) * Real.cos (0 * u)))
  have hF : IntegrableOn F (Set.Ioi (0 : ℝ)) :=
    integrableOn_gaussianDigammaGaussOuter hgauss hε t
  have hF0 : IntegrableOn F0 (Set.Ioi (0 : ℝ)) :=
    integrableOn_gaussianDigammaGaussOuter hgauss hε 0
  rw [gaussianDigammaGain_eq_archimedeanDensityDifference hε t,
    integral_symmetricGaussian_mul_archimedeanDensityDifference hgauss hε t,
    integral_symmetricGaussian_mul_archimedeanDensityDifference hgauss hε 0]
  have hcombine :
      2 * (∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiDigammaDensity u *
          (Real.sqrt (Real.pi / ε) *
            (1 - Real.exp (-u ^ 2 / (4 * ε)) *
              Real.cos (t * u)))) -
      2 * (∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiDigammaDensity u *
          (Real.sqrt (Real.pi / ε) *
            (1 - Real.exp (-u ^ 2 / (4 * ε)) *
              Real.cos (0 * u)))) =
      2 * ∫ u in Set.Ioi (0 : ℝ), F u - F0 u := by
    rw [integral_sub hF hF0]
    ring
  rw [hcombine]
  have hpoint : (fun u : ℝ => F u - F0 u) =
      fun u : ℝ => Real.sqrt (Real.pi / ε) *
        (gaussianSuzukiDigammaDensity u *
          Real.exp (-u ^ 2 / (4 * ε)) *
            (1 - Real.cos (t * u))) := by
    funext u
    unfold F F0
    rw [zero_mul, Real.cos_zero]
    ring
  rw [hpoint, integral_const_mul]
  let I : ℝ := ∫ u in Set.Ioi (0 : ℝ),
    gaussianSuzukiDigammaDensity u *
      Real.exp (-u ^ 2 / (4 * ε)) * (1 - Real.cos (t * u))
  change
    1 / Real.pi * (2 * (Real.sqrt (Real.pi / ε) * I)) =
      2 / Real.sqrt (Real.pi * ε) * I
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hsqrtε : Real.sqrt ε ≠ 0 :=
    (Real.sqrt_pos.2 hε).ne'
  have hsqrtPiSq : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt hpi
  have hsqrt : Real.sqrt (Real.pi / ε) =
      Real.pi / Real.sqrt (Real.pi * ε) := by
    rw [Real.sqrt_div hpi, Real.sqrt_mul hpi]
    field_simp [hsqrtPi, hsqrtε]
    rw [hsqrtPiSq]
  rw [hsqrt]
  field_simp [Real.pi_ne_zero,
    (Real.sqrt_pos.2 (mul_pos Real.pi_pos hε)).ne']

theorem integrableOn_gaussianReflectedOscillationIntegrand
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    IntegrableOn
      (fun u : ℝ =>
        Real.exp (-u / 2 - u ^ 2 / (4 * ε)) *
          (1 - Real.cos (t * u)))
      (Set.Ioi (0 : ℝ)) := by
  let f : ℝ → ℝ := fun u =>
    Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
      (1 - Real.cos (t * u))
  have hcomp : Integrable (fun u : ℝ => f (-u)) :=
    (gaussianContinuousPrimeOscillationIntegrable hε t).comp_neg
  apply hcomp.integrableOn.congr_fun
  · intro u hu
    dsimp only [f]
    rw [show t * -u = -(t * u) by ring, Real.cos_neg]
    congr 2
    congr 1
    ring
  · exact measurableSet_Ioi

theorem integral_gaussianSuzukiDigammaDensity_eq_reflected_add_missing
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    (∫ u in Set.Ioi (0 : ℝ),
      gaussianSuzukiDigammaDensity u *
        Real.exp (-u ^ 2 / (4 * ε)) *
          (1 - Real.cos (t * u))) =
      (∫ u in Set.Ioi (0 : ℝ),
        Real.exp (-u / 2 - u ^ 2 / (4 * ε)) *
          (1 - Real.cos (t * u))) +
      ∫ u in Set.Ioi (0 : ℝ),
        gaussianSuzukiMissingCurvatureIntegrand ε t u := by
  have hreflected := integrableOn_gaussianReflectedOscillationIntegrand hε t
  have hmissing :=
    integrableOn_gaussianSuzukiMissingCurvatureIntegrand hε t
  rw [← integral_add hreflected hmissing]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hudensity :=
    gaussianSuzukiDigammaDensity_eq_reflected_add_missing hu
  have hfactor :
      Real.exp (-u ^ 2 / (4 * ε)) * Real.exp (-u / 2) =
        Real.exp (-u / 2 - u ^ 2 / (4 * ε)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold gaussianSuzukiMissingCurvatureIntegrand
  change
    gaussianSuzukiDigammaDensity u *
        Real.exp (-u ^ 2 / (4 * ε)) *
          (1 - Real.cos (t * u)) =
      Real.exp (-u / 2 - u ^ 2 / (4 * ε)) *
          (1 - Real.cos (t * u)) +
        Real.exp (-u ^ 2 / (4 * ε)) *
          suzukiMissingCurvature u *
            (1 - Real.cos (t * u))
  rw [hudensity]
  calc
    (Real.exp (-u / 2) + suzukiMissingCurvature u) *
          Real.exp (-u ^ 2 / (4 * ε)) *
          (1 - Real.cos (t * u)) =
        (Real.exp (-u ^ 2 / (4 * ε)) * Real.exp (-u / 2)) *
            (1 - Real.cos (t * u)) +
          Real.exp (-u ^ 2 / (4 * ε)) *
            suzukiMissingCurvature u *
              (1 - Real.cos (t * u)) := by ring
    _ = _ := by rw [hfactor]

/-- The pointwise Gauss difference formula implies the exact digamma/screw
transform required by `GaussianScrewBridge`. -/
theorem gaussianDigammaScrewTransform_of_quarterLineGaussDifference
    (hgauss : QuarterLineDigammaGaussDifferenceFormula) :
    GaussianDigammaScrewTransform := by
  intro ε hε t
  unfold gaussianDigammaRemainderGain
    gaussianReflectedContinuousPrimeOscillationEnergy
    gaussianSuzukiMissingCurvatureEnergy
  rw [gaussianDigammaGain_eq_gaussianSuzukiDigammaEnergy hgauss hε t,
    integral_gaussianSuzukiDigammaDensity_eq_reflected_add_missing hε t]
  ring

end

end RiemannGaussian
