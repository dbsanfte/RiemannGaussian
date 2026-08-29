import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaEnergy

/-!
# Divisor-preserving radial flux for the paired-eta field

The preceding module exposes the squared paired-eta logarithmic-derivative
energy but makes no through-divisor `L²` integrability claim. This module
develops the divisor-preserving `L¹` object needed at the frontier: outward
logarithmic flux on shrinking circles.

First, Lean proves that paired eta and zeta have identical analytic order at
every nontrivial zeta zero. Consequently the convergent arithmetic quotient
`D / E` has local residue equal to the genuine analytic zeta-zero
multiplicity. Its contour integral therefore converges to `2 * pi * I` times
that multiplicity.

The imaginary contour integral is then proved equal to the real interval
integral of the outward radial projection. Finally that projection is
rewritten exactly using the normalized bilinear eta numerators from the
preceding module. The resulting normalized-numerator flux is interval
integrable on all sufficiently small positive circles, converges to
`2 * pi` times the positive multiplicity, and is eventually positive.

This is a local divisor-recovery theorem, not an RH theorem or a global
coercivity estimate. Its role is to ensure that subsequent excision or
renormalization arguments retain zero mass instead of losing it through
Lean's pointwise totalization of division.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Paired eta and zeta have the same analytic order at every nontrivial
zeta zero. The elementary eta factor is analytic and nonzero there because
all nontrivial zeros have real part strictly between zero and one. -/
theorem analyticOrderAt_pairedEtaCore_eq_riemannZeta
    (rho : NontrivialZetaZero) :
    analyticOrderAt pairedEtaCore rho.1 =
      analyticOrderAt riemannZeta rho.1 := by
  have hupper : rho.1.re < 1 := NontrivialZetaZero.re_lt_one rho
  have hpositive : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have hfactorAnalytic : AnalyticAt ℂ pairedEtaFactor rho.1 := by
    have hfactorDifferentiable : Differentiable ℂ pairedEtaFactor := by
      intro s
      exact (hasDerivAt_pairedEtaFactor s).differentiableAt
    exact hfactorDifferentiable.analyticAt rho.1
  have hfactorNe : pairedEtaFactor rho.1 ≠ 0 := by
    exact pairedEtaFactor_ne_zero_of_re_lt_one hupper
  have hfactorOrder : analyticOrderAt pairedEtaFactor rho.1 = 0 :=
    hfactorAnalytic.analyticOrderAt_eq_zero.mpr hfactorNe
  have heq :
      pairedEtaCore =ᶠ[𝓝 rho.1]
        fun z => pairedEtaFactor z * riemannZeta z := by
    filter_upwards
      [(Complex.isOpen_re_gt 0).mem_nhds hpositive,
        isOpen_compl_singleton.mem_nhds
          (show rho.1 ∈ ({1}ᶜ : Set ℂ) by simpa using rho.2.2.2)] with z hz0 hz1
    simpa [pairedEtaFactor] using
      pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
        hz0 (by simpa using hz1)
  calc
    analyticOrderAt pairedEtaCore rho.1 =
        analyticOrderAt
          (fun z => pairedEtaFactor z * riemannZeta z) rho.1 :=
      analyticOrderAt_congr heq
    _ = analyticOrderAt pairedEtaFactor rho.1 +
        analyticOrderAt riemannZeta rho.1 :=
      analyticOrderAt_mul hfactorAnalytic
        (analyticAt_riemannZeta_nontrivialZero rho)
    _ = analyticOrderAt riemannZeta rho.1 := by
      rw [hfactorOrder, zero_add]

/-- The natural-valued analytic order of paired eta is the genuine analytic
zeta-zero multiplicity. -/
theorem analyticOrderNatAt_pairedEtaCore_eq_analyticZetaZeroMultiplicity
    (rho : NontrivialZetaZero) :
    analyticOrderNatAt pairedEtaCore rho.1 =
      analyticZetaZeroMultiplicity rho := by
  simp only [analyticOrderNatAt, analyticZetaZeroMultiplicity,
    analyticOrderAt_pairedEtaCore_eq_riemannZeta rho]

/-- The local residue of the convergent paired-eta arithmetic quotient is
the genuine analytic zeta-zero multiplicity. This holds for every
nontrivial zero, not only for zeros to the right of the critical line. -/
theorem tendsto_sub_mul_pairedEtaArithmeticQuotient
    (rho : NontrivialZetaZero) :
    Tendsto
      (fun s : ℂ => (s - rho.1) *
        (pairedEtaArithmeticDerivativeValue s / pairedEtaCore s))
      (𝓝[≠] rho.1)
      (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  have hpositive : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have heta : AnalyticAt ℂ pairedEtaCore rho.1 :=
    analyticOnNhd_pairedEtaCore rho.1 hpositive
  have hfinite : analyticOrderAt pairedEtaCore rho.1 ≠ ⊤ := by
    rw [analyticOrderAt_pairedEtaCore_eq_riemannZeta rho]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hbase :=
    AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt heta hfinite
  rw [analyticOrderNatAt_pairedEtaCore_eq_analyticZetaZeroMultiplicity rho]
    at hbase
  have hnearFull : ∀ᶠ s in 𝓝 rho.1, 0 < s.re :=
    (Complex.isOpen_re_gt 0).mem_nhds hpositive
  have hnear : ∀ᶠ s in 𝓝[≠] rho.1, 0 < s.re :=
    hnearFull.filter_mono nhdsWithin_le_nhds
  apply hbase.congr'
  filter_upwards [hnear] with s hs
  rw [logDeriv_pairedEtaCore_eq_tsum hs]
  rfl

/-- Away from its divisor in the positive half-plane, the convergent
paired-eta arithmetic quotient is analytic. -/
theorem analyticAt_pairedEtaArithmeticQuotient_of_re_pos_of_ne
    {s : ℂ} (hs : 0 < s.re) (hne : pairedEtaCore s ≠ 0) :
    AnalyticAt ℂ
      (fun w : ℂ =>
        pairedEtaArithmeticDerivativeValue w / pairedEtaCore w) s := by
  have heta : AnalyticAt ℂ pairedEtaCore s :=
    analyticOnNhd_pairedEtaCore s hs
  have hlog : AnalyticAt ℂ (logDeriv pairedEtaCore) s := by
    simpa only [logDeriv] using heta.deriv.div heta hne
  have hpositive : ∀ᶠ w in 𝓝 s, 0 < w.re :=
    (Complex.isOpen_re_gt 0).mem_nhds hs
  apply hlog.congr
  filter_upwards [hpositive] with w hw
  rw [logDeriv_pairedEtaCore_eq_tsum hw]
  rfl

/-- The paired-eta arithmetic quotient is circle integrable on every
sufficiently small positive circle around a nontrivial zero. Analytic
finite order supplies the punctured zero-free neighborhood internally. -/
theorem eventually_circleIntegrable_pairedEtaArithmeticQuotient
    (rho : NontrivialZetaZero) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      CircleIntegrable
        (fun s : ℂ =>
          pairedEtaArithmeticDerivativeValue s / pairedEtaCore s)
        rho.1 r := by
  have hpositiveAt : 0 < rho.1.re :=
    NontrivialZetaZero.zero_lt_re rho
  have heta : AnalyticAt ℂ pairedEtaCore rho.1 :=
    analyticOnNhd_pairedEtaCore rho.1 hpositiveAt
  have hfinite : analyticOrderAt pairedEtaCore rho.1 ≠ ⊤ := by
    rw [analyticOrderAt_pairedEtaCore_eq_riemannZeta rho]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hetaNePunctured : ∀ᶠ s in 𝓝[≠] rho.1,
      pairedEtaCore s ≠ 0 :=
    heta.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hzero =>
      hfinite (analyticOrderAt_eq_top.mpr hzero)
  have hetaNeFull : ∀ᶠ s in 𝓝 rho.1, s ≠ rho.1 →
      pairedEtaCore s ≠ 0 := by
    rw [eventually_nhdsWithin_iff] at hetaNePunctured
    filter_upwards [hetaNePunctured] with s hs
    intro hsne
    exact hs (by simpa using hsne)
  have hpositiveFull : ∀ᶠ s in 𝓝 rho.1, 0 < s.re :=
    (Complex.isOpen_re_gt 0).mem_nhds hpositiveAt
  have hlocal : ∀ᶠ s in 𝓝 rho.1, s ≠ rho.1 →
      0 < s.re ∧ pairedEtaCore s ≠ 0 := by
    filter_upwards [hpositiveFull, hetaNeFull] with s hs hne
    exact fun hsrho => ⟨hs, hne hsrho⟩
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  have hrange : Ioo (0 : ℝ) delta ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT hdelta
  filter_upwards [hrange] with r hr
  apply ContinuousOn.circleIntegrable hr.1.le
  intro s hsphere
  have hdist : ‖s - rho.1‖ = r := by
    simpa [mem_sphere] using hsphere
  have hsball : s ∈ ball rho.1 delta := by
    rw [mem_ball, dist_eq_norm, hdist]
    exact hr.2
  have hsne : s ≠ rho.1 := by
    intro heq
    subst s
    simp only [sub_self, norm_zero] at hdist
    exact (ne_of_gt hr.1) hdist.symm
  rcases hball hsball hsne with ⟨hspositive, hseta⟩
  exact
    (analyticAt_pairedEtaArithmeticQuotient_of_re_pos_of_ne
      hspositive hseta).continuousAt.continuousWithinAt

/-- The paired-eta arithmetic quotient has contour integral tending to
`2 * pi * I` times the genuine analytic multiplicity on shrinking positive
circles. This is the complex divisor-preserving flux statement. -/
theorem tendsto_circleIntegral_pairedEtaArithmeticQuotient
    (rho : NontrivialZetaZero) :
    Tendsto
      (fun r : ℝ =>
        ∮ s in C(rho.1, r),
          pairedEtaArithmeticDerivativeValue s / pairedEtaCore s)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I) *
        (analyticZetaZeroMultiplicity rho : ℂ))) := by
  exact tendsto_circleIntegral_nhdsGT_zero_of_tendsto_sub_mul
    (eventually_circleIntegrable_pairedEtaArithmeticQuotient rho)
    (tendsto_sub_mul_pairedEtaArithmeticQuotient rho)

/-- For any circle-integrable complex field, the imaginary part of its
contour integral is the interval integral of its outward radial projection.
This fixes the orientation and sign used by the real flux below. -/
theorem circleIntegral_im_eq_intervalIntegral_radialProjection
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) :
    (∮ z in C(c, r), f z).im =
      ∫ theta : ℝ in 0..2 * Real.pi,
        (circleMap 0 r theta * f (circleMap c r theta)).re := by
  have hweighted : IntervalIntegrable
      (fun theta : ℝ =>
        deriv (circleMap c r) theta * f (circleMap c r theta))
      volume 0 (2 * Real.pi) := by
    simpa only [smul_eq_mul] using hf.out
  have him := Complex.imCLM.intervalIntegral_comp_comm hweighted
  calc
    (∮ z in C(c, r), f z).im =
        (∫ theta : ℝ in 0..2 * Real.pi,
          deriv (circleMap c r) theta * f (circleMap c r theta)).im := rfl
    _ = ∫ theta : ℝ in 0..2 * Real.pi,
        (deriv (circleMap c r) theta * f (circleMap c r theta)).im :=
      him.symm
    _ = ∫ theta : ℝ in 0..2 * Real.pi,
        (circleMap 0 r theta * f (circleMap c r theta)).re := by
      apply intervalIntegral.integral_congr
      intro theta _
      change
        (deriv (circleMap c r) theta * f (circleMap c r theta)).im =
          (circleMap 0 r theta * f (circleMap c r theta)).re
      rw [deriv_circleMap]
      simp only [Complex.mul_im, Complex.mul_re, I_re, I_im]
      ring

/-- The outward radial projection of a circle-integrable complex field is
genuinely interval integrable. -/
theorem CircleIntegrable.intervalIntegrable_radialProjection
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : CircleIntegrable f c r) :
    IntervalIntegrable
      (fun theta : ℝ =>
        (circleMap 0 r theta * f (circleMap c r theta)).re)
      volume 0 (2 * Real.pi) := by
  have hweighted : IntervalIntegrable
      (fun theta : ℝ =>
        deriv (circleMap c r) theta * f (circleMap c r theta))
      volume 0 (2 * Real.pi) := by
    simpa only [smul_eq_mul] using hf.out
  have him : IntervalIntegrable
      (fun theta : ℝ =>
        (deriv (circleMap c r) theta * f (circleMap c r theta)).im)
      volume 0 (2 * Real.pi) := by
    constructor
    · simpa [Function.comp_def] using
        Complex.imCLM.integrableOn_comp hweighted.1
    · simpa [Function.comp_def] using
        Complex.imCLM.integrableOn_comp hweighted.2
  apply him.congr
  intro theta _
  change
    (deriv (circleMap c r) theta * f (circleMap c r theta)).im =
      (circleMap 0 r theta * f (circleMap c r theta)).re
  rw [deriv_circleMap]
  simp only [Complex.mul_im, Complex.mul_re, I_re, I_im]
  ring

/-- The real outward radial flux of the convergent paired-eta arithmetic
quotient on the circle of radius `r` about `rho`. -/
def pairedEtaArithmeticRadialFlux
    (rho : NontrivialZetaZero) (r : ℝ) : ℝ :=
  ∫ theta : ℝ in 0..2 * Real.pi,
    (circleMap 0 r theta *
      (pairedEtaArithmeticDerivativeValue (circleMap rho.1 r theta) /
        pairedEtaCore (circleMap rho.1 r theta))).re

/-- On every circle where the quotient is integrable, its real radial flux
is exactly the imaginary part of its complex contour integral. -/
theorem pairedEtaArithmeticRadialFlux_eq_circleIntegral_im
    (rho : NontrivialZetaZero) {r : ℝ}
    (hintegrable : CircleIntegrable
      (fun s : ℂ =>
        pairedEtaArithmeticDerivativeValue s / pairedEtaCore s)
      rho.1 r) :
    pairedEtaArithmeticRadialFlux rho r =
      (∮ s in C(rho.1, r),
        pairedEtaArithmeticDerivativeValue s / pairedEtaCore s).im := by
  exact (circleIntegral_im_eq_intervalIntegral_radialProjection
    hintegrable).symm

/-- The real arithmetic radial flux converges to `2 * pi` times the genuine
analytic zeta-zero multiplicity. -/
theorem tendsto_pairedEtaArithmeticRadialFlux
    (rho : NontrivialZetaZero) :
    Tendsto (pairedEtaArithmeticRadialFlux rho)
      (𝓝[>] 0)
      (𝓝 (2 * Real.pi *
        (analyticZetaZeroMultiplicity rho : ℝ))) := by
  have hcircle :=
    tendsto_circleIntegral_pairedEtaArithmeticQuotient rho
  have him := Complex.continuous_im.continuousAt.tendsto.comp hcircle
  have hintegrable :=
    eventually_circleIntegrable_pairedEtaArithmeticQuotient rho
  have hflux : Tendsto (pairedEtaArithmeticRadialFlux rho)
      (𝓝[>] 0)
      (𝓝 ((2 * (Real.pi : ℂ) * Complex.I *
        (analyticZetaZeroMultiplicity rho : ℂ)).im)) := by
    apply him.congr'
    filter_upwards [hintegrable] with r hr
    change
      (∮ s in C(rho.1, r),
        pairedEtaArithmeticDerivativeValue s / pairedEtaCore s).im =
          pairedEtaArithmeticRadialFlux rho r
    exact (pairedEtaArithmeticRadialFlux_eq_circleIntegral_im
      rho hr).symm
  convert hflux using 1
  norm_num

/-- The same radial flux written directly through the normalized bilinear
eta numerators and the squared eta denominator. This is the divisor-preserving
`L¹` formulation used instead of assuming an unproved through-divisor `L²`
estimate for the squared quotient energy. -/
def pairedEtaNormalizedNumeratorRadialFlux
    (rho : NontrivialZetaZero) (r : ℝ) : ℝ :=
  ∫ theta : ℝ in 0..2 * Real.pi,
    let s := circleMap rho.1 r theta
    (circleMap 0 r theta).re *
        (pairedEtaLogDerivativeRealNumerator s /
          pairedEtaCoreNormSq s) -
      (circleMap 0 r theta).im *
        (pairedEtaLogDerivativeImaginaryNumerator s /
          pairedEtaCoreNormSq s)

/-- The normalized-numerator radial flux is pointwise the arithmetic
quotient radial flux, including under Lean's totalized division convention. -/
theorem pairedEtaNormalizedNumeratorRadialFlux_eq_arithmetic
    (rho : NontrivialZetaZero) (r : ℝ) :
    pairedEtaNormalizedNumeratorRadialFlux rho r =
      pairedEtaArithmeticRadialFlux rho r := by
  unfold pairedEtaNormalizedNumeratorRadialFlux
    pairedEtaArithmeticRadialFlux
  apply intervalIntegral.integral_congr
  intro theta _
  dsimp only
  rw [← pairedEtaArithmeticQuotient_re,
    ← pairedEtaArithmeticQuotient_im]
  rw [Complex.mul_re]

/-- The normalized-numerator radial-flux integrand is genuinely `L¹` on
every sufficiently small positive circle about a nontrivial zero. -/
theorem eventually_intervalIntegrable_pairedEtaNormalizedNumeratorRadialFlux
    (rho : NontrivialZetaZero) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      IntervalIntegrable
        (fun theta : ℝ =>
          let s := circleMap rho.1 r theta
          (circleMap 0 r theta).re *
              (pairedEtaLogDerivativeRealNumerator s /
                pairedEtaCoreNormSq s) -
            (circleMap 0 r theta).im *
              (pairedEtaLogDerivativeImaginaryNumerator s /
                pairedEtaCoreNormSq s))
        volume 0 (2 * Real.pi) := by
  have hcircle :=
    eventually_circleIntegrable_pairedEtaArithmeticQuotient rho
  filter_upwards [hcircle] with r hr
  have hradial :=
    CircleIntegrable.intervalIntegrable_radialProjection hr
  apply hradial.congr
  intro theta _
  dsimp only
  rw [← pairedEtaArithmeticQuotient_re,
    ← pairedEtaArithmeticQuotient_im]
  rw [Complex.mul_re]

/-- The normalized bilinear eta flux retains precisely `2 * pi` times the
genuine analytic multiplicity in the shrinking-circle limit. -/
theorem tendsto_pairedEtaNormalizedNumeratorRadialFlux
    (rho : NontrivialZetaZero) :
    Tendsto (pairedEtaNormalizedNumeratorRadialFlux rho)
      (𝓝[>] 0)
      (𝓝 (2 * Real.pi *
        (analyticZetaZeroMultiplicity rho : ℝ))) := by
  have h := tendsto_pairedEtaArithmeticRadialFlux rho
  apply h.congr'
  exact Filter.Eventually.of_forall fun r =>
    (pairedEtaNormalizedNumeratorRadialFlux_eq_arithmetic rho r).symm

/-- The limiting normalized eta flux at every nontrivial zero is strictly
positive because analytic zero multiplicity is positive. -/
theorem pairedEtaNormalizedNumeratorRadialFlux_limit_pos
    (rho : NontrivialZetaZero) :
    0 < 2 * Real.pi *
      (analyticZetaZeroMultiplicity rho : ℝ) := by
  have hm : 0 < (analyticZetaZeroMultiplicity rho : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  positivity

/-- On all sufficiently small positive circles, the normalized bilinear eta
flux is strictly positive. This is local divisor positivity, not the missing
global arithmetic coercivity estimate. -/
theorem eventually_pairedEtaNormalizedNumeratorRadialFlux_pos
    (rho : NontrivialZetaZero) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      0 < pairedEtaNormalizedNumeratorRadialFlux rho r := by
  exact (tendsto_pairedEtaNormalizedNumeratorRadialFlux rho).eventually
    (eventually_gt_nhds
      (pairedEtaNormalizedNumeratorRadialFlux_limit_pos rho))

end
end RiemannGaussian
