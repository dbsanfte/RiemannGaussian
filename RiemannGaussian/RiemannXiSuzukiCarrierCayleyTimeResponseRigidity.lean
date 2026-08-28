import Mathlib.Analysis.Normed.Group.FunctionSeries
import RiemannGaussian.RiemannXiSuzukiCarrierCayleyTimeResponseBoundary
import RiemannGaussian.RiemannXiBoundaryHeatActionLimit

/-!
# Uniform boundary-collar rigidity of the Suzuki initial response

The pointwise boundary theorem for the complete Suzuki initial velocity can
be strengthened because its dominating divisor density is independent of the
approach height.  This file proves uniform convergence of the genuine finite
spectral windows throughout a short positive boundary collar.

Consequently, failure of RH is not merely detected at the limiting boundary
point.  It forces a fixed positive real part in every sufficiently large
finite Suzuki window, uniformly throughout a whole collar.  The same result
is then expressed using the exact spectral-xi reflection residual, producing
a directly targetable entire-function rigidity obstruction.
-/

open Complex Filter Set Topology
open scoped Classical ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- Genuine finite Blaschke logarithmic-derivative windows converge uniformly
to the complete divisor sum throughout some positive vertical collar based at
every real point. -/
theorem exists_tendstoUniformlyOn_riemannXiUpperBlaschkeLogDerivativeWindow_approach
    (x : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧
      TendstoUniformlyOn
        (fun T : ℝ ↦ fun y : ℝ ↦
          riemannXiUpperBlaschkeLogDerivativeWindow
            (upperBoundaryApproachPoint x y) T)
        (fun y : ℝ ↦ riemannXiUpperBlaschkeCompleteLogDerivative
          (upperBoundaryApproachPoint x y))
        atTop (Ioo 0 (delta / 2)) := by
  obtain ⟨delta, hdelta, hgap⟩ :=
    exists_uniform_upper_zetaSpectralCoordinate_gap_real x
  refine ⟨delta, hdelta, ?_⟩
  have hfinset : TendstoUniformlyOn
      (fun s : Finset NontrivialZetaZero ↦ fun y : ℝ ↦
        ∑ rho ∈ s, zetaUpperBlaschkeSelectedLogDerivativeSummand
          (upperBoundaryApproachPoint x y) rho)
      (fun y : ℝ ↦ ∑' rho : NontrivialZetaZero,
        zetaUpperBlaschkeSelectedLogDerivativeSummand
          (upperBoundaryApproachPoint x y) rho)
      atTop (Ioo 0 (delta / 2)) :=
    tendstoUniformlyOn_tsum
      ((summable_zetaUpperBlaschkeBoundaryDensitySummand x).mul_left 2)
      (fun rho y hy ↦
        norm_zetaUpperBlaschkeSelectedLogDerivativeSummand_approach_le
          hdelta hgap hy.1 hy.2 rho)
  have hwindow : TendstoUniformlyOn
      (fun T : ℝ ↦ fun y : ℝ ↦
        ∑ rho ∈ spectralZetaZeroWindow T,
          zetaUpperBlaschkeSelectedLogDerivativeSummand
            (upperBoundaryApproachPoint x y) rho)
      (fun y : ℝ ↦ ∑' rho : NontrivialZetaZero,
        zetaUpperBlaschkeSelectedLogDerivativeSummand
          (upperBoundaryApproachPoint x y) rho)
      atTop (Ioo 0 (delta / 2)) := by
    intro u hu
    exact tendsto_spectralZetaZeroWindow_atTop (hfinset u hu)
  simpa only [sum_zetaUpperBlaschkeSelectedLogDerivativeSummand_eq_window,
    riemannXiUpperBlaschkeCompleteLogDerivative] using hwindow

/-- Genuine finite signed Suzuki initial velocities converge uniformly to the
complete velocity throughout some positive vertical boundary collar. -/
theorem exists_tendstoUniformlyOn_suzukiXiOffAxisSignedPInitialVelocityWindow_approach
    (x : ℝ) :
    ∃ delta : ℝ, 0 < delta ∧
      TendstoUniformlyOn
        (fun T : ℝ ↦ fun y : ℝ ↦
          suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
            0 T (upperBoundaryApproachPoint x y))
        (fun y : ℝ ↦ riemannXiSuzukiOffAxisSignedPInitialVelocity
          (upperBoundaryApproachPoint x y))
        atTop (Ioo 0 (delta / 2)) := by
  obtain ⟨delta, hdelta, hlog⟩ :=
    exists_tendstoUniformlyOn_riemannXiUpperBlaschkeLogDerivativeWindow_approach
      x
  refine ⟨delta, hdelta, ?_⟩
  have hscaled : TendstoUniformlyOn
      (fun T : ℝ ↦ (fun z : ℂ ↦ -Complex.I * z) ∘
        fun y : ℝ ↦ riemannXiUpperBlaschkeLogDerivativeWindow
          (upperBoundaryApproachPoint x y) T)
      ((fun z : ℂ ↦ -Complex.I * z) ∘
        fun y : ℝ ↦ riemannXiUpperBlaschkeCompleteLogDerivative
          (upperBoundaryApproachPoint x y))
      atTop (Ioo 0 (delta / 2)) :=
    (uniformContinuous_const_smul (-Complex.I)).comp_tendstoUniformlyOn hlog
  have heq : ∀ᶠ T : ℝ in atTop,
      Set.EqOn
        ((fun z : ℂ ↦ -Complex.I * z) ∘
          fun y : ℝ ↦ riemannXiUpperBlaschkeLogDerivativeWindow
            (upperBoundaryApproachPoint x y) T)
        (fun y : ℝ ↦
          suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
            0 T (upperBoundaryApproachPoint x y))
        (Ioo 0 (delta / 2)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    intro y _hy
    exact
      (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time
        hT (upperBoundaryApproachPoint x y)).symm
  change TendstoUniformlyOn
    (fun T : ℝ ↦ fun y : ℝ ↦
      suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
        0 T (upperBoundaryApproachPoint x y))
    ((fun z : ℂ ↦ -Complex.I * z) ∘
      fun y : ℝ ↦ riemannXiUpperBlaschkeCompleteLogDerivative
        (upperBoundaryApproachPoint x y))
    atTop (Ioo 0 (delta / 2))
  exact hscaled.congr heq

/-- Under failure of RH, the complete Suzuki initial velocity has uniformly
positive real part throughout some positive vertical boundary collar. -/
theorem exists_positive_riemannXiSuzukiOffAxisSignedPInitialVelocity_collar_of_not_rh
    (x : ℝ) (hRH : ¬RiemannHypothesis) :
    ∃ delta c : ℝ, 0 < delta ∧ 0 < c ∧
      ∀ y ∈ Ioo 0 delta,
        c < (riemannXiSuzukiOffAxisSignedPInitialVelocity
          (upperBoundaryApproachPoint x y)).re := by
  let D : ℝ := riemannXiUpperBlaschkeBoundaryDensityTotal x
  have hD : 0 < D := by
    exact riemannXiUpperBlaschkeBoundaryDensityTotal_pos_of_not_rh x hRH
  have hboundary :
      riemannXiSuzukiOffAxisSignedPInitialVelocity (x : ℂ) = (D : ℂ) := by
    simpa only [D] using
      riemannXiSuzukiOffAxisSignedPInitialVelocity_real_eq_density x
  have htarget :
      {z : ℂ | D / 2 < z.re} ∈
        nhds (riemannXiSuzukiOffAxisSignedPInitialVelocity (x : ℂ)) := by
    apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    rw [hboundary]
    change D / 2 < D
    linarith
  have hevent : ∀ᶠ y : ℝ in nhdsWithin 0 (Ioi 0),
      D / 2 < (riemannXiSuzukiOffAxisSignedPInitialVelocity
        (upperBoundaryApproachPoint x y)).re :=
    (tendsto_riemannXiSuzukiOffAxisSignedPInitialVelocity_approach x).eventually
      htarget
  obtain ⟨delta, hdelta, hsubset⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  exact ⟨delta, D / 2, hdelta, by positivity,
    fun y hy ↦ hsubset hy⟩

/-- Failure of RH forces a fixed positive real part in every sufficiently
large genuine finite Suzuki window, uniformly throughout a whole positive
boundary collar. -/
theorem exists_uniform_positive_suzukiXiOffAxisSignedPInitialVelocityWindow_collar_of_not_rh
    (x : ℝ) (hRH : ¬RiemannHypothesis) :
    ∃ delta c R : ℝ, 0 < delta ∧ 0 < c ∧ 0 ≤ R ∧
      ∀ {y T : ℝ}, y ∈ Ioo 0 delta → R ≤ T →
        c < (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
          0 T (upperBoundaryApproachPoint x y)).re := by
  obtain ⟨eta, c, heta, hc, hcomplete⟩ :=
    exists_positive_riemannXiSuzukiOffAxisSignedPInitialVelocity_collar_of_not_rh
      x hRH
  obtain ⟨deltaGap, hdeltaGap, huniform⟩ :=
    exists_tendstoUniformlyOn_suzukiXiOffAxisSignedPInitialVelocityWindow_approach
      x
  have hmetric : ∀ᶠ T : ℝ in atTop,
      ∀ y ∈ Ioo 0 (deltaGap / 2),
        dist
          (riemannXiSuzukiOffAxisSignedPInitialVelocity
            (upperBoundaryApproachPoint x y))
          (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
            0 T (upperBoundaryApproachPoint x y)) < c / 2 :=
    (Metric.tendstoUniformlyOn_iff.mp huniform) (c / 2) (by positivity)
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp hmetric
  refine ⟨min eta (deltaGap / 2), c / 2, max T0 0,
    lt_min heta (by positivity), by positivity, le_max_right _ _, ?_⟩
  intro y T hy hT
  have hyEta : y ∈ Ioo 0 eta :=
    ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩
  have hyGap : y ∈ Ioo 0 (deltaGap / 2) :=
    ⟨hy.1, hy.2.trans_le (min_le_right _ _)⟩
  have hT0T : T0 ≤ T := (le_max_left T0 0).trans hT
  have hdist := hT0 T hT0T y hyGap
  rw [dist_eq] at hdist
  have hreAbs :
      |(riemannXiSuzukiOffAxisSignedPInitialVelocity
          (upperBoundaryApproachPoint x y) -
        suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
          0 T (upperBoundaryApproachPoint x y)).re| ≤
        ‖riemannXiSuzukiOffAxisSignedPInitialVelocity
            (upperBoundaryApproachPoint x y) -
          suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
            0 T (upperBoundaryApproachPoint x y)‖ :=
    Complex.abs_re_le_norm _
  rw [sub_re] at hreAbs
  have hreDiff :
      |(riemannXiSuzukiOffAxisSignedPInitialVelocity
          (upperBoundaryApproachPoint x y)).re -
        (suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow
          0 T (upperBoundaryApproachPoint x y)).re| < c / 2 :=
    hreAbs.trans_lt hdist
  have hcompletePos := hcomplete y hyEta
  nlinarith [lt_of_abs_lt hreDiff]

/-- The same uniform positive collar obstruction, expressed entirely through
the exact finite spectral-xi reflection residual. -/
theorem exists_uniform_positive_neg_I_mul_riemannXiUpperSpectralReflectionResidual_collar_of_not_rh
    (x : ℝ) (hRH : ¬RiemannHypothesis) :
    ∃ delta c R : ℝ, 0 < delta ∧ 0 < c ∧ 0 ≤ R ∧
      ∀ {y T : ℝ}, y ∈ Ioo 0 delta → R ≤ T →
        c < (-Complex.I * riemannXiUpperSpectralReflectionResidual
          (upperBoundaryApproachPoint x y) T).re := by
  obtain ⟨deltaFinite, c, R, hdeltaFinite, hc, hR, hfinite⟩ :=
    exists_uniform_positive_suzukiXiOffAxisSignedPInitialVelocityWindow_collar_of_not_rh
      x hRH
  obtain ⟨deltaGap, hdeltaGap, hgap⟩ :=
    exists_uniform_upper_zetaSpectralCoordinate_gap_real x
  refine ⟨min deltaFinite (deltaGap / 2), c, R,
    lt_min hdeltaFinite (by positivity), hc, hR, ?_⟩
  intro y T hy hT
  have hyFinite : y ∈ Ioo 0 deltaFinite :=
    ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩
  have hyGap : y < deltaGap / 2 :=
    hy.2.trans_le (min_le_right _ _)
  have hxi :
      riemannXiSpectral (upperBoundaryApproachPoint x y) ≠ 0 :=
    riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
      hdeltaGap hgap hy.1 hyGap
  have hpositive := hfinite hyFinite hT
  have hz : 0 < (upperBoundaryApproachPoint x y).im := by
    simpa using hy.1
  rw [
    suzukiXiOffAxisSignedSpectralPResponseDerivativeWindow_zero_time_eq_reflectionResidual
      hz hxi (hR.trans hT)] at hpositive
  exact hpositive

/-- Any cofinal mechanism that makes the scaled xi reflection residual enter
every positive threshold in every boundary collar rules out the uniform
obstruction above and therefore proves RH. -/
theorem riemannHypothesis_of_cofinal_small_neg_I_mul_reflectionResidual
    (x : ℝ)
    (hsmall : ∀ delta c R : ℝ,
      0 < delta → 0 < c → 0 ≤ R →
        ∃ y ∈ Ioo 0 delta, ∃ T : ℝ, R ≤ T ∧
          (-Complex.I * riemannXiUpperSpectralReflectionResidual
            (upperBoundaryApproachPoint x y) T).re ≤ c) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨delta, c, R, hdelta, hc, hR, hpersistent⟩ :=
    exists_uniform_positive_neg_I_mul_riemannXiUpperSpectralReflectionResidual_collar_of_not_rh
      x hRH
  obtain ⟨y, hy, T, hT, hupper⟩ := hsmall delta c R hdelta hc hR
  exact (not_lt_of_ge hupper) (hpersistent hy hT)

/-- Under RH every finite upper-divisor Blaschke logarithmic-derivative
window is identically zero. -/
theorem riemannXiUpperBlaschkeLogDerivativeWindow_eq_zero_of_rh
    (hRH : RiemannHypothesis) (z : ℂ) (T : ℝ) :
    riemannXiUpperBlaschkeLogDerivativeWindow z T = 0 := by
  unfold riemannXiUpperBlaschkeLogDerivativeWindow
  apply Finset.sum_eq_zero
  intro rho hrho
  have hupper : 0 < (zetaSpectralCoordinate rho.1).im :=
    (mem_spectralUpperZetaZeroWindow.mp hrho).2
  have him : (zetaSpectralCoordinate rho.1).im = 0 :=
    (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
      rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  exfalso
  linarith

/-- Under RH the exact finite spectral-xi reflection residual vanishes at
every noncolliding upper point and every nonnegative window. -/
theorem riemannXiUpperSpectralReflectionResidual_eq_zero_of_rh
    (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 < z.im)
    (hxi : riemannXiSpectral z ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    riemannXiUpperSpectralReflectionResidual z T = 0 := by
  rw [riemannXiUpperSpectralReflectionResidual_eq_logDerivativeWindow
      hz hxi hT,
    riemannXiUpperBlaschkeLogDerivativeWindow_eq_zero_of_rh hRH]

/-- Cofinal smallness of the finite spectral-xi reflection residual in every
positive boundary collar and beyond every spectral cutoff is exactly RH. -/
theorem cofinal_small_neg_I_mul_riemannXiUpperSpectralReflectionResidual_iff_rh
    (x : ℝ) :
    (∀ delta c R : ℝ,
      0 < delta → 0 < c → 0 ≤ R →
        ∃ y ∈ Ioo 0 delta, ∃ T : ℝ, R ≤ T ∧
          (-Complex.I * riemannXiUpperSpectralReflectionResidual
            (upperBoundaryApproachPoint x y) T).re ≤ c) ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_cofinal_small_neg_I_mul_reflectionResidual x
  · intro hRH delta c R hdelta hc hR
    obtain ⟨deltaGap, hdeltaGap, hgap⟩ :=
      exists_uniform_upper_zetaSpectralCoordinate_gap_real x
    let d : ℝ := min delta (deltaGap / 2)
    let y : ℝ := d / 2
    let T : ℝ := max R 0
    have hd : 0 < d := by
      dsimp [d]
      exact lt_min hdelta (by positivity)
    have hy : y ∈ Ioo 0 delta := by
      dsimp [y]
      constructor
      · positivity
      · have hdle : d ≤ delta := by
          dsimp [d]
          exact min_le_left _ _
        nlinarith
    refine ⟨y, hy, T, ?_, ?_⟩
    · dsimp [T]
      exact le_max_left _ _
    · have hyGap : y < deltaGap / 2 := by
        have hdle : d ≤ deltaGap / 2 := by
          dsimp [d]
          exact min_le_right _ _
        dsimp [y]
        nlinarith
      have hxi : riemannXiSpectral
          (upperBoundaryApproachPoint x y) ≠ 0 :=
        riemannXiSpectral_upperBoundaryApproachPoint_ne_zero
          hdeltaGap hgap hy.1 hyGap
      have hz : 0 < (upperBoundaryApproachPoint x y).im := by
        simpa using hy.1
      have hT : 0 ≤ T := by
        dsimp [T]
        exact le_max_right _ _
      rw [riemannXiUpperSpectralReflectionResidual_eq_zero_of_rh
        hRH hz hxi hT, mul_zero, zero_re]
      exact hc.le

end

end RiemannGaussian
