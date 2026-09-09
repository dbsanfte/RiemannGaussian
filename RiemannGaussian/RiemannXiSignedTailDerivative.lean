/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticHalfPlaneDerivative
import RiemannGaussian.RiemannXiJensenDiskBound

/-!
# Quantitative derivative control of the complete omitted xi divisor

The finite zero window stays fixed throughout the analytic argument.
Its omitted tail has an analytic representative through every selected
xi zero, and its nonpositive imaginary part extends through those points.
The half-plane derivative bound consequently controls the actual tail
slope by its central signed mass, without discarding its complex phase.
-/

open Complex Filter Metric Set Topology
open scoped Topology
namespace RiemannGaussian
noncomputable section

/-- An interior region on which a fixed symmetric Cauchy head contains
every pair that could have positive imaginary contribution. -/
def riemannXiSignedTailDomain (T : ℝ) : Set ℂ :=
  {z | |z.re| + 1 / 2 < T ∧ 0 < z.im ∧ z.im < 1}

/-- The actual fixed-window tail has an analytic representative with
nonpositive imaginary part throughout its interior, including all removable
xi-node values. It agrees with the original complex remainder off the divisor. -/
theorem exists_riemannXiSignedWindowTail {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ riemannXiSignedTailDomain T, AnalyticAt ℂ F z ∧ (F z).im ≤ 0) ∧
      (∀ z ∉ spectralXiZeroWindow T,
        F z = riemannXiSpectralWindowLogDerivativeRawRemainder T z) := by
  obtain ⟨F, hF, heq⟩ := exists_riemannXiSpectralWindowLogDerivativeRegularization hT
  have hrect {z : ℂ} (hz : z ∈ riemannXiSignedTailDomain T) : z ∈ spectralContourRectangle T := by
    rcases hz with ⟨hre, hy0, hy1⟩
    constructor
    · linarith
    · rw [abs_of_pos hy0]
      exact hy1.le
  have hopen : IsOpen (riemannXiSignedTailDomain T) := by
    have h1 : IsOpen {z : ℂ | |z.re| + 1 / 2 < T} :=
      isOpen_lt (by fun_prop) continuous_const
    have h2 : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have h3 : IsOpen {z : ℂ | z.im < 1} := isOpen_lt Complex.continuous_im continuous_const
    exact h1.inter (h2.inter h3)
  refine ⟨F, ?_, heq⟩
  intro z hz
  refine ⟨hF z (hrect hz), ?_⟩
  have ht : Tendsto (fun w => (F w).im) (𝓝[≠] z) (𝓝 (F z).im) :=
    (Complex.continuous_im.continuousAt.tendsto.comp
      (hF z (hrect hz)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  have hoff := (spectralXiZeroWindow T).eventually_cofinite_notMem.filter_mono (nhdsNE_le_cofinite z)
  have hUn : ∀ᶠ w in 𝓝 z, w ∈ riemannXiSignedTailDomain T := hopen.mem_nhds hz
  have hU : ∀ᶠ w in 𝓝[≠] z, w ∈ riemannXiSignedTailDomain T :=
    hUn.filter_mono nhdsWithin_le_nhds
  filter_upwards [hoff, hU] with w hw hwu
  have hxi : riemannXiSpectral w ≠ 0 := by
    intro hzero
    exact hw ((mem_spectralXiZeroWindow_iff hT w).mpr ⟨hzero, (hrect hwu).1⟩)
  rw [heq w hw, riemannXiSpectralWindowLogDerivativeRawRemainder, sub_im]
  exact sub_nonpos.mpr (im_logDeriv_riemannXiSpectral_le_finite_window hwu.2.1.le hxi hwu.1.le)

private lemma inner_ball_subset_domain {c : ℂ} (hc0 : 0 < c.im) (hc1 : c.im < 1 / 2)
    {T : ℝ} (hT : |c.re| + 1 ≤ T) : ball c (c.im / 2) ⊆ riemannXiSignedTailDomain T := by
  intro z hz
  have hd : ‖z - c‖ < c.im / 2 := by simpa only [mem_ball, dist_eq_norm] using hz
  have hre : |z.re| ≤ ‖z - c‖ + |c.re| := by
    calc
      |z.re| = |(z - c).re + c.re| := by simp
      _ ≤ |(z - c).re| + |c.re| := abs_add_le (z - c).re c.re
      _ ≤ _ := by linarith [Complex.abs_re_le_norm (z - c)]
  have him := Complex.abs_im_le_norm (z - c)
  simp only [sub_im] at him
  have hi := abs_le.mp him
  exact ⟨by linarith, by linarith [hi.1], by linarith [hi.2]⟩

/-- The complete omitted divisor has an independent derivative bound at
every nonzero xi point in the upper zero strip. The right side is exactly
four times its retained negative imaginary mass divided by observation height. -/
theorem norm_deriv_riemannXiSpectralWindowRawRemainder_le {c : ℂ}
    (hc0 : 0 < c.im) (hc1 : c.im < 1 / 2) (hxi : riemannXiSpectral c ≠ 0)
    {T : ℝ} (hT : |c.re| + 1 ≤ T) :
    ‖deriv (riemannXiSpectralWindowLogDerivativeRawRemainder T) c‖ ≤
      4 * ((riemannXiSpectralWindowCauchySum T c).im -
        (logDeriv riemannXiSpectral c).im) / c.im := by
  have hT0 : 0 ≤ T := by linarith [abs_nonneg c.re]
  obtain ⟨F, hF, heq⟩ := exists_riemannXiSignedWindowTail hT0
  have hball := inner_ball_subset_domain hc0 hc1 hT
  have hcn : c ∉ spectralXiZeroWindow T := by
    intro hc
    exact hxi ((mem_spectralXiZeroWindow_iff hT0 c).mp hc).1
  have hnear : F =ᶠ[𝓝 c] riemannXiSpectralWindowLogDerivativeRawRemainder T := by
    have hn := (spectralXiZeroWindow T).finite_toSet.isClosed.isOpen_compl.mem_nhds hcn
    filter_upwards [hn] with z hz
    exact heq z hz
  have hf : DifferentiableOn ℂ F (ball c (c.im / 2)) :=
    fun z hz => (hF z (hball hz)).1.differentiableAt.differentiableWithinAt
  have hb := norm_deriv_le_of_im_nonpos_on_ball (half_pos hc0) hf
    (fun z hz => (hF z (hball hz)).2)
  rw [hnear.deriv_eq, heq c hcn, riemannXiSpectralWindowLogDerivativeRawRemainder, sub_im] at hb
  exact hb.trans_eq (by ring)

/-- The derivative of the fixed complex Cauchy head is its literal finite
inverse-square sum, retaining all analytic multiplicities and phases. -/
theorem hasDerivAt_riemannXiSpectralWindowCauchySum (T : ℝ) {c : ℂ}
    (hxi : riemannXiSpectral c ≠ 0) :
    HasDerivAt (riemannXiSpectralWindowCauchySum T)
      (∑ rho ∈ spectralZetaZeroWindow T,
        -(analyticZetaZeroMultiplicity rho : ℂ) / (c - zetaSpectralCoordinate rho.1) ^ 2) c := by
  apply HasDerivAt.fun_sum
  intro rho _hrho
  have hn : c - zetaSpectralCoordinate rho.1 ≠ 0 := by
    intro he
    exact hxi ((riemannXiSpectral_eq_zero_iff_exists_zetaZero c).mpr ⟨rho, sub_eq_zero.mp he⟩)
  change HasDerivAt (fun z : ℂ => (analyticZetaZeroMultiplicity rho : ℂ) /
    (z - zetaSpectralCoordinate rho.1)) _ c
  simpa only [zero_mul, mul_one, zero_sub, id_eq] using
    (hasDerivAt_const c (analyticZetaZeroMultiplicity rho : ℂ)).fun_div
      ((hasDerivAt_id c).sub_const (zetaSpectralCoordinate rho.1)) hn

private lemma deriv_raw (T : ℝ) {c : ℂ} (hxi : riemannXiSpectral c ≠ 0) :
    deriv (riemannXiSpectralWindowLogDerivativeRawRemainder T) c =
      deriv (logDeriv riemannXiSpectral) c - deriv (riemannXiSpectralWindowCauchySum T) c := by
  change deriv (fun z => logDeriv riemannXiSpectral z - riemannXiSpectralWindowCauchySum T z) c = _
  exact deriv_fun_sub (analyticAt_logDeriv_riemannXiSpectral_of_ne hxi).differentiableAt
    (hasDerivAt_riemannXiSpectralWindowCauchySum T hxi).differentiableAt

/-- The actual logarithmic-derivative slope lies in an explicit complex
disk about its finite Cauchy-head slope. The radius is determined by the
same head's excess imaginary mass, not an independent norm tail. -/
theorem norm_deriv_logDeriv_riemannXiSpectral_sub_window_le {c : ℂ}
    (hc0 : 0 < c.im) (hc1 : c.im < 1 / 2) (hxi : riemannXiSpectral c ≠ 0)
    {T : ℝ} (hT : |c.re| + 1 ≤ T) :
    ‖deriv (logDeriv riemannXiSpectral) c - deriv (riemannXiSpectralWindowCauchySum T) c‖ ≤
      4 * ((riemannXiSpectralWindowCauchySum T c).im -
        (logDeriv riemannXiSpectral c).im) / c.im := by
  have h := norm_deriv_riemannXiSpectralWindowRawRemainder_le hc0 hc1 hxi hT
  rwa [deriv_raw T hxi] at h

/-- The complete omitted tail slope tends to zero, with its convergence
deduced from the actual signed tail mass and the proved full xi expansion. -/
theorem tendsto_deriv_riemannXiSpectralWindowRawRemainder {c : ℂ}
    (hc0 : 0 < c.im) (hc1 : c.im < 1 / 2) (hxi : riemannXiSpectral c ≠ 0) :
    Tendsto (fun T => deriv (riemannXiSpectralWindowLogDerivativeRawRemainder T) c) atTop (𝓝 0) := by
  have hm := ((Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_riemannXiSpectralWindowCauchySum hxi)).sub_const
      (logDeriv riemannXiSpectral c).im).const_mul 4
  have ht := hm.div_const c.im
  have ht0 : Tendsto (fun T => 4 * ((riemannXiSpectralWindowCauchySum T c).im -
      (logDeriv riemannXiSpectral c).im) / c.im) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, mul_zero, zero_div] using ht
  apply squeeze_zero_norm' _ ht0
  filter_upwards [eventually_ge_atTop (|c.re| + 1)] with T hT
  exact norm_deriv_riemannXiSpectralWindowRawRemainder_le hc0 hc1 hxi hT

/-- The finite multiplicity-weighted Cauchy slopes converge to the full
actual xi logarithmic-derivative slope in the upper zero strip. -/
theorem tendsto_deriv_riemannXiSpectralWindowCauchySum {c : ℂ}
    (hc0 : 0 < c.im) (hc1 : c.im < 1 / 2) (hxi : riemannXiSpectral c ≠ 0) :
    Tendsto (fun T => deriv (riemannXiSpectralWindowCauchySum T) c) atTop
      (𝓝 (deriv (logDeriv riemannXiSpectral) c)) := by
  have h := (tendsto_const_nhds (x := deriv (logDeriv riemannXiSpectral) c)).sub
    (tendsto_deriv_riemannXiSpectralWindowRawRemainder hc0 hc1 hxi)
  have h' : Tendsto (fun T => deriv (logDeriv riemannXiSpectral) c -
      deriv (riemannXiSpectralWindowLogDerivativeRawRemainder T) c) atTop
      (𝓝 (deriv (logDeriv riemannXiSpectral) c)) := by simpa only [sub_zero] using h
  apply h'.congr'
  filter_upwards with T
  rw [deriv_raw T hxi]
  ring

end
end RiemannGaussian
