import RiemannGaussian.RiemannXiHyperbolicHeat
import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceContinuation

/-!
# Arithmetic Laplace residues and the fixed-proper-time xi heat

The completed Suzuki Laplace continuation carries an artificial factor
`z⁻²`, inherited from the logarithmic-average Mellin transform.  Consequently
its residue at the shifted coordinate `p_rho = rho - 1/2` is
`m_rho / p_rho²`.  This file removes that normalization before extracting
zero residues.

The resulting pole-cleared response is the completed-xi logarithmic
derivative plus an explicitly holomorphic Archimedean correction.  Lean proves
that its local residue at every shifted nontrivial zeta zero is exactly the
analytic multiplicity, without a `p_rho ≠ 0` hypothesis.  Multiplying those
local residues by the already constructed fixed-positive-time heat weights
then gives the genuine spectral-xi heat residues term by term.  Absolute
summability identifies their complete sum with the existing entire
fixed-proper-time heat sum.

This is a local-residue-to-global-series identity.  It does not yet represent
the heat sum by one arithmetic contour integral or prove an arithmetic sign
or rigidity estimate.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter Set
open scoped Topology

/-- The zero-free right-half-plane domain of the pole-cleared arithmetic
Laplace response. -/
def suzukiChebyshevLogAverageLaplacePoleClearedDomain : Set ℂ :=
  {z : ℂ | 0 < (z + 1 / 2).re ∧ riemannXi (z + 1 / 2) ≠ 0}

/-- The pole-cleared continuation domain is open. -/
theorem isOpen_suzukiChebyshevLogAverageLaplacePoleClearedDomain :
    IsOpen suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
  have hshift : Continuous (fun z : ℂ => z + 1 / 2) := by
    fun_prop
  have hpositive : IsOpen {z : ℂ | 0 < (z + 1 / 2).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp hshift)
  have hxi : IsOpen {z : ℂ | riemannXi (z + 1 / 2) ≠ 0} :=
    isOpen_ne.preimage (differentiable_riemannXi.continuous.comp hshift)
  rw [show suzukiChebyshevLogAverageLaplacePoleClearedDomain =
      {z : ℂ | 0 < (z + 1 / 2).re} ∩
        {z : ℂ | riemannXi (z + 1 / 2) ≠ 0} by
    ext z
    simp [suzukiChebyshevLogAverageLaplacePoleClearedDomain]]
  exact hpositive.inter hxi

/-- The explicit Archimedean correction remaining after the completed-xi
logarithmic derivative is separated from the pole-cleared response. -/
def suzukiChebyshevLogAverageLaplaceRegularCorrection (z : ℂ) : ℂ :=
  -(1 / (z + 1 / 2)) + Complex.log Real.pi / 2 -
    Complex.digamma ((z + 1 / 2) / 2) / 2 +
    4 * (z + 1 / 2)

/-- The explicit correction is holomorphic whenever the shifted coordinate
has positive real part. -/
theorem analyticOnNhd_suzukiChebyshevLogAverageLaplaceRegularCorrection :
    AnalyticOnNhd ℂ
      suzukiChebyshevLogAverageLaplaceRegularCorrection
      {z : ℂ | 0 < (z + 1 / 2).re} := by
  let U : Set ℂ := {z : ℂ | 0 < (z + 1 / 2).re}
  have hshift : AnalyticOnNhd ℂ (fun z : ℂ => z + 1 / 2) U :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hinv : AnalyticOnNhd ℂ (fun z : ℂ => 1 / (z + 1 / 2)) U :=
    analyticOnNhd_const.div hshift fun z hz => by
      change 0 < (z + 1 / 2).re at hz
      intro hzero
      have hre := congrArg Complex.re hzero
      norm_num [Complex.div_re] at hz hre
      linarith
  have hhalf : AnalyticOnNhd ℂ
      (fun z : ℂ => (z + 1 / 2) / 2) U :=
    hshift.div_const
  have hdigamma : AnalyticOnNhd ℂ
      (fun z : ℂ => Complex.digamma ((z + 1 / 2) / 2)) U :=
    analyticOnNhd_digamma_re_pos.comp hhalf (by
      intro z hz
      change 0 < (z + 1 / 2).re at hz
      change 0 < ((z + 1 / 2) / 2).re
      norm_num [Complex.div_re]
      norm_num [Complex.div_re] at hz
      linarith)
  have hlogPi : AnalyticOnNhd ℂ
      (fun _ : ℂ => Complex.log Real.pi / 2) U :=
    analyticOnNhd_const
  have hlinear : AnalyticOnNhd ℂ
      (fun z : ℂ => 4 * (z + 1 / 2)) U :=
    analyticOnNhd_const.mul hshift
  unfold suzukiChebyshevLogAverageLaplaceRegularCorrection
  exact (((hinv.neg.add hlogPi).sub hdigamma.div_const).add hlinear)

/-- The pole-cleared arithmetic continuation.  Unlike the normalized
completed response, this function has multiplicity itself as its xi-zero
residue. -/
def suzukiChebyshevLogAverageLaplacePoleClearedContinuation (z : ℂ) : ℂ :=
  logDeriv riemannXi (z + 1 / 2) +
    suzukiChebyshevLogAverageLaplaceRegularCorrection z

/-- The pole-cleared response is holomorphic throughout its zero-free
right-half-plane domain. -/
theorem analyticOnNhd_suzukiChebyshevLogAverageLaplacePoleClearedContinuation :
    AnalyticOnNhd ℂ
      suzukiChebyshevLogAverageLaplacePoleClearedContinuation
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
  let D := suzukiChebyshevLogAverageLaplacePoleClearedDomain
  have hshift : AnalyticOnNhd ℂ (fun z : ℂ => z + 1 / 2) D :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hlog : AnalyticOnNhd ℂ
      (fun z : ℂ => logDeriv riemannXi (z + 1 / 2)) D :=
    analyticOnNhd_logDeriv_riemannXi_ne_zero.comp hshift (by
      intro z hz
      exact hz.2)
  have hregular : AnalyticOnNhd ℂ
      suzukiChebyshevLogAverageLaplaceRegularCorrection D :=
    analyticOnNhd_suzukiChebyshevLogAverageLaplaceRegularCorrection.mono
      (fun _ hz => hz.1)
  exact hlog.add hregular

/-- Away from the artificial normalization point, pole clearing is exactly
multiplication of the completed response by `z²`. -/
theorem suzukiChebyshevLogAverageLaplacePoleClearedContinuation_eq_sq_mul_completed
    {z : ℂ} (hz : z ≠ 0) :
    suzukiChebyshevLogAverageLaplacePoleClearedContinuation z =
      z ^ 2 * suzukiChebyshevLogAverageLaplaceCompletedContinuation z := by
  unfold suzukiChebyshevLogAverageLaplacePoleClearedContinuation
    suzukiChebyshevLogAverageLaplaceRegularCorrection
    suzukiChebyshevLogAverageLaplaceCompletedContinuation
  field_simp [hz]
  ring

/-- On the absolute-convergence half-plane, the pole-cleared continuation is
literally `z²` times the arithmetic Laplace integral. -/
theorem sq_mul_suzukiChebyshevLogAverageComplexLaplaceTransform_eq_poleCleared
    {z : ℂ} (hz : z ∈ suzukiChebyshevLogAverageComplexLaplaceDomain) :
    z ^ 2 * suzukiChebyshevLogAverageComplexLaplaceTransform z =
      suzukiChebyshevLogAverageLaplacePoleClearedContinuation z := by
  have hzRe : (1 / 2 : ℝ) < z.re := hz
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    norm_num at hzRe
  rw [suzukiChebyshevLogAverageComplexLaplaceTransform_eq_completedContinuation
    hz]
  exact
    (suzukiChebyshevLogAverageLaplacePoleClearedContinuation_eq_sq_mul_completed
      hz0).symm

/-- At every shifted nontrivial zeta zero, the local residue of the
pole-cleared arithmetic response is exactly the analytic zero multiplicity.
This statement has no exceptional `p_rho ≠ 0` hypothesis. -/
theorem tendsto_suzukiChebyshevLaplaceZeroCoordinate_mul_poleClearedContinuation
    (rho : NontrivialZetaZero) :
    Tendsto
      (fun z : ℂ =>
        (z - suzukiChebyshevLaplaceZeroCoordinate rho) *
          suzukiChebyshevLogAverageLaplacePoleClearedContinuation z)
      (𝓝[≠] suzukiChebyshevLaplaceZeroCoordinate rho)
      (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  let p : ℂ := suzukiChebyshevLaplaceZeroCoordinate rho
  have hshift : p + 1 / 2 = rho.1 := by
    dsimp [p]
    unfold suzukiChebyshevLaplaceZeroCoordinate
    ring
  have hpositive : 0 < (p + 1 / 2).re := by
    rw [hshift]
    exact NontrivialZetaZero.zero_lt_re rho
  have hregularAt : AnalyticAt ℂ
      suzukiChebyshevLogAverageLaplaceRegularCorrection p :=
    analyticOnNhd_suzukiChebyshevLogAverageLaplaceRegularCorrection
      p hpositive
  have hregular : Tendsto
      suzukiChebyshevLogAverageLaplaceRegularCorrection
      (𝓝[≠] p)
      (𝓝 (suzukiChebyshevLogAverageLaplaceRegularCorrection p)) :=
    hregularAt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
    have hfull : Tendsto (fun z : ℂ => z - p) (𝓝 p) (𝓝 (p - p)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa using hfull.mono_left nhdsWithin_le_nhds
  have hresidue :=
    tendsto_suzukiChebyshevLaplaceZeroCoordinate_mul_logDeriv_riemannXi rho
  change Tendsto
      (fun z : ℂ =>
        (z - p) *
          suzukiChebyshevLogAverageLaplacePoleClearedContinuation z)
      (𝓝[≠] p)
      (𝓝 (analyticZetaZeroMultiplicity rho : ℂ))
  have hsum := hresidue.add (hzero.mul hregular)
  have hsum' : Tendsto
      (fun z : ℂ =>
        (z - p) * logDeriv riemannXi (z + 1 / 2) +
          (z - p) *
            suzukiChebyshevLogAverageLaplaceRegularCorrection z)
      (𝓝[≠] p)
      (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
    simpa [p] using hsum
  apply hsum'.congr'
  filter_upwards with z
  unfold suzukiChebyshevLogAverageLaplacePoleClearedContinuation
  ring

/-- The fixed-time heat weight applied to one pole-cleared arithmetic
Laplace residue.  Only upper spectral zeros are selected. -/
def suzukiChebyshevLaplaceUpperHyperbolicHeatWeight
    (z : ℂ) (tau : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (upperHalfPlaneHyperbolicHeatIntegrand z
      (zetaSpectralCoordinate rho.1) tau : ℂ)
  else 0

/-- One heat-weighted residue of the pole-cleared arithmetic Laplace
continuation. -/
def suzukiChebyshevLaplaceUpperHyperbolicHeatResidue
    (z : ℂ) (tau : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  suzukiChebyshevLaplaceUpperHyperbolicHeatWeight z tau rho *
    (analyticZetaZeroMultiplicity rho : ℂ)

/-- The arithmetic pole-cleared heat residue is exactly the existing genuine
spectral-xi heat residue. -/
theorem suzukiChebyshevLaplaceUpperHyperbolicHeatResidue_eq_riemannXi
    (z : ℂ) (tau : ℝ) (rho : NontrivialZetaZero) :
    suzukiChebyshevLaplaceUpperHyperbolicHeatResidue z tau rho =
      riemannXiUpperHyperbolicHeatResidue z tau rho := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [suzukiChebyshevLaplaceUpperHyperbolicHeatResidue,
      suzukiChebyshevLaplaceUpperHyperbolicHeatWeight,
      riemannXiUpperHyperbolicHeatResidue, if_pos hupper, if_pos hupper]
  · rw [suzukiChebyshevLaplaceUpperHyperbolicHeatResidue,
      suzukiChebyshevLaplaceUpperHyperbolicHeatWeight,
      riemannXiUpperHyperbolicHeatResidue, if_neg hupper, if_neg hupper,
      zero_mul]

/-- Every arithmetic heat coefficient is obtained as the genuine local
residue limit of the pole-cleared continuation. -/
theorem tendsto_suzukiChebyshevLaplaceUpperHyperbolicHeat_mul_poleCleared
    (z : ℂ) (tau : ℝ) (rho : NontrivialZetaZero) :
    Tendsto
      (fun w : ℂ =>
        suzukiChebyshevLaplaceUpperHyperbolicHeatWeight z tau rho *
          ((w - suzukiChebyshevLaplaceZeroCoordinate rho) *
            suzukiChebyshevLogAverageLaplacePoleClearedContinuation w))
      (𝓝[≠] suzukiChebyshevLaplaceZeroCoordinate rho)
      (𝓝 (suzukiChebyshevLaplaceUpperHyperbolicHeatResidue z tau rho)) := by
  exact tendsto_const_nhds.mul
    (tendsto_suzukiChebyshevLaplaceZeroCoordinate_mul_poleClearedContinuation
      rho)

/-- The complete fixed-positive-time spectral heat is the absolutely
convergent sum of the local pole-cleared arithmetic Laplace residues. -/
theorem hasSum_suzukiChebyshevLaplaceUpperHyperbolicHeatResidue
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    HasSum (suzukiChebyshevLaplaceUpperHyperbolicHeatResidue z tau)
      (riemannXiUpperHyperbolicHeatSum z tau : ℂ) := by
  exact (hasSum_riemannXiUpperHyperbolicHeatResidue hz htau).congr_fun
    (fun rho =>
      suzukiChebyshevLaplaceUpperHyperbolicHeatResidue_eq_riemannXi
        z tau rho)

/-- The complete series of pole-cleared arithmetic heat residues is
absolutely summable at every positive proper time. -/
theorem summable_norm_suzukiChebyshevLaplaceUpperHyperbolicHeatResidue
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Summable (fun rho : NontrivialZetaZero =>
      ‖suzukiChebyshevLaplaceUpperHyperbolicHeatResidue z tau rho‖) :=
  (hasSum_suzukiChebyshevLaplaceUpperHyperbolicHeatResidue hz htau).summable.norm

end

end RiemannGaussian
