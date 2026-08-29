import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceComplex

/-!
# Completed continuation of Suzuki's arithmetic Laplace response

The literal logarithmic-time Laplace integral converges absolutely on
`Re z > 1/2`.  Its verified zeta response appears to have a pole at the
boundary point `z = 1/2`, but the pole of `zeta'/zeta` at `s = 1` has exactly
the opposite principal part.  This file performs that cancellation in Lean.

The resulting completed response is expressed through the entire
pole-cleared `riemannXi`, elementary terms, and `digamma`.  It is holomorphic
where `z` and `riemannXi (z + 1/2)` are nonzero and `Re (z + 1/2) > 0`.
That open domain contains the whole closed safe half-plane `Re z >= 1/2` and
genuinely crosses its boundary.  On the original convergence half-plane, the
completed response is proved equal to the literal arithmetic Laplace
integral.

This is analytic continuation of the verified arithmetic identity, not a
claim that the original integral converges outside its absolute-convergence
half-plane.  Zeros of `riemannXi` remain excluded from the holomorphic domain;
at every nonzero shifted zero coordinate, this file calculates the local
residue needed for subsequent fixed-proper-time heat extraction.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

/-- The pole-cleared xi function is nonzero throughout `Re s >= 1`. -/
theorem riemannXi_ne_zero_of_one_le_re
    {s : ℂ} (hs : 1 ≤ s.re) :
    riemannXi s ≠ 0 := by
  intro hzero
  have hzeta := (isNontrivialZetaZero_of_riemannXi_eq_zero hzero).1
  exact riemannZeta_ne_zero_of_one_le_re hs hzeta

/-- The natural zero-adaptive domain of the completed arithmetic Laplace
response.  The positivity condition keeps the digamma argument in its
holomorphic right half-plane. -/
def suzukiChebyshevLogAverageLaplaceContinuationDomain : Set ℂ :=
  {z : ℂ | z ≠ 0 ∧ 0 < (z + 1 / 2).re ∧ riemannXi (z + 1 / 2) ≠ 0}

/-- The completed continuation domain is open. -/
theorem isOpen_suzukiChebyshevLogAverageLaplaceContinuationDomain :
    IsOpen suzukiChebyshevLogAverageLaplaceContinuationDomain := by
  have hshift : Continuous (fun z : ℂ => z + 1 / 2) := by
    fun_prop
  have hzero : IsOpen {z : ℂ | z ≠ 0} :=
    isOpen_ne.preimage continuous_id
  have hpositive : IsOpen {z : ℂ | 0 < (z + 1 / 2).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp hshift)
  have hxi : IsOpen {z : ℂ | riemannXi (z + 1 / 2) ≠ 0} :=
    isOpen_ne.preimage (differentiable_riemannXi.continuous.comp hshift)
  rw [show suzukiChebyshevLogAverageLaplaceContinuationDomain =
      {z : ℂ | z ≠ 0} ∩
        ({z : ℂ | 0 < (z + 1 / 2).re} ∩
          {z : ℂ | riemannXi (z + 1 / 2) ≠ 0}) by
    ext z
    simp [suzukiChebyshevLogAverageLaplaceContinuationDomain]]
  exact hzero.inter (hpositive.inter hxi)

/-- Every point of the closed safe half-plane belongs to the completed
continuation domain. -/
theorem mem_suzukiChebyshevLogAverageLaplaceContinuationDomain_of_half_le_re
    {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    z ∈ suzukiChebyshevLogAverageLaplaceContinuationDomain := by
  refine ⟨?_, ?_, ?_⟩
  · intro hzero
    subst z
    norm_num at hz
  · norm_num [Complex.div_re]
    linarith
  · apply riemannXi_ne_zero_of_one_le_re
    norm_num [Complex.div_re]
    linarith

/-- In particular, the former absolute-convergence boundary point `z = 1/2`
is a regular point of the completed continuation domain. -/
theorem half_mem_suzukiChebyshevLogAverageLaplaceContinuationDomain :
    (1 / 2 : ℂ) ∈ suzukiChebyshevLogAverageLaplaceContinuationDomain := by
  apply mem_suzukiChebyshevLogAverageLaplaceContinuationDomain_of_half_le_re
  norm_num [Complex.div_re]

/-- The completed continuation domain genuinely reaches to the left of
`Re z = 1/2`; this is stronger than merely assigning a boundary value. -/
theorem exists_mem_suzukiChebyshevLogAverageLaplaceContinuationDomain_re_lt_half :
    ∃ z ∈ suzukiChebyshevLogAverageLaplaceContinuationDomain,
      z.re < 1 / 2 := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp
      isOpen_suzukiChebyshevLogAverageLaplaceContinuationDomain)
      (1 / 2 : ℂ)
      half_mem_suzukiChebyshevLogAverageLaplaceContinuationDomain
  let z : ℂ := ((1 / 2 - r / 2 : ℝ) : ℂ)
  refine ⟨z, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    change ‖((1 / 2 - r / 2 : ℝ) : ℂ) - (1 / 2 : ℂ)‖ < r
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [show (1 / 2 - r / 2 : ℝ) - 1 / 2 = -r / 2 by ring]
    rw [abs_of_nonpos (by linarith : -r / 2 ≤ 0)]
    linarith
  · dsimp [z]
    norm_num
    linarith

/-- The pole-cancelled analytic continuation of the arithmetic Laplace
response.  On `Re z > 1/2` it equals the literal integral; away from that
half-plane it denotes only the proved completed continuation. -/
def suzukiChebyshevLogAverageLaplaceCompletedContinuation (z : ℂ) : ℂ :=
  (logDeriv riemannXi (z + 1 / 2) - 1 / (z + 1 / 2) +
      Complex.log Real.pi / 2 -
      Complex.digamma ((z + 1 / 2) / 2) / 2 +
      4 * (z + 1 / 2)) /
    z ^ 2

/-- The completed-xi logarithmic derivative is analytic wherever xi is
nonzero. -/
theorem analyticOnNhd_logDeriv_riemannXi_ne_zero :
    AnalyticOnNhd ℂ (logDeriv riemannXi)
      {s : ℂ | riemannXi s ≠ 0} := by
  have hxi : AnalyticOnNhd ℂ riemannXi
      {s : ℂ | riemannXi s ≠ 0} :=
    analyticOnNhd_riemannXi.mono (subset_univ _)
  rw [show logDeriv riemannXi =
      fun s => deriv riemannXi s / riemannXi s by rfl]
  exact hxi.deriv.div hxi fun s hs => hs

/-- The pole-cancelled completed response is holomorphic throughout its
zero-adaptive continuation domain. -/
theorem analyticOnNhd_suzukiChebyshevLogAverageLaplaceCompletedContinuation :
    AnalyticOnNhd ℂ
      suzukiChebyshevLogAverageLaplaceCompletedContinuation
      suzukiChebyshevLogAverageLaplaceContinuationDomain := by
  let D := suzukiChebyshevLogAverageLaplaceContinuationDomain
  have hshift : AnalyticOnNhd ℂ (fun z : ℂ => z + 1 / 2) D :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hlog : AnalyticOnNhd ℂ
      (fun z : ℂ => logDeriv riemannXi (z + 1 / 2)) D :=
    analyticOnNhd_logDeriv_riemannXi_ne_zero.comp hshift (by
      intro z hz
      exact hz.2.2)
  have hshiftInv : AnalyticOnNhd ℂ
      (fun z : ℂ => 1 / (z + 1 / 2)) D :=
    analyticOnNhd_const.div hshift fun z hz => by
      change z ≠ 0 ∧ 0 < (z + 1 / 2).re ∧
        riemannXi (z + 1 / 2) ≠ 0 at hz
      intro hzero
      have hre := congrArg Complex.re hzero
      norm_num at hre
      have hpos := hz.2.1
      norm_num [Complex.div_re] at hpos
      linarith
  have hhalf : AnalyticOnNhd ℂ
      (fun z : ℂ => (z + 1 / 2) / 2) D :=
    hshift.div_const
  have hdigamma : AnalyticOnNhd ℂ
      (fun z : ℂ => Complex.digamma ((z + 1 / 2) / 2)) D :=
    analyticOnNhd_digamma_re_pos.comp hhalf (by
      intro z hz
      change z ≠ 0 ∧ 0 < (z + 1 / 2).re ∧
        riemannXi (z + 1 / 2) ≠ 0 at hz
      change 0 < ((z + 1 / 2) / 2).re
      norm_num [Complex.div_re]
      have hpos := hz.2.1
      norm_num [Complex.div_re] at hpos
      linarith)
  have hlogPi : AnalyticOnNhd ℂ
      (fun _ : ℂ => Complex.log Real.pi / 2) D :=
    analyticOnNhd_const
  have hlinear : AnalyticOnNhd ℂ
      (fun z : ℂ => 4 * (z + 1 / 2)) D :=
    analyticOnNhd_const.mul hshift
  have hnum : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        logDeriv riemannXi (z + 1 / 2) - 1 / (z + 1 / 2) +
          Complex.log Real.pi / 2 -
          Complex.digamma ((z + 1 / 2) / 2) / 2 +
          4 * (z + 1 / 2)) D :=
    (((hlog.sub hshiftInv).add hlogPi).sub hdigamma.div_const).add hlinear
  have hden : AnalyticOnNhd ℂ (fun z : ℂ => z ^ 2) D :=
    analyticOnNhd_id.pow 2
  unfold suzukiChebyshevLogAverageLaplaceCompletedContinuation
  exact hnum.div hden fun z hz => pow_ne_zero 2 hz.1

/-- The absolute-convergence half-plane is contained in the completed
continuation domain. -/
theorem mapsTo_suzukiChebyshevLogAverageComplexLaplaceDomain_continuationDomain :
    MapsTo id suzukiChebyshevLogAverageComplexLaplaceDomain
      suzukiChebyshevLogAverageLaplaceContinuationDomain := by
  intro z hz
  apply mem_suzukiChebyshevLogAverageLaplaceContinuationDomain_of_half_le_re
  exact hz.le

/-- On the original convergence half-plane, the apparent zeta pole cancels
and the zeta response equals the completed continuation. -/
theorem suzukiChebyshevLogAverageComplexZetaResponse_eq_completedContinuation
    {z : ℂ} (hz : z ∈ suzukiChebyshevLogAverageComplexLaplaceDomain) :
    suzukiChebyshevLogAverageComplexZetaResponse z =
      suzukiChebyshevLogAverageLaplaceCompletedContinuation z := by
  change (1 / 2 : ℝ) < z.re at hz
  have hs : (1 : ℝ) < (z + 1 / 2).re := by
    norm_num [Complex.div_re]
    linarith
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    norm_num at hz
  have hzHalf : z - 1 / 2 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [Complex.div_re] at hre
    linarith
  have hpole :
      -(1 / (z - 1 / 2)) / z ^ 2 + 4 / (z - 1 / 2) =
        4 * (z + 1 / 2) / z ^ 2 := by
    let d : ℂ := z - 1 / 2
    have hd : d ≠ 0 := by
      exact hzHalf
    have hsrel : z + 1 / 2 = d + 1 := by
      dsimp [d]
      ring
    rw [hsrel]
    change -(1 / d) / z ^ 2 + 4 / d = 4 * (d + 1) / z ^ 2
    field_simp [hz0, hd]
    ring
  unfold suzukiChebyshevLogAverageComplexZetaResponse
    suzukiChebyshevLogAverageLaplaceCompletedContinuation
  rw [logDeriv_riemannZeta_eq_logDeriv_riemannXi_sub_mellinCompletedCorrection
    hs]
  unfold suzukiChebyshevMellinCompletedCorrection
  rw [show z + 1 / 2 - 1 = z - 1 / 2 by ring]
  calc
    (logDeriv riemannXi (z + 1 / 2) -
            (1 / (z + 1 / 2) + 1 / (z - 1 / 2) -
              Complex.log Real.pi / 2 +
              Complex.digamma ((z + 1 / 2) / 2) / 2)) /
          z ^ 2 + 4 / (z - 1 / 2) =
        (logDeriv riemannXi (z + 1 / 2) - 1 / (z + 1 / 2) +
            Complex.log Real.pi / 2 -
            Complex.digamma ((z + 1 / 2) / 2) / 2) /
          z ^ 2 +
          (-(1 / (z - 1 / 2)) / z ^ 2 + 4 / (z - 1 / 2)) := by
      ring
    _ = (logDeriv riemannXi (z + 1 / 2) - 1 / (z + 1 / 2) +
            Complex.log Real.pi / 2 -
            Complex.digamma ((z + 1 / 2) / 2) / 2) /
          z ^ 2 + 4 * (z + 1 / 2) / z ^ 2 := by
      rw [hpole]
    _ = (logDeriv riemannXi (z + 1 / 2) - 1 / (z + 1 / 2) +
            Complex.log Real.pi / 2 -
            Complex.digamma ((z + 1 / 2) / 2) / 2 +
            4 * (z + 1 / 2)) /
          z ^ 2 := by
      ring

/-- The literal arithmetic complex Laplace transform agrees with the
completed continuation everywhere that the literal integral converges. -/
theorem suzukiChebyshevLogAverageComplexLaplaceTransform_eq_completedContinuation
    {z : ℂ} (hz : z ∈ suzukiChebyshevLogAverageComplexLaplaceDomain) :
    suzukiChebyshevLogAverageComplexLaplaceTransform z =
      suzukiChebyshevLogAverageLaplaceCompletedContinuation z := by
  rw [suzukiChebyshevLogAverageComplexLaplaceTransform_eq_zetaResponse hz]
  exact
    suzukiChebyshevLogAverageComplexZetaResponse_eq_completedContinuation hz

/-- The Laplace-plane location of a nontrivial zeta zero. -/
def suzukiChebyshevLaplaceZeroCoordinate
    (rho : NontrivialZetaZero) : ℂ :=
  rho.1 - 1 / 2

/-- Shifting a Laplace zero coordinate by `1/2` returns the original zeta
zero. -/
@[simp]
theorem suzukiChebyshevLaplaceZeroCoordinate_add_half
    (rho : NontrivialZetaZero) :
    suzukiChebyshevLaplaceZeroCoordinate rho + (2 : ℂ)⁻¹ = rho.1 := by
  unfold suzukiChebyshevLaplaceZeroCoordinate
  ring

/-- Rotation by `-i` identifies the Laplace zero coordinate with the existing
spectral zero coordinate. -/
theorem neg_I_mul_suzukiChebyshevLaplaceZeroCoordinate
    (rho : NontrivialZetaZero) :
    -Complex.I * suzukiChebyshevLaplaceZeroCoordinate rho =
      zetaSpectralCoordinate rho.1 := by
  unfold suzukiChebyshevLaplaceZeroCoordinate zetaSpectralCoordinate
  norm_num

/-- In Laplace coordinates, the local logarithmic residue of completed xi is
the genuine analytic zeta-zero multiplicity. -/
theorem tendsto_suzukiChebyshevLaplaceZeroCoordinate_mul_logDeriv_riemannXi
    (rho : NontrivialZetaZero) :
    Tendsto
      (fun z : ℂ =>
        (z - suzukiChebyshevLaplaceZeroCoordinate rho) *
          logDeriv riemannXi (z + 1 / 2))
      (𝓝[≠] suzukiChebyshevLaplaceZeroCoordinate rho)
      (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) := by
  have hfinite : analyticOrderAt riemannXi rho.1 ≠ ⊤ := by
    rw [analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hbase :=
    AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
      (analyticAt_riemannXi rho.1) hfinite
  rw [analyticOrderNatAt_riemannXi_eq_analyticZetaZeroMultiplicity] at hbase
  let p : ℂ := suzukiChebyshevLaplaceZeroCoordinate rho
  have hshiftFull : Tendsto (fun z : ℂ => z + 1 / 2)
      (𝓝 p) (𝓝 rho.1) := by
    have hconst : Continuous (fun _ : ℂ => (1 / 2 : ℂ)) :=
      continuous_const
    change Tendsto (id + fun _ : ℂ => (1 / 2 : ℂ))
      (𝓝 p) (𝓝 rho.1)
    simpa [p, suzukiChebyshevLaplaceZeroCoordinate] using
      ((continuous_id.add hconst).tendsto p)
  have hshift : Tendsto (fun z : ℂ => z + 1 / 2)
      (𝓝[≠] p) (𝓝[≠] rho.1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hshiftFull.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      change z ≠ p at hz
      change z + 1 / 2 ≠ rho.1
      intro heq
      apply hz
      calc
        z = (z + 1 / 2) - 1 / 2 := by ring
        _ = rho.1 - 1 / 2 := by rw [heq]
        _ = p := by rfl
  have hcomposed := hbase.comp hshift
  apply hcomposed.congr'
  filter_upwards with z
  dsimp [p, suzukiChebyshevLaplaceZeroCoordinate]
  congr 1
  ring

/-- Every nonzero shifted zeta zero is a genuine pole of the completed
arithmetic Laplace continuation.  Its residue is the analytic zero
multiplicity divided by the square of the shifted coordinate. -/
theorem tendsto_suzukiChebyshevLaplaceZeroCoordinate_mul_completedContinuation
    (rho : NontrivialZetaZero)
    (hp : suzukiChebyshevLaplaceZeroCoordinate rho ≠ 0) :
    Tendsto
      (fun z : ℂ =>
        (z - suzukiChebyshevLaplaceZeroCoordinate rho) *
          suzukiChebyshevLogAverageLaplaceCompletedContinuation z)
      (𝓝[≠] suzukiChebyshevLaplaceZeroCoordinate rho)
      (𝓝 ((analyticZetaZeroMultiplicity rho : ℂ) /
        suzukiChebyshevLaplaceZeroCoordinate rho ^ 2)) := by
  let p : ℂ := suzukiChebyshevLaplaceZeroCoordinate rho
  let B : ℂ → ℂ := fun z =>
    -1 / (z + 1 / 2) + Complex.log Real.pi / 2 -
      Complex.digamma ((z + 1 / 2) / 2) / 2 +
      4 * (z + 1 / 2)
  have hp' : p ≠ 0 := hp
  have hshiftAt : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) p := by
    fun_prop
  have hshiftNe : p + 1 / 2 ≠ 0 := by
    change suzukiChebyshevLaplaceZeroCoordinate rho + 1 / 2 ≠ 0
    rw [one_div, suzukiChebyshevLaplaceZeroCoordinate_add_half]
    exact NontrivialZetaZero.coe_ne_zero rho
  have hhalfAt : AnalyticAt ℂ
      (fun z : ℂ => (z + 1 / 2) / 2) p :=
    hshiftAt.div_const
  have hrhoHalfPos : 0 < (rho.1 / 2).re := by
    norm_num [Complex.div_re]
    exact NontrivialZetaZero.zero_lt_re rho
  have hdigammaAt : AnalyticAt ℂ
      (fun z : ℂ => Complex.digamma ((z + 1 / 2) / 2)) p := by
    have hbase : AnalyticAt ℂ Complex.digamma (rho.1 / 2) :=
      analyticOnNhd_digamma_re_pos (rho.1 / 2) hrhoHalfPos
    have hcomp := hbase.comp_of_eq hhalfAt (by
      change (suzukiChebyshevLaplaceZeroCoordinate rho + 1 / 2) / 2 =
        rho.1 / 2
      rw [one_div, suzukiChebyshevLaplaceZeroCoordinate_add_half])
    apply hcomp.congr
    filter_upwards with z
    rfl
  have hBAnalytic : AnalyticAt ℂ B p := by
    dsimp [B]
    have hinvAt : AnalyticAt ℂ (fun z : ℂ => 1 / (z + 1 / 2)) p :=
      analyticAt_const.div hshiftAt hshiftNe
    have hlogPiAt : AnalyticAt ℂ
        (fun _ : ℂ => Complex.log Real.pi / 2) p :=
      analyticAt_const
    have hlinearAt : AnalyticAt ℂ
        (fun z : ℂ => 4 * (z + 1 / 2)) p :=
      analyticAt_const.mul hshiftAt
    have hnegInvAt : AnalyticAt ℂ
        (fun z : ℂ => -1 / (z + 1 / 2)) p := by
      apply hinvAt.neg.congr
      filter_upwards with z
      change -(1 / (z + 1 / 2)) = -1 / (z + 1 / 2)
      ring
    have hdigammaHalfAt : AnalyticAt ℂ
        (fun z : ℂ => Complex.digamma ((z + 1 / 2) / 2) / 2) p :=
      hdigammaAt.div_const
    exact (((hnegInvAt.add hlogPiAt).sub hdigammaHalfAt).add hlinearAt)
  have hB : Tendsto B (𝓝[≠] p) (𝓝 (B p)) :=
    hBAnalytic.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun z : ℂ => z - p) (𝓝[≠] p) (𝓝 0) := by
    have hfull : Tendsto (fun z : ℂ => z - p) (𝓝 p) (𝓝 (p - p)) :=
      tendsto_id.sub tendsto_const_nhds
    simpa using hfull.mono_left nhdsWithin_le_nhds
  have hinvSq : Tendsto (fun z : ℂ => (z ^ 2)⁻¹)
      (𝓝[≠] p) (𝓝 ((p ^ 2)⁻¹)) := by
    exact ((tendsto_id.mono_left nhdsWithin_le_nhds).pow 2).inv₀
      (pow_ne_zero 2 hp')
  have hresidue :=
    tendsto_suzukiChebyshevLaplaceZeroCoordinate_mul_logDeriv_riemannXi rho
  change Tendsto
      (fun z : ℂ =>
        (z - p) * suzukiChebyshevLogAverageLaplaceCompletedContinuation z)
      (𝓝[≠] p)
      (𝓝 ((analyticZetaZeroMultiplicity rho : ℂ) / p ^ 2))
  have hsum := (hresidue.mul hinvSq).add ((hzero.mul hB).mul hinvSq)
  have hsum' : Tendsto
      (fun z : ℂ =>
        ((z - p) * logDeriv riemannXi (z + 1 / 2)) * (z ^ 2)⁻¹ +
          ((z - p) * B z) * (z ^ 2)⁻¹)
      (𝓝[≠] p)
      (𝓝 ((analyticZetaZeroMultiplicity rho : ℂ) / p ^ 2)) := by
    simpa [div_eq_mul_inv] using hsum
  apply hsum'.congr'
  filter_upwards with z
  unfold suzukiChebyshevLogAverageLaplaceCompletedContinuation
  dsimp [B]
  rw [div_eq_mul_inv]
  ring

/-- Spectral-xi recovery in the entire completed continuation domain.  This
form has no singular term at the former boundary `z = 1/2`. -/
theorem xiSpectralNegativeLogDerivative_neg_I_mul_eq_completedContinuation
    {z : ℂ} (hz : z ∈
      suzukiChebyshevLogAverageLaplaceContinuationDomain) :
    xiSpectralNegativeLogDerivative (-Complex.I * z) =
      -(z ^ 2) *
          suzukiChebyshevLogAverageLaplaceCompletedContinuation z -
        1 / (z + 1 / 2) + Complex.log Real.pi / 2 -
        Complex.digamma ((z + 1 / 2) / 2) / 2 +
        4 * (z + 1 / 2) := by
  have hz0 : z ≠ 0 := hz.1
  have hs0 : z + 1 / 2 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    norm_num [Complex.div_re] at hre
    have hpos := hz.2.1
    norm_num [Complex.div_re] at hpos
    linarith
  rw [xiSpectralNegativeLogDerivative_neg_I_mul_complexLaplaceParameter]
  unfold suzukiChebyshevLogAverageLaplaceCompletedContinuation
  field_simp [hz0, hs0]
  ring

end

end RiemannGaussian
