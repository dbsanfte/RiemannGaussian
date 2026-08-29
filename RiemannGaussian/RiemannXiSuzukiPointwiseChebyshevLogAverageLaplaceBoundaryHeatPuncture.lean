import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeat

/-!
# Local puncture data for the arithmetic boundary heat

The zero-free Cauchy--Green identity must eventually be passed across the
isolated poles contributed by nontrivial zeta zeros.  The first local input is
the residue of the *actual* heat-weighted response.  Unlike the earlier
constant-weight statement, the heat kernel now varies with the integration
variable.

Continuity of the real-smooth heat kernel and the already checked
pole-cleared arithmetic residue imply that multiplication by the moving
kernel preserves the simple-pole limit.  Thus every selected puncture has
exactly the boundary-heat coefficient required by the global residue series.
No holomorphicity of the heat kernel is used or asserted.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter Metric Set
open scoped Topology

/-- A shifted nontrivial zeta zero has a punctured neighborhood contained in
the zero-free pole-cleared continuation domain.  This records both positivity
of the shifted real coordinate and isolation of the xi zero. -/
theorem eventually_mem_suzukiChebyshevLogAverageLaplacePoleClearedDomain_punctured
    (rho : NontrivialZetaZero) :
    ∀ᶠ w in 𝓝[≠] suzukiChebyshevLaplaceZeroCoordinate rho,
      w ∈ suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
  let p : ℂ := suzukiChebyshevLaplaceZeroCoordinate rho
  have hshiftFull : Tendsto (fun w : ℂ => w + 1 / 2)
      (𝓝 p) (𝓝 rho.1) := by
    have hcontinuous : Continuous (fun w : ℂ => w + 1 / 2) := by
      fun_prop
    simpa [p, suzukiChebyshevLaplaceZeroCoordinate] using
      hcontinuous.tendsto p
  have hshift : Tendsto (fun w : ℂ => w + 1 / 2)
      (𝓝[≠] p) (𝓝[≠] rho.1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hshiftFull.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      change w ≠ p at hw
      change w + 1 / 2 ≠ rho.1
      intro heq
      apply hw
      calc
        w = (w + 1 / 2) - 1 / 2 := by ring
        _ = rho.1 - 1 / 2 := by rw [heq]
        _ = p := by rfl
  have hfinite : analyticOrderAt riemannXi rho.1 ≠ ⊤ := by
    rw [analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hxiNear : ∀ᶠ s in 𝓝[≠] rho.1, riemannXi s ≠ 0 :=
    (analyticAt_riemannXi rho.1).eventually_eq_zero_or_eventually_ne_zero
      |>.resolve_left fun hzero =>
        hfinite (analyticOrderAt_eq_top.mpr hzero)
  have hxi : ∀ᶠ w in 𝓝[≠] p, riemannXi (w + 1 / 2) ≠ 0 :=
    hshift.eventually hxiNear
  have hpositiveFull : ∀ᶠ w in 𝓝 p, 0 < (w + 1 / 2).re := by
    have hpositiveAt : 0 < (p + 1 / 2).re := by
      simpa [p, suzukiChebyshevLaplaceZeroCoordinate] using
        NontrivialZetaZero.zero_lt_re rho
    have hcontinuous : Continuous (fun w : ℂ => (w + 1 / 2).re) := by
      fun_prop
    exact (isOpen_lt continuous_const hcontinuous).mem_nhds hpositiveAt
  have hpositive : ∀ᶠ w in 𝓝[≠] p, 0 < (w + 1 / 2).re :=
    hpositiveFull.filter_mono nhdsWithin_le_nhds
  filter_upwards [hpositive, hxi] with w hwPositive hwXi
  exact ⟨hwPositive, hwXi⟩

/-- An explicit positive-radius form of the local punctured-domain fact. -/
theorem exists_ball_punctured_subset_suzukiChebyshevLogAverageLaplacePoleClearedDomain
    (rho : NontrivialZetaZero) :
    ∃ R : ℝ, 0 < R ∧
      ball (suzukiChebyshevLaplaceZeroCoordinate rho) R \
          {suzukiChebyshevLaplaceZeroCoordinate rho} ⊆
        suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
  have hpunctured :=
    eventually_mem_suzukiChebyshevLogAverageLaplacePoleClearedDomain_punctured
      rho
  rw [eventually_nhdsWithin_iff] at hpunctured
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hpunctured
  exact ⟨R, hR, fun w hw => hball hw.1 hw.2⟩

/-- A general small-circle residue limit requiring only a simple-pole limit
and eventual circle integrability.  In particular, the function itself need
not be holomorphic: this is the form needed for a non-holomorphic
Cauchy--Green weight. -/
theorem tendsto_circleIntegral_nhdsGT_zero_of_tendsto_sub_mul
    {f : ℂ → ℂ} {c L : ℂ}
    (hintegrable : ∀ᶠ r : ℝ in 𝓝[>] 0, CircleIntegrable f c r)
    (hresidue : Tendsto (fun z : ℂ => (z - c) * f z)
      (𝓝[≠] c) (𝓝 L)) :
    Tendsto (fun r : ℝ => ∮ z in C(c, r), f z)
      (𝓝[>] 0) (𝓝 ((2 * Real.pi * Complex.I) * L)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let eta : ℝ := epsilon / (4 * Real.pi)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hclose : ∀ᶠ z in 𝓝[≠] c,
      dist ((z - c) * f z) L < eta :=
    (Metric.tendsto_nhds.mp hresidue) eta heta
  rw [eventually_nhdsWithin_iff] at hclose
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hclose
  have hrange : Ioo (0 : ℝ) delta ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT hdelta
  filter_upwards [hintegrable, hrange] with r hfintegrable hr
  have hr0 : 0 < r := hr.1
  have hrdelta : r < delta := hr.2
  have hprincipalIntegrable : CircleIntegrable
      (fun z : ℂ => (z - c)⁻¹ * L) c r := by
    have hinv : CircleIntegrable (fun z : ℂ => (z - c)⁻¹) c r := by
      rw [circleIntegrable_sub_inv_iff]
      exact Or.inr (by
        simp only [mem_sphere, dist_self, abs_of_pos hr0]
        exact hr0.ne'.symm)
    exact hinv.mul_continuousOn continuousOn_const
  have hprincipalIntegral :
      (∮ z in C(c, r), (z - c)⁻¹ * L) =
        (2 * Real.pi * Complex.I) * L := by
    calc
      (∮ z in C(c, r), (z - c)⁻¹ * L) =
          (∮ z in C(c, r), (z - c)⁻¹) * L := by
        simpa using circleIntegral.integral_smul_const
          (fun z : ℂ => (z - c)⁻¹) L c r
      _ = (2 * Real.pi * Complex.I) * L := by
        rw [circleIntegral.integral_sub_center_inv c hr0.ne']
  have hpoint : ∀ z ∈ sphere c r,
      ‖f z - (z - c)⁻¹ * L‖ ≤ eta / r := by
    intro z hz
    have hnorm : ‖z - c‖ = r := by
      simpa [mem_sphere, dist_eq_norm] using hz
    have hzc : z - c ≠ 0 :=
      norm_ne_zero_iff.mp (by rw [hnorm]; exact hr0.ne')
    have hzball : z ∈ ball c delta := by
      rw [mem_ball]
      have hdist : dist z c = r := by
        rw [dist_eq_norm]
        exact hnorm
      linarith
    have hgap : ‖(z - c) * f z - L‖ ≤ eta := by
      have hzNe : z ∈ ({c} : Set ℂ)ᶜ := by
        simpa [sub_ne_zero] using hzc
      have := (hball hzball hzNe).le
      simpa [dist_eq_norm] using this
    have heq :
        f z - (z - c)⁻¹ * L =
          (z - c)⁻¹ * ((z - c) * f z - L) := by
      field_simp [hzc]
    rw [heq, norm_mul, norm_inv, hnorm]
    rw [div_eq_mul_inv]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left hgap (inv_nonneg.mpr hr0.le)
  rw [← hprincipalIntegral, dist_eq_norm]
  rw [← circleIntegral.integral_sub hfintegrable hprincipalIntegrable]
  calc
    ‖∮ z in C(c, r), f z - (z - c)⁻¹ * L‖ ≤
        2 * Real.pi * r * (eta / r) :=
      circleIntegral.norm_integral_le_of_norm_le_const hr0.le hpoint
    _ = epsilon / 2 := by
      dsimp [eta]
      field_simp [hr0.ne', Real.pi_ne_zero]
      ring
    _ < epsilon := by linarith

/-- Multiplying the pole-cleared arithmetic response by the *moving* boundary
heat kernel preserves its local residue.  This is the local puncture datum
needed for a genuine Cauchy--Green excision argument. -/
theorem tendsto_sub_mul_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    Tendsto
      (fun w : ℂ =>
        (w - suzukiChebyshevLaplaceZeroCoordinate rho) *
          suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau w)
      (𝓝[≠] suzukiChebyshevLaplaceZeroCoordinate rho)
      (𝓝 (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
          (suzukiChebyshevLaplaceZeroCoordinate rho) *
        (analyticZetaZeroMultiplicity rho : ℂ))) := by
  let p : ℂ := suzukiChebyshevLaplaceZeroCoordinate rho
  have hkernel : Tendsto
      (suzukiChebyshevLaplaceBoundaryHeatKernel x tau)
      (𝓝[≠] p)
      (𝓝 (suzukiChebyshevLaplaceBoundaryHeatKernel x tau p)) :=
    (differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel
      x tau p).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpole :=
    tendsto_suzukiChebyshevLaplaceZeroCoordinate_mul_poleClearedContinuation
      rho
  have hproduct := hkernel.mul hpole
  apply hproduct.congr'
  filter_upwards with w
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
  ring

/-- At a selected upper-spectral puncture, the moving weighted-response
residue is exactly the previously constructed arithmetic boundary-heat
residue. -/
theorem tendsto_sub_mul_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_selected
    (x tau : ℝ) (rho : NontrivialZetaZero)
    (hp : (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0) :
    Tendsto
      (fun w : ℂ =>
        (w - suzukiChebyshevLaplaceZeroCoordinate rho) *
          suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau w)
      (𝓝[≠] suzukiChebyshevLaplaceZeroCoordinate rho)
      (𝓝 (suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho)) := by
  simpa [suzukiChebyshevLaplaceBoundaryHeatResidue, hp] using
    tendsto_sub_mul_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau rho

/-- The heat-weighted response is circle integrable on every sufficiently
small positive circle around one shifted xi zero. -/
theorem eventually_circleIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      CircleIntegrable
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau)
        (suzukiChebyshevLaplaceZeroCoordinate rho) r := by
  let p : ℂ := suzukiChebyshevLaplaceZeroCoordinate rho
  obtain ⟨R, hR, hdomain⟩ :=
    exists_ball_punctured_subset_suzukiChebyshevLogAverageLaplacePoleClearedDomain
      rho
  have hrange : Ioo (0 : ℝ) R ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT hR
  filter_upwards [hrange] with r hr
  have hr0 : 0 < r := hr.1
  have hrR : r < R := hr.2
  have hsphereDomain : sphere p r ⊆
      suzukiChebyshevLogAverageLaplacePoleClearedDomain := by
    intro z hz
    have hdist : dist z p = r := by
      rw [dist_eq_norm]
      simpa [mem_sphere, dist_eq_norm] using hz
    have hzball : z ∈ ball p R := by
      rw [mem_ball, hdist]
      exact hrR
    have hzNe : z ≠ p := by
      intro hzp
      subst z
      rw [dist_self] at hdist
      linarith
    exact hdomain ⟨by simpa [p] using hzball, by simpa [p] using hzNe⟩
  have hkernel : ContinuousOn
      (suzukiChebyshevLaplaceBoundaryHeatKernel x tau) (sphere p r) :=
    (differentiable_real_suzukiChebyshevLaplaceBoundaryHeatKernel
      x tau).continuous.continuousOn
  have hpoleCleared : ContinuousOn
      suzukiChebyshevLogAverageLaplacePoleClearedContinuation (sphere p r) :=
    analyticOnNhd_suzukiChebyshevLogAverageLaplacePoleClearedContinuation
      |>.continuousOn.mono hsphereDomain
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
  exact (hkernel.mul hpoleCleared).circleIntegrable hr0.le

/-- The genuine small-circle integral of the non-holomorphic weighted
response converges to `2 pi i` times its local heat-weighted residue. -/
theorem tendsto_circleIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau : ℝ) (rho : NontrivialZetaZero) :
    Tendsto
      (fun r : ℝ =>
        ∮ w in C(suzukiChebyshevLaplaceZeroCoordinate rho, r),
          suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau w)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I) *
        (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (suzukiChebyshevLaplaceZeroCoordinate rho) *
          (analyticZetaZeroMultiplicity rho : ℂ)))) := by
  exact tendsto_circleIntegral_nhdsGT_zero_of_tendsto_sub_mul
    (eventually_circleIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau rho)
    (tendsto_sub_mul_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau rho)

/-- At a selected upper-spectral puncture, the small-circle limit is exactly
`2 pi i` times the boundary-heat coefficient appearing in the complete
summable residue series. -/
theorem tendsto_circleIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_selected
    (x tau : ℝ) (rho : NontrivialZetaZero)
    (hp : (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0) :
    Tendsto
      (fun r : ℝ =>
        ∮ w in C(suzukiChebyshevLaplaceZeroCoordinate rho, r),
          suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau w)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I) *
        suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho)) := by
  simpa [suzukiChebyshevLaplaceBoundaryHeatResidue, hp] using
    tendsto_circleIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau rho

/-- A common shrinking radius may be used for any finite family of shifted
xi-zero punctures; the sum of their circle integrals converges to the sum of
their exact heat-weighted residues. -/
theorem tendsto_finset_sum_circleIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
    (x tau : ℝ) (S : Finset NontrivialZetaZero) :
    Tendsto
      (fun r : ℝ =>
        ∑ rho ∈ S,
          ∮ w in C(suzukiChebyshevLaplaceZeroCoordinate rho, r),
            suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau w)
      (𝓝[>] 0)
      (𝓝 (∑ rho ∈ S,
        (2 * Real.pi * Complex.I) *
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
              (suzukiChebyshevLaplaceZeroCoordinate rho) *
            (analyticZetaZeroMultiplicity rho : ℂ)))) := by
  exact tendsto_finsetSum S fun rho _ =>
    tendsto_circleIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
      x tau rho

/-- If every puncture in a finite family lies in the selected half-strip,
the common-radius circle sum converges to `2 pi i` times the corresponding
finite boundary-heat residue sum. -/
theorem tendsto_finset_sum_circleIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_selected
    (x tau : ℝ) (S : Finset NontrivialZetaZero)
    (hS : ∀ rho ∈ S,
      (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0) :
    Tendsto
      (fun r : ℝ =>
        ∑ rho ∈ S,
          ∮ w in C(suzukiChebyshevLaplaceZeroCoordinate rho, r),
            suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau w)
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I) *
        ∑ rho ∈ S,
          suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho)) := by
  have hsum := tendsto_finsetSum S fun rho hrho =>
    tendsto_circleIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_selected
      x tau rho (hS rho hrho)
  convert hsum using 1
  rw [Finset.mul_sum]

end

end RiemannGaussian
