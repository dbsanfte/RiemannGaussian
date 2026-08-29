import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSimplePoleExcision

/-!
# Finite principal-part regularization for arithmetic boundary heat

This file removes every pole of the arithmetic pole-cleared Laplace response
in a bounded shifted-coordinate slab.  The finite divisor is not assumed: it
is the image of the repository's genuine finite spectral zero window under
the exact rotation from spectral to Laplace coordinates.

At each selected shifted xi zero, the response is proved to equal its true
multiplicity-weighted principal part plus an analytic local remainder.  The
finite removable-singularity theorem then produces one function analytic on
the complete slab and equal to the raw principal-part subtraction away from
the selected divisor.  This is the holomorphic component needed to assemble
finite Cauchy--Green excision term by term.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter Set
open scoped Topology

/-! ## The genuine finite Laplace divisor -/

/-- Shifted Laplace zero coordinates are injective. -/
theorem suzukiChebyshevLaplaceZeroCoordinate_injective :
    Function.Injective suzukiChebyshevLaplaceZeroCoordinate := by
  intro rho sigma h
  apply Subtype.ext
  have h' := congrArg (fun z : ℂ => z + (2 : ℂ)⁻¹) h
  simpa using h'

/-- The Laplace imaginary coordinate is the spectral real coordinate used
to define the existing finite zero windows. -/
theorem suzukiChebyshevLaplaceZeroCoordinate_im_eq_spectral_re
    (rho : NontrivialZetaZero) :
    (suzukiChebyshevLaplaceZeroCoordinate rho).im =
      (zetaSpectralCoordinate rho.1).re := by
  unfold suzukiChebyshevLaplaceZeroCoordinate zetaSpectralCoordinate
  simp

/-- The finite set of shifted xi-zero coordinates with bounded imaginary
part. -/
noncomputable def suzukiChebyshevLaplaceZeroWindow (T : ℝ) : Finset ℂ :=
  (spectralZetaZeroWindow T).image
    suzukiChebyshevLaplaceZeroCoordinate

/-- Membership in the finite shifted window is exactly xi vanishing together
with the imaginary-height bound. -/
theorem mem_suzukiChebyshevLaplaceZeroWindow_iff
    {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    z ∈ suzukiChebyshevLaplaceZeroWindow T ↔
      riemannXi (z + 1 / 2) = 0 ∧ |z.im| ≤ T := by
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, rfl⟩
    constructor
    · rw [show suzukiChebyshevLaplaceZeroCoordinate rho + 1 / 2 =
          rho.1 by
        simpa only [one_div] using
          suzukiChebyshevLaplaceZeroCoordinate_add_half rho]
      exact riemannXi_eq_zero_of_isNontrivialZetaZero rho.2
    · rw [suzukiChebyshevLaplaceZeroCoordinate_im_eq_spectral_re]
      exact (mem_spectralZetaZeroWindow hT rho).mp hrho
  · rintro ⟨hzero, hzT⟩
    let rho : NontrivialZetaZero :=
      ⟨z + 1 / 2,
        (riemannXi_eq_zero_iff_isNontrivialZetaZero (z + 1 / 2)).mp hzero⟩
    have hcoord : suzukiChebyshevLaplaceZeroCoordinate rho = z := by
      dsimp [rho]
      unfold suzukiChebyshevLaplaceZeroCoordinate
      ring
    apply Finset.mem_image.mpr
    refine ⟨rho, ?_, hcoord⟩
    apply (mem_spectralZetaZeroWindow hT rho).mpr
    rw [← suzukiChebyshevLaplaceZeroCoordinate_im_eq_spectral_re, hcoord]
    exact hzT

/-- The positive shifted-coordinate slab on which a bounded-height window
contains every xi zero. -/
def suzukiChebyshevLaplaceFiniteSlab (T : ℝ) : Set ℂ :=
  {z : ℂ | 0 < (z + 1 / 2).re ∧ |z.im| ≤ T}

/-! ## Principal parts and the raw remainder -/

/-- The true multiplicity-weighted principal part of the pole-cleared
response at one shifted xi zero. -/
def suzukiChebyshevLaplacePoleClearedPrincipalPart
    (rho : NontrivialZetaZero) (z : ℂ) : ℂ :=
  simplePoleKernel (analyticZetaZeroMultiplicity rho : ℂ)
    (suzukiChebyshevLaplaceZeroCoordinate rho) z

/-- A pole-cleared principal part is analytic away from its selected shifted
zero. -/
theorem analyticAt_suzukiChebyshevLaplacePoleClearedPrincipalPart_of_ne
    (rho : NontrivialZetaZero) {z : ℂ}
    (hz : z ≠ suzukiChebyshevLaplaceZeroCoordinate rho) :
    AnalyticAt ℂ (suzukiChebyshevLaplacePoleClearedPrincipalPart rho) z := by
  unfold suzukiChebyshevLaplacePoleClearedPrincipalPart simplePoleKernel
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr hz)

/-- Sum of the true principal parts in one finite shifted zero window. -/
def suzukiChebyshevLaplacePoleClearedWindowPrincipalSum
    (T : ℝ) (z : ℂ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    suzukiChebyshevLaplacePoleClearedPrincipalPart rho z

/-- Raw remainder after subtracting every selected principal part from the
actual pole-cleared arithmetic response. -/
def suzukiChebyshevLaplacePoleClearedWindowRawRemainder
    (T : ℝ) (z : ℂ) : ℂ :=
  suzukiChebyshevLogAverageLaplacePoleClearedContinuation z -
    suzukiChebyshevLaplacePoleClearedWindowPrincipalSum T z

/-- The finite principal sum is analytic away from the selected shifted zero
set. -/
theorem analyticAt_suzukiChebyshevLaplacePoleClearedWindowPrincipalSum_of_not_mem
    (T : ℝ) {z : ℂ}
    (hz : z ∉ suzukiChebyshevLaplaceZeroWindow T) :
    AnalyticAt ℂ
      (suzukiChebyshevLaplacePoleClearedWindowPrincipalSum T) z := by
  unfold suzukiChebyshevLaplacePoleClearedWindowPrincipalSum
  apply analyticAt_finset_sum_apply
  intro rho hrho
  apply analyticAt_suzukiChebyshevLaplacePoleClearedPrincipalPart_of_ne
  intro heq
  apply hz
  apply Finset.mem_image.mpr
  exact ⟨rho, hrho, heq.symm⟩

/-- Inside the complete bounded-height slab, the raw remainder is analytic
away from the finite selected divisor. -/
theorem analyticAt_suzukiChebyshevLaplacePoleClearedWindowRawRemainder_of_not_mem
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hzSlab : z ∈ suzukiChebyshevLaplaceFiniteSlab T)
    (hz : z ∉ suzukiChebyshevLaplaceZeroWindow T) :
    AnalyticAt ℂ
      (suzukiChebyshevLaplacePoleClearedWindowRawRemainder T) z := by
  have hxi : riemannXi (z + 1 / 2) ≠ 0 := by
    intro hzero
    exact hz ((mem_suzukiChebyshevLaplaceZeroWindow_iff hT z).mpr
      ⟨hzero, hzSlab.2⟩)
  unfold suzukiChebyshevLaplacePoleClearedWindowRawRemainder
  exact
    (analyticOnNhd_suzukiChebyshevLogAverageLaplacePoleClearedContinuation
      z ⟨hzSlab.1, hxi⟩).sub
      (analyticAt_suzukiChebyshevLaplacePoleClearedWindowPrincipalSum_of_not_mem
        T hz)

/-! ## Local removability at every selected zero -/

/-- The pole-cleared arithmetic response differs locally from its exact
multiplicity-weighted principal part by a function analytic through the
selected shifted xi zero. -/
theorem exists_suzukiChebyshevLogAverageLaplacePoleClearedContinuation_eq_principalPart_add_analytic
    (rho : NontrivialZetaZero) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (suzukiChebyshevLaplaceZeroCoordinate rho) ∧
      suzukiChebyshevLogAverageLaplacePoleClearedContinuation =ᶠ[𝓝[≠]
          suzukiChebyshevLaplaceZeroCoordinate rho]
        fun z =>
          suzukiChebyshevLaplacePoleClearedPrincipalPart rho z + h z := by
  have hfinite : analyticOrderAt riemannXi rho.1 ≠ ⊤ := by
    rw [analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  obtain ⟨k, hkAnalytic, hk⟩ :=
    AnalyticAt.exists_logDeriv_eq_principalPart_add_analytic
      (analyticAt_riemannXi rho.1) hfinite
  let p : ℂ := suzukiChebyshevLaplaceZeroCoordinate rho
  let h : ℂ → ℂ := fun z =>
    k (z + 1 / 2) +
      suzukiChebyshevLogAverageLaplaceRegularCorrection z
  have hshiftAt : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) p := by
    fun_prop
  have hshiftValue : p + 1 / 2 = rho.1 := by
    dsimp [p]
    simpa only [one_div] using
      suzukiChebyshevLaplaceZeroCoordinate_add_half rho
  have hkShift : AnalyticAt ℂ (fun z : ℂ => k (z + 1 / 2)) p :=
    hkAnalytic.comp_of_eq hshiftAt hshiftValue
  have hpositive : 0 < (p + 1 / 2).re := by
    rw [hshiftValue]
    exact NontrivialZetaZero.zero_lt_re rho
  have hregular : AnalyticAt ℂ
      suzukiChebyshevLogAverageLaplaceRegularCorrection p :=
    analyticOnNhd_suzukiChebyshevLogAverageLaplaceRegularCorrection
      p hpositive
  have hhAnalytic : AnalyticAt ℂ h p := by
    unfold h
    exact hkShift.add hregular
  refine ⟨h, hhAnalytic, ?_⟩
  have hshiftFull : Tendsto (fun z : ℂ => z + 1 / 2)
      (𝓝 p) (𝓝 rho.1) := by
    have ht := hshiftAt.continuousAt.tendsto
    rw [hshiftValue] at ht
    exact ht
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
  have hkShifted := hk.comp_tendsto hshift
  filter_upwards [hkShifted] with z hz
  change logDeriv riemannXi (z + 1 / 2) =
      (analyticOrderNatAt riemannXi rho.1 : ℂ) /
          (z + 1 / 2 - rho.1) + k (z + 1 / 2) at hz
  unfold suzukiChebyshevLogAverageLaplacePoleClearedContinuation
    suzukiChebyshevLaplacePoleClearedPrincipalPart simplePoleKernel h
  rw [hz, analyticOrderNatAt_riemannXi_eq_analyticZetaZeroMultiplicity]
  have hden : z + 1 / 2 - rho.1 = z - p := by
    rw [← hshiftValue]
    ring
  rw [hden]
  ring

/-- At each selected zero, the raw finite-window remainder agrees in a
punctured neighborhood with a function analytic through that zero. -/
theorem exists_suzukiChebyshevLaplacePoleClearedWindowRawRemainder_eq_analyticAt
    {T : ℝ} (_hT : 0 ≤ T) (rho : NontrivialZetaZero)
    (hrho : rho ∈ spectralZetaZeroWindow T) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (suzukiChebyshevLaplaceZeroCoordinate rho) ∧
      suzukiChebyshevLaplacePoleClearedWindowRawRemainder T =ᶠ[𝓝[≠]
        suzukiChebyshevLaplaceZeroCoordinate rho] h := by
  obtain ⟨k, hkAnalytic, hk⟩ :=
    exists_suzukiChebyshevLogAverageLaplacePoleClearedContinuation_eq_principalPart_add_analytic
      rho
  let W := spectralZetaZeroWindow T
  let h : ℂ → ℂ := fun z =>
    k z - ∑ sigma ∈ W.erase rho,
      suzukiChebyshevLaplacePoleClearedPrincipalPart sigma z
  have hother : AnalyticAt ℂ
      (fun z => ∑ sigma ∈ W.erase rho,
        suzukiChebyshevLaplacePoleClearedPrincipalPart sigma z)
      (suzukiChebyshevLaplaceZeroCoordinate rho) := by
    have hterm (sigma : NontrivialZetaZero)
        (hsigma : sigma ∈ W.erase rho) :
        AnalyticAt ℂ (suzukiChebyshevLaplacePoleClearedPrincipalPart sigma)
          (suzukiChebyshevLaplaceZeroCoordinate rho) := by
      apply analyticAt_suzukiChebyshevLaplacePoleClearedPrincipalPart_of_ne
      intro heq
      have hrs : rho = sigma :=
        suzukiChebyshevLaplaceZeroCoordinate_injective heq
      exact (Finset.mem_erase.mp hsigma).1 hrs.symm
    exact analyticAt_finset_sum_apply (W.erase rho)
      suzukiChebyshevLaplacePoleClearedPrincipalPart hterm
  have hhAnalytic : AnalyticAt ℂ h
      (suzukiChebyshevLaplaceZeroCoordinate rho) := by
    unfold h
    exact hkAnalytic.sub hother
  refine ⟨h, hhAnalytic, ?_⟩
  filter_upwards [hk] with z hz
  unfold suzukiChebyshevLaplacePoleClearedWindowRawRemainder
    suzukiChebyshevLaplacePoleClearedWindowPrincipalSum h
  rw [hz]
  have hsum := W.add_sum_erase
    (fun sigma => suzukiChebyshevLaplacePoleClearedPrincipalPart sigma z)
    hrho
  rw [← hsum]
  ring

/-! ## One analytic representative on the complete finite slab -/

/-- The finite-window raw remainder has a single analytic representative on
the complete positive shifted-coordinate slab.  Away from the finite genuine
xi divisor, the representative is definitionally the original response minus
the exact principal-part sum. -/
theorem exists_suzukiChebyshevLaplacePoleClearedWindowRegularization
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ suzukiChebyshevLaplaceFiniteSlab T,
        AnalyticAt ℂ F z) ∧
      (∀ z ∉ suzukiChebyshevLaplaceZeroWindow T,
        F z = suzukiChebyshevLaplacePoleClearedWindowRawRemainder T z) := by
  apply exists_analyticAtOn_of_finite_removable
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, rfl⟩
    constructor
    · rw [show suzukiChebyshevLaplaceZeroCoordinate rho + 1 / 2 =
          rho.1 by
        simpa only [one_div] using
          suzukiChebyshevLaplaceZeroCoordinate_add_half rho]
      exact NontrivialZetaZero.zero_lt_re rho
    · rw [suzukiChebyshevLaplaceZeroCoordinate_im_eq_spectral_re]
      exact (mem_spectralZetaZeroWindow hT rho).mp hrho
  · intro z hzSlab hz
    exact
      analyticAt_suzukiChebyshevLaplacePoleClearedWindowRawRemainder_of_not_mem
        hT hzSlab hz
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, rfl⟩
    exact
      exists_suzukiChebyshevLaplacePoleClearedWindowRawRemainder_eq_analyticAt
        hT rho hrho

/-- The actual pole-cleared response is exactly its finite principal sum plus
the raw remainder, at every point under Lean's totalized division convention. -/
theorem suzukiChebyshevLogAverageLaplacePoleClearedContinuation_eq_windowPrincipalSum_add_rawRemainder
    (T : ℝ) (z : ℂ) :
    suzukiChebyshevLogAverageLaplacePoleClearedContinuation z =
      suzukiChebyshevLaplacePoleClearedWindowPrincipalSum T z +
        suzukiChebyshevLaplacePoleClearedWindowRawRemainder T z := by
  unfold suzukiChebyshevLaplacePoleClearedWindowRawRemainder
  ring

/-- There is one analytic finite-window remainder which reconstructs the
actual pole-cleared response away from the genuine finite divisor. -/
theorem exists_suzukiChebyshevLaplacePoleClearedWindowAnalyticDecomposition
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ suzukiChebyshevLaplaceFiniteSlab T,
        AnalyticAt ℂ F z) ∧
      (∀ z ∉ suzukiChebyshevLaplaceZeroWindow T,
        suzukiChebyshevLogAverageLaplacePoleClearedContinuation z =
          suzukiChebyshevLaplacePoleClearedWindowPrincipalSum T z + F z) := by
  obtain ⟨F, hF, hFraw⟩ :=
    exists_suzukiChebyshevLaplacePoleClearedWindowRegularization hT
  refine ⟨F, hF, ?_⟩
  intro z hz
  rw [hFraw z hz]
  exact
    suzukiChebyshevLogAverageLaplacePoleClearedContinuation_eq_windowPrincipalSum_add_rawRemainder
      T z

/-- After multiplication by the smooth heat kernel, the actual arithmetic
response is a finite sum of the exact heat-weighted principal parts plus one
heat-weighted analytic remainder. -/
theorem exists_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_finitePrincipalPartDecomposition
    (x tau : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ suzukiChebyshevLaplaceFiniteSlab T,
        AnalyticAt ℂ F z) ∧
      (∀ z ∉ suzukiChebyshevLaplaceZeroWindow T,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau z =
          (∑ rho ∈ spectralZetaZeroWindow T,
            suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau
              (analyticZetaZeroMultiplicity rho : ℂ)
              (suzukiChebyshevLaplaceZeroCoordinate rho) z) +
            suzukiChebyshevLaplaceBoundaryHeatKernel x tau z * F z) := by
  obtain ⟨F, hF, hdecomp⟩ :=
    exists_suzukiChebyshevLaplacePoleClearedWindowAnalyticDecomposition hT
  refine ⟨F, hF, ?_⟩
  intro z hz
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedResponse
  rw [hdecomp z hz]
  unfold
    suzukiChebyshevLaplacePoleClearedWindowPrincipalSum
    suzukiChebyshevLaplacePoleClearedPrincipalPart
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
  rw [mul_add, Finset.mul_sum]

end

end RiemannGaussian
