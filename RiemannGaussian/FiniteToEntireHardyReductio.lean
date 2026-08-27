import RiemannGaussian.FiniteToEntireHardyFrontier
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# From failure of RH to the finite Hardy frontier

This file removes a previously implicit premise from the finite-to-entire
Hardy route.  It proves that every upper-half-plane zero of an entire function
gives an upper-half-plane zero of `f + i * eta * f'` for some positive real
`eta`.  Multiple zeros are fixed by every member of the homotopy.  At a simple
zero, the analytic map

`z ↦ i * f z / f' z`

has derivative `i`, so its local inverse supplies the required homotopy root
for all sufficiently small parameters.

For spectral xi, failure of RH first gives an upper-half-plane zero using the
already checked spectral characterization and conjugation symmetry.  The
last theorem composes this fact with the root-pinned separable approximation
and finite Hardy results.  Thus the existing canonical finite frontier now
follows from `¬ RiemannHypothesis`; a positive homotopy root is no longer an
assumption at the reductio entry point.
-/

open Filter Polynomial Set
open scoped ComplexConjugate Topology

namespace RiemannGaussian

noncomputable section

/-- Near a simple root of `f`, this map uses the homotopy root as its
parameter: `eta = i f / f'`. -/
def analyticERootParameter (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * f z / deriv f z

/-- The complex-parameter version of the analytic homotopy. -/
def analyticEComplexValue (f : ℂ → ℂ) (eta z : ℂ) : ℂ :=
  f z + Complex.I * eta * deriv f z

theorem analyticERootParameter_analyticAt
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f z) (hderiv : deriv f z ≠ 0) :
    AnalyticAt ℂ (analyticERootParameter f) z := by
  unfold analyticERootParameter
  fun_prop

/-- At a simple root, the root-parameter map has derivative `i`, hence is
locally invertible. -/
theorem analyticERootParameter_hasDerivAt_of_root
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z : ℂ}
    (hroot : f z = 0) (hderiv : deriv f z ≠ 0) :
    HasDerivAt (analyticERootParameter f) Complex.I z := by
  have hdf : Differentiable ℂ (deriv f) := by
    simpa only [differentiableOn_univ] using
      hf.differentiableOn.deriv isOpen_univ
  have hparamdiff : DifferentiableAt ℂ (analyticERootParameter f) z :=
    (analyticERootParameter_analyticAt (hf.analyticAt z) hderiv).differentiableAt
  have hcalc : deriv (analyticERootParameter f) z = Complex.I := by
    rw [show analyticERootParameter f =
        fun w ↦ (Complex.I * f w) / deriv f w by rfl,
      deriv_fun_div ((hf z).const_mul Complex.I) (hdf z) hderiv,
      deriv_const_mul_field, hroot]
    field_simp
    ring
  rw [← hcalc]
  exact hparamdiff.hasDerivAt

@[simp] theorem analyticERootParameter_zero_of_root
    {f : ℂ → ℂ} {z : ℂ} (hroot : f z = 0) :
    analyticERootParameter f z = 0 := by
  simp [analyticERootParameter, hroot]

/-- A simple root admits a locally convergent complex-parameter curve of
exact homotopy roots. -/
theorem exists_analyticE_root_germ_of_simple_root
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    (hroot : f z₀ = 0) (hsimple : deriv f z₀ ≠ 0) :
    ∃ rootCurve : ℂ → ℂ,
      Tendsto rootCurve (𝓝 0) (𝓝 z₀) ∧
      ∀ᶠ eta in 𝓝 0,
        analyticEComplexValue f eta (rootCurve eta) = 0 := by
  let g : ℂ → ℂ := analyticERootParameter f
  have hgan : AnalyticAt ℂ g z₀ :=
    analyticERootParameter_analyticAt (hf.analyticAt z₀) hsimple
  have hgderiv : deriv g z₀ = Complex.I :=
    (analyticERootParameter_hasDerivAt_of_root hf hroot hsimple).deriv
  have hgderiv_ne : deriv g z₀ ≠ 0 := by
    rw [hgderiv]
    exact Complex.I_ne_zero
  have hgzero : g z₀ = 0 :=
    analyticERootParameter_zero_of_root hroot
  let rootCurve : ℂ → ℂ :=
    hgan.hasStrictDerivAt.localInverse g (deriv g z₀) z₀ hgderiv_ne
  have hcurve : Tendsto rootCurve (𝓝 0) (𝓝 z₀) := by
    rw [← hgzero]
    exact HasStrictFDerivAt.localInverse_tendsto
      (hgan.hasStrictDerivAt.hasStrictFDerivAt_equiv hgderiv_ne)
  have hinverse : ∀ᶠ eta in 𝓝 0, g (rootCurve eta) = eta := by
    rw [← hgzero]
    exact hgan.hasStrictDerivAt.eventually_right_inverse hgderiv_ne
  have hdfcont : Continuous (deriv f) := by
    exact (show Differentiable ℂ (deriv f) by
      simpa only [differentiableOn_univ] using
        hf.differentiableOn.deriv isOpen_univ).continuous
  have hderivEventually :
      ∀ᶠ eta in 𝓝 0, deriv f (rootCurve eta) ≠ 0 :=
    hcurve.eventually (hdfcont.continuousAt.eventually_ne hsimple)
  refine ⟨rootCurve, hcurve, ?_⟩
  filter_upwards [hinverse, hderivEventually] with eta heta hne
  have hquot : Complex.I * f (rootCurve eta) =
      eta * deriv f (rootCurve eta) := by
    apply (div_eq_iff hne).mp
    simpa [g, analyticERootParameter] using heta
  unfold analyticEComplexValue
  calc
    f (rootCurve eta) + Complex.I * eta * deriv f (rootCurve eta) =
        f (rootCurve eta) + Complex.I *
          (Complex.I * f (rootCurve eta)) := by rw [hquot]; ring
    _ = 0 := by rw [← mul_assoc, Complex.I_mul_I]; ring

/-- A simple upper-half-plane root persists as an upper-half-plane root of
`f + i eta f'` for at least one positive real parameter. -/
theorem exists_positive_analyticEValue_upper_root_of_simple_root
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im) (hroot : f z₀ = 0)
    (hsimple : deriv f z₀ ≠ 0) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ,
      0 < z.im ∧ analyticEValue f eta z = 0 := by
  obtain ⟨rootCurve, hcurve, hrootCurve⟩ :=
    exists_analyticE_root_germ_of_simple_root hf hroot hsimple
  have hupper : ∀ᶠ e in 𝓝 (0 : ℂ), 0 < (rootCurve e).im :=
    hcurve.eventually
      (Complex.continuous_im.continuousAt.eventually (lt_mem_nhds hz₀))
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff.mp (hrootCurve.and hupper)
  let eta : ℝ := r / 2
  have heta : 0 < eta := half_pos hr
  have hdist : dist (↑eta : ℂ) 0 < r := by
    simpa [eta, abs_of_pos hr] using half_lt_self hr
  have hgood := hball hdist
  refine ⟨eta, heta, rootCurve (eta : ℂ), hgood.2, ?_⟩
  simpa [analyticEComplexValue, analyticEValue] using hgood.1

/-- Every upper-half-plane zero of an entire function yields an upper root
of a positive member of the `f + i eta f'` homotopy.  Multiple roots are
fixed by the homotopy; simple roots persist by a local analytic inverse. -/
theorem exists_positive_analyticEValue_upper_root_of_root
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    (hz₀ : 0 < z₀.im) (hroot : f z₀ = 0) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ,
      0 < z.im ∧ analyticEValue f eta z = 0 := by
  by_cases hsimple : deriv f z₀ = 0
  · refine ⟨1, zero_lt_one, z₀, hz₀, ?_⟩
    simp [analyticEValue, hroot, hsimple]
  · exact exists_positive_analyticEValue_upper_root_of_simple_root
      hf hz₀ hroot hsimple

/-- RH is equivalent to saying that every zero of spectral xi lies on the
real spectral axis. -/
theorem riemannHypothesis_iff_riemannXiSpectral_zero_im_eq_zero :
    RiemannHypothesis ↔
      ∀ z : ℂ, riemannXiSpectral z = 0 → z.im = 0 := by
  constructor
  · intro hRH z hz
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero z).mp hz
    exact (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
      rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  · intro hzeros
    apply riemannHypothesis_iff_spectralCoordinate_real.mpr
    intro s hs hnontrivial hone
    let rho : NontrivialZetaZero :=
      ⟨s, hs, hnontrivial, hone⟩
    exact hzeros (zetaSpectralCoordinate s)
      ((riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr
        ⟨rho, rfl⟩)

/-- Failure of RH supplies an upper-half-plane zero of spectral xi.  If the
first nonreal zero obtained from negating the spectral characterization lies
below the axis, conjugation reflects it upward. -/
theorem exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ z : ℂ, riemannXiSpectral z = 0 ∧ 0 < z.im := by
  have hnot : ¬ ∀ z : ℂ, riemannXiSpectral z = 0 → z.im = 0 := by
    intro h
    exact hRH
      (riemannHypothesis_iff_riemannXiSpectral_zero_im_eq_zero.mpr h)
  push Not at hnot
  obtain ⟨z, hz, him⟩ := hnot
  by_cases hpos : 0 < z.im
  · exact ⟨z, hz, hpos⟩
  · refine ⟨conj z, ?_, ?_⟩
    · simpa using congrArg conj hz
    · rw [Complex.conj_im]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) him)

/-- A failure of RH therefore reaches the established positive-homotopy
frontier without assuming the existence of a homotopy root. -/
theorem exists_positive_riemannXiSpectral_analyticEValue_upper_root_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ,
      0 < z.im ∧ analyticEValue riemannXiSpectral eta z = 0 := by
  obtain ⟨z₀, hroot, hz₀⟩ :=
    exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
  exact exists_positive_analyticEValue_upper_root_of_root
    differentiable_riemannXiSpectral hz₀ hroot

/-- Fully composed reductio entry point: if RH fails, one positive spectral-xi
homotopy and one upper root yield a fully checked sequence of separable,
root-pinned finite models carrying the complete canonical Hardy frontier. -/
theorem exists_canonicalFiniteHardyFrontier_sequence_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        ∀ n, CanonicalFiniteHardyFrontier (B n) eta z := by
  obtain ⟨eta, heta, z, hz, hroot⟩ :=
    exists_positive_riemannXiSpectral_analyticEValue_upper_root_of_not_rh hRH
  obtain ⟨B, hB, hfrontier⟩ :=
    exists_riemannXiSpectral_canonicalFiniteHardyFrontier_sequence
      heta hz hroot
  exact ⟨eta, heta, z, hz, B, hB, hfrontier⟩

end

end RiemannGaussian
