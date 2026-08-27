import RiemannGaussian.FiniteToEntireHeatFrontier
import RiemannGaussian.RiemannXiHyperbolicHeatWindow
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Zero-free logarithmic-derivative convergence

This file proves the analytic prerequisite for transporting finite root
divisors to spectral xi.  Locally uniform convergence of holomorphic
functions gives locally uniform convergence of their logarithmic derivatives
on every open region where the limiting function has no zero.  It is then
applied to the exact separable, root-pinned polynomial sequence forced by
failure of RH.

No passage through a limiting zero is asserted here.  Multiplicity-preserving
zero-count stability across a zero-free boundary is the next step.
-/

open Complex Filter Metric Polynomial Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- Locally uniform holomorphic convergence passes to logarithmic
derivatives on every zero-free open region. -/
theorem logDeriv_tendstoLocallyUniformlyOn
    {ι : Type*} {phi : Filter ι} [phi.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hF : TendstoLocallyUniformlyOn F f phi U)
    (hhol : ∀ᶠ n in phi, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) (hzero : ∀ w ∈ U, f w ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n ↦ logDeriv (F n)) (logDeriv f) phi U := by
  have hfdiff : DifferentiableOn ℂ f U :=
    hF.differentiableOn hhol hU
  have hderiv := hF.deriv hhol hU
  have hquotient := hderiv.div₀ hF
    (hfdiff.deriv hU).continuousOn hfdiff.continuousOn hzero
  refine (hquotient.congr
    (G := fun n ↦ logDeriv (F n)) ?_).congr_right ?_
  · intro n w _
    rfl
  · intro w _
    rfl

/-- On a compact subset where the limit has no zero, all sufficiently late
approximants are themselves zero-free. -/
theorem eventually_forall_ne_zero_on_compact_of_tendstoLocallyUniformlyOn
    {ι : Type*} {phi : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U K : Set ℂ}
    (hF : TendstoLocallyUniformlyOn F f phi U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContinuousOn f U) (hzero : ∀ w ∈ U, f w ≠ 0) :
    ∀ᶠ n in phi, ∀ w ∈ K, F n w ≠ 0 := by
  have hnormContinuous : ContinuousOn (fun w ↦ ‖f w‖) K :=
    continuous_norm.comp_continuousOn (hf.mono hKU)
  have hnormPos : ∀ w ∈ K, 0 < ‖f w‖ := by
    intro w hw
    exact norm_pos_iff.mpr (hzero w (hKU hw))
  obtain ⟨delta, hdelta, hdeltaLe⟩ :=
    hK.exists_forall_le' hnormContinuous hnormPos
  have hUniform :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hF K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hUniform
  filter_upwards [hUniform delta hdelta] with n hn
  intro w hw hFn
  have hdist := hn w hw
  rw [hFn, dist_zero_right] at hdist
  exact (not_lt_of_ge (hdeltaLe w hw)) hdist

/-- The approximant logarithmic derivatives are eventually continuous on
every compact zero-free subset. -/
theorem eventually_logDeriv_continuousOn_compact
    {ι : Type*} {phi : Filter ι} [phi.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U K : Set ℂ}
    (hF : TendstoLocallyUniformlyOn F f phi U)
    (hhol : ∀ᶠ n in phi, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hzero : ∀ w ∈ U, f w ≠ 0) :
    ∀ᶠ n in phi, ContinuousOn (logDeriv (F n)) K := by
  have hfdiff : DifferentiableOn ℂ f U :=
    hF.differentiableOn hhol hU
  have hFnzero :=
    eventually_forall_ne_zero_on_compact_of_tendstoLocallyUniformlyOn
      hF hU hK hKU hfdiff.continuousOn hzero
  filter_upwards [hhol, hFnzero] with n hnDiff hnZero
  have hderivContinuous : ContinuousOn (deriv (F n)) K :=
    (hnDiff.deriv hU).continuousOn.mono hKU
  have hfunctionContinuous : ContinuousOn (F n) K :=
    hnDiff.continuousOn.mono hKU
  unfold logDeriv
  exact (hderivContinuous.div₀ hfunctionContinuous hnZero).congr
    fun _ _ ↦ rfl

/-- Logarithmic-derivative circle integrals converge across any compact
circle contained in a zero-free open region. -/
theorem tendsto_circleIntegral_logDeriv_of_tendstoLocallyUniformlyOn
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hF : TendstoLocallyUniformlyOn F f phi U)
    (hhol : ∀ᶠ n in phi, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) (hzero : ∀ w ∈ U, f w ≠ 0)
    (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (hsphere : sphere c R ⊆ U) :
    Tendsto
      (fun n ↦ ∮ w in C(c, R), logDeriv (F n) w) phi
      (nhds (∮ w in C(c, R), logDeriv f w)) := by
  have hlog := logDeriv_tendstoLocallyUniformlyOn hF hhol hU hzero
  have hUniform :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp
      hlog (sphere c R) hsphere (isCompact_sphere c R)
  have hcontinuous := eventually_logDeriv_continuousOn_compact
    hF hhol hU (isCompact_sphere c R) hsphere hzero
  exact hUniform.tendsto_circleIntegral_of_continuousOn hR hcontinuous

/-- Polynomial specialization of zero-free logarithmic-derivative
convergence. -/
theorem realPolynomial_logDeriv_tendstoLocallyUniformlyOn
    {ι : Type*} {phi : Filter ι} [phi.NeBot]
    (A : ι → ℝ[X]) {f : ℂ → ℂ} {U : Set ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w) f phi U)
    (hU : IsOpen U) (hzero : ∀ w ∈ U, f w ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n ↦ logDeriv
        (fun w ↦ ((A n).map Complex.ofRealHom).eval w))
      (logDeriv f) phi U := by
  exact logDeriv_tendstoLocallyUniformlyOn hA
    (Eventually.of_forall fun n ↦
      ((A n).map Complex.ofRealHom).differentiableOn)
    hU hzero

/-- Circle-integral specialization for a locally uniformly convergent
sequence of real polynomials. -/
theorem realPolynomial_circleIntegral_logDeriv_tendsto
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X]) {f : ℂ → ℂ} {U : Set ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w) f phi U)
    (hU : IsOpen U) (hzero : ∀ w ∈ U, f w ≠ 0)
    (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (hsphere : sphere c R ⊆ U) :
    Tendsto
      (fun n ↦ ∮ w in C(c, R),
        logDeriv (fun u ↦ ((A n).map Complex.ofRealHom).eval u) w) phi
      (nhds (∮ w in C(c, R), logDeriv f w)) := by
  exact tendsto_circleIntegral_logDeriv_of_tendstoLocallyUniformlyOn
    hA
    (Eventually.of_forall fun n ↦
      ((A n).map Complex.ofRealHom).differentiableOn)
    hU hzero c hR hsphere

/-- Real polynomial approximants to spectral xi have locally uniformly
convergent logarithmic derivatives on every zero-free open region. -/
theorem riemannXiSpectral_polynomial_logDeriv_tendstoLocallyUniformlyOn
    {ι : Type*} {phi : Filter ι} [phi.NeBot]
    (A : ι → ℝ[X]) {U : Set ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi U)
    (hU : IsOpen U) (hzero : ∀ w ∈ U, riemannXiSpectral w ≠ 0) :
    TendstoLocallyUniformlyOn
      (fun n ↦ logDeriv
        (fun w ↦ ((A n).map Complex.ofRealHom).eval w))
      (logDeriv riemannXiSpectral) phi U :=
  realPolynomial_logDeriv_tendstoLocallyUniformlyOn A hA hU hzero

/-- Spectral-xi specialization of convergence of logarithmic-derivative
circle integrals. -/
theorem riemannXiSpectral_polynomial_circleIntegral_logDeriv_tendsto
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X]) {U : Set ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi U)
    (hU : IsOpen U)
    (hzero : ∀ w ∈ U, riemannXiSpectral w ≠ 0)
    (c : ℂ) {R : ℝ} (hR : 0 ≤ R) (hsphere : sphere c R ⊆ U) :
    Tendsto
      (fun n ↦ ∮ w in C(c, R),
        logDeriv (fun u ↦ ((A n).map Complex.ofRealHom).eval u) w) phi
      (nhds (∮ w in C(c, R), logDeriv riemannXiSpectral w)) :=
  realPolynomial_circleIntegral_logDeriv_tendsto
    A hA hU hzero c hR hsphere

/-- Under failure of RH, the same exact root-pinned finite Hardy sequence has
logarithmic derivatives converging locally uniformly to `xi'/xi` on every
zero-free open region. -/
theorem exists_canonicalFiniteHardyFrontier_logDeriv_sequence_of_not_rh
    (hRH : ¬RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        ∀ U : Set ℂ, IsOpen U →
          (∀ w ∈ U, riemannXiSpectral w ≠ 0) →
          TendstoLocallyUniformlyOn
            (fun n ↦ logDeriv
              (fun w ↦ ((B n).map Complex.ofRealHom).eval w))
            (logDeriv riemannXiSpectral) atTop U := by
  obtain ⟨eta, heta, z, hz, B, hB, hfrontier⟩ :=
    exists_canonicalFiniteHardyFrontier_sequence_of_not_rh hRH
  refine ⟨eta, heta, z, hz, B, hB, hfrontier, ?_⟩
  intro U hU hzero
  exact riemannXiSpectral_polynomial_logDeriv_tendstoLocallyUniformlyOn
    B (hB.mono (subset_univ U)) hU hzero

end

end RiemannGaussian
