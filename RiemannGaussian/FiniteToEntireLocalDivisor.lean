import RiemannGaussian.FiniteToEntireRootCountCircle

/-!
# Local divisor identification for polynomial approximants

This file identifies the stabilized polynomial root counts from the preceding
circle-integral passage with the genuine analytic multiplicity of the limiting
entire function.  It first proves a local argument principle directly from the
analytic principal-part decomposition of `f'/f`.  Consequently, every
spectral-xi zero has a fixed isolating ball in which the approximants carry
exactly its analytic zeta multiplicity.  The result applies simultaneously to
the same root-pinned canonical Hardy sequence forced by failure of RH.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The local argument principle on some sufficiently small circle around
one finite-order analytic point. -/
theorem AnalyticAt.exists_circleIntegral_logDeriv_eq_order
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hfinite : analyticOrderAt f a ≠ ⊤) :
    ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ closedBall a R, z ≠ a → f z ≠ 0) ∧
        (∮ z in C(a, R), logDeriv f z) =
          (analyticOrderNatAt f a : ℂ) *
            (2 * Real.pi : ℝ) * Complex.I := by
  obtain ⟨h, hh, heq⟩ :=
    AnalyticAt.exists_logDeriv_eq_principalPart_add_analytic hf hfinite
  have hhan : ∀ᶠ z in 𝓝 a, AnalyticAt ℂ h z :=
    hh.eventually_analyticAt
  have heq' : ∀ᶠ z in 𝓝 a, z ≠ a →
      logDeriv f z =
        (analyticOrderNatAt f a : ℂ) / (z - a) + h z := by
    change ∀ᶠ z in 𝓝[≠] a,
      logDeriv f z =
        (analyticOrderNatAt f a : ℂ) / (z - a) + h z at heq
    rw [eventually_nhdsWithin_iff] at heq
    exact heq
  have hfne : ∀ᶠ z in 𝓝[≠] a, f z ≠ 0 :=
    hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hzero ↦
      hfinite (analyticOrderAt_eq_top.mpr hzero)
  have hfne' : ∀ᶠ z in 𝓝 a, z ≠ a → f z ≠ 0 := by
    rw [eventually_nhdsWithin_iff] at hfne
    exact hfne
  have hlocal : ∀ᶠ z in 𝓝 a,
      AnalyticAt ℂ h z ∧
        (z ≠ a → logDeriv f z =
          (analyticOrderNatAt f a : ℂ) / (z - a) + h z) ∧
        (z ≠ a → f z ≠ 0) :=
    by
      filter_upwards [hhan, heq', hfne'] with z hzAnalytic hzEq hzNe
      exact ⟨hzAnalytic, hzEq, hzNe⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hlocal
  let R := ε / 2
  have hR : 0 < R := by positivity
  have hclosed : closedBall a R ⊆ ball a ε := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    dsimp [R] at hz ⊢
    linarith
  have hanalytic : ∀ z ∈ closedBall a R, AnalyticAt ℂ h z := by
    intro z hz
    exact (hεsub (hclosed hz)).1
  have hfzero : ∀ z ∈ closedBall a R, z ≠ a → f z ≠ 0 := by
    intro z hz hza
    exact (hεsub (hclosed hz)).2.2 hza
  have hEqSphere : ∀ z ∈ sphere a R,
      logDeriv f z =
        (analyticOrderNatAt f a : ℂ) / (z - a) + h z := by
    intro z hz
    apply (hεsub (hclosed (sphere_subset_closedBall hz))).2.1
    intro hza
    subst z
    rw [mem_sphere, dist_self] at hz
    exact hR.ne' hz.symm
  have hprincipal : CircleIntegrable
      (fun z ↦ (analyticOrderNatAt f a : ℂ) / (z - a)) a R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply continuousOn_const.div₀
      (continuousOn_id.sub continuousOn_const)
    intro z hz
    change z - a ≠ 0
    intro hsub
    have hza : z = a := sub_eq_zero.mp hsub
    subst z
    rw [mem_sphere, dist_self] at hz
    exact hR.ne' hz.symm
  have hhCircle : CircleIntegrable h a R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact (hanalytic z (sphere_subset_closedBall hz)).continuousAt.continuousWithinAt
  have hhIntegral : (∮ z in C(a, R), h z) = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable
      hR.le countable_empty
    · intro z hz
      exact (hanalytic z hz).continuousAt.continuousWithinAt
    · intro z hz
      exact (hanalytic z (ball_subset_closedBall hz.1)).differentiableAt
  refine ⟨R, hR, hfzero, ?_⟩
  rw [circleIntegral.integral_congr hR.le hEqSphere,
    circleIntegral.integral_add hprincipal hhCircle, hhIntegral, add_zero]
  simp only [div_eq_mul_inv, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_center_inv a hR.ne']
  push_cast
  ring

/-- Locally uniform real-polynomial approximants eventually carry exactly
the analytic multiplicity of the limiting function in a sufficiently small
ball around a finite-order point. -/
theorem AnalyticAt.exists_eventuallyEq_realPolynomialRootCountInBall_order
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X]) {f : ℂ → ℂ} {a : ℂ}
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      f phi Set.univ)
    (hf : AnalyticAt ℂ f a) (hfinite : analyticOrderAt f a ≠ ⊤) :
    ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ closedBall a R, z ≠ a → f z ≠ 0) ∧
      ∀ᶠ n in phi,
        realPolynomialRootCountInBall (A n) a R =
          analyticOrderNatAt f a := by
  obtain ⟨R, hR, hzero, hIntegralOrder⟩ :=
    AnalyticAt.exists_circleIntegral_logDeriv_eq_order hf hfinite
  have hhol : ∀ᶠ n in phi, DifferentiableOn ℂ
      (fun w ↦ ((A n).map Complex.ofRealHom).eval w) Set.univ :=
    Eventually.of_forall fun n ↦
      ((A n).map Complex.ofRealHom).differentiableOn
  have hfdiff : Differentiable ℂ f := by
    rw [← differentiableOn_univ]
    exact hA.differentiableOn hhol isOpen_univ
  let U : Set ℂ := {z | f z ≠ 0}
  have hU : IsOpen U := isOpen_ne.preimage hfdiff.continuous
  have hzeroU : ∀ z ∈ U, f z ≠ 0 := fun _ hz ↦ hz
  have hsphere : sphere a R ⊆ U := by
    intro z hz
    apply hzero z (sphere_subset_closedBall hz)
    intro hza
    subst z
    rw [mem_sphere, dist_self] at hz
    exact hR.ne' hz.symm
  obtain ⟨m, hm, hIntegralM⟩ :=
    exists_eventuallyEq_realPolynomialRootCountInBall_of_tendstoLocallyUniformlyOn
      A (hA.mono (subset_univ U)) hU hzeroU a hR.le hsphere
  have hscale : ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
    have htwoPi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
    exact mul_ne_zero htwoPi Complex.I_ne_zero
  have hmCast : (m : ℂ) = (analyticOrderNatAt f a : ℂ) := by
    apply mul_right_cancel₀ hscale
    calc
      (m : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I) =
          (m : ℂ) * (2 * Real.pi : ℝ) * Complex.I := by ring
      _ = (∮ z in C(a, R), logDeriv f z) := hIntegralM.symm
      _ = (analyticOrderNatAt f a : ℂ) *
          (2 * Real.pi : ℝ) * Complex.I := hIntegralOrder
      _ = (analyticOrderNatAt f a : ℂ) *
          (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := by ring
  have hmOrder : m = analyticOrderNatAt f a := by
    exact_mod_cast hmCast
  refine ⟨R, hR, hzero, ?_⟩
  filter_upwards [hm] with n hn
  exact hn.trans hmOrder

/-- Every spectral xi zero has a fixed small ball in which globally
convergent real-polynomial approximants eventually carry exactly its genuine
analytic zeta multiplicity. -/
theorem exists_eventuallyEq_riemannXiSpectral_localRootCount
    {ι : Type*} {phi : Filter ι} [phi.NeBot] [phi.IsCountablyGenerated]
    (A : ι → ℝ[X])
    (hA : TendstoLocallyUniformlyOn
      (fun n w ↦ ((A n).map Complex.ofRealHom).eval w)
      riemannXiSpectral phi Set.univ)
    (rho : NontrivialZetaZero) :
    ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ closedBall (zetaSpectralCoordinate rho.1) R,
        z ≠ zetaSpectralCoordinate rho.1 → riemannXiSpectral z ≠ 0) ∧
      ∀ᶠ n in phi,
        realPolynomialRootCountInBall (A n)
          (zetaSpectralCoordinate rho.1) R =
            analyticZetaZeroMultiplicity rho := by
  have hfinite : analyticOrderAt riemannXiSpectral
      (zetaSpectralCoordinate rho.1) ≠ ⊤ := by
    rw [analyticOrderAt_riemannXiSpectral_zetaSpectralCoordinate,
      analyticOrderAt_riemannXi_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  obtain ⟨R, hR, hzero, hcount⟩ :=
    AnalyticAt.exists_eventuallyEq_realPolynomialRootCountInBall_order
      A hA (analyticAt_riemannXiSpectral
        (zetaSpectralCoordinate rho.1)) hfinite
  refine ⟨R, hR, hzero, ?_⟩
  simpa only
    [analyticOrderNatAt_riemannXiSpectral_zetaSpectralCoordinate] using
      hcount

/-- Under failure of RH, the same root-pinned canonical Hardy sequence
recovers the exact analytic multiplicity of every spectral xi zero in a
sufficiently small fixed ball around that zero. -/
theorem exists_canonicalFiniteHardyFrontier_localRootCounts_of_not_rh
    (hRH : ¬RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        ∀ rho : NontrivialZetaZero,
          ∃ R : ℝ, 0 < R ∧
            (∀ w ∈ closedBall (zetaSpectralCoordinate rho.1) R,
              w ≠ zetaSpectralCoordinate rho.1 →
                riemannXiSpectral w ≠ 0) ∧
            ∀ᶠ n in atTop,
              realPolynomialRootCountInBall (B n)
                (zetaSpectralCoordinate rho.1) R =
                  analyticZetaZeroMultiplicity rho := by
  obtain ⟨eta, heta, z, hz, B, hB, hfrontier⟩ :=
    exists_canonicalFiniteHardyFrontier_sequence_of_not_rh hRH
  refine ⟨eta, heta, z, hz, B, hB, hfrontier, ?_⟩
  intro rho
  exact exists_eventuallyEq_riemannXiSpectral_localRootCount B hB rho

end

end RiemannGaussian
