import RiemannGaussian.FiniteToEntireLocalDivisor
import RiemannGaussian.FiniteToEntireRouche
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteLogNormFlux

/-!
# Rouché stability for finite paired-eta sums

The finite paired-eta sums converge locally uniformly only on the positive
half-plane, while the existing global Rouché theorem assumes entire
analyticity of both compared functions. This module proves the local form
needed at the eta frontier directly on an open analytic domain.

On every positive, zero-free eta circle, sufficiently long finite eta sums
are nonzero on the circle and have exactly the same logarithmic-derivative
circle integral as the limiting eta core. Applying the local argument
principle around a nontrivial zeta zero then gives one fixed isolating circle
on which every sufficiently long finite eta sum has contour winding equal to
the genuine analytic zeta-zero multiplicity.

This is exact divisor stability for the finite arithmetic approximants. It
does not bound the resulting multiplicities or exclude off-critical-line
zeros.
-/

open Complex Filter Metric Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- Locally uniform convergence gives strict Rouché domination on every
compact subset where the limiting function is continuous and nonzero. -/
theorem eventually_forall_norm_sub_lt_norm_on_compact_of_tendstoLocallyUniformlyOn
    {iota : Type*} {phi : Filter iota}
    {F : iota → ℂ → ℂ} {f : ℂ → ℂ} {U K : Set ℂ}
    (hF : TendstoLocallyUniformlyOn F f phi U)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContinuousOn f U) (hzero : ∀ w ∈ K, f w ≠ 0) :
    ∀ᶠ n in phi, ∀ w ∈ K, ‖F n w - f w‖ < ‖f w‖ := by
  have hnormContinuous : ContinuousOn (fun w ↦ ‖f w‖) K :=
    continuous_norm.comp_continuousOn (hf.mono hKU)
  have hnormPos : ∀ w ∈ K, 0 < ‖f w‖ := by
    intro w hw
    exact norm_pos_iff.mpr (hzero w hw)
  obtain ⟨delta, hdelta, hdeltaLe⟩ :=
    hK.exists_forall_le' hnormContinuous hnormPos
  have hUniform :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp
      hF K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hUniform
  filter_upwards [hUniform delta hdelta] with n hn
  intro w hw
  calc
    ‖F n w - f w‖ = dist (f w) (F n w) := by
      rw [dist_eq_norm, norm_sub_rev]
    _ < delta := hn w hw
    _ ≤ ‖f w‖ := hdeltaLe w hw

/-- Local Rouché domination on a circle inside an analytic domain forces
equality of logarithmic-derivative circle integrals. -/
theorem circleIntegral_logDeriv_eq_of_norm_sub_lt_of_analyticOnNhd
    {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hsphere : sphere c R ⊆ U)
    (hboundary : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    (∮ z in C(c, R), logDeriv g z) =
      ∮ z in C(c, R), logDeriv f z := by
  obtain ⟨hfzero, hgzero⟩ :=
    ne_zero_on_sphere_of_norm_sub_lt hboundary
  let q : ℂ → ℂ := fun z => g z / f z
  have hprimitive : ∀ z ∈ sphere c R,
      HasDerivWithinAt (fun u => Complex.log (q u))
        (logDeriv g z - logDeriv f z) (sphere c R) z := by
    intro z hz
    have hclose : ‖q z - 1‖ < 1 := by
      have hfnorm : 0 < ‖f z‖ := norm_pos_iff.mpr (hfzero z hz)
      have hform : q z - 1 = (g z - f z) / f z := by
        dsimp only [q]
        field_simp [hfzero z hz]
      rw [hform, norm_div]
      exact (div_lt_one hfnorm).mpr (hboundary z hz)
    have hreal : 0 < (q z).re := by
      have hre : |(q z).re - 1| < 1 := by
        calc
          |(q z).re - 1| = |(q z - 1).re| := by simp
          _ ≤ ‖q z - 1‖ := Complex.abs_re_le_norm _
          _ < 1 := hclose
      linarith [abs_lt.mp hre]
    have hslit : q z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl hreal
    have hfdiff : DifferentiableAt ℂ f z :=
      (hf z (hsphere hz)).differentiableAt
    have hgdiff : DifferentiableAt ℂ g z :=
      (hg z (hsphere hz)).differentiableAt
    have hqdiff : DifferentiableAt ℂ q z :=
      hgdiff.div hfdiff (hfzero z hz)
    have hlog := hqdiff.hasDerivAt.clog hslit
    have hquotient :
        logDeriv q z = logDeriv g z - logDeriv f z := by
      simpa [q] using
        (logDeriv_div z (hgzero z hz) (hfzero z hz) hgdiff hfdiff)
    have hlog' : HasDerivAt (fun u => Complex.log (q u))
        (logDeriv q z) z := by
      simpa [logDeriv_apply] using hlog
    rw [hquotient] at hlog'
    exact hlog'.hasDerivWithinAt
  have hzero :
      (∮ z in C(c, R), logDeriv g z - logDeriv f z) = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR hprimitive
  have hfContinuous : ContinuousOn (logDeriv f) (sphere c R) := by
    unfold logDeriv
    exact ((hf.deriv).continuousOn.mono hsphere).div₀
      (hf.continuousOn.mono hsphere) hfzero
  have hgContinuous : ContinuousOn (logDeriv g) (sphere c R) := by
    unfold logDeriv
    exact ((hg.deriv).continuousOn.mono hsphere).div₀
      (hg.continuousOn.mono hsphere) hgzero
  have hfIntegrable : CircleIntegrable (logDeriv f) c R :=
    hfContinuous.circleIntegrable hR
  have hgIntegrable : CircleIntegrable (logDeriv g) c R :=
    hgContinuous.circleIntegrable hR
  rw [circleIntegral.integral_sub hgIntegrable hfIntegrable] at hzero
  exact sub_eq_zero.mp hzero

/-- On any circle contained in the positive eta half-plane and avoiding the
limiting eta divisor, every sufficiently long finite eta sum is nonzero on
the circle and has exactly the limiting logarithmic-derivative integral. -/
theorem eventually_pairedEtaCorePartialSum_circle_nonzero_and_logDeriv_eq
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hgeometry : ∀ z ∈ sphere c R,
      0 < z.re ∧ pairedEtaCore z ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      (∀ z ∈ sphere c R, pairedEtaCorePartialSum N z ≠ 0) ∧
        (∮ z in C(c, R), logDeriv (pairedEtaCorePartialSum N) z) =
          ∮ z in C(c, R), logDeriv pairedEtaCore z := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU : IsOpen U := Complex.isOpen_re_gt 0
  have hsphere : sphere c R ⊆ U := fun z hz => (hgeometry z hz).1
  have hdomination : ∀ᶠ N : ℕ in atTop,
      ∀ z ∈ sphere c R,
        ‖pairedEtaCorePartialSum N z - pairedEtaCore z‖ <
          ‖pairedEtaCore z‖ :=
    eventually_forall_norm_sub_lt_norm_on_compact_of_tendstoLocallyUniformlyOn
      tendstoLocallyUniformlyOn_pairedEtaCorePartialSum hU
      (isCompact_sphere c R) hsphere
      analyticOnNhd_pairedEtaCore.continuousOn
      (fun z hz => (hgeometry z hz).2)
  filter_upwards [hdomination] with N hN
  have hnonzero := (ne_zero_on_sphere_of_norm_sub_lt hN).2
  refine ⟨hnonzero, ?_⟩
  apply circleIntegral_logDeriv_eq_of_norm_sub_lt_of_analyticOnNhd
    analyticOnNhd_pairedEtaCore
    (fun z _ => (differentiable_pairedEtaCorePartialSum N).analyticAt z)
    hR hsphere hN

/-- Below every prescribed positive radius around a nontrivial zeta zero,
there is one positive, isolating eta circle on which all sufficiently long
finite eta sums are nonzero and have logarithmic-derivative winding equal to
the genuine analytic zeta-zero multiplicity. -/
theorem exists_lt_eventually_pairedEtaCorePartialSum_logDeriv_eq_multiplicity
    (rho : NontrivialZetaZero) {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, 0 < R ∧ R < r ∧
      (∀ z ∈ closedBall rho.1 R, z ≠ rho.1 → pairedEtaCore z ≠ 0) ∧
      ∀ᶠ N : ℕ in atTop,
        (∀ z ∈ sphere rho.1 R,
          pairedEtaCorePartialSum N z ≠ 0) ∧
        (∮ z in C(rho.1, R), logDeriv (pairedEtaCorePartialSum N) z) =
          (analyticZetaZeroMultiplicity rho : ℂ) *
            (2 * Real.pi : ℝ) * Complex.I := by
  have hrho : 0 < rho.1.re := NontrivialZetaZero.zero_lt_re rho
  have hbound : 0 < min r (rho.1.re / 2) := by positivity
  have heta : AnalyticAt ℂ pairedEtaCore rho.1 :=
    analyticOnNhd_pairedEtaCore rho.1 hrho
  have hfinite : analyticOrderAt pairedEtaCore rho.1 ≠ ⊤ := by
    rw [analyticOrderAt_pairedEtaCore_eq_riemannZeta rho]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  obtain ⟨R, hR, hRbound, hzero, hIntegral⟩ :=
    AnalyticAt.exists_lt_circleIntegral_logDeriv_eq_order
      heta hfinite hbound
  have hRlt : R < r := hRbound.trans_le (min_le_left _ _)
  have hRre : R < rho.1.re / 2 :=
    hRbound.trans_le (min_le_right _ _)
  have hgeometry : ∀ z ∈ sphere rho.1 R,
      0 < z.re ∧ pairedEtaCore z ≠ 0 := by
    intro z hz
    have hdist : dist z rho.1 = R := mem_sphere.mp hz
    have hdiff : |z.re - rho.1.re| ≤ R := by
      calc
        |z.re - rho.1.re| = |(z - rho.1).re| := by simp
        _ ≤ ‖z - rho.1‖ := Complex.abs_re_le_norm _
        _ = dist z rho.1 := by rw [dist_eq_norm]
        _ = R := hdist
    have hzre : 0 < z.re := by
      linarith [neg_le_abs (z.re - rho.1.re)]
    have hzne : z ≠ rho.1 := by
      intro hzr
      subst z
      rw [mem_sphere, dist_self] at hz
      exact hR.ne' hz.symm
    exact ⟨hzre, hzero z (sphere_subset_closedBall hz) hzne⟩
  have heventually :=
    eventually_pairedEtaCorePartialSum_circle_nonzero_and_logDeriv_eq
      hR.le hgeometry
  refine ⟨R, hR, hRlt, hzero, ?_⟩
  filter_upwards [heventually] with N hN
  refine ⟨hN.1, ?_⟩
  calc
    (∮ z in C(rho.1, R), logDeriv (pairedEtaCorePartialSum N) z) =
        ∮ z in C(rho.1, R), logDeriv pairedEtaCore z := hN.2
    _ = (analyticOrderNatAt pairedEtaCore rho.1 : ℂ) *
        (2 * Real.pi : ℝ) * Complex.I := hIntegral
    _ = (analyticZetaZeroMultiplicity rho : ℂ) *
        (2 * Real.pi : ℝ) * Complex.I := by
      rw [analyticOrderNatAt_pairedEtaCore_eq_analyticZetaZeroMultiplicity rho]

end

end RiemannGaussian
