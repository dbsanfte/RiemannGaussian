/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ComplexAngularResolvent

/-!
# The actual reflection remainder and its angular leading term

One analytic carrier chart works for every smoothing parameter on one
fixed neighborhood. It identifies the complete weight-derivative remainder
with a second angular harmonic whose two coefficients are smooth and
independent of smoothing. The companion heat term remains explicit.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- One carrier chart simultaneously controls the carrier and its coupled
mass for every real smoothing parameter, including at the selected zero. -/
theorem exists_suzukiXiCarrier_uniform_mass_chart (rho : NontrivialZetaZero) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (zetaSpectralCoordinate rho.1) ∧
      q (zetaSpectralCoordinate rho.1) = (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ∧
      ∀ᶠ z in 𝓝 (zetaSpectralCoordinate rho.1), ∀ r : ℝ,
        suzukiXiSmoothCarrier r z =
          ((z - zetaSpectralCoordinate rho.1) * q z) /
            ((1 + r^2 * normSq ((z - zetaSpectralCoordinate rho.1) * q z) : ℝ) : ℂ) ∧
        (suzukiXiNormalizedMass r z : ℂ) * suzukiXiSmoothCarrier r z =
          (z - zetaSpectralCoordinate rho.1)^2 *
            (q z^2 * starRingEnd ℂ ((z - zetaSpectralCoordinate rho.1) * q z)) /
              ((1 + r^2 * normSq ((z - zetaSpectralCoordinate rho.1) * q z) : ℝ) : ℂ)^2 := by
  obtain ⟨q, p, hq, _hp, hq0, _hp0, he⟩ := exists_suzukiXiCarrier_pair_local_model rho
  refine ⟨q, hq, hq0, ?_⟩
  filter_upwards [eventually_nhdsWithin_iff.mp he] with z hz r
  by_cases hza : z = zetaSpectralCoordinate rho.1
  · subst z
    have hA := (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨rho, rfl⟩
    rw [suzukiXiSmoothCarrier_eq_zero_of_xi_zero r hA, suzukiXiNormalizedMass_eq_zero r hA]
    simp
  · have hlocal := hz hza
    constructor
    · rw [suzukiXiSmoothCarrier_eq_radial r hlocal.1, hlocal.2.2.1]
    · rw [suzukiXiNormalizedMass_eq_regular_chart r hlocal.1,
        suzukiXiSmoothCarrier_eq_radial r hlocal.1, hlocal.2.2.1, ofReal_div,
        ← mul_conj]
      ring

/-- The full reflection heat weight has a smooth double-pole numerator
with its exact signed Gaussian value at the selected node. -/
theorem exists_suzukiXiReflectionHeat_node_numerator (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∃ g : ℂ → ℂ, ContDiffAt ℝ ∞ g (zetaSpectralCoordinate rho.1) ∧
      g (zetaSpectralCoordinate rho.1) =
        -suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) ∧
      (fun z => suzukiXiReflectionWeight rho z * suzukiSmoothSpectralBoundaryHeat c tau z)
        =ᶠ[𝓝[≠] (zetaSpectralCoordinate rho.1)]
          fun z => g z / (z - zetaSpectralCoordinate rho.1)^2 := by
  let a := zetaSpectralCoordinate rho.1
  let b := starRingEnd ℂ a
  let t := fun z : ℂ => (z-a)/(z-b)-1
  let g := fun z : ℂ => -(t z)^2 * suzukiSmoothSpectralBoundaryHeat c tau z
  have hab : a ≠ b := by
    intro he
    have hi := congrArg Complex.im he
    change a.im = -a.im at hi
    exact him (by linarith)
  have ht : ContDiffAt ℝ ∞ t a := by
    have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => z-a) a := contDiffAt_id.sub contDiffAt_const
    have h2 : ContDiffAt ℝ ∞ (fun z : ℂ => z-b) a := contDiffAt_id.sub contDiffAt_const
    simpa only [t, div_eq_mul_inv] using
      (h1.mul (h2.fun_inv (sub_ne_zero.mpr hab))).sub contDiffAt_const
  refine ⟨g, (ht.pow 2).neg.mul (contDiff_suzukiSmoothSpectralBoundaryHeat c tau).contDiffAt,
    by simp [g, t, a], ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (continuousAt_id.eventually_ne hab).filter_mono nhdsWithin_le_nhds] with z hza hzb
  have ha := sub_ne_zero.mpr hza
  have hb := sub_ne_zero.mpr hzb
  unfold suzukiXiReflectionWeight suzukiXiReflectionCauchyDifference
  dsimp only [g, t, a, b] at ha hb ⊢
  field_simp
  ring

private lemma horizontal_deriv_local_double_pole {P g : ℂ → ℂ} {a z : ℂ}
    (he : P =ᶠ[𝓝 z] fun w => g w / (w-a)^2)
    (hg : DifferentiableAt ℝ g z) (hz : z ≠ a) :
    deriv (fun x : ℝ => P ((x : ℂ) + (z.im : ℂ)*I)) z.re =
      ((z-a)*fderiv ℝ g z 1 - 2*g z)/(z-a)^3 := by
  have hl : HasDerivAt (fun x : ℝ => (x : ℂ) + (z.im : ℂ)*I) 1 z.re :=
    Complex.ofRealCLM.hasDerivAt.add_const _
  have hline : (z.re : ℂ) + (z.im : ℂ)*I = z := Complex.re_add_im z
  have hgl := hg.hasFDerivAt.comp_hasDerivAt_of_eq z.re hl hline.symm
  have hdl := ((hl.sub_const a).pow 2)
  have hn : (((z.re : ℂ) + (z.im : ℂ)*I)-a)^2 ≠ 0 := by
    rw [hline]
    exact pow_ne_zero 2 (sub_ne_zero.mpr hz)
  have hlt : Tendsto (fun x : ℝ => (x : ℂ) + (z.im : ℂ)*I) (𝓝 z.re) (𝓝 z) := by
    simpa only [ContinuousAt, hline] using hl.continuousAt
  have he' := he.comp_tendsto hlt
  have hd := (hgl.div hdl hn).congr_of_eventuallyEq he'
  dsimp only [Function.comp_def, Pi.pow_apply] at hd
  rw [hd.deriv]
  simp only [hline, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp

/-- The actual complete remainder has an exact local angular decomposition.
Both coefficients and the neighborhood work for all smoothing radii. The
central values retain the Gaussian source and the original multiplicity. -/
theorem exists_suzukiXiReflectionMassRemainder_angular_chart
    (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∃ (N : ℂ → ℂ) (Q : ℂ → ℝ),
      ContDiffAt ℝ ∞ N (zetaSpectralCoordinate rho.1) ∧
      ContDiffAt ℝ ∞ Q (zetaSpectralCoordinate rho.1) ∧
      N (zetaSpectralCoordinate rho.1) =
        4*I*suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) /
          (analyticZetaZeroMultiplicity rho : ℂ)^3 ∧
      Q (zetaSpectralCoordinate rho.1) = 1 / (analyticZetaZeroMultiplicity rho : ℝ)^2 ∧
      ∀ᶠ z in 𝓝[≠] (zetaSpectralCoordinate rho.1), ∀ r : ℝ,
        suzukiXiPlanarReflectionMassRemainder rho r c tau z =
          N z * complexAngularResolventKernel r (Q z) (z - zetaSpectralCoordinate rho.1) +
            I * suzukiXiReflectionWeight rho z * suzukiXiSmoothCarrier r z *
              suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource c tau (I*z) := by
  obtain ⟨q, hq, hq0, heq⟩ := exists_suzukiXiCarrier_uniform_mass_chart rho
  obtain ⟨g, hg, hg0, heg⟩ := exists_suzukiXiReflectionHeat_node_numerator rho c tau him
  let a := zetaSpectralCoordinate rho.1
  let N := fun z : ℂ => 2*I*((z-a)*fderiv ℝ g z 1 - 2*g z)*q z^2*starRingEnd ℂ (q z)
  let Q := fun z : ℂ => normSq (q z)
  have hqR : ContDiffAt ℝ ∞ q a := hq.contDiffAt.restrict_scalars ℝ
  have hgx : ContDiffAt ℝ ∞ (fun z : ℂ => fderiv ℝ g z 1) a :=
    (hg.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hN : ContDiffAt ℝ ∞ N a :=
    ((contDiffAt_const.mul (((contDiffAt_id.sub contDiffAt_const).mul hgx).sub
      (contDiffAt_const.mul hg))).mul (hqR.pow 2)).mul
        (Complex.conjCLE.contDiff.contDiffAt.comp a hqR)
  have hQ : ContDiffAt ℝ ∞ Q a := by
    simpa only [Q, normSq_eq_norm_sq] using hqR.norm_sq (𝕜 := ℂ)
  refine ⟨N, Q, hN, hQ, ?_, ?_, ?_⟩
  · dsimp only [N, a]
    rw [hq0, hg0]
    simp only [sub_self, zero_mul, zero_sub, map_inv₀, map_natCast]
    ring
  · dsimp only [Q, a]
    rw [hq0, map_inv₀, normSq_natCast]
    ring
  · have heg' := eventually_nhdsNE_eventually_nhds_iff.mpr heg
    have hg' := (hg.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
    filter_upwards [heg', heq.filter_mono nhdsWithin_le_nhds,
      hg'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hgz hqz hgd hza r
    have hP := horizontal_deriv_local_double_pole hgz hgd.differentiableAt_one hza
    change deriv (suzukiXiHorizontalReflectionHeat rho c tau z.im) z.re = _ at hP
    unfold suzukiXiPlanarReflectionMassRemainder suzukiXiReflectionMassRemainder
    rw [hP]
    simp only [suzukiXiHorizontalMass, suzukiXiHorizontalCarrier, Complex.re_add_im]
    have hcoupled := (hqz r).2
    change (suzukiXiNormalizedMass r z : ℂ) * suzukiXiSmoothCarrier r z = _ at hcoupled
    rw [mul_assoc (2*I*(r:ℂ)^2*_), hcoupled]
    dsimp only [N, Q, complexAngularResolventKernel]
    simp only [map_mul, ofReal_div, ofReal_pow, ofReal_add, ofReal_one,
      ofReal_mul]
    have hw : z-a ≠ 0 := sub_ne_zero.mpr hza
    dsimp only [a] at hw ⊢
    field_simp

end
end RiemannGaussian
