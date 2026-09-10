/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiReflectionRemainderCompact

/-!
# The exact signed mass variation near a selected xi zero

One analytic carrier chart supplies the mass and carrier simultaneously
for every smoothing radius. Differentiating that same mass chart retains
the local coefficient derivative and the complete angular dependence.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- One analytic chart describes both original normalized fields for all
smoothing radii, on a fixed neighborhood including the zero itself. -/
theorem exists_suzukiXiMass_and_carrier_uniform_chart (rho : NontrivialZetaZero) :
    ∃ q : ℂ → ℂ, AnalyticAt ℂ q (zetaSpectralCoordinate rho.1) ∧
      q (zetaSpectralCoordinate rho.1) = (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ∧
      ∀ᶠ z in 𝓝 (zetaSpectralCoordinate rho.1), ∀ r : ℝ,
        suzukiXiNormalizedMass r z = normSq ((z-zetaSpectralCoordinate rho.1)*q z) /
          (1+r^2*normSq ((z-zetaSpectralCoordinate rho.1)*q z)) ∧
        suzukiXiSmoothCarrier r z = ((z-zetaSpectralCoordinate rho.1)*q z) /
          ((1+r^2*normSq ((z-zetaSpectralCoordinate rho.1)*q z) : ℝ) : ℂ) := by
  obtain ⟨q, p, hq, _hp, hq0, _hp0, he⟩ := exists_suzukiXiCarrier_pair_local_model rho
  refine ⟨q, hq, hq0, ?_⟩
  filter_upwards [eventually_nhdsWithin_iff.mp he] with z hz r
  by_cases hza : z = zetaSpectralCoordinate rho.1
  · subst z
    have hA := (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).mpr ⟨rho, rfl⟩
    rw [suzukiXiNormalizedMass_eq_zero r hA, suzukiXiSmoothCarrier_eq_zero_of_xi_zero r hA]
    simp
  · have hl := hz hza
    rw [suzukiXiNormalizedMass_eq_regular_chart r hl.1,
      suzukiXiSmoothCarrier_eq_radial r hl.1, hl.2.2.1]
    exact ⟨rfl, rfl⟩

private lemma horizontal_normSq_deriv (a z : ℂ) :
    HasDerivAt (fun x : ℝ => normSq (((x:ℂ)+(z.im:ℂ)*I)-a))
      (2*(z-a).re) z.re := by
  have h := (((hasDerivAt_id z.re).sub_const a.re).pow 2).add_const ((z.im-a.im)^2)
  convert! h using 1
  · funext x
    simp only [normSq_apply, sub_re, sub_im, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, mul_zero, I_im, sub_zero, add_zero, add_im, mul_im, zero_add, mul_one, id_eq,
      Pi.pow_apply]
    ring
  · simp

private lemma mass_horizontal_deriv {q : ℂ → ℂ} {a z : ℂ} (r : ℝ)
    (hq : DifferentiableAt ℝ (fun w => normSq (q w)) z)
    (he : suzukiXiNormalizedMass r =ᶠ[𝓝 z] fun w =>
      normSq ((w-a)*q w)/(1+r^2*normSq ((w-a)*q w))) :
    deriv (suzukiXiHorizontalMass r z.im) z.re =
      (2*(z-a).re*normSq (q z) + normSq (z-a)*fderiv ℝ (fun w => normSq (q w)) z 1) /
        (1+r^2*normSq (z-a)*normSq (q z))^2 := by
  have hl : HasDerivAt (fun x : ℝ => (x:ℂ)+(z.im:ℂ)*I) 1 z.re :=
    Complex.ofRealCLM.hasDerivAt.add_const _
  have hQ := hq.hasFDerivAt.comp_hasDerivAt_of_eq z.re hl (Complex.re_add_im z).symm
  have hT := (horizontal_normSq_deriv a z).mul hQ
  dsimp only [Function.comp_def, Pi.mul_apply] at hT
  have hden : 0 < 1+r^2*normSq (z-a)*normSq (q z) := by
    have hw := normSq_nonneg (z-a)
    have hq0 := normSq_nonneg (q z)
    positivity
  have hTval : normSq (((z.re:ℂ)+(z.im:ℂ)*I)-a)*normSq (q ((z.re:ℂ)+(z.im:ℂ)*I)) =
      normSq (z-a)*normSq (q z) := by rw [Complex.re_add_im]
  have hd := hT.div ((hT.const_mul (r^2)).const_add 1) (by
    dsimp only [Pi.mul_apply]
    rw [hTval]
    convert hden.ne' using 1
    ring)
  have he' := he.comp_tendsto (show Tendsto (fun x : ℝ => (x:ℂ)+(z.im:ℂ)*I)
      (𝓝 z.re) (𝓝 z) by simpa only [ContinuousAt, Complex.re_add_im] using hl.continuousAt)
  have he'' : suzukiXiHorizontalMass r z.im =ᶠ[𝓝 z.re] fun x : ℝ =>
      (normSq (((x:ℂ)+(z.im:ℂ)*I)-a)*normSq (q ((x:ℂ)+(z.im:ℂ)*I))) /
        (1+r^2*(normSq (((x:ℂ)+(z.im:ℂ)*I)-a)*normSq (q ((x:ℂ)+(z.im:ℂ)*I)))) := by
    simpa only [suzukiXiHorizontalMass, Function.comp_def, map_mul] using! he'
  have h := hd.congr_of_eventuallyEq he''
  rw [h.deriv]
  simp only [Pi.mul_apply, Complex.re_add_im]
  field_simp
  ring

/-- The actual signed variation has one exact node chart for all radii.
Its derivative term is retained, rather than replaced by an unsigned
bound or a frozen coefficient. -/
theorem exists_suzukiXiReflectionMassVariation_node_chart
    (rho : NontrivialZetaZero) (c tau : ℝ)
    (him : (zetaSpectralCoordinate rho.1).im ≠ 0) :
    ∃ (q g : ℂ → ℂ),
      AnalyticAt ℂ q (zetaSpectralCoordinate rho.1) ∧
      ContDiffAt ℝ ∞ g (zetaSpectralCoordinate rho.1) ∧
      q (zetaSpectralCoordinate rho.1) = (analyticZetaZeroMultiplicity rho : ℂ)⁻¹ ∧
      g (zetaSpectralCoordinate rho.1) =
        -suzukiSmoothSpectralBoundaryHeat c tau (zetaSpectralCoordinate rho.1) ∧
      ∀ᶠ z in 𝓝[≠] (zetaSpectralCoordinate rho.1), ∀ r : ℝ,
        suzukiXiPlanarReflectionMassVariation rho r c tau z =
          g z*q z*
            ((2*(z-zetaSpectralCoordinate rho.1).re*normSq (q z) +
              normSq (z-zetaSpectralCoordinate rho.1)*fderiv ℝ (fun w => normSq (q w)) z 1 : ℝ) : ℂ) /
          ((z-zetaSpectralCoordinate rho.1)*
            ((1+r^2*normSq (z-zetaSpectralCoordinate rho.1)*normSq (q z) : ℝ) : ℂ)^3) := by
  obtain ⟨q, hq, hq0, heq⟩ := exists_suzukiXiMass_and_carrier_uniform_chart rho
  obtain ⟨g, hg, hg0, heg⟩ := exists_suzukiXiReflectionHeat_node_numerator rho c tau him
  refine ⟨q, g, hq, hg, hq0, hg0, ?_⟩
  have hQ : ContDiffAt ℝ ∞ (fun z => normSq (q z)) (zetaSpectralCoordinate rho.1) := by
    simpa only [normSq_eq_norm_sq] using (hq.contDiffAt.restrict_scalars ℝ).norm_sq (𝕜 := ℂ)
  have hQ' := (hQ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have heq' := eventually_eventually_nhds.mpr heq
  filter_upwards [heg, heq.filter_mono nhdsWithin_le_nhds,
    heq'.filter_mono nhdsWithin_le_nhds, hQ'.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hgz hqz hqez hQz hza r
  have hM : suzukiXiNormalizedMass r =ᶠ[𝓝 z] fun w =>
      normSq ((w-zetaSpectralCoordinate rho.1)*q w) /
        (1+r^2*normSq ((w-zetaSpectralCoordinate rho.1)*q w)) :=
    hqez.mono (fun w hw => (hw r).1)
  have hd := mass_horizontal_deriv r hQz.differentiableAt_one hM
  unfold suzukiXiPlanarReflectionMassVariation suzukiXiReflectionMassVariation
  rw [hd]
  simp only [suzukiXiHorizontalReflectionHeat, suzukiXiHorizontalCarrier, Complex.re_add_im]
  rw [hgz, (hqz r).2]
  simp only [map_mul, ofReal_div, ofReal_pow]
  have hw := sub_ne_zero.mpr hza
  field_simp

end
end RiemannGaussian
