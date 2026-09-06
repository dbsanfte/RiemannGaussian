import RiemannGaussian.EtaZetaPrimeProduct
import Mathlib.Analysis.Complex.Schwarz

/-!
# Quantitative higher-order vanishing from eta bounds and actual multiplicity

The pole-removed zeta function has the original zero's full analytic
multiplicity. The existing eta strip bound controls a fixed disc around
that zero. The higher-order Schwarz lemma then gives a power of the actual
distance, rather than only the first-order derivative bound.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Removing the pole multiplies zeta by its literal nonzero linear
factor at every point away from the pole. -/
theorem riemannZeta₁_eq_sub_one_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta₁ s = (s - 1) * riemannZeta s := by
  rw [riemannZeta_eq_inv_sub_mul hs]
  field_simp [sub_ne_zero.mpr hs]

/-- The entire pole-removed function retains every order of vanishing
of the original actual zeta zero, with an analytic local coefficient. -/
theorem riemannZeta₁_eventuallyEq_multiplicity_factor (rho : NontrivialZetaZero) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g rho.1 ∧ g rho.1 ≠ 0 ∧
      riemannZeta₁ =ᶠ[𝓝 rho.1] fun z ↦ (z - rho.1) ^ analyticZetaZeroMultiplicity rho * g z := by
  obtain ⟨g, hg, hgne, hfact⟩ := (analyticAt_riemannZeta_nontrivialZero rho).analyticOrderAt_ne_top.mp
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
  refine ⟨fun z ↦ (z - 1) * g z, (analyticAt_id.sub analyticAt_const).mul hg,
    mul_ne_zero (sub_ne_zero.mpr rho.2.2.2) hgne, ?_⟩
  filter_upwards [hfact, eventually_ne_nhds rho.2.2.2] with z hz hz1
  rw [riemannZeta₁_eq_sub_one_mul hz1, hz]
  change (z - 1) * ((z - rho.1) ^ analyticZetaZeroMultiplicity rho * g z) = _
  ring

/-- The complete actual multiplicity supplies the little-oh condition
for the higher-order Schwarz estimate. -/
theorem riemannZeta₁_isLittleO_multiplicity_pred (rho : NontrivialZetaZero) :
    (fun z ↦ riemannZeta₁ z - riemannZeta₁ rho.1) =o[𝓝 rho.1]
      (fun z ↦ ‖z - rho.1‖ ^ (analyticZetaZeroMultiplicity rho - 1)) := by
  obtain ⟨g, hg, _, hfact⟩ := riemannZeta₁_eventuallyEq_multiplicity_factor rho
  have hm : analyticZetaZeroMultiplicity rho - 1 + 1 = analyticZetaZeroMultiplicity rho :=
    Nat.sub_add_cancel (analyticZetaZeroMultiplicity_positive rho)
  have ht : Tendsto (fun z : ℂ ↦ (z - rho.1) * g z) (𝓝 rho.1) (𝓝 0) := by
    have hc : ContinuousAt (fun z : ℂ ↦ (z - rho.1) * g z) rho.1 := by fun_prop
    simpa using hc.tendsto
  have ho : (fun z : ℂ ↦ (z - rho.1) * g z) =o[𝓝 rho.1] (fun _ : ℂ ↦ (1 : ℂ)) :=
    (Asymptotics.isLittleO_one_iff ℂ).mpr ht
  have hp := (Asymptotics.isBigO_refl
    (fun z : ℂ ↦ (z - rho.1) ^ (analyticZetaZeroMultiplicity rho - 1)) (𝓝 rho.1)).mul_isLittleO ho
  have he : (fun z ↦ riemannZeta₁ z - riemannZeta₁ rho.1) =o[𝓝 rho.1]
      (fun z : ℂ ↦ (z - rho.1) ^ (analyticZetaZeroMultiplicity rho - 1)) := by
    refine hp.congr' ?_ ?_
    · filter_upwards [hfact] with z hz
      rw [riemannZeta₁_nontrivialZetaZero, sub_zero, hz, ← mul_assoc, ← pow_succ, hm]
    · filter_upwards with z
      simp
  simpa only [norm_pow] using he.norm_right

/-- The original eta rectangle bound controls a whole quarter-radius
disc about every zero in the indicated substrip. -/
theorem norm_riemannZeta₁_le_eta_zero_ball (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {z : ℂ} (hz : z ∈ ball rho.1 (1 / 4 : ℝ)) :
    ‖riemannZeta₁ z‖ ≤ 8 * (|rho.1.im| + 21) ^ 2 := by
  have hdist : ‖z - rho.1‖ < 1 / 4 := by simpa only [mem_ball, dist_eq_norm] using hz
  have hre : |z.re - rho.1.re| < 1 / 4 := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (z - rho.1)).trans_lt hdist
  have him : |z.im - rho.1.im| < 1 / 4 := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z - rho.1)).trans_lt hdist
  have hzlo : 1 / 2 ≤ z.re := by linarith [(abs_lt.mp hre).1]
  have hzhi : z.re ≤ 3 / 2 := by linarith [(abs_lt.mp hre).2, NontrivialZetaZero.re_lt_one rho]
  have himabs : |z.im| + 20 ≤ |rho.1.im| + 21 := by
    have h := abs_add_le (z.im - rho.1.im) rho.1.im
    rw [sub_add_cancel] at h
    linarith
  exact (norm_riemannZeta₁_le_etaStrip hzlo hzhi).trans (by gcongr)

/-- The actual multiplicity improves the local eta-derived value bound
to the corresponding power of the distance from the zero. -/
theorem norm_riemannZeta₁_le_etaMultiplicity_ball (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) {z : ℂ} (hz : z ∈ ball rho.1 (1 / 4 : ℝ)) :
    ‖riemannZeta₁ z‖ ≤ 8 * (|rho.1.im| + 21) ^ 2 *
      (4 * ‖z - rho.1‖) ^ analyticZetaZeroMultiplicity rho := by
  have hmaps : MapsTo riemannZeta₁ (ball rho.1 (1 / 4 : ℝ))
      (closedBall (riemannZeta₁ rho.1) (8 * (|rho.1.im| + 21) ^ 2)) := by
    intro w hw
    simpa only [mem_closedBall, riemannZeta₁_nontrivialZetaZero, dist_zero_right] using
      norm_riemannZeta₁_le_eta_zero_ball rho hrho hw
  have h := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
    differentiable_riemannZeta₁.differentiableOn hmaps (riemannZeta₁_isLittleO_multiplicity_pred rho) hz
  have hm : analyticZetaZeroMultiplicity rho - 1 + 1 = analyticZetaZeroMultiplicity rho :=
    Nat.sub_add_cancel (analyticZetaZeroMultiplicity_positive rho)
  have hscale : ‖z - rho.1‖ / (1 / 4 : ℝ) = 4 * ‖z - rho.1‖ := by ring
  simpa only [riemannZeta₁_nontrivialZetaZero, dist_zero_right, dist_eq_norm,
    sub_zero, hm, hscale] using h

/-- At the point reflected across the pole line, higher-order vanishing
gives the full multiplicity power of the horizontal zero gap. -/
theorem norm_riemannZeta₁_reflected_across_one_le_multiplicity
    (rho : NontrivialZetaZero) (hrho : 15 / 16 ≤ rho.1.re) :
    ‖riemannZeta₁ (((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im)‖ ≤
      8 * (|rho.1.im| + 21) ^ 2 * (8 * (1 - rho.1.re)) ^ analyticZetaZeroMultiplicity rho := by
  have hd : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have he : (((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im) - rho.1 =
      ((2 * (1 - rho.1.re) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
    ring
  have hn : ‖(((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im) - rho.1‖ = 2 * (1 - rho.1.re) := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hball : ((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im ∈ ball rho.1 (1 / 4 : ℝ) := by
    rw [mem_ball, dist_eq_norm, hn]
    linarith
  have h := norm_riemannZeta₁_le_etaMultiplicity_ball rho (by linarith) hball
  rw [hn] at h
  convert h using 1
  congr 2
  ring

end

end RiemannGaussian
