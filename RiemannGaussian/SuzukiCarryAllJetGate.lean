/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPhaseDensity
import RiemannGaussian.SuzukiCarryExceptionalGate

/-!
# The all-jet source-detector bypass

No nonzero quadratic/quartic jet is assumed at the pole exponent. The
amplitude, carry packet, prime powers and native phase/scale code are unchanged.
The independent signed prime estimate is not proved here.
-/

namespace RiemannGaussian.SuzukiCarryAllJetGate
noncomputable section
open Complex MeasureTheory Set Filter Metric
open SuzukiCarryPhaseDensity SuzukiCarryPhaseCosine SuzukiCarryPhaseInjectivity
open SuzukiCarryPhaseScaleGate SuzukiCarryRealJet
open scoped BigOperators Topology

theorem exists_small_literal_contrast {y epsilon : ℝ} (hy : y ≠ 0) (he : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ tau < epsilon ∧
      SuzukiCarryMellinRate.continuumResponse (1-I*y) tau ≠
        SuzukiCarryMellinRate.continuumResponse (1-I*y) 0 := by
  let s : ℂ := 1-I*y
  let f : ℝ → ℂ := sourceDensity s
  let X : ℝ → ℝ := boundedCoordinate
  have hs : 0 < s.re := by simp [s]
  have mf : Measurable f := measurable_sourceDensity s
  have hi : Integrable f := integrable_sourceDensity hs
  have mX : Measurable X := measurable_boundedCoordinate
  have hX : ∀ t, 0 < X t := fun t => (boundedCoordinate_bounds t).1
  have hXb : ∀ t, 0 ≤ X t ∧ X t ≤ 2 :=
    fun t => ⟨(hX t).le, (boundedCoordinate_bounds t).2⟩
  by_contra hn
  push Not at hn
  have hz : ∀ tau ∈ Ioo 0 epsilon, contrastResponse X f tau = 0 := by
    intro tau ht
    have hh := hn tau ht.1 ht.2
    have hformula := contrast_eq_sourceDensity hs tau
    rw [hh, sub_self] at hformula
    exact (mul_eq_zero.mp hformula.symm).resolve_left (Complex.exp_ne_zero _)
  have hsin : ∀ tau ∈ Ioo 0 epsilon, sineResponse X f tau = 0 := by
    intro tau ht
    have hc : HasDerivAt (contrastResponse X f) 0 tau :=
      (hasDerivAt_const tau (0 : ℂ)).congr_of_eventuallyEq
        (eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (fun t ht => hz t ht))
    exact (hasDerivAt_contrast mX hX mf hi tau).unique hc
  have hcos : ∀ tau ∈ Ioo 0 epsilon, ∫ t : ℝ, (Real.cos (tau*X t) : ℂ)*f t = 0 := by
    intro tau ht
    have hc : HasDerivAt (sineResponse X f) 0 tau :=
      (hasDerivAt_const tau (0 : ℂ)).congr_of_eventuallyEq
        (eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (fun t ht => hsin t ht))
    exact neg_eq_zero.mp ((hasDerivAt_sine mX hX mf hi tau).unique hc)
  let H : ℝ → ℂ := fun tau => cosineResponse X f (tau : ℂ)
  have ha : AnalyticOnNhd ℝ H univ := by
    intro tau _
    have hc := analytic_cosineResponse mX hXb mf hi (tau : ℂ) (mem_univ _)
    exact hc.restrictScalars.comp (f := fun r : ℝ => (r : ℂ)) (x := tau)
      (Complex.ofRealCLM.analyticAt tau)
  have hhalf : epsilon/2 ∈ Ioo 0 epsilon := by constructor <;> linarith
  have hall : EqOn H 0 univ := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ (epsilon/2))
    (eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hhalf) (fun tau ht => by
      exact (cosineResponse_real mX hXb mf hi tau).trans (hcos tau ht)))
  have hzero : ∀ tau : ℝ, ∫ t : ℝ, (Real.cos (tau*Real.exp t) : ℂ)*f t = 0 := by
    intro tau
    have hh := hall (mem_univ tau)
    change cosineResponse X f (tau : ℂ) = 0 at hh
    rw [cosineResponse_real mX hXb mf hi] at hh
    rw [← hh]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ≤ Real.log 2
    · have hx : X t = Real.exp t := by
        dsimp [X, boundedCoordinate]
        apply min_eq_right
        calc
          Real.exp t ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr ht
          _ = 2 := Real.exp_log (by norm_num)
      rw [hx]
    · have hfzero : f t = 0 := sourceDensity_zero (lt_of_not_ge ht) s
      rw [hfzero, mul_zero, mul_zero]
  exact sourceDensity_not_ae_zero hy (ae_eq_zero_of_complex_cosineExp_eq_zero mf hi hzero)

/-- A fixed positive four-response code detects every campaign exponent,
including a hypothetical common zero of its first two complex jets. -/
theorem exists_campaign_scale_code {beta y : ℝ} (hb : 19999/20000 ≤ beta)
    (hb1 : beta < 1) (hy : y ≠ 0) :
    ∃ tau : ℝ, 0 < tau ∧ scaleDet (1-I*y) (beta : ℂ) tau ≠ 0 := by
  have hb0 : 0 < beta := by linarith
  have hbeta := eventually_contrast_ne_zero_of_B (s := (beta : ℂ))
    (by simpa using hb0) (B_ofReal_ne_zero (by linarith : 15/16 ≤ beta))
  have hnear : ∀ᶠ tau : ℝ in 𝓝 (0 : ℝ), 0 < tau → contrast (beta : ℂ) tau ≠ 0 :=
    eventually_nhdsWithin_iff.mp hbeta
  obtain ⟨epsilon,he,hh⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨tau,ht,hte,hp⟩ := exists_small_literal_contrast hy he
  have hbp : contrast (1-I*y) tau ≠ 0 := sub_ne_zero.mpr hp
  have hbb := hh (by simpa only [Real.dist_eq, sub_zero, abs_of_pos ht] using hte) ht
  exact ⟨tau,ht,mul_ne_zero (mul_ne_zero (scale_factor_ne_zero
    (by simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; norm_num; linarith)) hbp) hbb⟩

/-- Cofinal native source lower bound with no exposed-zero, nonzero-jet or
floating certificate premise. This is a detector, not a prime upper bound. -/
theorem exists_fixed_campaign_code_source_lower {beta y : ℝ} (hb : 19999/20000 ≤ beta)
    (hb1 : beta < 1) (hy : y ≠ 0) :
    ∃ tau : ℝ, 0 < tau ∧ scaleDet (1-I*y) (beta : ℂ) tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖scaleDet (1-I*y) (beta : ℂ) tau‖/2)*Real.exp ((1+beta)*Real.log H) ≤
          ‖nativeScaleDet H (1-I*y) (beta : ℂ) tau‖ := by
  obtain ⟨tau,ht,hd⟩ := exists_campaign_scale_code hb hb1 hy
  refine ⟨tau,ht,hd,?_⟩
  simpa only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
    sub_zero] using eventually_nativeScaleDet_source_lower
      (p := 1-I*y) (s := (beta : ℂ)) (by simp) (by simp only [Complex.ofReal_re]; linarith) hd

end
end RiemannGaussian.SuzukiCarryAllJetGate
