/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiPositivityRH
import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# General compensators in the Suzuki--Landau argument

A nonnegative compensator may be subtracted from the positive measure's
Laplace transform whenever its own Laplace integral converges at every
positive damping. The compensator need not be affine or monotone. The
analytic subtraction preserves the full hypothetical zero residue.

Subexponential growth, together with genuine local integrability, supplies
this convergence. All arithmetic one-sided bounds remain hypotheses.
-/

namespace RiemannGaussian
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Complex Asymptotics
open scoped Topology ENNReal

private def timeDensity (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity (fun t => ENNReal.ofReal (f t))

private theorem timeDensity_nonneg_time (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Ioi 0))) :
    ∀ᵐ t ∂timeDensity f, 0 ≤ t := by
  rw [timeDensity, ae_withDensity_iff' hf.ennreal_ofReal]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact fun _ => ht.le

private theorem timeDensity_integrable_exp (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Ioi 0)))
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t) (x : ℝ)
    (hi : IntegrableOn (fun t : ℝ => f t * Real.exp (x * t)) (Ioi 0)) :
    x ∈ integrableExpSet id (timeDensity f) := by
  change Integrable (fun t : ℝ => Real.exp (x * t)) _
  rw [timeDensity, integrable_withDensity_iff_integrable_smul₀' hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hpos t ht), smul_eq_mul]

private theorem timeDensity_complexMGF (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Ioi 0)))
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t) (z : ℂ) :
    complexMGF id (timeDensity f) z =
      ∫ t in Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (z * (t : ℂ)) := by
  rw [complexMGF, timeDensity,
    integral_withDensity_eq_integral_toReal_smul₀ hf.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal (hpos t ht), Complex.real_smul]
  rfl

private theorem integrable_complex_weight (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Ioi 0)))
    (hpos : ∀ t : ℝ, 0 < t → 0 ≤ f t) (z : ℂ)
    (hi : IntegrableOn (fun t : ℝ => f t * Real.exp (z.re * t)) (Ioi 0)) :
    IntegrableOn (fun t : ℝ => (f t : ℂ) * Complex.exp (z * (t : ℂ))) (Ioi 0) := by
  apply (integrable_norm_iff (by fun_prop)).mp
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp [norm_real, Complex.norm_exp, abs_of_nonneg (hpos t ht)]

/-- Every positive exponential damping makes a locally integrable
subexponential real function absolutely integrable on positive time.
The growth hypothesis is asymptotic; local integrability controls the head. -/
theorem integrableOn_exp_weight_of_subexponential_growth {f : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ici 0))
    (hg : ∀ ε : ℝ, 0 < ε → f =O[atTop] (fun t => Real.exp (ε * t)))
    {x : ℝ} (hx : x < 0) :
    IntegrableOn (fun t : ℝ => f t * Real.exp (x * t)) (Ioi 0) := by
  have hl := hf.mul_continuousOn
    (show ContinuousOn (fun t : ℝ => Real.exp (x * t)) (Ici 0) by fun_prop)
    isClosed_Ici.isLocallyClosed
  have ho := (hg (-x / 2) (by linarith)).mul
    (isBigO_refl (fun t : ℝ => Real.exp (x * t)) atTop)
  have he : (fun t : ℝ => Real.exp (-x / 2 * t) * Real.exp (x * t)) =
      fun t => Real.exp (x / 2 * t) := by
    ext t
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at ho
  exact (hl.integrableOn_of_isBigO_atTop ho
    ⟨Ioi 0, Ioi_mem_atTop 0, integrableOn_exp_mul_Ioi (by linarith) 0⟩).mono_set
    Ioi_subset_Ici_self

/-- A measurable nonnegative function with global subexponential majorants
has a genuinely convergent Laplace integral at every positive damping. -/
theorem integrableOn_exp_weight_of_subexponential_majorants {f : ℝ → ℝ}
    (hf : AEMeasurable f (volume.restrict (Ioi 0)))
    (hp : ∀ t : ℝ, 0 < t → 0 ≤ f t)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 < t → f t ≤ C * Real.exp (ε * t))
    {x : ℝ} (hx : x < 0) :
    IntegrableOn (fun t : ℝ => f t * Real.exp (x * t)) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := hg (-x / 2) (by linarith)
  apply ((integrableOn_exp_mul_Ioi (by linarith : x / 2 < 0) 0).const_mul C).mono'
    (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp t ht) (Real.exp_pos _).le)]
  calc
    f t * Real.exp (x * t) ≤ C * Real.exp (-x / 2 * t) * Real.exp (x * t) :=
      mul_le_mul_of_nonneg_right (hC t ht) (Real.exp_pos _).le
    _ = C * Real.exp (x / 2 * t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The compensator's literal complex Laplace integral is analytic throughout
the positive half-plane. It has no pole there to cancel a zeta-zero residue. -/
theorem analyticOnNhd_positiveTimeLaplace_of_integrable_exp
    (f : ℝ → ℝ) (hf : AEMeasurable f (volume.restrict (Ioi 0)))
    (hp : ∀ t : ℝ, 0 < t → 0 ≤ f t)
    (hi : ∀ x : ℝ, x < 0 →
      IntegrableOn (fun t : ℝ => f t * Real.exp (x * t)) (Ioi 0)) :
    AnalyticOnNhd ℂ (fun z : ℂ =>
      ∫ t in Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
      {z : ℂ | 0 < z.re} := by
  have hd : Iio (0 : ℝ) ⊆ interior (integrableExpSet id (timeDensity f)) :=
    isOpen_Iio.subset_interior_iff.mpr
      (fun x hx => timeDensity_integrable_exp f hf hp x (hi x hx))
  have he : (fun z : ℂ =>
      ∫ t in Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ))) =
      fun z => complexMGF id (timeDensity f) (-z) := by
    ext z
    exact (timeDensity_complexMGF f hf hp (-z)).symm
  rw [he]
  intro z hz
  exact (analyticAt_complexMGF
    (hd (by change -z.re < 0; exact neg_neg_of_pos hz))).comp analyticAt_id.neg

/-- Any nonnegative compensator whose Laplace integral converges at every
positive damping can be removed after Landau continuation. This preserves
the residue of every hypothetical right-half zero, in either orientation
of the original signed signal. The arithmetic lower bound is a premise. -/
theorem riemannHypothesis_of_suzuki_signal_scaled_compensated_lower_bound
    {a : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ)
    (hf : AEMeasurable f (volume.restrict (Ioi 0)))
    (hfpos : ∀ t : ℝ, 0 < t → 0 ≤ f t)
    (hfi : ∀ x : ℝ, x < 0 →
      IntegrableOn (fun t : ℝ => f t * Real.exp (x * t)) (Ioi 0))
    (hb : ∀ t : ℝ, 0 < t → -f t ≤ a * suzukiChebyshevLogAverageLaplaceSignal t) :
    RiemannHypothesis := by
  let g : ℝ → ℝ := fun t => a * suzukiChebyshevLogAverageLaplaceSignal t + f t
  have hg : AEMeasurable g (volume.restrict (Ioi 0)) :=
    (aemeasurable_suzukiChebyshevLogAverageLaplaceSignal.const_mul a).add hf
  have hgpos : ∀ t : ℝ, 0 < t → 0 ≤ g t := by intro t ht; dsimp [g]; linarith [hb t ht]
  have hfm : ∀ x : ℝ, x < 0 → x ∈ integrableExpSet id (timeDensity f) := by
    intro x hx
    exact timeDensity_integrable_exp f hf hfpos x (hfi x hx)
  have hfd : Iio (0 : ℝ) ⊆ interior (integrableExpSet id (timeDensity f)) :=
    isOpen_Iio.subset_interior_iff.mpr hfm
  have hgi : ∀ x : ℝ, x < -1 / 2 → x ∈ integrableExpSet id (timeDensity g) := by
    intro x hx
    apply timeDensity_integrable_exp g hg hgpos x
    have hi := (integrableOn_suzukiChebyshevLogAverageLaplaceKernel
      (lambda := -x) (by linarith)).const_mul a |>.add
        (hfi x (by linarith : x < 0))
    apply hi.congr
    filter_upwards [] with t
    dsimp [g, suzukiChebyshevLogAverageLaplaceKernel]
    ring_nf
  have heq : ∀ z : ℂ, 1 / 2 < z.re →
      complexMGF id (timeDensity g) (-z) =
        (a : ℂ) * suzukiChebyshevLogAverageComplexLaplaceTransform z +
          complexMGF id (timeDensity f) (-z) := by
    intro z hz
    have hsig : IntegrableOn
        (fun t : ℝ => (suzukiChebyshevLogAverageLaplaceSignal t : ℂ) *
          Complex.exp (-z * (t : ℂ))) (Ioi (0 : ℝ)) := by
      have h := integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand hz
      unfold suzukiChebyshevLogAverageComplexLaplaceIntegrand at h
      exact (integrable_indicator_iff measurableSet_Ioi).mp h
    have hfint := integrable_complex_weight f hf hfpos (-z)
      (hfi (-z).re (by simp only [neg_re]; linarith : (-z).re < 0))
    rw [timeDensity_complexMGF g hg hgpos, timeDensity_complexMGF f hf hfpos]
    have hfun : (fun t : ℝ => (g t : ℂ) * Complex.exp (-z * (t : ℂ))) =
        fun t => (a : ℂ) * ((suzukiChebyshevLogAverageLaplaceSignal t : ℂ) *
          Complex.exp (-z * (t : ℂ))) +
          (f t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
      ext t
      dsimp [g]
      push_cast
      ring
    rw [hfun, integral_add (hsig.const_mul (a : ℂ)) hfint, integral_const_mul]
    unfold suzukiChebyshevLogAverageComplexLaplaceTransform
      suzukiChebyshevLogAverageComplexLaplaceIntegrand
    rw [integral_indicator measurableSet_Ioi]
  have hF : AnalyticOnNhd ℝ (fun x : ℝ =>
      a * (suzukiChebyshevLogAverageLaplaceCompletedContinuation (-x : ℂ)).re +
        mgf id (timeDensity f) x) (Iio 0) :=
    fun x hx => (analyticAt_const.mul
      (analyticOnNhd_suzukiCompletedResponse_neg_real x hx)).add (analyticAt_mgf (hfd hx))
  have hgd : Iio (0 : ℝ) ⊆ interior (integrableExpSet id (timeDensity g)) := by
    apply Iio_subset_interior_integrableExpSet_of_analytic_mgf
      measurable_id.aemeasurable (timeDensity_nonneg_time g hg)
      (a := -1 / 2) hgi hF
    intro x hx
    change x < -1 / 2 at hx
    have hz : 1 / 2 < (-x : ℂ).re := by simp only [neg_re, ofReal_re]; linarith
    have h := heq (-x) hz
    rw [suzukiChebyshevLogAverageComplexLaplaceTransform_eq_completedContinuation hz] at h
    have hr := congrArg Complex.re h
    simpa [complexMGF_ofReal] using hr.symm
  let H : ℂ → ℂ := fun z => (a : ℂ)⁻¹ * (complexMGF id (timeDensity g) (-z) -
    complexMGF id (timeDensity f) (-z))
  have hH : AnalyticOnNhd ℂ H {z : ℂ | 0 < z.re} := by
    intro z hz
    have hx : (-z).re ∈ Iio (0 : ℝ) := by change -z.re < 0; exact neg_neg_of_pos hz
    exact analyticAt_const.mul
      (((analyticAt_complexMGF (hgd hx)).comp analyticAt_id.neg).sub
        ((analyticAt_complexMGF (hfd hx)).comp analyticAt_id.neg))
  apply riemannHypothesis_of_suzukiLaplace_extension H hH
  intro z hz
  dsimp [H]
  rw [heq z hz]
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  field_simp
  ring

/-- Every locally integrable nonnegative subexponential compensator is
admissible in the actual Suzuki--Landau argument. No finite-dimensional
family, monotonicity, or particular growth profile is required. -/
theorem riemannHypothesis_of_suzuki_signal_scaled_subexponential_compensator
    {a : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ)
    (hf : LocallyIntegrableOn f (Ici 0))
    (hp : ∀ t : ℝ, 0 < t → 0 ≤ f t)
    (hg : ∀ ε : ℝ, 0 < ε → f =O[atTop] (fun t => Real.exp (ε * t)))
    (hb : ∀ t : ℝ, 0 < t → -f t ≤ a * suzukiChebyshevLogAverageLaplaceSignal t) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_suzuki_signal_scaled_compensated_lower_bound ha f
    (hf.mono_set Ioi_subset_Ici_self).aestronglyMeasurable.aemeasurable hp _ hb
  exact fun _ hx => integrableOn_exp_weight_of_subexponential_growth hf hg hx

/-- It suffices to bound only the negative part of the signed signal by
every positive exponential. The constants may depend on the exponent;
one does not need to construct or search for a common compensator. -/
theorem riemannHypothesis_of_suzuki_signal_scaled_subexponential_lower_bound
    {a : ℝ} (ha : a ≠ 0)
    (hb : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      -(C * Real.exp (ε * t)) ≤ a * suzukiChebyshevLogAverageLaplaceSignal t) :
    RiemannHypothesis := by
  let f : ℝ → ℝ := fun t => max 0 (-a * suzukiChebyshevLogAverageLaplaceSignal t)
  have hf : AEMeasurable f (volume.restrict (Ioi 0)) :=
    aemeasurable_const.max (aemeasurable_suzukiChebyshevLogAverageLaplaceSignal.const_mul (-a))
  have hp : ∀ t : ℝ, 0 < t → 0 ≤ f t := fun t _ => le_max_left _ _
  have hg : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 < t → f t ≤ C * Real.exp (ε * t) := by
    intro ε hε
    obtain ⟨C, hC, h⟩ := hb ε hε
    refine ⟨C, hC, fun t ht => max_le (by positivity) ?_⟩
    linarith [h t ht]
  apply riemannHypothesis_of_suzuki_signal_scaled_compensated_lower_bound ha f hf hp
    (fun _ hx => integrableOn_exp_weight_of_subexponential_majorants hf hp hg hx)
  intro t _
  have h := le_max_right 0 (-a * suzukiChebyshevLogAverageLaplaceSignal t)
  dsimp [f]
  linarith

end
end RiemannGaussian
