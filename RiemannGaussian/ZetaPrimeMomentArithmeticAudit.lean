/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentChebyshev
import RiemannGaussian.ZetaRieszPositiveDensityAudit

/-!
# Strength audit for scale-to-scale prime constraints

A fixed below-one oscillatory component is smaller than every error
envelope with a sublinear loss exponent in logarithmic coordinates.
The existing positive continuous-density model has exactly such a
component and nevertheless has coherent factorial source `-1`.
This does not refute a theorem about actual ordinary integer primes.
-/

set_option autoImplicit false
noncomputable section
open Filter Set Topology Real
namespace RiemannGaussian.ZetaPrimeMomentArithmeticAudit
open ZetaRieszPositiveDensityAudit

/-- Every positive fixed horizontal gain eventually beats a sublinear
logarithmic loss. Thus standard subexponential PNT envelopes permit the
diagnostic hypothetical-zero component. -/
theorem exponential_mode_below_sublinear_envelope {delta : ℝ} (hd : 0<delta)
    (loss : ℝ→ℝ) (hl : Tendsto (fun t => loss t/t) atTop (𝓝 0)) :
    Tendsto (fun t => exp (-delta*t+loss t)) atTop (𝓝 0) := by
  have hb : ∀ᶠ t : ℝ in atTop,loss t≤(delta/2)*t := by
    filter_upwards [hl.eventually_lt_const (by linarith : (0 : ℝ)<delta/2),
      eventually_gt_atTop (0 : ℝ)] with t ht ht0
    exact ((div_lt_iff₀ ht0).mp ht).le
  have ht : Tendsto (fun t : ℝ => exp (-(delta/2)*t)) atTop (𝓝 0) := by
    have hh := (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop
      (by linarith : (0 : ℝ)<delta/2)
    simpa only [Function.comp_def,id_eq,neg_mul] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hh)
  apply squeeze_zero' (Eventually.of_forall fun _ => (exp_pos _).le) _ ht
  filter_upwards [hb] with t h
  exact exp_le_exp.mpr (by linarith)

/-- The known positive density passes every such asymptotic relative-error
envelope. The whole common phase, not an arbitrary phase per atom, is used. -/
theorem model_relative_error_below_sublinear_envelope {u : ℝ} (hu : 1/2<u)
    (y : ℝ) (loss : ℝ→ℝ) (hl : Tendsto (fun t => loss t/t) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => |t*density u y t/exp t-1| * exp (loss t)) atTop (𝓝 0) := by
  have hd : 0<u-1/2 := by linarith
  have ht := (exponential_mode_below_sublinear_envelope hd loss hl).const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun _ => by positivity) _
    (by simpa only [mul_zero] using ht)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht0
  have hb := mul_le_mul_of_nonneg_right (relative_density_abs_le u y ht0.ne')
    (exp_pos (loss t)).le
  exact hb.trans_eq (by rw [mul_assoc,←exp_add])

/-- An explicit rejection test: positivity on a full unbounded half-line,
one fixed phase, all factorial orders, and arbitrarily strong subexponential
PNT envelopes can coexist with source `-1`. An arithmetic candidate must
therefore use more than these properties. This is a continuous model only. -/
theorem positive_coherent_model_with_subexponential_error {u y : ℝ}
    (hu : 1/2<u) (hu1 : u<1) (hy : 1≤|y|) :
    ∃ B : ℝ,0≤B ∧ (∀ t : ℝ,B<t → 0<density u y t) ∧
      Tendsto (densityMoment u y B) atTop (𝓝 (-1)) ∧
      ∀ loss : ℝ→ℝ,Tendsto (fun t => loss t/t) atTop (𝓝 0) →
        Tendsto (fun t : ℝ => |t*density u y t/exp t-1| * exp (loss t)) atTop (𝓝 0) := by
  have hd : 0<u-1/2 := by linarith
  let B : ℝ := 1/(u-1/2)
  have hB : 0≤B := (one_div_pos.mpr hd).le
  refine ⟨B,hB,?_,densityMoment_tendsto (by linarith) hu1 hB hy,
    fun loss hl => model_relative_error_below_sublinear_envelope hu y loss hl⟩
  intro t ht
  apply density_pos (lt_of_le_of_lt hB ht)
  have h := (div_lt_iff₀ hd).mp ht
  simpa only [mul_comm] using h.le

end RiemannGaussian.ZetaPrimeMomentArithmeticAudit
