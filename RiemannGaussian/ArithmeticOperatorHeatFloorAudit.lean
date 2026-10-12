/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFloorSourceAudit
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod

/-!
# All-scale linear heat smoothing retains the actual floor source blind spot

The actual centered floor is convolved over every logarithmic cutoff, not
over a finite sampled row set. Joint absolute integrability is proved before
Fubini. Every exponentially integrable complex row weight has the same
Mellin factor, so no such linear smoothing can restore a genuine zero mode.

For Gaussian heat the factor is explicit and nonzero: its zero set is
EXACTLY the old floor-transform zero set. This is a source-gate no-go for
linear cutoff heat smoothing, not a rejection of nonlinear co-Poisson
approximation, additive lattice coupling or the Gaussian/Weil endpoint.
-/

namespace RiemannGaussian.ArithmeticOperatorHeatFloorAudit
noncomputable section
open Complex MeasureTheory
open ArithmeticOperatorFloorSourceAudit
open scoped Topology

/-- The unchanged literal cutoff/density profile, with every floor endpoint. -/
def heatFloor (w : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ h : ℝ,w h*(centeredFloor (t+h) : ℂ)

/-- The actual Mellin source integral of the full smoothed cutoff profile. -/
def heatTransform (w : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ t : ℝ,Complex.exp (-s*t)*heatFloor w t

/-- Exact finite integer observation; no continuous floor surrogate is used. -/
theorem heatFloor_integer_identity (w : ℝ → ℂ) (t : ℝ) :
    heatFloor w t = ∫ h : ℝ,w h*
      (((⌊Real.exp (t+h)⌋ : ℤ) : ℂ)-(Real.exp (t+h) : ℂ)) := by
  simp [heatFloor,centeredFloor]

private theorem shifted_norm_integral (s : ℂ) (h : ℝ) :
    (∫ t : ℝ,‖Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ)‖) =
      Real.exp (s.re*h)*
        ∫ t : ℝ,‖Complex.exp (-s*t)*(centeredFloor t : ℂ)‖ := by
  have he (t : ℝ) :
      Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ) =
        Complex.exp (s*h)*(Complex.exp (-s*(t+h))*(centeredFloor (t+h) : ℂ)) := by
    rw [←mul_assoc,←Complex.exp_add]
    congr 2
    ring
  simp_rw [he,norm_mul,Complex.norm_exp]
  rw [show (s*(h : ℂ)).re=s.re*h by simp,integral_const_mul]
  simpa only [norm_mul,Complex.norm_exp,Complex.ofReal_add] using
    congrArg (fun x : ℝ => Real.exp (s.re*h)*x)
      (integral_add_right_eq_self
        (fun t : ℝ => ‖Complex.exp (-s*t)*(centeredFloor t : ℂ)‖) h)

/-- The joint kernel is genuinely absolutely integrable. The weighted
row hypothesis is explicit, rather than hidden inside an integral swap. -/
theorem integrable_joint {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    {w : ℝ → ℂ} (hw : Measurable w)
    (hi : Integrable (fun h : ℝ => ‖w h‖*Real.exp (s.re*h))) :
    Integrable (fun ht : ℝ×ℝ => w ht.1*
      (Complex.exp (-s*ht.2)*(centeredFloor (ht.2+ht.1) : ℂ))) := by
  have hm : Measurable (fun ht : ℝ×ℝ => w ht.1*
      (Complex.exp (-s*ht.2)*(centeredFloor (ht.2+ht.1) : ℂ))) := by
    unfold centeredFloor
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with h
    exact (integrable_shifted_floor hs hs1 h).const_mul (w h)
  · have he (h : ℝ) :
        (∫ t : ℝ,‖w h*(Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ))‖) =
          (‖w h‖*Real.exp (s.re*h))*
            ∫ t : ℝ,‖Complex.exp (-s*t)*(centeredFloor t : ℂ)‖ := by
      rw [show (fun t : ℝ => ‖w h*(Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ))‖) =
        fun t : ℝ => ‖w h‖*‖Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ)‖ by
          funext t; exact norm_mul _ _]
      rw [integral_const_mul,shifted_norm_integral]
      ring
    simp_rw [he]
    exact hi.mul_const _

/-- The outer source integral also exists; zero in the next theorem is
not Bochner's default value for a divergent integral. -/
theorem integrable_heatTransform {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    {w : ℝ → ℂ} (hw : Measurable w)
    (hi : Integrable (fun h : ℝ => ‖w h‖*Real.exp (s.re*h))) :
    Integrable (fun t : ℝ => Complex.exp (-s*t)*heatFloor w t) := by
  have h := (integrable_joint hs hs1 hw hi).integral_prod_right
  refine h.congr (Filter.Eventually.of_forall (fun t => ?_))
  change (∫ h : ℝ,w h*(Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ))) =
    Complex.exp (-s*t)*heatFloor w t
  symm
  rw [heatFloor,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with h
  ring

/-- Exact joined Mellin identity over ALL cutoff scales. -/
theorem heatTransform_eq {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    {w : ℝ → ℂ} (hw : Measurable w)
    (hi : Integrable (fun h : ℝ => ‖w h‖*Real.exp (s.re*h))) :
    heatTransform w s =
      (∫ h : ℝ,w h*Complex.exp (s*h))*floorTransform s := by
  have hswap := integral_integral_swap
    (f := fun h t : ℝ => w h*
      (Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ)))
    (integrable_joint hs hs1 hw hi)
  have he (t : ℝ) :
      Complex.exp (-s*t)*heatFloor w t =
        ∫ h : ℝ,w h*(Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ)) := by
    rw [heatFloor,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with h
    ring
  rw [heatTransform]
  simp_rw [he]
  rw [←hswap]
  simp_rw [integral_const_mul,integral_shifted_floor,←mul_assoc]
  exact integral_mul_const _ _

/-- Every admissible complex all-scale linear code is source-blind at
every actual strip zero. No exposure or simple-zero assumption enters. -/
theorem heatTransform_zero_at_zeta_zero {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    (hz : riemannZeta s=0) {w : ℝ → ℂ} (hw : Measurable w)
    (hi : Integrable (fun h : ℝ => ‖w h‖*Real.exp (s.re*h))) :
    heatTransform w s=0 := by
  rw [heatTransform_eq hs hs1 hw hi,floorTransform_zero_at_zeta_zero hs hs1 hz,mul_zero]

/-- The exact underlying Mellin symbol on the critical strip. This
identifies the blind factor before interpreting any heat positivity. -/
theorem floorTransform_eq_zeta_div {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1) :
    floorTransform s=riemannZeta s/s := by
  have hp : Complex.exp (s*(Real.log 2 : ℂ))=(2 : ℂ)^s := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ)≠0),
      show Complex.log (2 : ℂ)=(Real.log 2 : ℂ) by
        simpa only [Complex.ofReal_ofNat] using
          (Complex.ofReal_log (by norm_num : (0 : ℝ)≤2)).symm]
    congr 1
    ring
  have hfactor : (2 : ℂ)^s-2≠0 := by
    have hh := SuzukiCarryPhaseScaleGate.scale_factor_ne_zero
      (p := s) (s := 1) (by simpa using hs1.ne)
    have h2 : Complex.exp (Real.log 2 : ℂ)=2 := by
      rw [←Complex.ofReal_exp,Real.exp_log (by norm_num : (0 : ℝ)<2)]
      norm_num
    simpa only [one_mul,h2,hp] using hh
  have hne : s≠1 := by intro h; rw [h] at hs1; norm_num at hs1
  have he := dyadic_transform_identity hs hs1
  rw [hp,SuzukiIntegerCarryMellinAudit.carryTransform_eq_zeta hs hne] at he
  apply mul_left_cancel₀ hfactor
  calc
    _ = ((2 : ℂ)^s-2)*riemannZeta s/s := he
    _ = _ := by ring

/-- Positive logarithmic heat width, with an arbitrary full complex row phase. -/
def gaussianRow (a : ℝ) (v : ℂ) (h : ℝ) : ℂ :=
  Complex.exp (-(a : ℂ)*(h : ℂ)^2+v*h)

theorem integrable_gaussian_weight {a : ℝ} (ha : 0<a) (v s : ℂ) :
    Integrable (fun h : ℝ => ‖gaussianRow a v h‖*Real.exp (s.re*h)) := by
  have hg := (integrable_cexp_quadratic
    (show 0<(a : ℂ).re by simpa using ha) (v+s) 0).norm
  refine hg.congr (Filter.Eventually.of_forall (fun h => ?_))
  simp only [gaussianRow,Complex.norm_exp,←Real.exp_add]
  congr 1
  simp
  ring

theorem gaussian_factor_eq {a : ℝ} (ha : 0<a) (v s : ℂ) :
    (∫ h : ℝ,gaussianRow a v h*Complex.exp (s*h)) =
      ((Real.pi : ℂ)/(a : ℂ))^(1/2 : ℂ)*
        Complex.exp ((v+s)^2/(4*(a : ℂ))) := by
  have he (h : ℝ) : gaussianRow a v h*Complex.exp (s*h) =
      Complex.exp (-(a : ℂ)*(h : ℂ)^2+(v+s)*h+0) := by
    rw [gaussianRow,←Complex.exp_add]
    congr 1
    ring
  simp_rw [he]
  convert integral_cexp_quadratic
    (show (-(a : ℂ)).re<0 by simpa using ha) (v+s) 0 using 1
  simp [div_neg]

theorem gaussian_factor_ne_zero {a : ℝ} (ha : 0<a) (v s : ℂ) :
    (∫ h : ℝ,gaussianRow a v h*Complex.exp (s*h))≠0 := by
  rw [gaussian_factor_eq ha]
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  exact Complex.cpow_ne_zero_iff.mpr
    (Or.inl (div_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast ha.ne')))

/-- Heat smoothing preserves the entire zero set, not just one diagnostic
height. It adds no linear source channel, whatever its fixed phase. -/
theorem gaussian_heat_zero_iff_floor {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    {a : ℝ} (ha : 0<a) (v : ℂ) :
    heatTransform (gaussianRow a v) s=0 ↔ floorTransform s=0 := by
  rw [heatTransform_eq hs hs1 (by unfold gaussianRow; fun_prop)
    (integrable_gaussian_weight ha v s),mul_eq_zero]
  simp [gaussian_factor_ne_zero ha v s]

theorem gaussian_heat_zero_at_zeta_zero {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    (hz : riemannZeta s=0) {a : ℝ} (ha : 0<a) (v : ℂ) :
    heatTransform (gaussianRow a v) s=0 := by
  exact (gaussian_heat_zero_iff_floor hs hs1 ha v).mpr
    (floorTransform_zero_at_zeta_zero hs hs1 hz)

/-- The complete heat response is just an explicit nonzero Gaussian
factor times zeta/s. No pole renormalization or artificial prime filter. -/
theorem gaussian_heat_eq_zeta {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    {a : ℝ} (ha : 0<a) (v : ℂ) :
    heatTransform (gaussianRow a v) s =
      (((Real.pi : ℂ)/(a : ℂ))^(1/2 : ℂ)*
        Complex.exp ((v+s)^2/(4*(a : ℂ))))*(riemannZeta s/s) := by
  rw [heatTransform_eq hs hs1 (by unfold gaussianRow; fun_prop)
    (integrable_gaussian_weight ha v s),gaussian_factor_eq ha,floorTransform_eq_zeta_div hs hs1]

theorem gaussian_heat_zero_iff_zeta {s : ℂ} (hs : 0<s.re) (hs1 : s.re<1)
    {a : ℝ} (ha : 0<a) (v : ℂ) :
    heatTransform (gaussianRow a v) s=0 ↔ riemannZeta s=0 := by
  have hs0 : s≠0 := by intro h; rw [h] at hs; norm_num at hs
  rw [gaussian_heat_zero_iff_floor hs hs1 ha v,floorTransform_eq_zeta_div hs hs1,div_eq_zero_iff]
  simp [hs0]

end
end RiemannGaussian.ArithmeticOperatorHeatFloorAudit
