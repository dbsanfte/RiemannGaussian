/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorDilationAudit
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor

/-!
# All finite linear cutoff combinations have the same source blind spot

The centered floor has an exact dyadic equation and a genuinely integrable
Mellin transform on 0<Re(s)<1. At a zeta zero the entire transform is zero,
so arbitrary finite shifts, Gaussian row weights and modular row codes
cannot restore its lost linear power-mode response. This does not cover
products of profiles or correlations of different arithmetic columns.
-/

namespace RiemannGaussian.ArithmeticOperatorFloorSourceAudit
noncomputable section
open Complex MeasureTheory Set
open SuzukiIntegerCarryMellinAudit
open scoped BigOperators

/-- Exact floor error; no cutoff endpoint is rounded or deleted. -/
def centeredFloor (t : ℝ) : ℝ := (⌊Real.exp t⌋ : ℤ)-Real.exp t

/-- The ordinary Mellin transform in logarithmic coordinates. -/
def floorTransform (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-s*t)*(centeredFloor t : ℂ)

theorem centeredFloor_abs_le_one (t : ℝ) : |centeredFloor t| ≤ 1 := by
  have hlo := Int.floor_le (Real.exp t)
  have hhi := Int.lt_floor_add_one (Real.exp t)
  rw [centeredFloor, abs_le]
  constructor <;> linarith

theorem centeredFloor_abs_le_exp (t : ℝ) :
    |centeredFloor t| ≤ Real.exp t := by
  have hf0 : (0 : ℝ) ≤ (⌊Real.exp t⌋ : ℤ) := by
    exact_mod_cast Int.floor_nonneg.mpr (Real.exp_pos t).le
  have hf1 := Int.floor_le (Real.exp t)
  rw [centeredFloor,abs_of_nonpos (by linarith)]
  linarith

/-- Exact quotient-colour equation, including every discontinuity endpoint. -/
theorem centeredFloor_dyadic (t : ℝ) :
    centeredFloor (t+Real.log 2)-2*centeredFloor t = carryLogColour t := by
  have hf : (⌊2*Real.exp t⌋ : ℤ)/2 = ⌊Real.exp t⌋ := by
    simpa using Int.natCast_mul_floor_div_cancel (n := 2) (by norm_num : (2 : ℕ) ≠ 0)
      (Real.exp t)
  have hh := Int.emod_add_mul_ediv (⌊2*Real.exp t⌋ : ℤ) 2
  rw [hf] at hh
  unfold centeredFloor carryLogColour
  rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_comm (Real.exp t) 2]
  by_cases he : Even (⌊2*Real.exp t⌋ : ℤ)
  · rw [ite_eq_left he]
    rw [Int.even_iff.mp he] at hh
    have hz : (⌊2*Real.exp t⌋ : ℤ)-2*⌊Real.exp t⌋ = 0 := by omega
    have hr : ((⌊2*Real.exp t⌋ : ℤ) : ℝ)-2*((⌊Real.exp t⌋ : ℤ) : ℝ) = 0 := by
      exact_mod_cast hz
    linarith
  · have ho := Int.not_even_iff.mp he
    rw [ite_eq_right he]
    have hz : (⌊2*Real.exp t⌋ : ℤ)-2*⌊Real.exp t⌋ = 1 := by omega
    have hr : ((⌊2*Real.exp t⌋ : ℤ) : ℝ)-2*((⌊Real.exp t⌋ : ℤ) : ℝ) = 1 := by
      exact_mod_cast hz
    linarith

/-- The transform is an actual integral, not a totalized nonintegrable zero. -/
theorem integrable_floorTransform {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    Integrable (fun t : ℝ => Complex.exp (-s*t)*(centeredFloor t : ℂ)) := by
  have hleft : Integrable ((Iic (0 : ℝ)).indicator
      (fun t => Real.exp ((1-s.re)*t))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      (integrableOn_exp_mul_Iic (by linarith : 0 < 1-s.re) 0)
  have hright : Integrable ((Ioi (0 : ℝ)).indicator
      (fun t => Real.exp (-s.re*t))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      (integrableOn_exp_mul_Ioi (by linarith : -s.re < 0) 0)
  have hm : Measurable (fun t : ℝ => Complex.exp (-s*t)*(centeredFloor t : ℂ)) := by
    unfold centeredFloor
    fun_prop
  apply (hleft.add hright).mono' hm.aestronglyMeasurable
  filter_upwards with t
  rw [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs]
  have he : (-s*(t : ℂ)).re = -s.re*t := by simp
  rw [he]
  simp only [Pi.add_apply]
  by_cases ht : t ≤ 0
  · rw [indicator_of_mem (show t ∈ Iic (0 : ℝ) from ht),
      indicator_of_notMem (show t ∉ Ioi (0 : ℝ) by simpa using ht),add_zero]
    calc
      Real.exp (-s.re*t)*|centeredFloor t| ≤ Real.exp (-s.re*t)*Real.exp t :=
        mul_le_mul_of_nonneg_left (centeredFloor_abs_le_exp t) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · rw [indicator_of_notMem (show t ∉ Iic (0 : ℝ) from ht),
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from lt_of_not_ge ht),zero_add]
    exact (mul_le_mul_of_nonneg_left (centeredFloor_abs_le_one t) (Real.exp_pos _).le).trans_eq
      (mul_one _)

theorem integral_shifted_floor {s : ℂ} (h : ℝ) :
    (∫ t : ℝ, Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ)) =
      Complex.exp (s*h)*floorTransform s := by
  have he (t : ℝ) : Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ) =
      Complex.exp (s*h)*(Complex.exp (-s*(t+h))*(centeredFloor (t+h) : ℂ)) := by
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    ring
  simp_rw [he]
  rw [integral_const_mul]
  simp only [← Complex.ofReal_add]
  exact congrArg (fun z : ℂ => Complex.exp (s*h)*z)
    (integral_add_right_eq_self (fun t : ℝ => Complex.exp (-s*t)*(centeredFloor t : ℂ)) h)

/-- Every centered floor retains the same zeta factor as binary carry. -/
theorem dyadic_transform_identity {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    (Complex.exp (s*(Real.log 2 : ℂ))-2)*floorTransform s = carryTransform s := by
  have hi := integrable_floorTransform hs hs1
  have hij : Integrable (fun t : ℝ => Complex.exp (-s*t)*
      (centeredFloor (t+Real.log 2) : ℂ)) := by
    have hc := (hi.comp_add_right (Real.log 2)).const_mul (Complex.exp (s*(Real.log 2 : ℂ)))
    refine hc.congr (Filter.Eventually.of_forall (fun t => ?_))
    dsimp only
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [carryTransform_eq_actual_colour_integral hs]
  have he (t : ℝ) : Complex.exp (-s*t)*(carryLogColour t : ℂ) =
      Complex.exp (-s*t)*(centeredFloor (t+Real.log 2) : ℂ)-
        2*(Complex.exp (-s*t)*(centeredFloor t : ℂ)) := by
    rw [← centeredFloor_dyadic]
    push_cast
    ring
  simp_rw [he]
  rw [integral_sub hij (hi.const_mul 2),integral_shifted_floor,integral_const_mul]
  unfold floorTransform
  ring

/-- The complete ordinary floor transform annihilates every genuine zero
in the critical strip, independently of exposure or multiplicity. -/
theorem floorTransform_zero_at_zeta_zero {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) : floorTransform s = 0 := by
  have hne : s ≠ 1 := by intro h; rw [h] at hs1; norm_num at hs1
  have he := dyadic_transform_identity hs hs1
  rw [carryTransform_eq_zero_of_zeta_zero hs hne hz] at he
  have hfactor : Complex.exp (s*(Real.log 2 : ℂ))-2 ≠ 0 := by
    have hh := SuzukiCarryPhaseScaleGate.scale_factor_ne_zero
      (p := s) (s := 1) (by simpa using hs1.ne)
    have h2 : Complex.exp (Real.log 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_exp,Real.exp_log (by norm_num)]; norm_num
    simpa only [one_mul,h2] using hh
  exact (mul_eq_zero.mp he).resolve_left hfactor

/-- Arbitrary finite row weighting cannot restore a power mode already
annihilated by the full centered-floor observation. -/
theorem finite_shifted_floor_source_vanishes {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) (S : Finset ℕ) (coefficient : ℕ → ℂ) (shift : ℕ → ℝ) :
    (∑ j ∈ S, coefficient j*
      ∫ t : ℝ, Complex.exp (-s*t)*(centeredFloor (t+shift j) : ℂ)) = 0 := by
  simp only [integral_shifted_floor,floorTransform_zero_at_zeta_zero hs hs1 hz,
    mul_zero,Finset.sum_const_zero]

/-- A finite balanced cutoff combination, with its exact floor endpoints. -/
def balancedCutoff (S : Finset ℕ) (coefficient : ℕ → ℂ) (scale : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ S, coefficient j*((⌊scale j*Real.exp t⌋ : ℤ) : ℂ)

/-- Balance removes only the linear density; the entire remaining exact
floor combination is retained in the centered-floor coordinates. -/
theorem balancedCutoff_eq (S : Finset ℕ) (coefficient : ℕ → ℂ) (scale : ℕ → ℝ)
    (hscale : ∀ j ∈ S, 0 < scale j) (hb : (∑ j ∈ S, coefficient j*(scale j : ℂ)) = 0)
    (t : ℝ) :
    balancedCutoff S coefficient scale t =
      ∑ j ∈ S, coefficient j*(centeredFloor (t+Real.log (scale j)) : ℂ) := by
  have he (j : ℕ) (hj : j ∈ S) :
      coefficient j*((⌊scale j*Real.exp t⌋ : ℤ) : ℂ) =
        coefficient j*(centeredFloor (t+Real.log (scale j)) : ℂ)+
          coefficient j*(scale j : ℂ)*(Real.exp t : ℂ) := by
    unfold centeredFloor
    rw [Real.exp_add, Real.exp_log (hscale j hj)]
    rw [mul_comm (Real.exp t) (scale j)]
    push_cast
    ring
  unfold balancedCutoff
  rw [Finset.sum_congr rfl he,Finset.sum_add_distrib,← Finset.sum_mul,hb,zero_mul,add_zero]

theorem integrable_shifted_floor {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) (h : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (-s*t)*(centeredFloor (t+h) : ℂ)) := by
  have hi := ((integrable_floorTransform hs hs1).comp_add_right h).const_mul (Complex.exp (s*h))
  refine hi.congr (Filter.Eventually.of_forall (fun t => ?_))
  dsimp only
  rw [← mul_assoc,← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The joined source test is zero for every finite balanced cutoff code,
not merely for a binary carry or for termwise estimates of its rows. -/
theorem integral_balancedCutoff_zero_at_zeta_zero {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1) (hz : riemannZeta s = 0) (S : Finset ℕ)
    (coefficient : ℕ → ℂ) (scale : ℕ → ℝ)
    (hscale : ∀ j ∈ S, 0 < scale j) (hb : (∑ j ∈ S, coefficient j*(scale j : ℂ)) = 0) :
    (∫ t : ℝ, Complex.exp (-s*t)*balancedCutoff S coefficient scale t) = 0 := by
  simp_rw [balancedCutoff_eq S coefficient scale hscale hb,Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ =>
    ((integrable_shifted_floor hs hs1 (Real.log (scale j))).const_mul (coefficient j)).congr
      (Filter.Eventually.of_forall (fun _ => by ring)))]
  have he (j : ℕ) :
      (∫ t : ℝ, Complex.exp (-s*t)*(coefficient j*
        (centeredFloor (t+Real.log (scale j)) : ℂ))) =
        coefficient j*(∫ t : ℝ, Complex.exp (-s*t)*
          (centeredFloor (t+Real.log (scale j)) : ℂ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  simp_rw [he]
  exact finite_shifted_floor_source_vanishes hs hs1 hz S coefficient (fun j => Real.log (scale j))

end
end RiemannGaussian.ArithmeticOperatorFloorSourceAudit
