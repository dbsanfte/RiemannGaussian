/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaZeroCountFormula
import RiemannGaussian.ZetaRightPhase

/-!
# Certifying the complete zero count from a horizontal path

The right counting line stays in the positive zeta half-plane at every
height. If the remaining horizontal segment does too, the full boundary
phase is exactly the principal argument of its critical-line endpoint.
Zero symmetries prove regularity of the entire height from this same check.
The numerical horizontal-path and endpoint checks remain explicit premises.
-/

namespace RiemannGaussian.ZetaCountingEndpoint
noncomputable section
open Complex MeasureTheory Set
open GammaCountingPhase
open scoped Interval

/-- Nonvanishing on the right half of a horizontal critical-strip segment
excludes the entire symmetric zero boundary, using both zero symmetries. -/
theorem regular_of_horizontal_nonzero {T : ℝ}
    (hn : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), riemannZeta ((x : ℂ) + T * I) ≠ 0) :
    ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T := by
  have hu : ∀ ρ : NontrivialZetaZero, ρ.1.im = T → False := by
    intro ρ hi
    have hr (τ : NontrivialZetaZero) (hx : 1 / 2 ≤ τ.1.re) (ht : τ.1.im = T) : False := by
      have hh := hn τ.1.re ⟨hx, by linarith [NontrivialZetaZero.re_lt_one τ]⟩
      have he : (τ.1.re : ℂ) + T * I = τ.1 := by rw [← ht]; exact Complex.re_add_im _
      exact hh (by rw [he]; exact τ.2.1)
    by_cases hx : 1 / 2 ≤ ρ.1.re
    · exact hr ρ hx hi
    · apply hr (NontrivialZetaZero.conjugatePartner ρ)
      · simp only [NontrivialZetaZero.conjugatePartner_coe, sub_re, one_re, conj_re]
        linarith
      · simpa using hi
  intro ρ he
  by_cases hi : 0 ≤ ρ.1.im
  · exact hu ρ (by simpa only [abs_of_nonneg hi] using he)
  · apply hu (NontrivialZetaZero.conjugate ρ)
    simpa only [NontrivialZetaZero.conjugate_coe, conj_im,
      abs_of_neg (lt_of_not_ge hi)] using he

/-- Positivity on the horizontal path supplies the complete regular-height
condition; it is not an extra unverified zero-list assumption. -/
theorem regular_of_horizontal_positive {T : ℝ}
    (hp : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), 0 < (riemannZeta ((x : ℂ) + T * I)).re) :
    ∀ ρ : NontrivialZetaZero, |ρ.1.im| ≠ T :=
  regular_of_horizontal_nonzero fun x hx => Complex.ne_zero_of_re_pos (hp x hx)

private theorem vertical_log_deriv (t : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.log (riemannZeta ((3 / 2 : ℂ) + y * I)))
      (I * logDeriv riemannZeta ((3 / 2 : ℂ) + t * I)) t := by
  have hn : (3 / 2 : ℂ) + t * I ≠ 1 := by
    intro he
    have hh := congrArg Complex.re he
    norm_num at hh
  have hl : HasDerivAt (fun y : ℝ => (3 / 2 : ℂ) + y * I) I t := by
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add (3 / 2 : ℂ)
  have hd := ((analyticOn_riemannZeta _ hn).differentiableAt.hasDerivAt.comp t hl).clog_real
    (Or.inl (ZetaRightPhase.zeta_re_pos t))
  convert! hd using 1
  simp only [logDeriv_apply, Function.comp_def, riemannZeta]
  ring

private theorem horizontal_log_deriv {T x : ℝ} (hT : T ≠ 0)
    (hp : 0 < (riemannZeta ((x : ℂ) + T * I)).re) :
    HasDerivAt (fun y : ℝ => Complex.log (riemannZeta ((y : ℂ) + T * I)))
      (logDeriv riemannZeta ((x : ℂ) + T * I)) x := by
  have hn : (x : ℂ) + T * I ≠ 1 := by
    intro he
    apply hT
    simpa using congrArg Complex.im he
  have hl : HasDerivAt (fun y : ℝ => (y : ℂ) + T * I) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp.add_const ((T : ℂ) * I)
  have hd := ((analyticOn_riemannZeta _ hn).differentiableAt.hasDerivAt.comp x hl).clog_real
    (Or.inl hp)
  convert! hd using 1
  simp only [mul_one, logDeriv_apply, Function.comp_def, riemannZeta]

private theorem base_log_im : (Complex.log (riemannZeta (3 / 2 : ℂ))).im = 0 := by
  rw [Complex.log_im, Complex.arg_eq_zero_iff]
  refine ⟨by simpa using (ZetaRightPhase.zeta_re_pos 0).le, ?_⟩
  have hh := riemannZeta_conj (3 / 2 : ℂ)
  have hc : (starRingEnd ℂ) (3 / 2 : ℂ) = 3 / 2 := by
    rw [map_div₀, map_ofNat, map_ofNat]
  rw [hc] at hh
  have hi := congrArg Complex.im hh
  norm_num at hi
  linarith

/-- The actual, unwrapped zeta boundary phase is precisely its endpoint
argument when the certified horizontal segment has positive real part.
The right vertical segment requires no numerical verification. -/
theorem pathPhase_eq_arg {T : ℝ} (hT : 0 < T)
    (hp : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), 0 < (riemannZeta ((x : ℂ) + T * I)).re) :
    pathPhase (logDeriv riemannZeta) T = (riemannZeta ((1 / 2 : ℂ) + T * I)).arg := by
  have hb := regular_of_horizontal_positive hp
  have hv := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => vertical_log_deriv t)
    ((ZetaZeroCountFormula.zeta_vertical_integrable T).const_mul I)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (1 / 2 : ℝ)) (b := 3 / 2)
    (fun x hx => horizontal_log_deriv hT.ne' (hp x
      (by simpa only [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 3 / 2)] using hx)))
    (ZetaZeroCountFormula.zeta_horizontal_integrable hT hb)
  have hvi := congrArg Complex.im hv
  have hhi := congrArg Complex.im hh
  have hvc := Complex.imCLM.intervalIntegral_comp_comm (μ := volume)
    ((ZetaZeroCountFormula.zeta_vertical_integrable T).const_mul I)
  have hhc := Complex.imCLM.intervalIntegral_comp_comm (μ := volume)
    (ZetaZeroCountFormula.zeta_horizontal_integrable hT hb)
  simp only [Complex.imCLM_apply, Complex.I_mul_im] at hvc hhc
  rw [← hvc] at hvi
  rw [← hhc] at hhi
  simp only [Complex.sub_im, Complex.ofReal_zero, zero_mul, add_zero, base_log_im,
    sub_zero] at hvi
  simp only [Complex.sub_im] at hhi
  unfold pathPhase
  rw [hvi, hhi]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one,
    sub_sub_cancel, Complex.log_im]

/-- Complete zero counting using the finite theta approximation and one
endpoint argument. The horizontal positivity and numerical approximation
conditions are the full remaining, independently checkable obligations. -/
theorem count_eq_of_endpoint {T : ℝ} (hT : 0 < T) (hH : T ≤ 22000)
    (hp : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), 0 < (riemannZeta ((x : ℂ) + T * I)).re)
    (m : ℕ)
    (hm : |2 + (2 / Real.pi) * (GammaPhaseApproximation.thetaApproximation 200 T +
      (riemannZeta ((1 / 2 : ℂ) + T * I)).arg) - m| ≤ 9 / 10) :
    ZetaFiniteZeroCount.count T = m := by
  apply ZetaZeroCountFormula.count_eq_of_approximation hT hH
    (regular_of_horizontal_positive hp) m
  simpa only [ZetaZeroCountFormula.approximateCount, pathPhase_eq_arg hT hp] using hm

/-- A coarse phase bracket suffices for the first complete count: no
high-precision endpoint argument is needed when its imaginary part is
nonnegative and the unwrapped theta phase is between minus pi/2 and zero. -/
theorem count_eq_two_of_phase {T : ℝ} (hT : 0 < T)
    (hp : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), 0 < (riemannZeta ((x : ℂ) + T * I)).re)
    (hi : 0 ≤ (riemannZeta ((1 / 2 : ℂ) + T * I)).im)
    (hθ : -(Real.pi / 2) < GammaPhaseApproximation.theta T)
    (hθ' : GammaPhaseApproximation.theta T < 0) : ZetaFiniteZeroCount.count T = 2 := by
  have hc := ZetaZeroCountFormula.count_formula hT (regular_of_horizontal_positive hp)
  rw [pathPhase_eq_arg hT hp] at hc
  have ha := Complex.arg_nonneg_iff.mpr hi
  have ha' := Complex.arg_lt_pi_div_two_iff.mpr
    (Or.inl (hp (1 / 2) (by norm_num)))
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at ha'
  have he : Real.pi * (ZetaFiniteZeroCount.count T : ℝ) = 2 * Real.pi +
      2 * (GammaPhaseApproximation.theta T + (riemannZeta ((1 / 2 : ℂ) + T * I)).arg) := by
    rw [hc]
    field_simp
  have hlow : (1 : ℝ) < ZetaFiniteZeroCount.count T := by nlinarith [Real.pi_pos]
  have hupp : (ZetaFiniteZeroCount.count T : ℝ) < 3 := by nlinarith [Real.pi_pos]
  have hlow' : 1 < ZetaFiniteZeroCount.count T := by exact_mod_cast hlow
  have hupp' : ZetaFiniteZeroCount.count T < 3 := by exact_mod_cast hupp
  omega

/-- An unwrapped theta sector determines the complete count when the
horizontal path has positive real part and its endpoint lies above the
real axis. The sector index retains every complete phase turn. -/
theorem count_eq_of_phase_sector {T : ℝ} (hT : 0 < T)
    (hp : ∀ x ∈ Icc (1 / 2 : ℝ) (3 / 2), 0 < (riemannZeta ((x : ℂ) + T * I)).re)
    (hi : 0 ≤ (riemannZeta ((1 / 2 : ℂ) + T * I)).im) (m : ℕ)
    (hθ : (m : ℝ) * Real.pi - Real.pi / 2 < GammaPhaseApproximation.theta T)
    (hθ' : GammaPhaseApproximation.theta T < (m : ℝ) * Real.pi) :
    ZetaFiniteZeroCount.count T = 2 * m + 2 := by
  have hc := ZetaZeroCountFormula.count_formula hT (regular_of_horizontal_positive hp)
  rw [pathPhase_eq_arg hT hp] at hc
  have ha := Complex.arg_nonneg_iff.mpr hi
  have ha' := Complex.arg_lt_pi_div_two_iff.mpr
    (Or.inl (hp (1 / 2) (by norm_num)))
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at ha'
  have he : Real.pi * (ZetaFiniteZeroCount.count T : ℝ) = 2 * Real.pi +
      2 * (GammaPhaseApproximation.theta T + (riemannZeta ((1 / 2 : ℂ) + T * I)).arg) := by
    rw [hc]
    field_simp
  have hlow : (2 * (m : ℝ) + 1) < ZetaFiniteZeroCount.count T := by nlinarith [Real.pi_pos]
  have hupp : (ZetaFiniteZeroCount.count T : ℝ) < 2 * (m : ℝ) + 3 := by nlinarith [Real.pi_pos]
  have hlow' : 2 * m + 1 < ZetaFiniteZeroCount.count T := by exact_mod_cast hlow
  have hupp' : ZetaFiniteZeroCount.count T < 2 * m + 3 := by exact_mod_cast hupp
  omega

end
end RiemannGaussian.ZetaCountingEndpoint
