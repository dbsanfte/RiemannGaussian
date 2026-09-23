/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DigammaMidpointApproximation
import RiemannGaussian.TrigammaHalfPlane

/-!
# Explicit approximation of the unwrapped Gamma phase

The phase is an integral of the actual logarithmic derivative, so no whole
turn is discarded. Shifting to the right pays an explicit finite sum of
arctangents. The remaining midpoint primitive has an error uniform in the
imaginary coordinate. This supplies a numerical analytic input for complete
low-zero counting, not a zero count or a finite RH certificate by itself.
-/

namespace RiemannGaussian.GammaPhaseApproximation
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped Interval

/-- The full continuous Gamma phase, normalized at the positive real axis. -/
def phase (a t : ℝ) : ℝ := ∫ y : ℝ in 0..t, (Complex.digamma ((a : ℂ) + y * I)).re

/-- The midpoint primitive, with its principal logarithm taken only in
the right half-plane. Its imaginary part is not reduced modulo a full turn. -/
def primitive (a t : ℝ) : ℝ :=
  (((a : ℂ) - 1 / 2 + t * I) * log ((a : ℂ) - 1 / 2 + t * I) -
    ((a : ℂ) - 1 / 2 + t * I)).im

/-- The primitive is a finite expression in real logarithms and arctangents. -/
theorem primitive_eq_real {a : ℝ} (ha : 1 / 2 < a) (t : ℝ) :
    primitive a t = (a - 1 / 2) * Real.arctan (t / (a - 1 / 2)) +
      t / 2 * Real.log ((a - 1 / 2) ^ 2 + t ^ 2) - t := by
  let z : ℂ := (a : ℂ) - 1 / 2 + t * I
  have hz : 0 < z.re := by simp [z]; linarith
  have harg : z.arg = Real.arctan (t / (a - 1 / 2)) := by
    have hh := Real.arctan_tan (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz))
      (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz))
    rw [Complex.tan_arg] at hh
    simpa [z] using hh.symm
  have hn : Real.log ‖z‖ = Real.log ((a - 1 / 2) ^ 2 + t ^ 2) / 2 := by
    rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg z)]
    simp [z, Complex.normSq_apply, pow_two]
  have hzre : z.re = a - 1 / 2 := by simp [z]
  have hzim : z.im = t := by simp [z]
  change (z * log z - z).im = _
  rw [Complex.sub_im, Complex.mul_im, Complex.log_im, Complex.log_re,
    harg, hn, hzre, hzim]
  ring

private theorem continuous_digamma_line {a : ℝ} (ha : 0 < a) :
    Continuous (fun t : ℝ => Complex.digamma ((a : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_digamma_euler (by simpa using ha)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y : ℝ => (a : ℂ) + y * I) t)

/-- The actual phase density is integrable on every finite vertical segment. -/
theorem phase_integrable {a : ℝ} (ha : 0 < a) (t : ℝ) :
    IntervalIntegrable (fun y : ℝ => (Complex.digamma ((a : ℂ) + y * I)).re)
      volume 0 t := (Complex.continuous_re.comp (continuous_digamma_line ha)).intervalIntegrable _ _

/-- The unwrapped phase differentiates to the actual digamma density. -/
theorem phase_hasDerivAt {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (phase a) (Complex.digamma ((a : ℂ) + t * I)).re t := by
  have hc := Complex.continuous_re.comp (continuous_digamma_line ha)
  exact intervalIntegral.integral_hasDerivAt_right (phase_integrable ha t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

private theorem continuous_log_line {a : ℝ} (ha : 1 / 2 < a) :
    Continuous (fun t : ℝ => log ((a : ℂ) - 1 / 2 + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hp : (a : ℂ) - 1 / 2 + t * I ∈ slitPlane :=
    Or.inl (by simp; linarith)
  exact (by fun_prop : ContinuousAt (fun y : ℝ => (a : ℂ) - 1 / 2 + y * I) t).clog hp

/-- Differentiating the full midpoint primitive retains the real logarithm
of the complex modulus with no phase wrapping. -/
theorem primitive_hasDerivAt {a : ℝ} (ha : 1 / 2 < a) (t : ℝ) :
    HasDerivAt (primitive a)
      (log ((a : ℂ) - 1 / 2 + t * I)).re t := by
  let p : ℝ → ℂ := fun y => (a : ℂ) - 1 / 2 + y * I
  have hp : HasDerivAt p I t := by
    simpa [p] using ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add ((a : ℂ) - 1 / 2)
  have hslit : p t ∈ slitPlane := Or.inl (by simp [p]; linarith)
  have hn : p t ≠ 0 := Complex.ne_zero_of_re_pos (by simpa [p] using sub_pos.mpr ha)
  have hg := (hp.mul (hp.clog_real hslit)).sub hp
  have he : I * log (p t) + p t * (I / p t) - I = I * log (p t) := by
    field_simp
    ring
  rw [he] at hg
  convert! Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hg using 1
  simp only [Complex.imCLM_apply, Complex.I_mul_im, p]

/-- The midpoint logarithmic density integrates to its explicit endpoint. -/
theorem integral_log_re {a : ℝ} (ha : 1 / 2 < a) (t : ℝ) :
    (∫ y : ℝ in 0..t, (log ((a : ℂ) - 1 / 2 + y * I)).re) = primitive a t := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => primitive_hasDerivAt ha y)
    ((Complex.continuous_re.comp (continuous_log_line ha)).intervalIntegrable 0 t)
  have hzero : primitive a 0 = 0 := by
    have hl : log ((a : ℂ) - 1 / 2) = (Real.log (a - 1 / 2) : ℂ) := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat] using (Complex.ofReal_log (by linarith : 0 ≤ a - 1 / 2)).symm
    simp only [primitive, Complex.ofReal_zero, zero_mul, add_zero]
    rw [hl]
    simp
  simpa only [hzero, sub_zero] using hh

/-- An independent error estimate for the actual unwrapped Gamma phase,
valid at every real height on a fixed right vertical line. -/
theorem abs_phase_sub_primitive_le {a : ℝ} (ha : 3 / 2 ≤ a) (t : ℝ) :
    |phase a t - primitive a t| ≤ |t| / (2 * (a - 1 / 2) ^ 2) := by
  have ha0 : 0 < a := by linarith
  have ha1 : 1 / 2 < a := by linarith
  have he : phase a t - primitive a t =
      ∫ y : ℝ in 0..t, (Complex.digamma ((a : ℂ) + y * I)).re -
        (log ((a : ℂ) - 1 / 2 + y * I)).re := by
    have hi : IntervalIntegrable (fun y : ℝ => (log ((a : ℂ) - 1 / 2 + y * I)).re)
        volume 0 t := (Complex.continuous_re.comp (continuous_log_line ha1)).intervalIntegrable 0 t
    rw [intervalIntegral.integral_sub (phase_integrable ha0 t) hi, integral_log_re ha1]
    rfl
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := t) (C := 1 / (2 * (a - 1 / 2) ^ 2))
    (f := fun y : ℝ => (Complex.digamma ((a : ℂ) + y * I)).re -
      (log ((a : ℂ) - 1 / 2 + y * I)).re) (by
      intro y _
      have hh := DigammaMidpointApproximation.norm_digamma_sub_log_midpoint_le
        (z := (a : ℂ) + y * I) (by simpa using ha)
      have hr := (Complex.abs_re_le_norm
        (Complex.digamma ((a : ℂ) + y * I) - log ((a : ℂ) + y * I - 1 / 2))).trans hh
      simpa only [Real.norm_eq_abs, sub_re, add_re, mul_re, ofReal_re, ofReal_im,
        I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero,
        show (a : ℂ) + y * I - 1 / 2 = (a : ℂ) - 1 / 2 + y * I by ring] using hr)
  rw [he]
  simpa only [Real.norm_eq_abs, sub_zero, div_eq_mul_inv, one_mul, mul_comm] using hb

/-- The exact Gamma shift pays one arctangent, with no reduction modulo `2*pi`. -/
theorem phase_add_one {a : ℝ} (ha : 0 < a) (t : ℝ) :
    phase (a + 1) t = phase a t + Real.arctan (t / a) := by
  have hd (y : ℝ) :
      (Complex.digamma (((a + 1 : ℝ) : ℂ) + y * I)).re =
        (Complex.digamma ((a : ℂ) + y * I)).re + a / (a ^ 2 + y ^ 2) := by
    have hh := Complex.digamma_apply_add_one ((a : ℂ) + y * I) (by
      intro m hm
      have hr := congrArg Complex.re hm
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, neg_re, natCast_re] at hr
      linarith [Nat.cast_nonneg (α := ℝ) m])
    rw [show (((a + 1 : ℝ) : ℂ) + y * I) = ((a : ℂ) + y * I) + 1 by push_cast; ring,
      hh, add_re]
    simp [Complex.inv_re, Complex.normSq_apply, pow_two]
  have hi : IntervalIntegrable (fun y : ℝ => a / (a ^ 2 + y ^ 2)) volume 0 t := by
    apply Continuous.intervalIntegrable
    apply continuous_const.div (by fun_prop)
    intro y
    positivity
  calc
    phase (a + 1) t = ∫ y : ℝ in 0..t,
        (Complex.digamma ((a : ℂ) + y * I)).re + a / (a ^ 2 + y ^ 2) := by
      apply intervalIntegral.integral_congr
      intro y _
      exact hd y
    _ = phase a t + Real.arctan (t / a) := by
      rw [intervalIntegral.integral_add (phase_integrable ha t) hi, integral_div_sq_add_sq]
      simp [phase]

/-- Finite Gamma shifting retains the entire continuous phase. -/
theorem phase_add_nat {a : ℝ} (ha : 0 < a) (M : ℕ) (t : ℝ) :
    phase (a + M) t = phase a t + ∑ n ∈ Finset.range M, Real.arctan (t / (a + n)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
      phase_add_one (by positivity : 0 < a + M), ih, Finset.sum_range_succ]
    ring

/-- A finite elementary approximation to the Gamma phase on any positive
vertical line, obtained by an explicit natural-number shift. -/
def shiftedApproximation (a : ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  primitive (a + M) t - ∑ n ∈ Finset.range M, Real.arctan (t / (a + n))

/-- Quantitative error for the finite shifted approximation; all analytic
premises concern the line and shift, not an assumed approximation. -/
theorem abs_phase_sub_shiftedApproximation_le {a : ℝ} (ha : 0 < a)
    (M : ℕ) (hM : 3 / 2 ≤ a + M) (t : ℝ) :
    |phase a t - shiftedApproximation a M t| ≤ |t| / (2 * (a + M - 1 / 2) ^ 2) := by
  have he : phase a t - shiftedApproximation a M t =
      phase (a + M) t - primitive (a + M) t := by
    rw [phase_add_nat ha]
    unfold shiftedApproximation
    ring
  rw [he]
  exact abs_phase_sub_primitive_le hM t

/-- The continuously unwrapped Riemann--Siegel theta phase, normalized at zero. -/
def theta (T : ℝ) : ℝ := phase (1 / 4) (T / 2) - T / 2 * Real.log Real.pi

/-- The explicit finite shifted approximation to the theta phase. -/
def thetaApproximation (M : ℕ) (T : ℝ) : ℝ :=
  shiftedApproximation (1 / 4) M (T / 2) - T / 2 * Real.log Real.pi

/-- A uniform, fully discharged phase error through the complete height range
needed by the Rosser--Schoenfeld low-zero verification. This is an analytic
input to a total count, not a total count itself. -/
theorem theta_error_lt_one_seventh {T : ℝ} (hT : |T| ≤ 22000) :
    |theta T - thetaApproximation 200 T| < 1 / 7 := by
  have he : theta T - thetaApproximation 200 T =
      phase (1 / 4) (T / 2) - shiftedApproximation (1 / 4) 200 (T / 2) := by
    unfold theta thetaApproximation
    ring
  rw [he]
  have hh := abs_phase_sub_shiftedApproximation_le (by norm_num : (0 : ℝ) < 1 / 4)
    200 (by norm_num) (T / 2)
  calc
    _ ≤ |T / 2| / (2 * ((1 / 4 : ℝ) + 200 - 1 / 2) ^ 2) := hh
    _ ≤ (22000 / 2 : ℝ) / (2 * ((1 / 4 : ℝ) + 200 - 1 / 2) ^ 2) := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hT (by norm_num))
        (by norm_num)
    _ < _ := by norm_num

end
end RiemannGaussian.GammaPhaseApproximation
