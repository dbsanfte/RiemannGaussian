/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianHalfLaplaceMoments

/-!
# Complex half-Gaussian moments with exact endpoints

Every polynomial moment is genuinely integrable at every complex damping
and every positive Gaussian scale. Its phase and endpoint survive the full
integration-by-parts recurrence. Three recurrences isolate the complete
inverse-cube pole remainder without taking norms of intermediate terms.
-/

namespace RiemannGaussian.GaussianComplexHalfMoments
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology
open GaussianFermiZeroPair

/-- The complete complex Gaussian monomial, including its original damping phase. -/
def atom (B : ℝ) (n : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  ((t ^ n * window B t : ℝ) : ℂ) * Complex.exp (-z * (t : ℂ))

/-- The genuine half-line moment of the original complex Gaussian atom. -/
def moment (B : ℝ) (n : ℕ) (z : ℂ) : ℂ := ∫ t in Ioi (0 : ℝ), atom B n z t

/-- The undivided original half-Gaussian Laplace transform. -/
def transform (B : ℝ) (z : ℂ) : ℂ := moment B 0 z

/-- Its exact norm retains the real damping and polynomial order. -/
theorem norm_atom (B : ℝ) (n : ℕ) (z : ℂ) (t : ℝ) :
    ‖atom B n z t‖ = |t| ^ n * window B t * Real.exp (-z.re * t) := by
  rw [atom, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_pos (show 0 < window B t from Real.exp_pos _), Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

private theorem norm_atom_le {B : ℝ} (hB : 0 < B) (n : ℕ) (z : ℂ) (t : ℝ) :
    ‖atom B n z t‖ ≤ Real.exp (z.re ^ 2 / (2 * B)) *
      (|t| ^ n * Real.exp (-(B / 2) * t ^ 2)) := by
  have hq : -(B / 2) * t ^ 2 - z.re * t ≤ z.re ^ 2 / (2 * B) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * B)).mpr
    nlinarith [sq_nonneg (B * t + z.re)]
  have he : window B t * Real.exp (-z.re * t) ≤
      Real.exp (z.re ^ 2 / (2 * B)) * Real.exp (-(B / 2) * t ^ 2) := by
    unfold window
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [norm_atom, mul_assoc]
  have h := mul_le_mul_of_nonneg_left he (pow_nonneg (abs_nonneg t) n)
  nlinarith only [h]

/-- Every original complex polynomial moment is absolutely integrable,
including negative real damping; no convergence assumption is left over. -/
theorem integrable_atom {B : ℝ} (hB : 0 < B) (n : ℕ) (z : ℂ) :
    Integrable (atom B n z) := by
  have hg : Integrable (fun t : ℝ => t ^ n * Real.exp (-(B / 2) * t ^ 2)) := by
    simpa only [Real.rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq
      (half_pos hB) (show (-1 : ℝ) < (n : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hb : Integrable (fun t : ℝ => Real.exp (z.re ^ 2 / (2 * B)) *
      (|t| ^ n * Real.exp (-(B / 2) * t ^ 2))) := by
    simpa [norm_mul, Real.norm_eq_abs, abs_pow, Real.exp_pos] using
      hg.norm.const_mul (Real.exp (z.re ^ 2 / (2 * B)))
  exact hb.mono' (by unfold atom window; fun_prop) (Eventually.of_forall (norm_atom_le hB n z))

/-- The original complex monomial has zero boundary value at positive infinity. -/
theorem tendsto_atom {B : ℝ} (hB : 0 < B) (n : ℕ) (z : ℂ) :
    Tendsto (atom B n z) atTop (𝓝 0) := by
  have hf : (atTop : Filter ℝ) ≤ cocompact ℝ := by
    rw [cocompact_eq_atBot_atTop]
    exact le_sup_right
  have hg := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (half_pos hB) (n : ℝ)).mono_left hf
  have hb : Tendsto (fun t : ℝ => Real.exp (z.re ^ 2 / (2 * B)) *
      (|t| ^ n * Real.exp (-(B / 2) * t ^ 2))) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using hg.const_mul (Real.exp (z.re ^ 2 / (2 * B)))
  exact squeeze_zero_norm (norm_atom_le hB n z) hb

private theorem hasDerivAt_atom_zero (B : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (atom B 0 z) (-2 * (B : ℂ) * atom B 1 z t - z * atom B 0 z t) t := by
  have hg := ((((hasDerivAt_id t).pow 2).const_mul (-B)).exp).ofReal_comp
  have hp := (((hasDerivAt_id t).ofReal_comp).const_mul (-z)).cexp
  convert! hg.mul hp using 1
  · ext u
    simp [atom, window]
  · simp [atom, window]
    ring

/-- The first signed recurrence keeps the nonzero endpoint exactly. -/
theorem moment_one {B : ℝ} (hB : 0 < B) (z : ℂ) :
    2 * (B : ℂ) * moment B 1 z + z * moment B 0 z = 1 := by
  have hi := ((integrable_atom hB 1 z).const_mul (-2 * (B : ℂ))).sub
    ((integrable_atom hB 0 z).const_mul z)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun t _ => hasDerivAt_atom_zero B z t) hi.integrableOn (tendsto_atom hB 0 z)
  rw [integral_sub ((integrable_atom hB 1 z).const_mul (-2 * (B : ℂ))).integrableOn
    ((integrable_atom hB 0 z).const_mul z).integrableOn,
    integral_const_mul, integral_const_mul] at h
  rw [show atom B 0 z 0 = 1 by simp [atom, window], zero_sub] at h
  change -2 * (B : ℂ) * moment B 1 z - z * moment B 0 z = -1 at h
  linear_combination -h

private theorem hasDerivAt_atom_succ (B : ℝ) (n : ℕ) (z : ℂ) (t : ℝ) :
    HasDerivAt (atom B (n + 1) z)
      (((n + 1 : ℕ) : ℂ) * atom B n z t - z * atom B (n + 1) z t -
        2 * (B : ℂ) * atom B (n + 2) z t) t := by
  have h := (((hasDerivAt_id t).pow (n + 1)).ofReal_comp).mul (hasDerivAt_atom_zero B z t)
  convert! h using 1
  · ext u
    simp [atom, mul_assoc]
  · simp only [atom, pow_zero, pow_one, one_mul, Pi.pow_apply, id_eq, Nat.add_sub_cancel]
    rw [pow_succ, show t ^ (n + 2) = t ^ n * t ^ 2 by ring]
    push_cast
    ring

/-- Every higher moment satisfies the complete complex three-term recurrence. -/
theorem moment_recurrence {B : ℝ} (hB : 0 < B) (n : ℕ) (z : ℂ) :
    2 * (B : ℂ) * moment B (n + 2) z + z * moment B (n + 1) z =
      ((n + 1 : ℕ) : ℂ) * moment B n z := by
  have hfirst : Integrable (fun t : ℝ => ((n + 1 : ℕ) : ℂ) * atom B n z t -
      z * atom B (n + 1) z t) := ((integrable_atom hB n z).const_mul ((n + 1 : ℕ) : ℂ)).sub
    ((integrable_atom hB (n + 1) z).const_mul z)
  have hi := hfirst.sub ((integrable_atom hB (n + 2) z).const_mul (2 * (B : ℂ)))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
    (fun t _ => hasDerivAt_atom_succ B n z t) hi.integrableOn (tendsto_atom hB (n + 1) z)
  rw [integral_sub hfirst.integrableOn
    ((integrable_atom hB (n + 2) z).const_mul (2 * (B : ℂ))).integrableOn,
    integral_sub ((integrable_atom hB n z).const_mul ((n + 1 : ℕ) : ℂ)).integrableOn
      ((integrable_atom hB (n + 1) z).const_mul z).integrableOn,
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  rw [show atom B (n + 1) z 0 = 0 by simp [atom, window], sub_zero] at h
  change ((n + 1 : ℕ) : ℂ) * moment B n z - z * moment B (n + 1) z -
    2 * (B : ℂ) * moment B (n + 2) z = 0 at h
  linear_combination -h

/-- The full inverse-cube endpoint identity holds before any division,
including at the origin. Its two signed odd moments remain coupled. -/
theorem third_endpoint_identity {B : ℝ} (hB : 0 < B) (z : ℂ) :
    z ^ 3 * transform B z - z ^ 2 = -2 * (B : ℂ) +
      12 * (B : ℂ) ^ 2 * moment B 1 z - 8 * (B : ℂ) ^ 3 * moment B 3 z := by
  have h0 := moment_one hB z
  have h1 := moment_recurrence hB 0 z
  have h2 := moment_recurrence hB 1 z
  norm_num at h1 h2
  unfold transform
  linear_combination (z ^ 2 - 2 * (B : ℂ)) * h0 - 2 * (B : ℂ) * z * h1 +
    4 * (B : ℂ) ^ 2 * h2

/-- Real damping recovers the repository's original half-Gaussian transform exactly. -/
theorem transform_real (B x : ℝ) :
    transform B (x : ℂ) = (GaussianFermiLaplaceOrder.halfGaussian B x : ℂ) := by
  unfold transform moment atom GaussianFermiLaplaceOrder.halfGaussian
  simp only [pow_zero, one_mul, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp]
  simpa only using! (integral_complex_ofReal
    (f := fun t : ℝ => window B t * Real.exp (-x * t)) (μ := volume.restrict (Ioi (0 : ℝ))))

/-- The complete first odd Gaussian moment has its exact scale-dependent endpoint value. -/
theorem moment_one_zero {B : ℝ} (hB : 0 < B) :
    moment B 1 0 = 1 / (2 * (B : ℂ)) := by
  have h := moment_one hB 0
  simp only [zero_mul, add_zero] at h
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
    (Complex.ofReal_ne_zero.mpr hB.ne'))).mpr
  linear_combination h

/-- The complete third odd Gaussian moment is evaluated from the same signed recurrence. -/
theorem moment_three_zero {B : ℝ} (hB : 0 < B) :
    moment B 3 0 = 1 / (2 * (B : ℂ) ^ 2) := by
  have h := moment_recurrence hB 1 0
  norm_num at h
  rw [moment_one_zero hB] at h
  have hB0 := Complex.ofReal_ne_zero.mpr hB.ne'
  field_simp at h ⊢
  linear_combination h

end
end RiemannGaussian.GaussianComplexHalfMoments
