/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerMaclaurinCertificate

/-!
# Certified distances from actual zeta values to rational complex targets

The checked finite approximation and its analytic error give a strict
norm bound around an explicitly supplied target. This is the numerical
interface needed for a Newton isolation certificate.
-/

namespace RiemannGaussian.ZetaEulerMaclaurinValue
open Complex LeanCert.Core LeanCert.Engine CertifiedComplexInterval
open ZetaEulerMaclaurinEnclosure ZetaEulerMaclaurinCertificate

/-- Check a strict error ball around a rational complex target, retaining
both signed coordinates of the finite approximation. -/
def closeCheck (cfg : DyadicConfig) (N : ℕ) (A : Box) (re im eps : ℚ) : Bool :=
  admissible cfg N A && match evaluate cfg N 18 A with
  | .error _ => false
  | .ok B =>
    let D := add cfg.precision B (neg (rational cfg.precision re im))
    decide (magnitude D.re + magnitude D.im + errorAllowance ≤ eps)

/-- A successful distance check bounds the actual complex zeta value,
including every interval and truncation error. -/
theorem norm_sub_lt_of_closeCheck {cfg : DyadicConfig} {N : ℕ} {A : Box}
    {re im eps : ℚ} (h : closeCheck cfg N A re im eps = true)
    {s : ℂ} (hs : Mem s A) :
    ‖riemannZeta s - ((re : ℂ) + (im : ℂ) * I)‖ < (eps : ℝ) := by
  unfold closeCheck at h
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
  cases he : evaluate cfg N 18 A with
  | error err => simp only [he, Bool.false_eq_true] at hb
  | ok B =>
    simp only [he, decide_eq_true_eq] at hb
    obtain ⟨hp, herr⟩ := error_of_admissible ha hs
    have hm := mem_add (mem_evaluate hp hs N 18 he)
      (mem_neg (mem_rational hp re im)) cfg.precision
    have hn := (Complex.norm_le_abs_re_add_abs_im _).trans
      (add_le_add (abs_le_magnitude hm.1) (abs_le_magnitude hm.2))
    have hh :
        (magnitude (add cfg.precision B (neg (rational cfg.precision re im))).re : ℝ) +
        (magnitude (add cfg.precision B (neg (rational cfg.precision re im))).im : ℝ) +
        (errorAllowance : ℝ) ≤ eps := by exact_mod_cast hb
    have ht := norm_sub_le_norm_sub_add_norm_sub (riemannZeta s) (ZetaEulerMaclaurin.approximation N s 18)
      ((re : ℂ) + (im : ℂ) * I)
    simp only [← sub_eq_add_neg] at hn
    linarith

end RiemannGaussian.ZetaEulerMaclaurinValue
