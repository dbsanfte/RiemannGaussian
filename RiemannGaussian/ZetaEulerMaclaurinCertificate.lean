/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerMaclaurinEnclosure

/-!
# A checked nonvanishing test for actual zeta on complex rectangles

The test checks the input geometry, the complete finite approximation and
its separation from zero after paying the proved Euler--Maclaurin error.
It does not assume a numerical zeta value or a zero list. A successful
check applies to every point of the input rectangle, not just its center.
-/

namespace RiemannGaussian.ZetaEulerMaclaurinCertificate
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaEulerMaclaurinEnclosure

/-- A rational absolute bound for either coordinate of a rectangle. -/
def magnitude (I : IntervalDyadic) : ℚ := max |I.lo.toRat| |I.hi.toRat|

/-- The endpoint maximum bounds every enclosed real coordinate. -/
theorem abs_le_magnitude {x : ℝ} {I : IntervalDyadic} (h : x ∈ I) :
    |x| ≤ (magnitude I : ℝ) := by
  have hlo : (|I.lo.toRat| : ℝ) ≤ (magnitude I : ℝ) := by
    exact_mod_cast le_max_left |I.lo.toRat| |I.hi.toRat|
  have hhi : (|I.hi.toRat| : ℝ) ≤ (magnitude I : ℝ) := by
    exact_mod_cast le_max_right |I.lo.toRat| |I.hi.toRat|
  exact abs_le.mpr ⟨(neg_le_neg hlo).trans ((neg_abs_le _).trans h.1),
    h.2.trans ((le_abs_self _).trans hhi)⟩

/-- The proved analytic error allowance, represented by an exact rational. -/
def errorAllowance : ℚ := 1 / 10 ^ 12

/-- Check every analytic side condition by exact rational comparisons. -/
def admissible (cfg : DyadicConfig) (N : ℕ) (A : Box) : Bool := decide
  (cfg.precision ≤ 0 ∧ N ≤ 22020 ∧ (1 / 2 : ℚ) ≤ A.re.lo.toRat ∧
    magnitude A.re + magnitude A.im + 20 ≤ (N + 1 : ℚ) ∧
    (A.re.hi.toRat < 1 ∨ 1 < A.re.lo.toRat ∨ A.im.hi.toRat < 0 ∨ 0 < A.im.lo.toRat))

/-- Successful geometry checks supply the actual zeta remainder theorem. -/
theorem error_of_admissible {cfg : DyadicConfig} {N : ℕ} {A : Box}
    (h : admissible cfg N A = true) {s : ℂ} (hs : Mem s A) :
    cfg.precision ≤ 0 ∧
      ‖riemannZeta s - ZetaEulerMaclaurin.approximation N s 18‖ < (errorAllowance : ℝ) := by
  simp only [admissible, decide_eq_true_eq] at h
  obtain ⟨hp, hN, hsig, hnorm, hne⟩ := h
  have hsig' : 1 / 2 ≤ s.re := by
    have hh : (1 / 2 : ℝ) ≤ (A.re.lo.toRat : ℝ) := by
      calc (1 / 2 : ℝ) = ((1 / 2 : ℚ) : ℝ) := by norm_num
           _ ≤ _ := Rat.cast_le.mpr hsig
    exact hh.trans hs.1.1
  have hnorm' : ‖s‖ + 20 ≤ (N + 1 : ℝ) := by
    have hh : (magnitude A.re : ℝ) + (magnitude A.im : ℝ) + 20 ≤ (N + 1 : ℝ) := by
      exact_mod_cast hnorm
    have hh' := (Complex.norm_le_abs_re_add_abs_im s).trans
      (add_le_add (abs_le_magnitude hs.1) (abs_le_magnitude hs.2))
    linarith
  have hne' : s ≠ 1 := by
    intro he
    subst s
    rcases hne with hlt | hgt | hlt | hgt
    · have hh : (A.re.hi.toRat : ℝ) < 1 := by exact_mod_cast hlt
      exact (not_le_of_gt hh) hs.1.2
    · have hh : (1 : ℝ) < A.re.lo.toRat := by exact_mod_cast hgt
      exact (not_le_of_gt hh) hs.1.1
    · have hh : (A.im.hi.toRat : ℝ) < 0 := by exact_mod_cast hlt
      exact (not_le_of_gt hh) hs.2.2
    · have hh : (0 : ℝ) < A.im.lo.toRat := by exact_mod_cast hgt
      exact (not_le_of_gt hh) hs.2.1
  exact ⟨hp, by simpa only [errorAllowance, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_ofNat] using ZetaEulerMaclaurinBudget.uniform_error_of_norm hsig' hne' N hN hnorm'⟩

/-- Successful evaluation bounds both coordinates of actual zeta, with the
analytic truncation error added explicitly on both sides. -/
theorem coordinate_bounds {cfg : DyadicConfig} {N : ℕ} {A B : Box}
    (ha : admissible cfg N A = true) (he : evaluate cfg N 18 A = .ok B)
    {s : ℂ} (hs : Mem s A) :
    (B.re.lo.toRat : ℝ) - errorAllowance < (riemannZeta s).re ∧
    (riemannZeta s).re < (B.re.hi.toRat : ℝ) + errorAllowance ∧
    (B.im.lo.toRat : ℝ) - errorAllowance < (riemannZeta s).im ∧
    (riemannZeta s).im < (B.im.hi.toRat : ℝ) + errorAllowance := by
  obtain ⟨hp, herror⟩ := error_of_admissible ha hs
  have hb := mem_evaluate hp hs N 18 he
  have hr := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt herror)
  have hi := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt herror)
  simp only [Complex.sub_re, Complex.sub_im] at hr hi
  obtain ⟨⟨hlr, hur⟩, ⟨hli, hui⟩⟩ := hb
  exact ⟨by linarith [hr.1], by linarith [hr.2], by linarith [hi.1], by linarith [hi.2]⟩

/-- Separation by the full error allowance in at least one signed coordinate. -/
def separated (B : Box) : Bool := decide
  (B.re.hi.toRat ≤ -errorAllowance ∨ errorAllowance ≤ B.re.lo.toRat ∨
   B.im.hi.toRat ≤ -errorAllowance ∨ errorAllowance ≤ B.im.lo.toRat)

/-- A fully computable zero-exclusion test; failed domain or evaluation
checks return false and yield no mathematical conclusion. -/
def check (cfg : DyadicConfig) (N : ℕ) (A : Box) : Bool :=
  admissible cfg N A && match evaluate cfg N 18 A with
    | .error _ => false
    | .ok B => separated B

/-- A successful test proves actual zeta nonzero throughout the input rectangle. -/
theorem nonzero_of_check {cfg : DyadicConfig} {N : ℕ} {A : Box}
    (h : check cfg N A = true) {s : ℂ} (hs : Mem s A) : riemannZeta s ≠ 0 := by
  unfold check at h
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h
  cases he : evaluate cfg N 18 A with
  | error err => simp only [he, Bool.false_eq_true] at hb
  | ok B =>
    simp only [he, separated, decide_eq_true_eq] at hb
    obtain ⟨hlr, hur, hli, hui⟩ := coordinate_bounds ha he hs
    intro hz
    simp only [hz, Complex.zero_re, Complex.zero_im] at hlr hur hli hui
    rcases hb with hb | hb | hb | hb
    · have hh : (B.re.hi.toRat : ℝ) ≤ -(errorAllowance : ℝ) := by exact_mod_cast hb
      linarith
    · have hh : (errorAllowance : ℝ) ≤ B.re.lo.toRat := by exact_mod_cast hb
      linarith
    · have hh : (B.im.hi.toRat : ℝ) ≤ -(errorAllowance : ℝ) := by exact_mod_cast hb
      linarith
    · have hh : (errorAllowance : ℝ) ≤ B.im.lo.toRat := by exact_mod_cast hb
      linarith

end RiemannGaussian.ZetaEulerMaclaurinCertificate
