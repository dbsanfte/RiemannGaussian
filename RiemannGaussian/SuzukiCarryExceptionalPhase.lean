/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryMellinBranches

/-!
# Real phase equations for the carry source determinant

The real-height Mellin coefficients are real. Consequently the exceptional
equation is two real equations, and its imaginary equation alone gives a
sufficient source gate. No all-height nonvanishing is asserted here.
-/

namespace RiemannGaussian.SuzukiCarryExceptionalPhase
noncomputable section
open Complex MeasureTheory Filter
open SuzukiCarryMellinJet SuzukiCarryMellinBranches SuzukiCarryMellinLimit
open SuzukiCarryMellinRate
open scoped Topology ComplexConjugate

theorem B_conj (s : ℂ) : B (conj s) = conj (B s) := by
  rw [B, B, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]

theorem C_conj (s : ℂ) : C (conj s) = conj (C s) := by
  rw [C, C, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]

theorem B_ofReal (beta : ℝ) :
    B (beta : ℂ) =
      ((∫ t : ℝ, Real.exp (beta*t)*quadraticDensity (Real.exp t) : ℝ) : ℂ) := by
  rw [B, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]

theorem C_ofReal (beta : ℝ) :
    C (beta : ℂ) =
      ((∫ t : ℝ, Real.exp (beta*t)*quarticDensity (Real.exp t) : ℝ) : ℂ) := by
  rw [C, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]

@[simp] theorem B_ofReal_im (beta : ℝ) : (B (beta : ℂ)).im = 0 := by
  rw [B_ofReal]
  rfl

@[simp] theorem C_ofReal_im (beta : ℝ) : (C (beta : ℂ)).im = 0 := by
  rw [C_ofReal]
  rfl

theorem B_eq_ofReal_re (beta : ℝ) : B (beta : ℂ) = ((B (beta : ℂ)).re : ℂ) := by
  apply Complex.ext <;> simp

theorem C_eq_ofReal_re (beta : ℝ) : C (beta : ℂ) = ((C (beta : ℂ)).re : ℂ) := by
  apply Complex.ext <;> simp

/-- This is the imaginary equation of the actual wedge, with no density
sign assumption and no absolute values of individual cell contributions. -/
theorem wedge_im (beta : ℝ) (p : ℂ) :
    (B p*C (beta : ℂ)-C p*B (beta : ℂ)).im =
      (B p).im*(C (beta : ℂ)).re-(C p).im*(B (beta : ℂ)).re := by
  simp [Complex.sub_im, Complex.mul_im]

theorem wedge_re (beta : ℝ) (p : ℂ) :
    (B p*C (beta : ℂ)-C p*B (beta : ℂ)).re =
      (B p).re*(C (beta : ℂ)).re-(C p).re*(B (beta : ℂ)).re := by
  simp [Complex.sub_re, Complex.mul_re]

/-- Exact real exceptional locus. Either unequal real equation discharges
the source gate; neither equation has been certified on the whole strip. -/
theorem exceptional_iff_real_equations {beta : ℝ} (hb : 0 < beta) (y : ℝ) :
    exceptional beta y ↔
      (B (SuzukiCarryPoleCenter.poleExponent y)).re*(C (beta : ℂ)).re =
        (C (SuzukiCarryPoleCenter.poleExponent y)).re*(B (beta : ℂ)).re ∧
      (B (SuzukiCarryPoleCenter.poleExponent y)).im*(C (beta : ℂ)).re =
        (C (SuzukiCarryPoleCenter.poleExponent y)).im*(B (beta : ℂ)).re := by
  rw [exceptional_iff_wedge_zero hb y, Complex.ext_iff]
  simp only [Complex.zero_re, Complex.zero_im, wedge_re, wedge_im, sub_eq_zero]

theorem wedge_ne_zero_of_im {beta : ℝ} {p : ℂ}
    (h : (B p).im*(C (beta : ℂ)).re ≠ (C p).im*(B (beta : ℂ)).re) :
    B p*C (beta : ℂ)-C p*B (beta : ℂ) ≠ 0 := by
  intro hz
  have hi := congrArg Complex.im hz
  rw [wedge_im, Complex.zero_im, sub_eq_zero] at hi
  exact h hi

theorem wedge_zero_iff_ratio {beta : ℝ} {p : ℂ}
    (hp : B p ≠ 0) (hb : B (beta : ℂ) ≠ 0) :
    B p*C (beta : ℂ)-C p*B (beta : ℂ) = 0 ↔
      C p/B p = ((C (beta : ℂ)).re/(B (beta : ℂ)).re : ℝ) := by
  have hbr : (B (beta : ℂ)).re ≠ 0 := by
    intro hz
    apply hb
    rw [B_eq_ofReal_re, hz, Complex.ofReal_zero]
  rw [Complex.ofReal_div]
  rw [← B_eq_ofReal_re, ← C_eq_ofReal_re]
  rw [div_eq_div_iff hp hb, sub_eq_zero]
  constructor <;> intro h <;> simpa only [mul_comm] using h.symm

/-- A certified imaginary-phase separation immediately provides a fixed
positive code and a cofinal source-sized native determinant. -/
theorem exists_fixed_code_of_im_separation {beta : ℝ} (hb : 0 < beta) {y : ℝ}
    (h : (B (SuzukiCarryPoleCenter.poleExponent y)).im*(C (beta : ℂ)).re ≠
      (C (SuzukiCarryPoleCenter.poleExponent y)).im*(B (beta : ℂ)).re) :
    ∃ tau : ℝ, 0 < tau ∧
      continuumDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau ≠ 0 ∧
      ∀ᶠ H : ℕ in atTop,
        (‖continuumDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖/2)*
          Real.exp ((1+beta)*Real.log H) ≤
            ‖nativeDet H (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau‖ := by
  apply exists_fixed_code_of_not_exceptional hb
  exact mt (exceptional_iff_wedge_zero hb y).mp (wedge_ne_zero_of_im h)

end
end RiemannGaussian.SuzukiCarryExceptionalPhase
