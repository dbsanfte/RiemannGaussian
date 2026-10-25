/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldExplicitFormula
import RiemannGaussian.ZetaQuasiRHOpenAI

/-!
# The existing quasi-RH baseline for the actual smoothed prime primitive

This transfers the attributed external seven-eighths theorem to a global
exponential envelope. It is an application of the existing baseline, not a
new zero-free region or a proof of the local all-exponent arithmetic target.
-/

namespace RiemannGaussian
noncomputable section
open Complex

/-- The imported strict seven-eighths half-plane bounds every actual nontrivial zero. -/
theorem suzukiLocalZero_re_le_seven_eighths (rho : NontrivialZetaZero) :
    rho.1.re ≤ 7 / 8 := by
  by_contra h
  exact ZetaQuasiRHOpenAI.nonvanishing (lt_of_not_ge h) rho.2.1

private theorem norm_zero_term_le_seven_eighths (rho : NontrivialZetaZero)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖RosserSchoenfeldZeroPrimitive.term rho t‖ ≤
      (Real.exp ((7 / 8 : ℝ) * t) + 1) *
        ((analyticZetaZeroMultiplicity rho : ℝ) / ‖rho.1‖ ^ 2) := by
  have hh := norm_sub_le (Complex.exp ((rho.1 : ℂ) * t)) 1
  rw [Complex.norm_exp] at hh
  norm_num [Complex.mul_re] at hh
  have he : Real.exp (rho.1.re * t) ≤ Real.exp ((7 / 8 : ℝ) * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (suzukiLocalZero_re_le_seven_eighths rho) ht)
  unfold RosserSchoenfeldZeroPrimitive.term RosserSchoenfeldZeroPrimitive.atom
  rw [norm_mul, Complex.norm_natCast, norm_div, norm_pow]
  have hn : ‖Complex.exp (rho.1 * t) - 1‖ ≤ Real.exp ((7 / 8 : ℝ) * t) + 1 :=
    hh.trans (by linarith)
  have hq := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hn (sq_nonneg ‖rho.1‖))
    (Nat.cast_nonneg (analyticZetaZeroMultiplicity rho) : (0 : ℝ) ≤ analyticZetaZeroMultiplicity rho)
  convert hq using 1
  ring

/-- The complete multiplicity-weighted zero primitive inherits the existing exponent. -/
theorem suzukiLocalZeroPrimitive_norm_le_seven_eighths {t : ℝ} (ht : 0 ≤ t) :
    ‖RosserSchoenfeldZeroPrimitive.value t‖ ≤
      (463 / 10000 : ℝ) * (Real.exp ((7 / 8 : ℝ) * t) + 1) := by
  have hs := RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left
    (Real.exp ((7 / 8 : ℝ) * t) + 1)
  have hb := (RosserSchoenfeldZeroPrimitive.summable_norm_term ht).tsum_le_tsum
    (fun rho => norm_zero_term_le_seven_eighths rho ht) hs
  rw [tsum_mul_left] at hb
  have hc := mul_le_mul_of_nonneg_left RosserSchoenfeldZeroMass.norm_square_mass_lt.le
    (show 0 ≤ Real.exp ((7 / 8 : ℝ) * t) + 1 by positivity)
  apply ((norm_tsum_le_tsum_norm
    (RosserSchoenfeldZeroPrimitive.summable_norm_term ht)).trans hb).trans
  simpa only [mul_comm] using hc

/-- A uniform all-time bound for the actual unweighted prime hinge primitive,
with the full affine main term and the existing external baseline retained. -/
theorem suzukiLocalPrimePrimitive_error_le_seven_eighths {t : ℝ} (ht : 0 ≤ t) :
    |RosserSchoenfeldPrimePrimitive.value t -
      (Real.exp t - 1 - Real.log (2 * Real.pi) * t)| ≤
      ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24) * Real.exp ((7 / 8 : ℝ) * t) := by
  have hz := suzukiLocalZeroPrimitive_norm_le_seven_eighths ht
  have hv := RosserSchoenfeldTrivialPrimitive.norm_value_le ht
  have he := RosserSchoenfeldExplicitFormula.prime_eq_spectral ht
  have hb : ‖(RosserSchoenfeldPrimePrimitive.value t : ℂ) -
      RosserSchoenfeldExplicitFormula.mainTerm t‖ ≤
      ‖RosserSchoenfeldZeroPrimitive.value t‖ +
        ‖RosserSchoenfeldTrivialPrimitive.value t‖ := by
    rw [he, RosserSchoenfeldExplicitFormula.spectral]
    rw [show RosserSchoenfeldExplicitFormula.mainTerm t -
        RosserSchoenfeldZeroPrimitive.value t + RosserSchoenfeldTrivialPrimitive.value t -
          RosserSchoenfeldExplicitFormula.mainTerm t =
        RosserSchoenfeldTrivialPrimitive.value t - RosserSchoenfeldZeroPrimitive.value t by ring]
    simpa only [add_comm] using norm_sub_le (RosserSchoenfeldTrivialPrimitive.value t)
      (RosserSchoenfeldZeroPrimitive.value t)
  have hexp : 1 ≤ Real.exp ((7 / 8 : ℝ) * t) := Real.one_le_exp_iff.mpr (by positivity)
  have hc : 0 ≤ Real.pi ^ 2 / 24 := by positivity
  have hh : ‖(RosserSchoenfeldPrimePrimitive.value t : ℂ) -
      RosserSchoenfeldExplicitFormula.mainTerm t‖ ≤
      ((463 / 5000 : ℝ) + Real.pi ^ 2 / 24) * Real.exp ((7 / 8 : ℝ) * t) := by
    nlinarith [mul_le_mul_of_nonneg_left hexp hc]
  simpa only [RosserSchoenfeldExplicitFormula.mainTerm_eq, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hh

end
end RiemannGaussian
