/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldExplicitFormula
import RiemannGaussian.RosserSchoenfeldZeroTail
import RiemannGaussian.RosserSchoenfeldZeroFree

/-!
# Quantitative smoothed prime error from the proved zero-free region

The exact prime formula is retained. Below an arbitrary height cutoff,
the proved signed-pole region gives exponential suppression. Above it,
the complete positive Poisson comparison pays every omitted zero. The
result has explicit constants and no unevaluated starting height.
-/

namespace RiemannGaussian.RosserSchoenfeldSmoothedError
noncomputable section
open Complex
open scoped Classical

/-- Every zero below the cutoff obeys its uniform proved edge margin. -/
theorem re_le_cutoff_edge {T : ℝ} (hT : 0 ≤ T) (ρ : NontrivialZetaZero)
    (hρ : |ρ.1.im| ≤ T) : ρ.1.re ≤ 1-zetaSignedPoleZeroMargin T := by
  have hh : zetaSignedPoleZeroMargin T ≤ zetaSignedPoleZeroMargin ρ.1.im := by
    unfold zetaSignedPoleZeroMargin
    apply div_le_div_of_nonneg_left (by norm_num) (zetaSignedPole_denominator_pos ρ.1.im)
    have hl := Real.log_le_log (by positivity : 0 < |ρ.1.im|+2)
      (show |ρ.1.im|+2 ≤ T+2 by linarith)
    rw [abs_of_nonneg hT]
    linarith
  linarith [zetaSignedPole_margin_lt_one_sub_re ρ]

private theorem norm_term_le_actual (ρ : NontrivialZetaZero) (t : ℝ) :
    ‖RosserSchoenfeldZeroPrimitive.term ρ t‖ ≤
      (Real.exp (ρ.1.re*t)+1)*((analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^2) := by
  have hh := norm_sub_le (Complex.exp ((ρ.1 : ℂ)*t)) 1
  rw [Complex.norm_exp] at hh
  norm_num [Complex.mul_re] at hh
  unfold RosserSchoenfeldZeroPrimitive.term RosserSchoenfeldZeroPrimitive.atom
  rw [norm_mul, Complex.norm_natCast, norm_div, norm_pow]
  have hc := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hh (sq_nonneg ‖(ρ.1 : ℂ)‖))
    (Nat.cast_nonneg (analyticZetaZeroMultiplicity ρ) : (0 : ℝ) ≤ analyticZetaZeroMultiplicity ρ)
  convert! hc using 1
  ring

private theorem norm_term_le_split {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t)
    (ρ : NontrivialZetaZero) :
    ‖RosserSchoenfeldZeroPrimitive.term ρ t‖ ≤
      (Real.exp ((1-zetaSignedPoleZeroMargin T)*t)+1)*
        ((analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^2)+
      Real.exp t*RosserSchoenfeldZeroTail.term T ρ := by
  have hw : 0 ≤ (analyticZetaZeroMultiplicity ρ : ℝ)/‖(ρ.1 : ℂ)‖^2 := by positivity
  by_cases hρ : T ≤ |ρ.1.im|
  · rw [RosserSchoenfeldZeroTail.term, if_pos hρ]
    have hh := RosserSchoenfeldZeroPrimitive.norm_term_le ρ ht
    have hp := mul_nonneg (Real.exp_nonneg ((1-zetaSignedPoleZeroMargin T)*t)) hw
    nlinarith only [hh, hp]
  · rw [RosserSchoenfeldZeroTail.term, if_neg hρ, mul_zero, add_zero]
    apply (norm_term_le_actual ρ t).trans
    apply mul_le_mul_of_nonneg_right _ hw
    exact add_le_add (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (re_le_cutoff_edge hT ρ (le_of_not_ge hρ)) ht)) le_rfl

/-- The complete zero primitive has a cutoff-dependent exponential error bound. -/
theorem norm_zero_value_lt {T t : ℝ} (hT : 2 ≤ T) (ht : 0 ≤ t) :
    ‖RosserSchoenfeldZeroPrimitive.value t‖ <
      (463/10000 : ℝ)*(Real.exp ((1-zetaSignedPoleZeroMargin T)*t)+1)+
        Real.exp t*((8+2*Real.log T)/T) := by
  have ha := RosserSchoenfeldZeroMass.norm_square_mass_summable.mul_left
    (Real.exp ((1-zetaSignedPoleZeroMargin T)*t)+1)
  have hb := (RosserSchoenfeldZeroTail.summable_term T).mul_left (Real.exp t)
  have hh := (RosserSchoenfeldZeroPrimitive.summable_norm_term ht).tsum_le_tsum
    (norm_term_le_split (by linarith : 0 ≤ T) ht) (ha.add hb)
  rw [ha.tsum_add hb, tsum_mul_left, tsum_mul_left] at hh
  have ha' := mul_lt_mul_of_pos_left RosserSchoenfeldZeroMass.norm_square_mass_lt
    (show 0 < Real.exp ((1-zetaSignedPoleZeroMargin T)*t)+1 by positivity)
  have hb' := mul_le_mul_of_nonneg_left (RosserSchoenfeldZeroTail.value_le hT)
    (Real.exp_nonneg t)
  apply ((norm_tsum_le_tsum_norm (RosserSchoenfeldZeroPrimitive.summable_norm_term ht)).trans hh).trans_lt
  simpa only [mul_comm, RosserSchoenfeldZeroTail.value] using add_lt_add_of_lt_of_le ha' hb'

/-- An explicit estimate for the actual smoothed prime sum using the proved
zero-free edge and a fully paid complete high-zero tail. -/
theorem norm_prime_sub_main_lt {T t : ℝ} (hT : 2 ≤ T) (ht : 0 ≤ t) :
    ‖(RosserSchoenfeldPrimePrimitive.value t : ℂ)-RosserSchoenfeldExplicitFormula.mainTerm t‖ <
      (463/10000 : ℝ)*(Real.exp ((1-zetaSignedPoleZeroMargin T)*t)+1)+
        Real.exp t*((8+2*Real.log T)/T)+Real.pi^2/24 := by
  rw [RosserSchoenfeldExplicitFormula.prime_eq_spectral ht,
    RosserSchoenfeldExplicitFormula.spectral]
  have he : RosserSchoenfeldExplicitFormula.mainTerm t-
      RosserSchoenfeldZeroPrimitive.value t+RosserSchoenfeldTrivialPrimitive.value t-
      RosserSchoenfeldExplicitFormula.mainTerm t =
        -RosserSchoenfeldZeroPrimitive.value t+RosserSchoenfeldTrivialPrimitive.value t := by ring
  rw [he]
  calc
    _ ≤ ‖RosserSchoenfeldZeroPrimitive.value t‖+‖RosserSchoenfeldTrivialPrimitive.value t‖ := by
      simpa only [norm_neg] using norm_add_le
        (-RosserSchoenfeldZeroPrimitive.value t) (RosserSchoenfeldTrivialPrimitive.value t)
    _ < _ := add_lt_add_of_lt_of_le (norm_zero_value_lt hT ht)
      (RosserSchoenfeldTrivialPrimitive.norm_value_le ht)

end
end RiemannGaussian.RosserSchoenfeldSmoothedError
