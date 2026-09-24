/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldSmoothedError
import RiemannGaussian.RosserSchoenfeldSmoothingBudget

/-!
# An explicit logarithmic-square error for the actual smoothed prime sum

At every logarithmic time at least 4900, the actual smoothed prime sum
differs from its elementary term by less than `exp(t)/(64*t^2)`.
The complete zero-free and high-zero estimates discharge the arithmetic
bound; the cutoff and all constants are explicit.
-/

namespace RiemannGaussian.RosserSchoenfeldLargeSmoothed
noncomputable section
open Real Complex
open RosserSchoenfeldSmoothingBudget

/-- The numerical smoothing error holds for the actual finite arithmetic sum. -/
theorem norm_prime_sub_main_lt {t : ℝ} (ht : 4900 ≤ t) :
    ‖(RosserSchoenfeldPrimePrimitive.value t : ℂ)-RosserSchoenfeldExplicitFormula.mainTerm t‖ <
      Real.exp t/(64*t^2) := by
  have ht0 : 0 < t := by linarith
  let r := Real.sqrt t
  have hr0 : 0 < r := Real.sqrt_pos.mpr ht0
  have hr2 : r^2 = t := Real.sq_sqrt ht0.le
  have hr : 70 ≤ r := by nlinarith
  let T := Real.exp ((3/8)*r)
  have hT : 2 ≤ T := cutoff_ge_two hr
  have hmargin := cutoff_margin hr
  change (4/15)/r ≤ zetaSignedPoleZeroMargin T at hmargin
  have hproduct : (4/15)*r ≤ zetaSignedPoleZeroMargin T*t := by
    have hh := mul_le_mul_of_nonneg_right hmargin ht0.le
    have he : ((4/15 : ℝ)/r)*t = (4/15)*r := by rw [← hr2]; field_simp
    rwa [he] at hh
  have he : Real.exp ((1-zetaSignedPoleZeroMargin T)*t) ≤
      Real.exp t*Real.exp (-(4/15)*r) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have htail : (8+2*Real.log T)/T = (8+(3/4)*r)*Real.exp (-(3/8)*r) := by
    dsimp [T]
    rw [Real.log_exp, neg_mul, Real.exp_neg, div_eq_mul_inv]
    ring
  have hconst : (463/10000 : ℝ)+Real.pi^2/24 ≤ 1 := by
    have hp0 := Real.pi_pos
    have hp := Real.pi_lt_four
    nlinarith
  have hexp : Real.exp t*Real.exp (-r^2) = 1 := by
    rw [hr2, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hb := RosserSchoenfeldSmoothedError.norm_prime_sub_main_lt hT ht0.le
  apply hb.trans_le
  calc
    _ ≤ (463/10000 : ℝ)*(Real.exp t*Real.exp (-(4/15)*r)+1)+
        Real.exp t*((8+(3/4)*r)*Real.exp (-(3/8)*r))+Real.pi^2/24 := by
      rw [htail]
      gcongr
    _ ≤ Real.exp t*((463/10000 : ℝ)*Real.exp (-(4/15)*r)+
        (8+(3/4)*r)*Real.exp (-(3/8)*r)+Real.exp (-r^2)) := by
      have hh : Real.exp t*((463/10000 : ℝ)*Real.exp (-(4/15)*r)+
          (8+(3/4)*r)*Real.exp (-(3/8)*r)+Real.exp (-r^2)) =
          (463/10000 : ℝ)*(Real.exp t*Real.exp (-(4/15)*r))+
            Real.exp t*((8+(3/4)*r)*Real.exp (-(3/8)*r))+1 := by
        rw [mul_add, hexp]
        ring
      rw [hh]
      linarith
    _ ≤ Real.exp t*(1/(64*r^4)) :=
      mul_le_mul_of_nonneg_left (exponential_budget hr) (Real.exp_nonneg t)
    _ = _ := by rw [show r^4 = t^2 by nlinarith only [hr2]]; ring

/-- The same estimate in real arithmetic, ready for monotone desmoothing. -/
theorem abs_prime_sub_main_lt {t : ℝ} (ht : 4900 ≤ t) :
    |RosserSchoenfeldPrimePrimitive.value t-
      (Real.exp t-1-Real.log (2*Real.pi)*t)| < Real.exp t/(64*t^2) := by
  have hh := norm_prime_sub_main_lt ht
  simpa only [RosserSchoenfeldExplicitFormula.mainTerm_eq, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hh

end
end RiemannGaussian.RosserSchoenfeldLargeSmoothed
