/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldZetaTwoBudget
import RiemannGaussian.RosserSchoenfeldZetaTwoSample

/-!
# A checked logarithmic derivative at two

An actual finite Euler--Maclaurin sample, with its complete analytic tail
and derivative remainder, bounds zeta's derivative on the real line.
The exact value zeta(2)=pi^2/6 yields the logarithmic-derivative estimate
needed by the fourth reciprocal zero mass.
-/

open Complex
namespace RiemannGaussian.RosserSchoenfeldZetaTwo
noncomputable section
open RosserSchoenfeldZetaTwoBudget

/-- An unconditional lower bound for the actual real derivative. -/
theorem derivative_lower :
    (-937548255/10^9 : ℝ) < (deriv riemannZeta 2).re := by
  have hpoint : RosserSchoenfeldZetaTwoSample.point = point := by
    rw [RosserSchoenfeldZetaTwoSample.point_eq]
    norm_num [point, height]
  have hnum := RosserSchoenfeldZetaTwoSample.approximation_im_lower
  rw [hpoint] at hnum
  have he := error point_geometry.1 point_geometry.2
  have hi := (Complex.abs_im_le_norm _).trans_lt he
  rw [Complex.sub_im] at hi
  have ha := (abs_lt.mp hi).1
  have hb := (abs_le.mp step_bound).2
  norm_num [height] at hb
  linarith

/-- The literal logarithmic derivative has this unconditional rational bound. -/
theorem log_derivative_upper :
    -(deriv riemannZeta 2 / riemannZeta 2).re < (569960994/10^9 : ℝ) := by
  have hd := derivative_lower
  have hp : (31415926535/10^10 : ℝ) < Real.pi := by
    have hh := Real.pi_gt_d20
    norm_num at hh
    linarith
  have hp2 : (31415926535/10^10 : ℝ)^2 < Real.pi^2 := by
    nlinarith [Real.pi_pos]
  have hζ : riemannZeta (2 : ℂ) = ((Real.pi^2/6 : ℝ) : ℂ) := by
    simpa only [ofReal_div, ofReal_pow, ofReal_ofNat] using riemannZeta_two
  rw [hζ, Complex.div_ofReal_re, ← neg_div]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < Real.pi^2/6)).mpr
  nlinarith

end
end RiemannGaussian.RosserSchoenfeldZetaTwo
