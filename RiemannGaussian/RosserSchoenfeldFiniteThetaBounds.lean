/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteThetaData06

/-!
# Actual finite Chebyshev estimates through 16000

The complete prime catalog, exact primorial comparisons and 69 closed
logarithmic cells discharge the source's finite anchored theta range.
No intermediate or unbounded range is assumed or claimed here.
-/

namespace RiemannGaussian.RosserSchoenfeldFiniteTheta

/-- The original lower and upper theta allowances throughout the finite anchored range. -/
theorem bounds_through_sixteen_thousand {x : ℝ} (hx : x ∈ Set.Icc (1451 : ℝ) 16000) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x := by
  exact (join (join bounds_chunk00 (join bounds_chunk01 bounds_chunk02)) (join (join bounds_chunk03 bounds_chunk04) (join bounds_chunk05 bounds_chunk06))) x hx

/-- The strict source lower bound, in its original multiplicative form. -/
theorem lower_lt_theta {x : ℝ} (hx : x ∈ Set.Icc (1451 : ℝ) 16000) :
    x*(1-(47/100)/Real.log x) < Chebyshev.theta x := by
  convert! (bounds_through_sixteen_thousand hx).1 using 1
  ring

/-- The strict source upper bound, retaining the smaller coefficient 31/100. -/
theorem theta_lt_upper {x : ℝ} (hx : x ∈ Set.Icc (1451 : ℝ) 16000) :
    Chebyshev.theta x < x*(1+(31/100)/Real.log x) := by
  convert! (bounds_through_sixteen_thousand hx).2 using 1
  ring

end RiemannGaussian.RosserSchoenfeldFiniteTheta
