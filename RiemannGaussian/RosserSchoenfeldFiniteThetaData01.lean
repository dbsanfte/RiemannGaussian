/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteThetaData00

/-!
# Checked finite Chebyshev cells: batch 2 of seven

Every primorial comparison is checked by kernel reduction against the
complete prime catalog. The closed cells include their boundary points.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteTheta
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

private theorem endpoint_2070 : (2008 : ℝ) < Chebyshev.theta 2070 ∧
    Chebyshev.theta 2070 < 2009 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_2134 : (2077 : ℝ) < Chebyshev.theta 2134 ∧
    Chebyshev.theta 2134 < 2078 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_2207 : (2138 : ℝ) < Chebyshev.theta 2207 ∧
    Chebyshev.theta 2207 < 2139 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_2272 : (2200 : ℝ) < Chebyshev.theta 2272 ∧
    Chebyshev.theta 2272 < 2201 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_2337 : (2262 : ℝ) < Chebyshev.theta 2337 ∧
    Chebyshev.theta 2337 < 2263 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_2403 : (2355 : ℝ) < Chebyshev.theta 2403 ∧
    Chebyshev.theta 2403 < 2356 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_2499 : (2433 : ℝ) < Chebyshev.theta 2499 ∧
    Chebyshev.theta 2499 < 2434 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_2582 : (2503 : ℝ) < Chebyshev.theta 2582 ∧
    Chebyshev.theta 2582 < 2505 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_2656 : (2559 : ℝ) < Chebyshev.theta 2656 ∧
    Chebyshev.theta 2656 < 2560 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

/-- An exact checked enclosure at the shared boundary of consecutive batches. -/
theorem endpoint_2716 : (2661 : ℝ) < Chebyshev.theta 2716 ∧
    Chebyshev.theta 2716 < 2662 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem checked_10 : checkCell 2006 2070 1947 2009 = true := by
  decide +kernel

private theorem cell_10 (x : ℝ) (hx : x ∈ Set.Icc (2006 : ℝ) 2070) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2006.1 endpoint_2070.2 checked_10 hx

private theorem checked_11 : checkCell 2070 2134 2008 2078 = true := by
  decide +kernel

private theorem cell_11 (x : ℝ) (hx : x ∈ Set.Icc (2070 : ℝ) 2134) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2070.1 endpoint_2134.2 checked_11 hx

private theorem checked_12 : checkCell 2134 2207 2077 2139 = true := by
  decide +kernel

private theorem cell_12 (x : ℝ) (hx : x ∈ Set.Icc (2134 : ℝ) 2207) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2134.1 endpoint_2207.2 checked_12 hx

private theorem checked_13 : checkCell 2207 2272 2138 2201 = true := by
  decide +kernel

private theorem cell_13 (x : ℝ) (hx : x ∈ Set.Icc (2207 : ℝ) 2272) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2207.1 endpoint_2272.2 checked_13 hx

private theorem checked_14 : checkCell 2272 2337 2200 2263 = true := by
  decide +kernel

private theorem cell_14 (x : ℝ) (hx : x ∈ Set.Icc (2272 : ℝ) 2337) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2272.1 endpoint_2337.2 checked_14 hx

private theorem checked_15 : checkCell 2337 2403 2262 2356 = true := by
  decide +kernel

private theorem cell_15 (x : ℝ) (hx : x ∈ Set.Icc (2337 : ℝ) 2403) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2337.1 endpoint_2403.2 checked_15 hx

private theorem checked_16 : checkCell 2403 2499 2355 2434 = true := by
  decide +kernel

private theorem cell_16 (x : ℝ) (hx : x ∈ Set.Icc (2403 : ℝ) 2499) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2403.1 endpoint_2499.2 checked_16 hx

private theorem checked_17 : checkCell 2499 2582 2433 2505 = true := by
  decide +kernel

private theorem cell_17 (x : ℝ) (hx : x ∈ Set.Icc (2499 : ℝ) 2582) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2499.1 endpoint_2582.2 checked_17 hx

private theorem checked_18 : checkCell 2582 2656 2503 2560 = true := by
  decide +kernel

private theorem cell_18 (x : ℝ) (hx : x ∈ Set.Icc (2582 : ℝ) 2656) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2582.1 endpoint_2656.2 checked_18 hx

private theorem checked_19 : checkCell 2656 2716 2559 2662 = true := by
  decide +kernel

private theorem cell_19 (x : ℝ) (hx : x ∈ Set.Icc (2656 : ℝ) 2716) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2656.1 endpoint_2716.2 checked_19 hx

/-- Both strict theta allowances on this complete closed batch interval. -/
theorem bounds_chunk01 : ∀ x ∈ Set.Icc (2006 : ℝ) 2716,
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x := by
  exact (join (join (join cell_10 cell_11) (join cell_12 (join cell_13 cell_14))) (join (join cell_15 cell_16) (join cell_17 (join cell_18 cell_19))))

end RiemannGaussian.RosserSchoenfeldFiniteTheta
