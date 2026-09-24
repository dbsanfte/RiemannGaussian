/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteThetaData01

/-!
# Checked finite Chebyshev cells: batch 3 of seven

Every primorial comparison is checked by kernel reduction against the
complete prime catalog. The closed cells include their boundary points.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteTheta
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

private theorem endpoint_2821 : (2772 : ℝ) < Chebyshev.theta 2821 ∧
    Chebyshev.theta 2821 < 2773 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_2938 : (2876 : ℝ) < Chebyshev.theta 2938 ∧
    Chebyshev.theta 2938 < 2877 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_3048 : (2980 : ℝ) < Chebyshev.theta 3048 ∧
    Chebyshev.theta 3048 < 2981 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_3157 : (3060 : ℝ) < Chebyshev.theta 3157 ∧
    Chebyshev.theta 3157 < 3061 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_3243 : (3149 : ℝ) < Chebyshev.theta 3243 ∧
    Chebyshev.theta 3243 < 3150 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_3336 : (3254 : ℝ) < Chebyshev.theta 3336 ∧
    Chebyshev.theta 3336 < 3255 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_3446 : (3343 : ℝ) < Chebyshev.theta 3446 ∧
    Chebyshev.theta 3446 < 3345 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_3541 : (3466 : ℝ) < Chebyshev.theta 3541 ∧
    Chebyshev.theta 3541 < 3467 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_3668 : (3589 : ℝ) < Chebyshev.theta 3668 ∧
    Chebyshev.theta 3668 < 3590 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

/-- An exact checked enclosure at the shared boundary of consecutive batches. -/
theorem endpoint_3798 : (3728 : ℝ) < Chebyshev.theta 3798 ∧
    Chebyshev.theta 3798 < 3730 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem checked_20 : checkCell 2716 2821 2661 2773 = true := by
  decide +kernel

private theorem cell_20 (x : ℝ) (hx : x ∈ Set.Icc (2716 : ℝ) 2821) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2716.1 endpoint_2821.2 checked_20 hx

private theorem checked_21 : checkCell 2821 2938 2772 2877 = true := by
  decide +kernel

private theorem cell_21 (x : ℝ) (hx : x ∈ Set.Icc (2821 : ℝ) 2938) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2821.1 endpoint_2938.2 checked_21 hx

private theorem checked_22 : checkCell 2938 3048 2876 2981 = true := by
  decide +kernel

private theorem cell_22 (x : ℝ) (hx : x ∈ Set.Icc (2938 : ℝ) 3048) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_2938.1 endpoint_3048.2 checked_22 hx

private theorem checked_23 : checkCell 3048 3157 2980 3061 = true := by
  decide +kernel

private theorem cell_23 (x : ℝ) (hx : x ∈ Set.Icc (3048 : ℝ) 3157) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_3048.1 endpoint_3157.2 checked_23 hx

private theorem checked_24 : checkCell 3157 3243 3060 3150 = true := by
  decide +kernel

private theorem cell_24 (x : ℝ) (hx : x ∈ Set.Icc (3157 : ℝ) 3243) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_3157.1 endpoint_3243.2 checked_24 hx

private theorem checked_25 : checkCell 3243 3336 3149 3255 = true := by
  decide +kernel

private theorem cell_25 (x : ℝ) (hx : x ∈ Set.Icc (3243 : ℝ) 3336) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_3243.1 endpoint_3336.2 checked_25 hx

private theorem checked_26 : checkCell 3336 3446 3254 3345 = true := by
  decide +kernel

private theorem cell_26 (x : ℝ) (hx : x ∈ Set.Icc (3336 : ℝ) 3446) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_3336.1 endpoint_3446.2 checked_26 hx

private theorem checked_27 : checkCell 3446 3541 3343 3467 = true := by
  decide +kernel

private theorem cell_27 (x : ℝ) (hx : x ∈ Set.Icc (3446 : ℝ) 3541) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_3446.1 endpoint_3541.2 checked_27 hx

private theorem checked_28 : checkCell 3541 3668 3466 3590 = true := by
  decide +kernel

private theorem cell_28 (x : ℝ) (hx : x ∈ Set.Icc (3541 : ℝ) 3668) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_3541.1 endpoint_3668.2 checked_28 hx

private theorem checked_29 : checkCell 3668 3798 3589 3730 = true := by
  decide +kernel

private theorem cell_29 (x : ℝ) (hx : x ∈ Set.Icc (3668 : ℝ) 3798) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_3668.1 endpoint_3798.2 checked_29 hx

/-- Both strict theta allowances on this complete closed batch interval. -/
theorem bounds_chunk02 : ∀ x ∈ Set.Icc (2716 : ℝ) 3798,
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x := by
  exact (join (join (join cell_20 cell_21) (join cell_22 (join cell_23 cell_24))) (join (join cell_25 cell_26) (join cell_27 (join cell_28 cell_29))))

end RiemannGaussian.RosserSchoenfeldFiniteTheta
