/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteThetaData03

/-!
# Checked finite Chebyshev cells: batch 5 of seven

Every primorial comparison is checked by kernel reduction against the
complete prime catalog. The closed cells include their boundary points.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteTheta
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

private theorem endpoint_5643 : (5528 : ℝ) < Chebyshev.theta 5643 ∧
    Chebyshev.theta 5643 < 5530 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_5833 : (5736 : ℝ) < Chebyshev.theta 5833 ∧
    Chebyshev.theta 5833 < 5738 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_6050 : (5945 : ℝ) < Chebyshev.theta 6050 ∧
    Chebyshev.theta 6050 < 5946 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_6270 : (6171 : ℝ) < Chebyshev.theta 6270 ∧
    Chebyshev.theta 6270 < 6173 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_6506 : (6408 : ℝ) < Chebyshev.theta 6506 ∧
    Chebyshev.theta 6506 < 6409 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_6754 : (6645 : ℝ) < Chebyshev.theta 6754 ∧
    Chebyshev.theta 6754 < 6647 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_7003 : (6928 : ℝ) < Chebyshev.theta 7003 ∧
    Chebyshev.theta 7003 < 6930 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_7298 : (7186 : ℝ) < Chebyshev.theta 7298 ∧
    Chebyshev.theta 7298 < 7187 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_7570 : (7453 : ℝ) < Chebyshev.theta 7570 ∧
    Chebyshev.theta 7570 < 7455 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

/-- An exact checked enclosure at the shared boundary of consecutive batches. -/
theorem endpoint_7849 : (7730 : ℝ) < Chebyshev.theta 7849 ∧
    Chebyshev.theta 7849 < 7732 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem checked_40 : checkCell 5445 5643 5347 5530 = true := by
  decide +kernel

private theorem cell_40 (x : ℝ) (hx : x ∈ Set.Icc (5445 : ℝ) 5643) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_5445.1 endpoint_5643.2 checked_40 hx

private theorem checked_41 : checkCell 5643 5833 5528 5738 = true := by
  decide +kernel

private theorem cell_41 (x : ℝ) (hx : x ∈ Set.Icc (5643 : ℝ) 5833) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_5643.1 endpoint_5833.2 checked_41 hx

private theorem checked_42 : checkCell 5833 6050 5736 5946 = true := by
  decide +kernel

private theorem cell_42 (x : ℝ) (hx : x ∈ Set.Icc (5833 : ℝ) 6050) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_5833.1 endpoint_6050.2 checked_42 hx

private theorem checked_43 : checkCell 6050 6270 5945 6173 = true := by
  decide +kernel

private theorem cell_43 (x : ℝ) (hx : x ∈ Set.Icc (6050 : ℝ) 6270) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_6050.1 endpoint_6270.2 checked_43 hx

private theorem checked_44 : checkCell 6270 6506 6171 6409 = true := by
  decide +kernel

private theorem cell_44 (x : ℝ) (hx : x ∈ Set.Icc (6270 : ℝ) 6506) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_6270.1 endpoint_6506.2 checked_44 hx

private theorem checked_45 : checkCell 6506 6754 6408 6647 = true := by
  decide +kernel

private theorem cell_45 (x : ℝ) (hx : x ∈ Set.Icc (6506 : ℝ) 6754) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_6506.1 endpoint_6754.2 checked_45 hx

private theorem checked_46 : checkCell 6754 7003 6645 6930 = true := by
  decide +kernel

private theorem cell_46 (x : ℝ) (hx : x ∈ Set.Icc (6754 : ℝ) 7003) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_6754.1 endpoint_7003.2 checked_46 hx

private theorem checked_47 : checkCell 7003 7298 6928 7187 = true := by
  decide +kernel

private theorem cell_47 (x : ℝ) (hx : x ∈ Set.Icc (7003 : ℝ) 7298) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_7003.1 endpoint_7298.2 checked_47 hx

private theorem checked_48 : checkCell 7298 7570 7186 7455 = true := by
  decide +kernel

private theorem cell_48 (x : ℝ) (hx : x ∈ Set.Icc (7298 : ℝ) 7570) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_7298.1 endpoint_7570.2 checked_48 hx

private theorem checked_49 : checkCell 7570 7849 7453 7732 = true := by
  decide +kernel

private theorem cell_49 (x : ℝ) (hx : x ∈ Set.Icc (7570 : ℝ) 7849) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_7570.1 endpoint_7849.2 checked_49 hx

/-- Both strict theta allowances on this complete closed batch interval. -/
theorem bounds_chunk04 : ∀ x ∈ Set.Icc (5445 : ℝ) 7849,
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x := by
  exact (join (join (join cell_40 cell_41) (join cell_42 (join cell_43 cell_44))) (join (join cell_45 cell_46) (join cell_47 (join cell_48 cell_49))))

end RiemannGaussian.RosserSchoenfeldFiniteTheta
