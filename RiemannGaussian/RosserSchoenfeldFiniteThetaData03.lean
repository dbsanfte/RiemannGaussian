/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteThetaData02

/-!
# Checked finite Chebyshev cells: batch 4 of seven

Every primorial comparison is checked by kernel reduction against the
complete prime catalog. The closed cells include their boundary points.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteTheta
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

private theorem endpoint_3943 : (3885 : ℝ) < Chebyshev.theta 3943 ∧
    Chebyshev.theta 3943 < 3887 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_4107 : (4035 : ℝ) < Chebyshev.theta 4107 ∧
    Chebyshev.theta 4107 < 4036 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_4265 : (4202 : ℝ) < Chebyshev.theta 4265 ∧
    Chebyshev.theta 4265 < 4203 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_4440 : (4344 : ℝ) < Chebyshev.theta 4440 ∧
    Chebyshev.theta 4440 < 4345 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_4591 : (4504 : ℝ) < Chebyshev.theta 4591 ∧
    Chebyshev.theta 4591 < 4505 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_4758 : (4664 : ℝ) < Chebyshev.theta 4758 ∧
    Chebyshev.theta 4758 < 4666 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_4927 : (4809 : ℝ) < Chebyshev.theta 4927 ∧
    Chebyshev.theta 4927 < 4810 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_5080 : (4987 : ℝ) < Chebyshev.theta 5080 ∧
    Chebyshev.theta 5080 < 4989 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_5265 : (5158 : ℝ) < Chebyshev.theta 5265 ∧
    Chebyshev.theta 5265 < 5160 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

/-- An exact checked enclosure at the shared boundary of consecutive batches. -/
theorem endpoint_5445 : (5347 : ℝ) < Chebyshev.theta 5445 ∧
    Chebyshev.theta 5445 < 5349 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem checked_30 : checkCell 3798 3943 3728 3887 = true := by
  decide +kernel

private theorem cell_30 (x : ℝ) (hx : x ∈ Set.Icc (3798 : ℝ) 3943) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_3798.1 endpoint_3943.2 checked_30 hx

private theorem checked_31 : checkCell 3943 4107 3885 4036 = true := by
  decide +kernel

private theorem cell_31 (x : ℝ) (hx : x ∈ Set.Icc (3943 : ℝ) 4107) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_3943.1 endpoint_4107.2 checked_31 hx

private theorem checked_32 : checkCell 4107 4265 4035 4203 = true := by
  decide +kernel

private theorem cell_32 (x : ℝ) (hx : x ∈ Set.Icc (4107 : ℝ) 4265) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_4107.1 endpoint_4265.2 checked_32 hx

private theorem checked_33 : checkCell 4265 4440 4202 4345 = true := by
  decide +kernel

private theorem cell_33 (x : ℝ) (hx : x ∈ Set.Icc (4265 : ℝ) 4440) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_4265.1 endpoint_4440.2 checked_33 hx

private theorem checked_34 : checkCell 4440 4591 4344 4505 = true := by
  decide +kernel

private theorem cell_34 (x : ℝ) (hx : x ∈ Set.Icc (4440 : ℝ) 4591) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_4440.1 endpoint_4591.2 checked_34 hx

private theorem checked_35 : checkCell 4591 4758 4504 4666 = true := by
  decide +kernel

private theorem cell_35 (x : ℝ) (hx : x ∈ Set.Icc (4591 : ℝ) 4758) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_4591.1 endpoint_4758.2 checked_35 hx

private theorem checked_36 : checkCell 4758 4927 4664 4810 = true := by
  decide +kernel

private theorem cell_36 (x : ℝ) (hx : x ∈ Set.Icc (4758 : ℝ) 4927) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_4758.1 endpoint_4927.2 checked_36 hx

private theorem checked_37 : checkCell 4927 5080 4809 4989 = true := by
  decide +kernel

private theorem cell_37 (x : ℝ) (hx : x ∈ Set.Icc (4927 : ℝ) 5080) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_4927.1 endpoint_5080.2 checked_37 hx

private theorem checked_38 : checkCell 5080 5265 4987 5160 = true := by
  decide +kernel

private theorem cell_38 (x : ℝ) (hx : x ∈ Set.Icc (5080 : ℝ) 5265) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_5080.1 endpoint_5265.2 checked_38 hx

private theorem checked_39 : checkCell 5265 5445 5158 5349 = true := by
  decide +kernel

private theorem cell_39 (x : ℝ) (hx : x ∈ Set.Icc (5265 : ℝ) 5445) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_5265.1 endpoint_5445.2 checked_39 hx

/-- Both strict theta allowances on this complete closed batch interval. -/
theorem bounds_chunk03 : ∀ x ∈ Set.Icc (3798 : ℝ) 5445,
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x := by
  exact (join (join (join cell_30 cell_31) (join cell_32 (join cell_33 cell_34))) (join (join cell_35 cell_36) (join cell_37 (join cell_38 cell_39))))

end RiemannGaussian.RosserSchoenfeldFiniteTheta
