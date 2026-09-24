/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteThetaData05

/-!
# Checked finite Chebyshev cells: batch 7 of seven

Every primorial comparison is checked by kernel reduction against the
complete prime catalog. The closed cells include their boundary points.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteTheta
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

private theorem endpoint_11878 : (11698 : ℝ) < Chebyshev.theta 11878 ∧
    Chebyshev.theta 11878 < 11700 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_12290 : (12140 : ℝ) < Chebyshev.theta 12290 ∧
    Chebyshev.theta 12290 < 12142 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_12751 : (12621 : ℝ) < Chebyshev.theta 12751 ∧
    Chebyshev.theta 12751 < 12623 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_13252 : (13133 : ℝ) < Chebyshev.theta 13252 ∧
    Chebyshev.theta 13252 < 13135 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_13786 : (13656 : ℝ) < Chebyshev.theta 13786 ∧
    Chebyshev.theta 13786 < 13658 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_14333 : (14143 : ℝ) < Chebyshev.theta 14333 ∧
    Chebyshev.theta 14333 < 14145 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_14844 : (14699 : ℝ) < Chebyshev.theta 14844 ∧
    Chebyshev.theta 14844 < 14701 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_15422 : (15296 : ℝ) < Chebyshev.theta 15422 ∧
    Chebyshev.theta 15422 < 15298 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

/-- An exact checked enclosure at the shared boundary of consecutive batches. -/
theorem endpoint_16000 : (15885 : ℝ) < Chebyshev.theta 16000 ∧
    Chebyshev.theta 16000 < 15887 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem checked_60 : checkCell 11450 11878 11305 11700 = true := by
  decide +kernel

private theorem cell_60 (x : ℝ) (hx : x ∈ Set.Icc (11450 : ℝ) 11878) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_11450.1 endpoint_11878.2 checked_60 hx

private theorem checked_61 : checkCell 11878 12290 11698 12142 = true := by
  decide +kernel

private theorem cell_61 (x : ℝ) (hx : x ∈ Set.Icc (11878 : ℝ) 12290) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_11878.1 endpoint_12290.2 checked_61 hx

private theorem checked_62 : checkCell 12290 12751 12140 12623 = true := by
  decide +kernel

private theorem cell_62 (x : ℝ) (hx : x ∈ Set.Icc (12290 : ℝ) 12751) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_12290.1 endpoint_12751.2 checked_62 hx

private theorem checked_63 : checkCell 12751 13252 12621 13135 = true := by
  decide +kernel

private theorem cell_63 (x : ℝ) (hx : x ∈ Set.Icc (12751 : ℝ) 13252) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_12751.1 endpoint_13252.2 checked_63 hx

private theorem checked_64 : checkCell 13252 13786 13133 13658 = true := by
  decide +kernel

private theorem cell_64 (x : ℝ) (hx : x ∈ Set.Icc (13252 : ℝ) 13786) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_13252.1 endpoint_13786.2 checked_64 hx

private theorem checked_65 : checkCell 13786 14333 13656 14145 = true := by
  decide +kernel

private theorem cell_65 (x : ℝ) (hx : x ∈ Set.Icc (13786 : ℝ) 14333) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_13786.1 endpoint_14333.2 checked_65 hx

private theorem checked_66 : checkCell 14333 14844 14143 14701 = true := by
  decide +kernel

private theorem cell_66 (x : ℝ) (hx : x ∈ Set.Icc (14333 : ℝ) 14844) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_14333.1 endpoint_14844.2 checked_66 hx

private theorem checked_67 : checkCell 14844 15422 14699 15298 = true := by
  decide +kernel

private theorem cell_67 (x : ℝ) (hx : x ∈ Set.Icc (14844 : ℝ) 15422) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_14844.1 endpoint_15422.2 checked_67 hx

private theorem checked_68 : checkCell 15422 16000 15296 15887 = true := by
  decide +kernel

private theorem cell_68 (x : ℝ) (hx : x ∈ Set.Icc (15422 : ℝ) 16000) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_15422.1 endpoint_16000.2 checked_68 hx

/-- Both strict theta allowances on this complete closed batch interval. -/
theorem bounds_chunk06 : ∀ x ∈ Set.Icc (11450 : ℝ) 16000,
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x := by
  exact (join (join (join cell_60 cell_61) (join cell_62 cell_63)) (join (join cell_64 cell_65) (join cell_66 (join cell_67 cell_68))))

end RiemannGaussian.RosserSchoenfeldFiniteTheta
