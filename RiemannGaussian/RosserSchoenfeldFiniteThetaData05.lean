/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteThetaData04

/-!
# Checked finite Chebyshev cells: batch 6 of seven

Every primorial comparison is checked by kernel reduction against the
complete prime catalog. The closed cells include their boundary points.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteTheta
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

private theorem endpoint_8139 : (8009 : ℝ) < Chebyshev.theta 8139 ∧
    Chebyshev.theta 8139 < 8011 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_8432 : (8307 : ℝ) < Chebyshev.theta 8432 ∧
    Chebyshev.theta 8432 < 8308 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_8743 : (8624 : ℝ) < Chebyshev.theta 8743 ∧
    Chebyshev.theta 8743 < 8626 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_9074 : (8960 : ℝ) < Chebyshev.theta 9074 ∧
    Chebyshev.theta 9074 < 8962 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_9426 : (9316 : ℝ) < Chebyshev.theta 9426 ∧
    Chebyshev.theta 9426 < 9318 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_9798 : (9702 : ℝ) < Chebyshev.theta 9798 ∧
    Chebyshev.theta 9798 < 9703 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_10200 : (10107 : ℝ) < Chebyshev.theta 10200 ∧
    Chebyshev.theta 10200 < 10109 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_10624 : (10504 : ℝ) < Chebyshev.theta 10624 ∧
    Chebyshev.theta 10624 < 10506 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_11040 : (10895 : ℝ) < Chebyshev.theta 11040 ∧
    Chebyshev.theta 11040 < 10897 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

/-- An exact checked enclosure at the shared boundary of consecutive batches. -/
theorem endpoint_11450 : (11305 : ℝ) < Chebyshev.theta 11450 ∧
    Chebyshev.theta 11450 < 11307 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem checked_50 : checkCell 7849 8139 7730 8011 = true := by
  decide +kernel

private theorem cell_50 (x : ℝ) (hx : x ∈ Set.Icc (7849 : ℝ) 8139) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_7849.1 endpoint_8139.2 checked_50 hx

private theorem checked_51 : checkCell 8139 8432 8009 8308 = true := by
  decide +kernel

private theorem cell_51 (x : ℝ) (hx : x ∈ Set.Icc (8139 : ℝ) 8432) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_8139.1 endpoint_8432.2 checked_51 hx

private theorem checked_52 : checkCell 8432 8743 8307 8626 = true := by
  decide +kernel

private theorem cell_52 (x : ℝ) (hx : x ∈ Set.Icc (8432 : ℝ) 8743) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_8432.1 endpoint_8743.2 checked_52 hx

private theorem checked_53 : checkCell 8743 9074 8624 8962 = true := by
  decide +kernel

private theorem cell_53 (x : ℝ) (hx : x ∈ Set.Icc (8743 : ℝ) 9074) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_8743.1 endpoint_9074.2 checked_53 hx

private theorem checked_54 : checkCell 9074 9426 8960 9318 = true := by
  decide +kernel

private theorem cell_54 (x : ℝ) (hx : x ∈ Set.Icc (9074 : ℝ) 9426) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_9074.1 endpoint_9426.2 checked_54 hx

private theorem checked_55 : checkCell 9426 9798 9316 9703 = true := by
  decide +kernel

private theorem cell_55 (x : ℝ) (hx : x ∈ Set.Icc (9426 : ℝ) 9798) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_9426.1 endpoint_9798.2 checked_55 hx

private theorem checked_56 : checkCell 9798 10200 9702 10109 = true := by
  decide +kernel

private theorem cell_56 (x : ℝ) (hx : x ∈ Set.Icc (9798 : ℝ) 10200) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_9798.1 endpoint_10200.2 checked_56 hx

private theorem checked_57 : checkCell 10200 10624 10107 10506 = true := by
  decide +kernel

private theorem cell_57 (x : ℝ) (hx : x ∈ Set.Icc (10200 : ℝ) 10624) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_10200.1 endpoint_10624.2 checked_57 hx

private theorem checked_58 : checkCell 10624 11040 10504 10897 = true := by
  decide +kernel

private theorem cell_58 (x : ℝ) (hx : x ∈ Set.Icc (10624 : ℝ) 11040) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_10624.1 endpoint_11040.2 checked_58 hx

private theorem checked_59 : checkCell 11040 11450 10895 11307 = true := by
  decide +kernel

private theorem cell_59 (x : ℝ) (hx : x ∈ Set.Icc (11040 : ℝ) 11450) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_11040.1 endpoint_11450.2 checked_59 hx

/-- Both strict theta allowances on this complete closed batch interval. -/
theorem bounds_chunk05 : ∀ x ∈ Set.Icc (7849 : ℝ) 11450,
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x := by
  exact (join (join (join cell_50 cell_51) (join cell_52 (join cell_53 cell_54))) (join (join cell_55 cell_56) (join cell_57 (join cell_58 cell_59))))

end RiemannGaussian.RosserSchoenfeldFiniteTheta
