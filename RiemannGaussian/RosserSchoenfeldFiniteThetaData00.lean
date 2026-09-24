/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteThetaCheck

/-!
# Checked finite Chebyshev cells: batch 1 of seven

Every primorial comparison is checked by kernel reduction against the
complete prime catalog. The closed cells include their boundary points.
-/

set_option Elab.async false
namespace RiemannGaussian.RosserSchoenfeldFiniteTheta
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

private theorem endpoint_1451 : (1396 : ℝ) < Chebyshev.theta 1451 ∧
    Chebyshev.theta 1451 < 1397 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_1489 : (1447 : ℝ) < Chebyshev.theta 1489 ∧
    Chebyshev.theta 1489 < 1448 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_1542 : (1484 : ℝ) < Chebyshev.theta 1542 ∧
    Chebyshev.theta 1542 < 1485 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_1582 : (1535 : ℝ) < Chebyshev.theta 1582 ∧
    Chebyshev.theta 1582 < 1536 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_1635 : (1601 : ℝ) < Chebyshev.theta 1635 ∧
    Chebyshev.theta 1635 < 1603 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_1704 : (1661 : ℝ) < Chebyshev.theta 1704 ∧
    Chebyshev.theta 1704 < 1662 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_1768 : (1720 : ℝ) < Chebyshev.theta 1768 ∧
    Chebyshev.theta 1768 < 1722 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_1830 : (1773 : ℝ) < Chebyshev.theta 1830 ∧
    Chebyshev.theta 1830 < 1774 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_1887 : (1833 : ℝ) < Chebyshev.theta 1887 ∧
    Chebyshev.theta 1887 < 1834 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem endpoint_1950 : (1886 : ℝ) < Chebyshev.theta 1950 ∧
    Chebyshev.theta 1950 < 1887 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

/-- An exact checked enclosure at the shared boundary of consecutive batches. -/
theorem endpoint_2006 : (1947 : ℝ) < Chebyshev.theta 2006 ∧
    Chebyshev.theta 2006 < 1948 := by
  exact theta_bounds_of_check (by decide) (by decide +kernel) (by decide +kernel)

private theorem checked_00 : checkCell 1451 1489 1396 1448 = true := by
  decide +kernel

private theorem cell_00 (x : ℝ) (hx : x ∈ Set.Icc (1451 : ℝ) 1489) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_1451.1 endpoint_1489.2 checked_00 hx

private theorem checked_01 : checkCell 1489 1542 1447 1485 = true := by
  decide +kernel

private theorem cell_01 (x : ℝ) (hx : x ∈ Set.Icc (1489 : ℝ) 1542) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_1489.1 endpoint_1542.2 checked_01 hx

private theorem checked_02 : checkCell 1542 1582 1484 1536 = true := by
  decide +kernel

private theorem cell_02 (x : ℝ) (hx : x ∈ Set.Icc (1542 : ℝ) 1582) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_1542.1 endpoint_1582.2 checked_02 hx

private theorem checked_03 : checkCell 1582 1635 1535 1603 = true := by
  decide +kernel

private theorem cell_03 (x : ℝ) (hx : x ∈ Set.Icc (1582 : ℝ) 1635) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_1582.1 endpoint_1635.2 checked_03 hx

private theorem checked_04 : checkCell 1635 1704 1601 1662 = true := by
  decide +kernel

private theorem cell_04 (x : ℝ) (hx : x ∈ Set.Icc (1635 : ℝ) 1704) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_1635.1 endpoint_1704.2 checked_04 hx

private theorem checked_05 : checkCell 1704 1768 1661 1722 = true := by
  decide +kernel

private theorem cell_05 (x : ℝ) (hx : x ∈ Set.Icc (1704 : ℝ) 1768) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_1704.1 endpoint_1768.2 checked_05 hx

private theorem checked_06 : checkCell 1768 1830 1720 1774 = true := by
  decide +kernel

private theorem cell_06 (x : ℝ) (hx : x ∈ Set.Icc (1768 : ℝ) 1830) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_1768.1 endpoint_1830.2 checked_06 hx

private theorem checked_07 : checkCell 1830 1887 1773 1834 = true := by
  decide +kernel

private theorem cell_07 (x : ℝ) (hx : x ∈ Set.Icc (1830 : ℝ) 1887) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_1830.1 endpoint_1887.2 checked_07 hx

private theorem checked_08 : checkCell 1887 1950 1833 1887 = true := by
  decide +kernel

private theorem cell_08 (x : ℝ) (hx : x ∈ Set.Icc (1887 : ℝ) 1950) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_1887.1 endpoint_1950.2 checked_08 hx

private theorem checked_09 : checkCell 1950 2006 1886 1948 = true := by
  decide +kernel

private theorem cell_09 (x : ℝ) (hx : x ∈ Set.Icc (1950 : ℝ) 2006) :
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x :=
  cell_bounds (by decide) (by decide) endpoint_1950.1 endpoint_2006.2 checked_09 hx

/-- Both strict theta allowances on this complete closed batch interval. -/
theorem bounds_chunk00 : ∀ x ∈ Set.Icc (1451 : ℝ) 2006,
    x-(47/100)*x/Real.log x < Chebyshev.theta x ∧
      Chebyshev.theta x < x+(31/100)*x/Real.log x := by
  exact (join (join (join cell_00 cell_01) (join cell_02 (join cell_03 cell_04))) (join (join cell_05 cell_06) (join cell_07 (join cell_08 cell_09))))

end RiemannGaussian.RosserSchoenfeldFiniteTheta
