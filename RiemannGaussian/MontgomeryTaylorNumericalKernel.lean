/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorKernelFormula
import RiemannGaussian.External.Zeta23InverseSamplingKernelBridge
import LeanCert.Tactic

/-!
# A rational-coefficient kernel with a proved uniform error

LeanCert is pinned in the Lake manifest. Every numerical check in this
module uses kernel verification, with no compiler or floating-point axiom.
The transcendental coefficient is enclosed once; the error in its rational
replacement is then paid uniformly over every relevant separation.
-/

namespace RiemannGaussian.MontgomeryTaylorNumericalKernel
noncomputable section
open MontgomeryTaylorKernelFormula
set_option leancert.trust "kernel"

private theorem sqrt_two_bounds : Real.sqrt 2 ∈
    Set.Icc ((1414213562373095 : ℝ) / 1000000000000000)
      ((1414213562373096 : ℝ) / 1000000000000000) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
set_option leancert.trust.kernelHeartbeats 4000000 in
private theorem eta_lower_interval :
    ∀ r ∈ Set.Icc ((1414213562373095 : ℝ) / 1000000000000000)
        ((1414213562373096 : ℝ) / 1000000000000000),
      (8274992963 : ℝ) / 10000000000 <
        Real.cos (r / 2) / (r * Real.sin (r / 2)) := by
  certify_bound 25 (trust := kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
set_option leancert.trust.kernelHeartbeats 4000000 in
private theorem eta_upper_interval :
    ∀ r ∈ Set.Icc ((1414213562373095 : ℝ) / 1000000000000000)
        ((1414213562373096 : ℝ) / 1000000000000000),
      Real.cos (r / 2) / (r * Real.sin (r / 2)) <
        (8274992964 : ℝ) / 10000000000 := by
  certify_bound 25 (trust := kernel)

/-- Exact rational bounds on the Montgomery--Taylor coefficient. -/
theorem eta_bounds : (8274992963 : ℝ) / 10000000000 < eta ∧
    eta < (8274992964 : ℝ) / 10000000000 := by
  rw [eta_eq_cos_div]
  exact ⟨eta_lower_interval _ sqrt_two_bounds, eta_upper_interval _ sqrt_two_bounds⟩

/-- The rational value used by the numerical checker. -/
def etaRat : ℚ := 8274992963 / 10000000000

/-- The remaining kernel formula uses only rational constants and π.
Its quantitative comparison below explicitly excludes its removable poles. -/
def kernel (x : ℝ) : ℝ :=
  (2 * Real.pi * (etaRat : ℝ) * x * Real.sin (Real.pi * x) - Real.cos (Real.pi * x)) /
    (2 * Real.pi ^ 2 * x ^ 2 - 1)

/-- Every separation beyond the small-frequency fallback has a positive
denominator and a uniformly bounded coefficient sensitivity. -/
theorem denominator_control {x : ℝ} (hx : (1 : ℝ) / 3 ≤ x) :
    0 < 2 * Real.pi ^ 2 * x ^ 2 - 1 ∧
      0 ≤ (2 * Real.pi * x) / (2 * Real.pi ^ 2 * x ^ 2 - 1) ∧
      (2 * Real.pi * x) / (2 * Real.pi ^ 2 * x ^ 2 - 1) ≤ 3 := by
  have hx0 : 0 ≤ x := by linarith
  have hxsq : (1 : ℝ) / 9 ≤ x ^ 2 := by nlinarith
  have hp2 : 9 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hden : 9 * x ^ 2 ≤ 2 * Real.pi ^ 2 * x ^ 2 - 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp2) (sq_nonneg x)]
  have hd0 : 0 < 2 * Real.pi ^ 2 * x ^ 2 - 1 := by linarith
  refine ⟨hd0, div_nonneg (by positivity) hd0.le, ?_⟩
  apply (div_le_iff₀ hd0).mpr
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hx0]

/-- Rounding the fixed coefficient introduces a uniformly paid error. -/
theorem kernel_error {x : ℝ} (hx : (1 : ℝ) / 3 ≤ x) :
    |kernel x - montgomeryTaylorKernel (2 * Real.pi * x)| ≤
      (3 : ℝ) / 10000000000 := by
  obtain ⟨hd, hrat0, hrat⟩ := denominator_control hx
  have he : |(etaRat : ℝ) - eta| ≤ (1 : ℝ) / 10000000000 := by
    norm_num [etaRat, abs_le] at *
    constructor <;> linarith [eta_bounds.1, eta_bounds.2]
  have hid : kernel x - montgomeryTaylorKernel (2 * Real.pi * x) =
      ((2 * Real.pi * x) / (2 * Real.pi ^ 2 * x ^ 2 - 1)) *
        ((etaRat : ℝ) - eta) * Real.sin (Real.pi * x) := by
    rw [cycles_quotient hd.ne']
    unfold kernel
    ring
  rw [hid, abs_mul, abs_mul, abs_of_nonneg hrat0]
  calc
    _ ≤ 3 * ((1 : ℝ) / 10000000000) * 1 := by
      gcongr
      exact Real.abs_sin_le_one _
    _ = _ := by norm_num

/-- The entire squared-correlation error is less than one part in a
billion, uniformly on the unbounded separation interval. -/
theorem squared_kernel_error {x : ℝ} (hx : (1 : ℝ) / 3 ≤ x) :
    |kernel x ^ 2 - montgomeryTaylorKernel (2 * Real.pi * x) ^ 2| ≤
      (1 : ℝ) / 1000000000 := by
  have he := kernel_error hx
  have hk := Zeta23InverseSampling.abs_montgomeryTaylorKernel_le_twelve_elevenths
    (2 * Real.pi * x)
  have hkn : |kernel x| ≤ (6 : ℝ) / 5 := by
    have h := abs_add_le (kernel x - montgomeryTaylorKernel (2 * Real.pi * x))
      (montgomeryTaylorKernel (2 * Real.pi * x))
    rw [sub_add_cancel] at h
    linarith
  rw [sq_sub_sq, abs_mul]
  have hsum : |kernel x + montgomeryTaylorKernel (2 * Real.pi * x)| ≤ 3 := by
    have h := abs_add_le (kernel x) (montgomeryTaylorKernel (2 * Real.pi * x))
    linarith
  calc
    _ ≤ 3 * ((3 : ℝ) / 10000000000) := by gcongr
    _ ≤ _ := by norm_num

end
end RiemannGaussian.MontgomeryTaylorNumericalKernel
