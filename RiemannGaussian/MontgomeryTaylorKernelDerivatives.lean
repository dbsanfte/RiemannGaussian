/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.MontgomeryTaylorNumericalKernel

/-!
# Explicit derivatives for certified kernel enclosures

The rational-coefficient model has elementary first and second derivatives.
The proofs below validate their use away from the removable denominator
zeros. The uniform model-to-kernel error is supplied separately by
`MontgomeryTaylorNumericalKernel.squared_kernel_error`.
-/

namespace RiemannGaussian.MontgomeryTaylorNumericalKernel
noncomputable section
open Real

/-- Numerator of the rational-coefficient kernel in cycle units. -/
def numerator (x : ℝ) : ℝ :=
  2 * Real.pi * (etaRat : ℝ) * x * sin (Real.pi * x) - cos (Real.pi * x)

/-- Denominator of the cycle-coordinate quotient. -/
def denominator (x : ℝ) : ℝ := 2 * Real.pi ^ 2 * x ^ 2 - 1

/-- Explicit first derivative of the numerator. -/
def numeratorD (x : ℝ) : ℝ :=
  2 * Real.pi * (etaRat : ℝ) * (sin (Real.pi * x) + Real.pi * x * cos (Real.pi * x)) + Real.pi * sin (Real.pi * x)

/-- Explicit second derivative of the numerator. -/
def numeratorDD (x : ℝ) : ℝ :=
  Real.pi ^ 2 * (4 * (etaRat : ℝ) + 1) * cos (Real.pi * x) -
    2 * Real.pi ^ 3 * (etaRat : ℝ) * x * sin (Real.pi * x)

/-- Explicit first derivative of the kernel model. -/
def kernelD (x : ℝ) : ℝ :=
  (numeratorD x - kernel x * (4 * Real.pi ^ 2 * x)) / denominator x

/-- Explicit second derivative of the kernel model. -/
def kernelDD (x : ℝ) : ℝ :=
  (numeratorDD x - 2 * kernelD x * (4 * Real.pi ^ 2 * x) - kernel x * (4 * Real.pi ^ 2)) /
    denominator x

/-- The first derivative of the squared-correlation model. -/
def squaredD (x : ℝ) : ℝ := 2 * kernel x * kernelD x

/-- The second derivative of the squared-correlation model. -/
def squaredDD (x : ℝ) : ℝ := 2 * kernelD x ^ 2 + 2 * kernel x * kernelDD x

private theorem denominator_hasDerivAt (x : ℝ) :
    HasDerivAt denominator (4 * Real.pi ^ 2 * x) x := by
  have h := (((hasDerivAt_id x).pow 2).const_mul (2 * Real.pi ^ 2)).sub_const 1
  exact h.congr_deriv (by dsimp; ring)

private theorem numerator_hasDerivAt (x : ℝ) :
    HasDerivAt numerator (numeratorD x) x := by
  have ht := (hasDerivAt_id x).const_mul Real.pi
  have hn := (((hasDerivAt_id x).const_mul (2 * Real.pi * (etaRat : ℝ))).mul ht.sin).sub ht.cos
  exact hn.congr_deriv (by dsimp [numeratorD]; ring)

private theorem numeratorD_hasDerivAt (x : ℝ) :
    HasDerivAt numeratorD (numeratorDD x) x := by
  have ht := (hasDerivAt_id x).const_mul Real.pi
  have hn := ((ht.sin.add (ht.mul ht.cos)).const_mul (2 * Real.pi * (etaRat : ℝ))).add
    (ht.sin.const_mul Real.pi)
  exact hn.congr_deriv (by dsimp [numeratorDD]; ring)

/-- The derivative formula is valid on the entire numerical verification
domain, including all large pair separations. -/
theorem kernel_hasDerivAt {x : ℝ} (hx : (1 : ℝ) / 3 ≤ x) :
    HasDerivAt kernel (kernelD x) x := by
  have hd : denominator x ≠ 0 := (denominator_control hx).1.ne'
  have h := (numerator_hasDerivAt x).div (denominator_hasDerivAt x) hd
  apply h.congr_deriv
  unfold kernelD
  rw [show kernel x = numerator x / denominator x from rfl]
  field_simp [hd]

/-- The checked second derivative preserves the quotient's denominator
condition rather than silently using a totalized singular formula. -/
theorem kernelD_hasDerivAt {x : ℝ} (hx : (1 : ℝ) / 3 ≤ x) :
    HasDerivAt kernelD (kernelDD x) x := by
  have hd : denominator x ≠ 0 := (denominator_control hx).1.ne'
  have hlin : HasDerivAt (fun y => 4 * Real.pi ^ 2 * y) (4 * Real.pi ^ 2) x := by
    exact ((hasDerivAt_id x).const_mul (4 * Real.pi ^ 2)).congr_deriv (by ring)
  have h := ((numeratorD_hasDerivAt x).sub ((kernel_hasDerivAt hx).mul hlin)).div
    (denominator_hasDerivAt x) hd
  apply h.congr_deriv
  dsimp only [kernelDD, kernelD, Pi.sub_apply, Pi.mul_apply]
  field_simp [hd]
  ring

/-- The explicit first derivative of the squared model. -/
theorem squared_hasDerivAt {x : ℝ} (hx : (1 : ℝ) / 3 ≤ x) :
    HasDerivAt (fun y => kernel y ^ 2) (squaredD x) x := by
  exact ((kernel_hasDerivAt hx).pow 2).congr_deriv (by simp [squaredD])

/-- The explicit curvature of the squared model. -/
theorem squaredD_hasDerivAt {x : ℝ} (hx : (1 : ℝ) / 3 ≤ x) :
    HasDerivAt squaredD (squaredDD x) x := by
  have h := ((kernel_hasDerivAt hx).const_mul 2).mul (kernelD_hasDerivAt hx)
  exact h.congr_deriv (by unfold squaredDD; ring)

end
end RiemannGaussian.MontgomeryTaylorNumericalKernel
