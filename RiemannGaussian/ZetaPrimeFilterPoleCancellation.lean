/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeFilterCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Spectral pole cancellation as an exact continuous primitive

Dividing a spectral polynomial by the pole factor produces a mathematically
defined primitive polynomial. If the original filter kills the pole, its
continuous density integral is exactly a boundary difference. The identity
holds for arbitrary polynomial filters and specializes to the actual
zero-isolating filter; it does not assume a signed arithmetic estimate.
-/

open Complex Filter MeasureTheory Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The polynomial implementing the continuous-density lowering operator. -/
def zetaPoleCancelPolynomial (q : Polynomial ℂ) (s : ℂ) : Polynomial ℂ :=
  q - Polynomial.C (s - 1) * (Polynomial.X * q)

/-- The canonical primitive polynomial, formed by exact monic division
at the pole mode and the necessary scalar normalization. -/
def zetaPrimeFilterPrimitivePolynomial (p : Polynomial ℂ) (s : ℂ) : Polynomial ℂ :=
  Polynomial.C (-(s - 1)⁻¹) * (p /ₘ (Polynomial.X - Polynomial.C (s - 1)⁻¹))

/-- The pole-cancelling operator on coefficients is exactly the lowering
operator on the full complex real-variable kernel. -/
theorem zetaPrimeFilterKernel_poleCancel (q : Polynomial ℂ) (N : ℕ) (s : ℂ) (x : ℝ) :
    zetaPrimeFilterKernel (zetaPoleCancelPolynomial q s) N s x =
      zetaPrimeFilterKernel q N s x - (s - 1) * zetaPrimeFilterKernel q (N + 1) s x := by
  simp only [zetaPrimeFilterKernel, zetaPoleCancelPolynomial, zetaFactorialPolynomial_sub,
    zetaFactorialPolynomial_C_mul, zetaFactorialPolynomial_X_mul]
  ring

/-- Exact polynomial division separates the pole value from the part
having a continuous primitive. This is an identity for every polynomial. -/
theorem zetaPoleCancelPolynomial_primitive (p : Polynomial ℂ) {s : ℂ} (hs : s ≠ 1) :
    zetaPoleCancelPolynomial (zetaPrimeFilterPrimitivePolynomial p s) s =
      p - Polynomial.C (p.eval (s - 1)⁻¹) := by
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hc : Polynomial.C (s - 1) * Polynomial.C (s - 1)⁻¹ = (1 : Polynomial ℂ) := by
    rw [← map_mul, mul_inv_cancel₀ hs0, map_one]
  calc
    _ = (Polynomial.X - Polynomial.C (s - 1)⁻¹) *
        (p /ₘ (Polynomial.X - Polynomial.C (s - 1)⁻¹)) := by
      unfold zetaPoleCancelPolynomial zetaPrimeFilterPrimitivePolynomial
      rw [map_neg]
      linear_combination (Polynomial.X * (p /ₘ (Polynomial.X - Polynomial.C (s - 1)⁻¹))) * hc
    _ = p - p %ₘ (Polynomial.X - Polynomial.C (s - 1)⁻¹) :=
      Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic p _
    _ = _ := by rw [Polynomial.modByMonic_X_sub_C_eq_C_eval]

/-- Every pole-annihilating filter is exactly recovered from its canonical
primitive polynomial; no existence choice or numerical coefficients occur. -/
theorem zetaPoleCancelPolynomial_primitive_of_eval_zero (p : Polynomial ℂ) {s : ℂ}
    (hs : s ≠ 1) (hp : p.eval (s - 1)⁻¹ = 0) :
    zetaPoleCancelPolynomial (zetaPrimeFilterPrimitivePolynomial p s) s = p := by
  rw [zetaPoleCancelPolynomial_primitive p hs, hp, map_zero, sub_zero]

/-- The complete complex filter is the derivative of an explicit primitive
whenever its pole mode vanishes. The equality retains its oscillatory phase. -/
theorem hasDerivAt_zetaPrimeFilterPrimitive (p : Polynomial ℂ) (N : ℕ) {s : ℂ}
    (hs : s ≠ 1) (hp : p.eval (s - 1)⁻¹ = 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun t : ℝ ↦ (t : ℂ) * zetaPrimeFilterKernel (zetaPrimeFilterPrimitivePolynomial p s) (N + 1) s t)
      (zetaPrimeFilterKernel p N s x) x := by
  have h := hasDerivAt_mul_zetaPrimeFilterKernel (zetaPrimeFilterPrimitivePolynomial p s) N s hx
  rw [← zetaPrimeFilterKernel_poleCancel, zetaPoleCancelPolynomial_primitive_of_eval_zero p hs hp] at h
  exact h

/-- Pole cancellation turns the actual continuous-density integral into
two explicit endpoint terms, before either is estimated. -/
theorem zetaPrimeFilterKernel_integral_eq_primitive (p : Polynomial ℂ) (N : ℕ) {s : ℂ}
    (hs : s ≠ 1) (hp : p.eval (s - 1)⁻¹ = 0) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in Set.Ioc a b, zetaPrimeFilterKernel p N s x) =
      (b : ℂ) * zetaPrimeFilterKernel (zetaPrimeFilterPrimitivePolynomial p s) (N + 1) s b -
        (a : ℂ) * zetaPrimeFilterKernel (zetaPrimeFilterPrimitivePolynomial p s) (N + 1) s a := by
  have hi : IntervalIntegrable (zetaPrimeFilterKernel p N s) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (show ContinuousOn (zetaPrimeFilterKernel p N s) (Set.Icc a b) from
      fun x hx ↦ (contDiffAt_zetaPrimeFilterKernel p N s (ha.trans_le hx.1)).continuousAt.continuousWithinAt).integrableOn_Icc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx ↦ by
      rw [Set.uIcc_of_le hab] at hx
      exact hasDerivAt_zetaPrimeFilterPrimitive p N hs hp (ha.trans_le hx.1)) hi
  simpa only [intervalIntegral.integral_of_le hab] using h

/-- The mathematically defined filter for every selected right-half zero
does kill the pole, so the primitive theorem applies without a new premise. -/
theorem zetaRightHalfZeroModeFilter_eval_pole (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    (zetaRightHalfZeroModeFilter rho hrho).eval ((3 / 2 + I * (rho.1.im : ℂ)) - 1)⁻¹ = 0 := by
  have he : (3 / 2 + I * (rho.1.im : ℂ)) - 1 = 1 / 2 + I * (rho.1.im : ℂ) := by ring
  rw [he, zetaRightHalfZeroModeFilter]
  apply adaptiveZetaZeroModeFilter_eval_pole
  rw [mem_adaptiveZetaZeroSupport, divisor_adaptiveZetaPoleRemoved_nontrivialZero]
  exact_mod_cast (analyticZetaZeroMultiplicity_positive rho).ne'

end

end RiemannGaussian
