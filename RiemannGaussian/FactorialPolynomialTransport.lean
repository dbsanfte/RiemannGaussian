/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianPolynomialTransport
import Mathlib.Data.Nat.Choose.Cast

/-!
# The exact polynomial operator inside a cleared factorial moment

After division by its unfiltered exponential moment, clearing before
differentiation acts by `(1-x⁻¹ D)^N` on the clearing polynomial. This is a
finite operator identity for every polynomial, retaining all downward
Leibniz orders. Its linear displacement and quadratic correction survive
Gaussian transport and must be included in any arithmetic sign estimate.
-/

namespace RiemannGaussian.FactorialPolynomialTransport
noncomputable section
open Polynomial
open scoped Classical
open GaussianPolynomialTransport

/-- One exact normalized factorial step as a linear endomorphism of
the complete polynomial space. -/
def step (x : ℂ) : Module.End ℂ (Polynomial ℂ) := 1 - x⁻¹ • Polynomial.derivative

/-- The full normalized polynomial multiplier after taking `N` signed
factorial derivatives of a polynomial times an exponential. -/
def shift (N : ℕ) (x : ℂ) (q : Polynomial ℂ) : Polynomial ℂ := (step x ^ N) q

/-- One factorial step retains the polynomial and its complete signed
derivative correction. -/
theorem step_apply (x : ℂ) (q : Polynomial ℂ) :
    step x q = q - Polynomial.C x⁻¹ * q.derivative := by
  simp [step, Polynomial.smul_eq_C_mul]

/-- The zeroth factorial order leaves the clearing polynomial intact. -/
theorem shift_zero (x : ℂ) (q : Polynomial ℂ) : shift 0 x q = q := by simp [shift]

/-- Every adjacent order is the same exact first-order operation;
no coefficient or correlation is removed. -/
theorem shift_succ (N : ℕ) (x : ℂ) (q : Polynomial ℂ) :
    shift (N + 1) x q = shift N x q - Polynomial.C x⁻¹ * (shift N x q).derivative := by
  rw [shift, pow_succ', Module.End.mul_apply, step_apply]
  rfl

/-- The operator's complete binomial expansion keeps all signed
derivatives and every exact natural binomial coefficient. -/
theorem shift_eq_binomial (N : ℕ) (x : ℂ) (q : Polynomial ℂ) :
    shift N x q = ∑ k ∈ Finset.range (N + 1),
      Polynomial.C ((N.choose k : ℂ) * (-x⁻¹) ^ k) * (Polynomial.derivative^[k]) q := by
  have he : step x = (-x⁻¹) • (Polynomial.derivative : Module.End ℂ (Polynomial ℂ)) + 1 := by
    apply LinearMap.ext
    intro p
    simp [step, Polynomial.smul_eq_C_mul, sub_eq_add_neg, add_comm]
  have h := congrArg (fun f : Module.End ℂ (Polynomial ℂ) ↦ f q)
    ((Commute.one_right ((-x⁻¹) • (Polynomial.derivative : Module.End ℂ (Polynomial ℂ)))).add_pow N)
  rw [shift, he]
  convert! h using 1
  simp only [LinearMap.sum_apply, one_pow, mul_one, Module.End.mul_apply,
    Module.End.natCast_apply, map_nsmul, smul_pow, LinearMap.smul_apply, Module.End.pow_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [Polynomial.smul_eq_C_mul, nsmul_eq_mul, mul_assoc]

/-- Polynomial addition commutes with the complete factorial operator. -/
theorem shift_add (N : ℕ) (x : ℂ) (p q : Polynomial ℂ) :
    shift N x (p + q) = shift N x p + shift N x q := (step x ^ N).map_add p q

private theorem shift_succ_step (N : ℕ) (x : ℂ) (q : Polynomial ℂ) :
    shift (N + 1) x q = step x (shift N x q) := by
  rw [shift, pow_succ', Module.End.mul_apply]
  rfl

private theorem step_C_mul (x c : ℂ) (q : Polynomial ℂ) :
    step x (Polynomial.C c * q) = Polynomial.C c * step x q := by
  rw [step_apply, Polynomial.derivative_C_mul, step_apply]
  ring

private theorem step_factor_mul (x r : ℂ) (q : Polynomial ℂ) :
    step x ((Polynomial.X - Polynomial.C r) * q) =
      (Polynomial.X - Polynomial.C r) * step x q - Polynomial.C x⁻¹ * q := by
  rw [step_apply, Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, one_mul, step_apply]
  ring

/-- The full polynomial derivative commutes with every factorial step,
so later heat corrections still refer to the original clearing polynomial. -/
theorem derivative_shift (N : ℕ) (x : ℂ) (q : Polynomial ℂ) :
    (shift N x q).derivative = shift N x q.derivative := by
  induction N with
  | zero => simp [shift_zero]
  | succ N h =>
    rw [shift_succ, Polynomial.derivative_sub, Polynomial.derivative_C_mul, h, shift_succ]

/-- A linear factor acting on an arbitrary cofactor couples adjacent
factorial orders exactly. The lower-order term carries its full sign. -/
theorem shift_factor_mul_succ (N : ℕ) (x r : ℂ) (q : Polynomial ℂ) :
    shift (N + 1) x ((Polynomial.X - Polynomial.C r) * q) =
      (Polynomial.X - Polynomial.C r) * shift (N + 1) x q -
        Polynomial.C (((N : ℂ) + 1) * x⁻¹) * shift N x q := by
  induction N with
  | zero =>
      simp only [shift_succ_step, shift_zero, Nat.cast_zero, zero_add, one_mul]
      exact step_factor_mul x r q
  | succ N h =>
    rw [shift_succ_step (N + 1), h, map_sub, step_factor_mul, step_C_mul,
      ← shift_succ_step, ← shift_succ_step]
    push_cast
    simp only [map_add, map_mul, map_one]
    ring

/-- Constants are unchanged at every order. -/
theorem shift_C (N : ℕ) (x c : ℂ) : shift N x (Polynomial.C c) = Polynomial.C c := by
  induction N with
  | zero => exact shift_zero x _
  | succ N h => rw [shift_succ, h, Polynomial.derivative_C, mul_zero, sub_zero]

/-- The true linear clearing factor is displaced by `N/x` before
Gaussian smoothing. -/
theorem shift_factor (N : ℕ) (x r : ℂ) :
    shift N x (Polynomial.X - Polynomial.C r) =
      Polynomial.X - Polynomial.C (r + (N : ℂ) * x⁻¹) := by
  induction N with
  | zero => simp [shift_zero]
  | succ N h =>
    rw [shift_succ, h]
    rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
      sub_zero, mul_one]
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_mul, map_one]
    ring

/-- Squared clearing factors carry an additional signed correction
`-N/x²`, already present before Gaussian smoothing. -/
theorem shift_factor_sq (N : ℕ) (x r : ℂ) :
    shift N x ((Polynomial.X - Polynomial.C r) ^ 2) =
      (Polynomial.X - Polynomial.C (r + (N : ℂ) * x⁻¹)) ^ 2 -
        Polynomial.C ((N : ℂ) * x⁻¹ ^ 2) := by
  induction N with
  | zero => simp [shift_zero]
  | succ N h =>
    rw [shift_succ, h]
    rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.derivative_pow,
      Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C]
    norm_num only [sub_zero, mul_one, Nat.reduceSub, pow_one, Nat.cast_add, Nat.cast_one,
      map_add, map_mul, map_pow, map_one, map_ofNat]
    ring

/-- The full finite multiplier after both factorial differentiation and
Gaussian polynomial transport. The argument `z` includes the Gaussian
displacement when this operator is used in the actual prime series. -/
def heat (B : ℝ) (N : ℕ) (x : ℂ) (q : Polynomial ℂ) (z : ℂ) : ℂ :=
  transport B (shift N x q) z

private theorem transport_sum {ι : Type*} (J : Finset ι) (f : ι → Polynomial ℂ) (B : ℝ) (z : ℂ) :
    transport B (∑ j ∈ J, f j) z = ∑ j ∈ J, transport B (f j) z := by
  have h0 : transport B (0 : Polynomial ℂ) z = 0 := by
    simpa only [map_zero] using transport_C B 0 z
  induction J using Finset.induction_on with
  | empty => simp [h0]
  | @insert j J hj h => simp only [Finset.sum_insert hj, transport_add, h]

/-- The complete factorial and Gaussian multiplier is a finite binomial
sum of exact Hermite transforms of all polynomial derivatives. -/
theorem heat_eq_binomial (B : ℝ) (N : ℕ) (x : ℂ) (q : Polynomial ℂ) (z : ℂ) :
    heat B N x q z = ∑ k ∈ Finset.range (N + 1),
      (N.choose k : ℂ) * (-x⁻¹) ^ k * transport B ((Polynomial.derivative^[k]) q) z := by
  rw [heat, shift_eq_binomial, transport_sum]
  simp_rw [transport_C_mul]

/-- A general clearing factor in the full heat retains both its
Gaussian derivative correction and the adjacent factorial-order coupling. -/
theorem heat_factor_mul_succ {B : ℝ} (hB : 0 < B) (N : ℕ) (x r z : ℂ) (q : Polynomial ℂ) :
    heat B (N + 1) x ((Polynomial.X - Polynomial.C r) * q) z =
      (z - r) * heat B (N + 1) x q z -
        2 * (B : ℂ) * heat B (N + 1) x q.derivative z -
        (((N : ℂ) + 1) * x⁻¹) * heat B N x q z := by
  rw [heat, shift_factor_mul_succ, transport_sub, transport_factor hB,
    transport_C_mul, derivative_shift]
  rfl

/-- The exact combined action on a constant remains unchanged. -/
theorem heat_C (B : ℝ) (N : ℕ) (x c z : ℂ) : heat B N x (Polynomial.C c) z = c := by
  rw [heat, shift_C, transport_C]

/-- The combined linear displacement retains both the factorial order
and the actual complex evaluation point. -/
theorem heat_factor (B : ℝ) (N : ℕ) (x r z : ℂ) :
    heat B N x (Polynomial.X - Polynomial.C r) z = z - r - (N : ℂ) * x⁻¹ := by
  rw [heat, shift_factor, transport_sub, transport_C]
  change transport B (Polynomial.monomial 1 1) z - _ = _
  rw [transport_monomial]
  simp only [hermite, one_mul]
  ring

/-- A squared factor after full transport has the subtractive budget
`2B+N/x²`. The factorial contribution must not be discarded in a sign test. -/
theorem heat_factor_sq {B : ℝ} (hB : 0 < B) (N : ℕ) (x r z : ℂ) :
    heat B N x ((Polynomial.X - Polynomial.C r) ^ 2) z =
      (z - r - (N : ℂ) * x⁻¹) ^ 2 - (2 * (B : ℂ) + (N : ℂ) * x⁻¹ ^ 2) := by
  rw [heat, shift_factor_sq, transport_sub, transport_linear_square hB, transport_C]
  ring

end
end RiemannGaussian.FactorialPolynomialTransport
