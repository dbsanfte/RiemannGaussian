/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianMellinVertical
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Algebra.Polynomial

/-!
# Exact polynomial transport through a vertical Gaussian

Multiplying by a polynomial before Gaussian smoothing is different from
multiplying by its value at the center afterwards. The full complex Stein
identity retains the displacement and derivative terms. Its finite Hermite
recursion evaluates every polynomial multiplier without discarding a phase.
This is the operator needed to keep meromorphic clearing factors inside a
vertical heat average.
-/

namespace RiemannGaussian.GaussianPolynomialTransport
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology

/-- The unnormalized vertical Gaussian with its complete Fourier phase. -/
def atom (B x y : ℝ) : ℂ :=
  Complex.exp (-((1 / (4 * B) : ℝ) : ℂ) * (y : ℂ) ^ 2 + I * (x : ℂ) * (y : ℂ))

/-- The positive real mass of the vertical Gaussian. -/
def mass (B : ℝ) : ℝ := Real.sqrt (Real.pi / (1 / (4 * B)))

/-- The actual polynomial-weighted Gaussian integral, before normalization. -/
def weighted (B x : ℝ) (s : ℂ) (q : Polynomial ℂ) : ℂ :=
  ∫ y : ℝ, q.eval (s - I * (y : ℂ)) * atom B x y

/-- Every monomial is integrable against the full Gaussian. -/
theorem integrable_real_pow_gaussian {B : ℝ} (hB : 0 < B) (n : ℕ) :
    Integrable (fun y : ℝ => y ^ n * Real.exp (-(1 / (4 * B)) * y ^ 2)) := by
  simpa only [Real.rpow_natCast] using
    integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < 1 / (4 * B))
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : (-1 : ℝ) < (n : ℝ))

/-- All complex polynomial coefficients are integrable against the real
Gaussian, using the complete finite polynomial expansion. -/
theorem integrable_eval_gaussian {B : ℝ} (hB : 0 < B) (q : Polynomial ℂ) :
    Integrable (fun y : ℝ => q.eval (y : ℂ) *
      (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ)) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    convert! hp.add hq using 1
    ext y
    simp [Polynomial.eval_add, add_mul]
  | monomial n c =>
    have hi := ((integrable_real_pow_gaussian hB n).ofReal).const_mul c
    convert! hi using 1
    ext y
    simp [Polynomial.eval_monomial, mul_assoc]

/-- The polynomial along the original vertical line has a genuinely
integrable Gaussian norm; no bound for the arithmetic response is assumed. -/
theorem integrable_vertical_polynomial_gaussian {B : ℝ} (hB : 0 < B)
    (s : ℂ) (q : Polynomial ℂ) :
    Integrable (fun y : ℝ => q.eval (s - I * (y : ℂ)) *
      (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ)) := by
  convert! integrable_eval_gaussian hB (q.comp (Polynomial.C s - Polynomial.C I * Polynomial.X)) using 1
  ext y
  simp

/-- The Gaussian and its unit complex phase remain separate in the
arithmetic sum-integral transport. -/
theorem atom_eq_gaussian_phase (B x y : ℝ) :
    atom B x y = (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) *
      Complex.exp (I * (y : ℂ) * (x : ℂ)) := by
  rw [atom, Complex.exp_add, Complex.ofReal_exp]
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- The Fourier phase has unit norm and leaves the full polynomial
Gaussian integrability intact. -/
theorem integrable_weighted {B : ℝ} (hB : 0 < B) (x : ℝ) (s : ℂ) (q : Polynomial ℂ) :
    Integrable (fun y : ℝ => q.eval (s - I * (y : ℂ)) * atom B x y) := by
  have hq : Continuous (fun y : ℝ => q.eval (s - I * (y : ℂ))) :=
    q.continuous.comp (by fun_prop)
  apply (integrable_vertical_polynomial_gaussian hB s q).norm.mono' (by
    unfold atom
    fun_prop)
  filter_upwards with y
  have ha : ‖atom B x y‖ = Real.exp (-(1 / (4 * B)) * y ^ 2) := by
    unfold atom
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, Complex.mul_re, Complex.mul_im]
  rw [norm_mul, ha, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- The Gaussian mass is strictly positive at positive width. -/
theorem mass_pos {B : ℝ} (hB : 0 < B) : 0 < mass B := by unfold mass; positivity

/-- The unweighted Fourier integral is evaluated with its exact phase
and normalization. -/
theorem integral_atom {B : ℝ} (hB : 0 < B) (x : ℝ) :
    (∫ y : ℝ, atom B x y) = (mass B : ℂ) * (Real.exp (-B * x ^ 2) : ℂ) := by
  have h := integral_gaussianMellin_vertical x 0 (by positivity : 0 < 1 / (4 * B))
  have he (y : ℝ) : Complex.exp ((x : ℂ) * ((0 : ℝ) + (y : ℂ) * I) +
      ((1 / (4 * B) : ℝ) : ℂ) * ((0 : ℝ) + (y : ℂ) * I) ^ 2) = atom B x y := by
    unfold atom
    congr 1
    ring_nf
    simp [sub_eq_add_neg]
  simp only [Complex.ofReal_zero, zero_add] at h he
  simp_rw [he] at h
  have hex : -x ^ 2 / (4 * (1 / (4 * B))) = -B * x ^ 2 := by field_simp
  simpa only [hex, Complex.ofReal_mul, mass] using h

/-- Constants pass through the Gaussian exactly. -/
theorem weighted_C {B : ℝ} (hB : 0 < B) (x : ℝ) (s c : ℂ) :
    weighted B x s (Polynomial.C c) = c * (mass B : ℂ) * (Real.exp (-B * x ^ 2) : ℂ) := by
  simp only [weighted, Polynomial.eval_C, integral_const_mul, integral_atom hB, mul_assoc]

/-- Addition retains the two complete polynomial-weighted integrals. -/
theorem weighted_add {B : ℝ} (hB : 0 < B) (x : ℝ) (s : ℂ) (p q : Polynomial ℂ) :
    weighted B x s (p + q) = weighted B x s p + weighted B x s q := by
  simp only [weighted, Polynomial.eval_add, add_mul]
  exact integral_add (integrable_weighted hB x s p) (integrable_weighted hB x s q)

/-- Complex scalar multiplication preserves the original integral. -/
theorem weighted_C_mul (B x : ℝ) (s c : ℂ) (q : Polynomial ℂ) :
    weighted B x s (Polynomial.C c * q) = c * weighted B x s q := by
  simp only [weighted, Polynomial.eval_mul, Polynomial.eval_C, mul_assoc, integral_const_mul]

/-- The complete weighted Gaussian has an exact derivative. The final
form is chosen to keep the Stein displacement and polynomial derivative. -/
theorem hasDerivAt_weighted (B x y : ℝ) (hB : B ≠ 0) (s : ℂ) (q : Polynomial ℂ) :
    HasDerivAt (fun v : ℝ => q.eval (s - I * (v : ℂ)) * atom B x v)
      ((-I / (2 * (B : ℂ))) *
        ((Polynomial.X * q).eval (s - I * (y : ℂ)) * atom B x y -
          (s + 2 * (B : ℂ) * (x : ℂ)) * (q.eval (s - I * (y : ℂ)) * atom B x y) +
          (2 * (B : ℂ)) * (q.derivative.eval (s - I * (y : ℂ)) * atom B x y))) y := by
  have hid := (hasDerivAt_id y).ofReal_comp
  have hlin := (hasDerivAt_const y s).sub (hid.const_mul I)
  have hq := (q.hasDerivAt (s - I * (y : ℂ))).comp y hlin
  have he := ((hid.pow 2).const_mul (-((1 / (4 * B) : ℝ) : ℂ))).add
    (hid.const_mul (I * (x : ℂ)))
  apply (hq.mul he.cexp).congr_deriv
  dsimp only [atom, Function.comp_apply, id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Complex.ofReal_one, mul_one,
    zero_sub, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hBc : (B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hB
  norm_num only [Nat.reduceSub, pow_one]
  field_simp
  ring_nf
  simp [sub_eq_add_neg]

/-- The complex Stein identity transports a polynomial factor through
the Gaussian, retaining both its displacement and derivative correction. -/
theorem weighted_X_mul {B : ℝ} (hB : 0 < B) (x : ℝ) (s : ℂ) (q : Polynomial ℂ) :
    weighted B x s (Polynomial.X * q) =
      (s + 2 * (B : ℂ) * (x : ℂ)) * weighted B x s q -
        (2 * (B : ℂ)) * weighted B x s q.derivative := by
  have hi := integrable_weighted hB x s q
  have hiX := integrable_weighted hB x s (Polynomial.X * q)
  have hiD := integrable_weighted hB x s q.derivative
  have hd := ((hiX.sub (hi.const_mul (s + 2 * (B : ℂ) * (x : ℂ)))).add
    (hiD.const_mul (2 * (B : ℂ)))).const_mul (-I / (2 * (B : ℂ)))
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable
    (fun y => hasDerivAt_weighted B x y hB.ne' s q) hd hi
  have hsub : Integrable (fun y : ℝ => (Polynomial.X * q).eval (s - I * (y : ℂ)) * atom B x y -
      (s + 2 * (B : ℂ) * (x : ℂ)) * (q.eval (s - I * (y : ℂ)) * atom B x y)) :=
    hiX.sub (hi.const_mul _)
  rw [integral_const_mul, integral_add hsub (hiD.const_mul (2 * (B : ℂ))),
    integral_sub hiX (hi.const_mul (s + 2 * (B : ℂ) * (x : ℂ))),
    integral_const_mul, integral_const_mul] at hz
  change (-I / (2 * (B : ℂ))) * (weighted B x s (Polynomial.X * q) -
    (s + 2 * (B : ℂ) * (x : ℂ)) * weighted B x s q +
    (2 * (B : ℂ)) * weighted B x s q.derivative) = 0 at hz
  have hc : -I / (2 * (B : ℂ)) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr I_ne_zero) (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr hB.ne'))
  have he := (mul_eq_zero.mp hz).resolve_left hc
  linear_combination he

/-- The finite Gaussian polynomial moments, with their signed contraction
term. This is the scaled Hermite recursion, valid at complex arguments. -/
def hermite (B : ℝ) (z : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => z
  | n + 2 => z * hermite B z (n + 1) - 2 * (B : ℂ) * (n + 1 : ℂ) * hermite B z n

/-- The exact finite polynomial resulting from Gaussian transport. -/
def transport (B : ℝ) (q : Polynomial ℂ) (z : ℂ) : ℂ :=
  q.sum (fun n c => c * hermite B z n)

/-- Polynomial addition retains all transported coefficients. -/
theorem transport_add (B : ℝ) (p q : Polynomial ℂ) (z : ℂ) :
    transport B (p + q) z = transport B p z + transport B q z :=
  Polynomial.sum_add_index _ _ _ (by intro n; simp) (by intro n a b; ring)

/-- Each monomial is exactly its signed Gaussian Hermite moment. -/
theorem transport_monomial (B : ℝ) (n : ℕ) (c z : ℂ) :
    transport B (Polynomial.monomial n c) z = c * hermite B z n :=
  Polynomial.sum_monomial_index _ _ (by simp)

/-- The Gaussian does not change a constant polynomial. -/
theorem transport_C (B : ℝ) (c z : ℂ) : transport B (Polynomial.C c) z = c := by
  simpa only [Polynomial.monomial_zero_left, hermite, mul_one] using transport_monomial B 0 c z

/-- Complex scalar multiplication commutes with polynomial transport. -/
theorem transport_C_mul (B : ℝ) (c : ℂ) (q : Polynomial ℂ) (z : ℂ) :
    transport B (Polynomial.C c * q) z = c * transport B q z := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, transport_add, hp, hq]
  | monomial n d => rw [Polynomial.C_mul_monomial, transport_monomial, transport_monomial]; ring

/-- The full Gaussian integral of one is its Fourier mass. -/
theorem weighted_one {B : ℝ} (hB : 0 < B) (x : ℝ) (s : ℂ) :
    weighted B x s 1 = (mass B : ℂ) * (Real.exp (-B * x ^ 2) : ℂ) := by
  simpa only [map_one, one_mul] using weighted_C hB x s 1

/-- The Stein recurrence evaluates every polynomial power exactly,
including the normalization and complex displacement. -/
theorem weighted_X_pow {B : ℝ} (hB : 0 < B) (x : ℝ) (s : ℂ) (n : ℕ) :
    weighted B x s (Polynomial.X ^ n) =
      (mass B : ℂ) * (Real.exp (-B * x ^ 2) : ℂ) * hermite B (s + 2 * (B : ℂ) * (x : ℂ)) n := by
  induction n using Nat.twoStepInduction with
  | zero => simpa only [pow_zero, hermite, mul_one] using weighted_one hB x s
  | one =>
    have h := weighted_X_mul hB x s (1 : Polynomial ℂ)
    simp only [mul_one, Polynomial.derivative_one, ← Polynomial.C_0, weighted_C hB,
      zero_mul, mul_zero, sub_zero, weighted_one hB] at h
    simpa only [pow_one, hermite, mul_comm, mul_left_comm, mul_assoc] using h
  | more n hn hn1 =>
    have h := weighted_X_mul hB x s (Polynomial.X ^ (n + 1))
    rw [← pow_succ', show n + 1 + 1 = n + 2 by omega,
      Polynomial.derivative_X_pow, Nat.add_sub_cancel, weighted_C_mul, hn, hn1] at h
    rw [h, hermite]
    push_cast
    ring

/-- Every complex polynomial multiplier passes through the full Gaussian
as its explicit finite Hermite transform, with no numerical coefficients. -/
theorem weighted_eq_transport {B : ℝ} (hB : 0 < B) (x : ℝ) (s : ℂ) (q : Polynomial ℂ) :
    weighted B x s q = (mass B : ℂ) * (Real.exp (-B * x ^ 2) : ℂ) *
      transport B q (s + 2 * (B : ℂ) * (x : ℂ)) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [weighted_add hB, hp, hq, transport_add]; ring
  | monomial n c =>
    rw [transport_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
      weighted_C_mul, weighted_X_pow hB]
    ring

/-- The finite transform obeys the same signed Weyl commutation law as
the original integral, at every complex argument. -/
theorem transport_X_mul {B : ℝ} (hB : 0 < B) (q : Polynomial ℂ) (z : ℂ) :
    transport B (Polynomial.X * q) z = z * transport B q z - 2 * (B : ℂ) * transport B q.derivative z := by
  have h := weighted_X_mul hB 0 z q
  simp_rw [weighted_eq_transport hB] at h
  simp only [Complex.ofReal_zero, mul_zero, add_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Real.exp_zero, Complex.ofReal_one, mul_one] at h
  have hm : (mass B : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mass_pos hB).ne'
  apply mul_left_cancel₀ hm
  linear_combination h

/-- Signed subtraction is retained by the finite polynomial transform. -/
theorem transport_sub (B : ℝ) (p q : Polynomial ℂ) (z : ℂ) :
    transport B (p - q) z = transport B p z - transport B q z := by
  have h := transport_add B (p - q) q z
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

/-- A clearing factor produces both an exact displaced factor and a
derivative correction after Gaussian smoothing. -/
theorem transport_factor {B : ℝ} (hB : 0 < B) (q : Polynomial ℂ) (r z : ℂ) :
    transport B ((Polynomial.X - Polynomial.C r) * q) z =
      (z - r) * transport B q z - 2 * (B : ℂ) * transport B q.derivative z := by
  rw [sub_mul, transport_sub, transport_X_mul hB, transport_C_mul]
  ring

/-- A double clearing factor retains its full coupled three-term
correction for every polynomial, rather than just the value at the root. -/
theorem transport_double_factor {B : ℝ} (hB : 0 < B) (q : Polynomial ℂ) (r z : ℂ) :
    transport B ((Polynomial.X - Polynomial.C r) ^ 2 * q) z =
      ((z - r) ^ 2 - 2 * (B : ℂ)) * transport B q z -
        4 * (B : ℂ) * (z - r) * transport B q.derivative z +
        4 * (B : ℂ) ^ 2 * transport B q.derivative.derivative z := by
  rw [pow_two, mul_assoc, transport_factor hB, transport_factor hB,
    Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_C, sub_zero, one_mul, transport_add, transport_factor hB]
  ring

/-- The exact Gaussian image of a squared linear factor retains the
subtractive variance term at every complex argument. -/
theorem transport_linear_square {B : ℝ} (hB : 0 < B) (r z : ℂ) :
    transport B ((Polynomial.X - Polynomial.C r) ^ 2) z = (z - r) ^ 2 - 2 * (B : ℂ) := by
  have h := transport_double_factor hB (1 : Polynomial ℂ) r z
  have h1 : transport B (1 : Polynomial ℂ) z = 1 := by simpa only [map_one] using transport_C B 1 z
  have h0 : transport B (0 : Polynomial ℂ) z = 0 := by simpa only [map_zero] using transport_C B 0 z
  simpa only [mul_one, Polynomial.derivative_one, Polynomial.derivative_zero,
    h1, h0, mul_zero, sub_zero, add_zero] using h

/-- Gaussian smoothing does not preserve a double clearing root: its
exact signed correction at that root is `-2B`. -/
theorem transport_double_root {B : ℝ} (hB : 0 < B) (r : ℂ) :
    transport B ((Polynomial.X - Polynomial.C r) ^ 2) r = -2 * (B : ℂ) := by
  rw [transport_linear_square hB, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  ring

end
end RiemannGaussian.GaussianPolynomialTransport
