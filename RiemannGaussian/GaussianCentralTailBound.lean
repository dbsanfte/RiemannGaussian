/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.GaussianSimplePoleHeat

/-!
# Gaussian localization with a polynomial outer envelope

A bound on a fixed central interval combines with any polynomial global
envelope to give a quantitative bound for the entire complex Gaussian
average. The outside allowance is exponentially small in inverse width.
All integrability and normalization factors are retained explicitly.
-/

namespace RiemannGaussian.GaussianCentralTailBound
noncomputable section
open Complex Filter MeasureTheory Set Topology
open GaussianPolynomialTransport GaussianSimplePoleHeat

/-- The complete mass-normalized complex vertical Gaussian average. -/
def average (B : ℝ) (f : ℝ → ℂ) : ℂ :=
  (mass B : ℂ)⁻¹ * ∫ y : ℝ, (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) * f y

/-- A fixed, nonnegative integrable envelope for all polynomial outer
growth after half the Gaussian exponent has paid for localization. -/
def envelope (d : ℕ) (y : ℝ) : ℝ := (1 + y ^ 2) ^ d * Real.exp (-(1 / 8) * y ^ 2)

/-- The complete polynomial Gaussian envelope is genuinely integrable. -/
theorem integrable_envelope (d : ℕ) : Integrable (envelope d) := by
  have hi := (integrable_eval_gaussian (B := 2) (by norm_num)
    ((1 + Polynomial.X ^ 2 : Polynomial ℂ) ^ d)).re
  convert! hi using 1
  ext y
  simp only [envelope, RCLike.re_to_complex, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X]
  have hp : ((1 : ℂ) + (y : ℂ) ^ 2) ^ d = (((1 + y ^ 2) ^ d : ℝ) : ℂ) := by push_cast; rfl
  rw [hp, ← Complex.ofReal_mul, Complex.ofReal_re]
  norm_num

/-- The finite outer-envelope mass; it is independent of the varying
Gaussian width and the factorial order. -/
def tailMass (d : ℕ) : ℝ := ∫ y : ℝ, envelope d y

/-- The fixed polynomial Gaussian envelope has nonnegative total mass. -/
theorem tailMass_nonneg (d : ℕ) : 0 ≤ tailMass d :=
  integral_nonneg (fun y ↦ by unfold envelope; positivity)

/-- The full outside allowance, including the original Gaussian mass
normalization. -/
def tailAllowance (δ : ℝ) (d : ℕ) (B : ℝ) : ℝ :=
  tailMass d / mass B * Real.exp (-(δ ^ 2 / (8 * B)))

/-- The outside allowance is nonnegative at every positive width. -/
theorem tailAllowance_nonneg (δ : ℝ) (d : ℕ) {B : ℝ} (hB : 0 < B) :
    0 ≤ tailAllowance δ d B := by
  unfold tailAllowance
  exact mul_nonneg (div_nonneg (tailMass_nonneg d) (mass_pos hB).le) (Real.exp_pos _).le

private theorem gaussian_tail_le {B δ y : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hδ : 0 ≤ δ) (hy : δ ≤ |y|) :
    Real.exp (-(1 / (4 * B)) * y ^ 2) ≤
      Real.exp (-(δ ^ 2 / (8 * B))) * Real.exp (-(1 / 8) * y ^ 2) := by
  have hsq : δ ^ 2 ≤ y ^ 2 := by nlinarith [sq_abs y]
  have hfirst : δ ^ 2 / (8 * B) ≤ y ^ 2 / (8 * B) :=
    div_le_div_of_nonneg_right hsq (by positivity)
  have hsecond : y ^ 2 / 8 ≤ y ^ 2 / (8 * B) :=
    div_le_div_of_nonneg_left (sq_nonneg y) (by positivity) (by linarith)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : -(1 / (4 * B)) * y ^ 2 = -(y ^ 2 / (8 * B)) - y ^ 2 / (8 * B) := by ring
  rw [he]
  linarith

/-- A central bound and a polynomial global bound control the entire
complex Gaussian average. No sign assumption is imposed on the integrand,
and both bounds apply to the same original function. -/
theorem norm_average_le {f : ℝ → ℂ} {B δ a b : ℝ} (d : ℕ)
    (hB : 0 < B) (hB1 : B ≤ 1) (hδ : 0 ≤ δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hi : Integrable (fun y : ℝ ↦ (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) * f y))
    (hcentral : ∀ y : ℝ, |y| ≤ δ → ‖f y‖ ≤ a)
    (hglobal : ∀ y : ℝ, ‖f y‖ ≤ b * (1 + y ^ 2) ^ d) :
    ‖average B f‖ ≤ a + b * tailAllowance δ d B := by
  have hg : Integrable (fun y : ℝ ↦ Real.exp (-(1 / (4 * B)) * y ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  have he : Integrable (fun y : ℝ ↦ a * Real.exp (-(1 / (4 * B)) * y ^ 2) +
      (b * Real.exp (-(δ ^ 2 / (8 * B)))) * envelope d y) :=
    (hg.const_mul a).add ((integrable_envelope d).const_mul _)
  have hpt (y : ℝ) : ‖(Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) * f y‖ ≤
      a * Real.exp (-(1 / (4 * B)) * y ^ 2) +
        (b * Real.exp (-(δ ^ 2 / (8 * B)))) * envelope d y := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    by_cases hy : |y| ≤ δ
    · have hh := mul_le_mul_of_nonneg_left (hcentral y hy)
        (Real.exp_pos (-(1 / (4 * B)) * y ^ 2)).le
      have hp : 0 ≤ (b * Real.exp (-(δ ^ 2 / (8 * B)))) * envelope d y := by
        unfold envelope
        positivity
      nlinarith
    · have hh := mul_le_mul (gaussian_tail_le hB hB1 hδ (le_of_not_ge hy)) (hglobal y)
        (norm_nonneg _) (by positivity : 0 ≤ Real.exp (-(δ ^ 2 / (8 * B))) * Real.exp (-(1 / 8) * y ^ 2))
      have hp : 0 ≤ a * Real.exp (-(1 / (4 * B)) * y ^ 2) := by positivity
      dsimp [envelope]
      nlinarith
  have hint := (norm_integral_le_integral_norm _).trans (integral_mono hi.norm he hpt)
  rw [integral_add (hg.const_mul a) ((integrable_envelope d).const_mul _),
    integral_const_mul, integral_const_mul, integral_gaussian] at hint
  change ‖∫ y : ℝ, (Real.exp (-(1 / (4 * B)) * y ^ 2) : ℂ) * f y‖ ≤
    a * mass B + (b * Real.exp (-(δ ^ 2 / (8 * B)))) * tailMass d at hint
  rw [average, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (mass_pos hB).le]
  calc
    _ ≤ (mass B)⁻¹ * (a * mass B + (b * Real.exp (-(δ ^ 2 / (8 * B)))) * tailMass d) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (mass_pos hB).le)
    _ = _ := by unfold tailAllowance; field_simp [(mass_pos hB).ne']

private theorem mass_eq_sqrt (B : ℝ) : mass B = Real.sqrt (4 * Real.pi * B) := by
  unfold mass
  congr 1
  rw [div_div_eq_mul_div, div_one]
  ring

private theorem mass_quadraticWidth {c u : ℝ} (hc : 0 < c) (hu : 0 < u) (n : ℕ) :
    mass (quadraticWidth c u n) = mass (c * u ^ 2) /
      Real.sqrt (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
  rw [mass_eq_sqrt, mass_eq_sqrt, ← Real.sqrt_div (by positivity)]
  unfold quadraticWidth
  congr 1
  ring

/-- The normalized outside allowance on the explicit quadratic width
has a Gaussian-in-order majorant. The sole extra factor from normalization
is at most linear in the order. -/
theorem tailAllowance_quadraticWidth_le (δ : ℝ) {c u : ℝ}
    (hc : 0 < c) (hu : 0 < u) (d n : ℕ) :
    tailAllowance δ d (quadraticWidth c u n) ≤
      (tailMass d / mass (c * u ^ 2)) * ((n : ℝ) + 2) *
        Real.exp (-(δ ^ 2 / (8 * (c * u ^ 2))) * ((n : ℝ) + 1) ^ 2) := by
  have hm : 0 < mass (c * u ^ 2) := mass_pos (by positivity)
  have ht : 0 ≤ tailMass d := tailMass_nonneg d
  have hden : 0 < (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by positivity
  have hsqrt : Real.sqrt (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) ≤ (n : ℝ) + 2 := by
    apply (Real.sqrt_le_iff).mpr
    push_cast
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : -(δ ^ 2 / (8 * quadraticWidth c u n)) ≤
      -(δ ^ 2 / (8 * (c * u ^ 2))) * ((n : ℝ) + 1) ^ 2 := by
    have hcoef : 0 ≤ δ ^ 2 / (8 * (c * u ^ 2)) := by positivity
    have heq : -(δ ^ 2 / (8 * quadraticWidth c u n)) =
        -(δ ^ 2 / (8 * (c * u ^ 2))) * ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
      unfold quadraticWidth
      push_cast
      field_simp
    rw [heq]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  unfold tailAllowance
  rw [mass_quadraticWidth hc hu, div_div_eq_mul_div]
  calc
    _ ≤ (tailMass d * ((n : ℝ) + 2) / mass (c * u ^ 2)) *
        Real.exp (-(δ ^ 2 / (8 * (c * u ^ 2))) * ((n : ℝ) + 1) ^ 2) := by
      apply mul_le_mul _ (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt (tailMass_nonneg d)) hm.le
    _ = _ := by ring

private theorem tendsto_geometric_gaussian {a G : ℝ} (ha : 0 < a) (hG : 0 < G) :
    Tendsto (fun n : ℕ ↦ G ^ n * ((n : ℝ) + 2) * Real.exp (-a * ((n : ℝ) + 1) ^ 2))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hx := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hn
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hn
  have hlim : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2) * Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa only [pow_one, Function.comp_def, add_mul, mul_zero, add_zero] using hx.add (he.const_mul 2)
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity)) _ hlim
  filter_upwards [hn.eventually (eventually_ge_atTop ((Real.log G + 1) / a))] with n hn'
  have hbound : Real.log G + 1 ≤ a * (n : ℝ) := by
    have hh := (div_le_iff₀ ha).mp hn'
    linarith
  have hex : (n : ℝ) * Real.log G + -a * ((n : ℝ) + 1) ^ 2 ≤ -(n : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n,
      mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hbound)]
  have hp : G ^ n * Real.exp (-a * ((n : ℝ) + 1) ^ 2) ≤ Real.exp (-(n : ℝ)) := by
    rw [← Real.exp_log hG, ← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by simpa only [Real.log_exp] using hex)
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- At quadratic widths the complete outside allowance absorbs every
fixed exponential growth rate in the factorial order. This is a joint
order/width limit, with no diagonal selection or omitted mass factor. -/
theorem tendsto_pow_mul_tailAllowance_quadraticWidth {δ c u G : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hu : 0 < u) (hG : 0 < G) (d : ℕ) :
    Tendsto (fun n : ℕ ↦ G ^ n * tailAllowance δ d (quadraticWidth c u n)) atTop (𝓝 0) := by
  have hlim := (tendsto_geometric_gaussian
    (by positivity : 0 < δ ^ 2 / (8 * (c * u ^ 2))) hG).const_mul (tailMass d / mass (c * u ^ 2))
  apply squeeze_zero (fun n ↦ mul_nonneg (pow_nonneg hG.le _)
    (tailAllowance_nonneg δ d (quadraticWidth_pos hc hu n))) _ (by simpa using hlim)
  intro n
  have h := mul_le_mul_of_nonneg_left (tailAllowance_quadraticWidth_le δ hc hu d n)
    (pow_nonneg hG.le n)
  simpa only [neg_mul, mul_neg, mul_assoc, mul_left_comm, mul_comm] using h

/-- The explicit quadratic Gaussian width tends to zero. -/
theorem tendsto_quadraticWidth (c u : ℝ) :
    Tendsto (quadraticWidth c u) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 hn)
  have h2 := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 2 hn)
  have hh := (h1.mul h2).const_mul (c * u ^ 2)
  change Tendsto (fun n ↦ quadraticWidth c u n) atTop (𝓝 0)
  simpa only [Function.comp_def, mul_zero, quadraticWidth, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm] using hh

end
end RiemannGaussian.GaussianCentralTailBound
