/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeBandAbel
import RiemannGaussian.ZetaPrimeFilterPoleCancellation

/-!
# The selected zero signal inside the signed Chebyshev-error integral

The continuous background and both Abel boundary terms have independent
geometric estimates for every pole-annihilating polynomial. Consequently
the actual selected zero's multiplicity is carried by the remaining
complex integral against `x - theta(x)`. The integrand retains both phase
channels. Its independent signed lower bound remains open.
-/

open Complex Filter MeasureTheory Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A uniform exponential tilt controls the density-weighted kernel on
the positive logarithmic axis. It will only be used at omitted boundaries. -/
theorem norm_mul_zetaPrimeFilterKernel_le (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {x q : ℝ} (hx : 1 ≤ x) (hq : 0 < q) :
    ‖(x : ℂ) * zetaPrimeFilterKernel p N s x‖ ≤
      q⁻¹ ^ N * Real.exp (-((s.re - 1) - q) * Real.log x) *
        ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have he : ‖(x : ℂ) * Complex.exp (-s * (Real.log x : ℂ))‖ =
      Real.exp (-(s.re - 1) * Real.log x) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, Complex.norm_exp,
      Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ = Real.exp (Real.log x) * Real.exp (-s.re * Real.log x) := by rw [Real.exp_log hx0]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum : (x : ℂ) * zetaPrimeFilterKernel p N s x =
      ∑ k ∈ p.support, p.coeff k * ((Real.log x : ℂ) ^ (N + k) / ((N + k).factorial : ℂ)) *
        ((x : ℂ) * Complex.exp (-s * (Real.log x : ℂ))) := by
    simp only [zetaPrimeFilterKernel, zetaFactorialPolynomial, Polynomial.sum,
      Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ p.support, ‖p.coeff k‖ *
        (q⁻¹ ^ (N + k) * Real.exp (-((s.re - 1) - q) * Real.log x)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hl, Complex.norm_natCast, he, mul_assoc]
      exact mul_le_mul_of_nonneg_left (logMoment_exp_envelope (N + k) hl hq (s.re - 1)) (norm_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_add]
      ring

/-- The complete coefficient budget used only for the two band endpoints. -/
def zetaPrimeBandEndpointConstant (p : Polynomial ℂ) : ℝ :=
  ∑ k ∈ p.support, ‖p.coeff k‖ * ((1 / 4 : ℝ) ^ k + (4 : ℝ) ^ k)

private theorem lower_ge_one (N : ℕ) : 1 ≤ zetaPrimeBandLower N := by
  apply Real.one_le_exp_iff.mpr
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg N) (Real.log_pos (by norm_num)).le) (by norm_num)

private theorem upper_log (N : ℕ) : Real.log (zetaPrimeBandUpper N) = 32 * (N : ℝ) * Real.log 2 := by
  simp only [zetaPrimeBandUpper, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_mul]

private theorem lower_bound (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖((zetaPrimeBandLower N : ℝ) : ℂ) *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) (zetaPrimeBandLower N)‖ ≤
      (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (1 / 4 : ℝ) ^ k := by
  have h := norm_mul_zetaPrimeFilterKernel_le p N (3 / 2 + I * y) (lower_ge_one N) (by norm_num : (0 : ℝ) < 4)
  have hs : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  have he : Real.exp (-((3 / 2 - 1 : ℝ) - 4) * Real.log (zetaPrimeBandLower N)) ≤ (2 : ℝ) ^ N := by
    rw [zetaPrimeBandLower, Real.log_exp]
    calc
      _ ≤ Real.exp ((N : ℝ) * Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hm : (0 : ℝ) ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (1 / 4 : ℝ) ^ k :=
    Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (norm_nonneg _) (by positivity))
  norm_num only [hs, inv_eq_one_div] at h
  norm_num only at he
  apply h.trans
  calc
    _ ≤ (1 / 4 : ℝ) ^ N * 2 ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (1 / 4 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) hm
    _ = (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (1 / 4 : ℝ) ^ k := by
      rw [← mul_pow]
      norm_num

private theorem upper_bound (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖((zetaPrimeBandUpper N : ℝ) : ℂ) *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) (zetaPrimeBandUpper N)‖ ≤
      (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (4 : ℝ) ^ k := by
  have hx := (lower_ge_one N).trans (zetaPrimeBandLower_le_upper N)
  have h := norm_mul_zetaPrimeFilterKernel_le p N (3 / 2 + I * y) hx (by norm_num : (0 : ℝ) < 1 / 4)
  have hs : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
  have he : Real.exp (-((3 / 2 - 1 : ℝ) - 1 / 4) * Real.log (zetaPrimeBandUpper N)) ≤ (1 / 8 : ℝ) ^ N := by
    have h3 := Real.exp_nat_mul (Real.log 2) 3
    norm_num only [Nat.cast_ofNat] at h3
    have he3 : Real.exp (-3 * Real.log 2) = (1 / 8 : ℝ) := by
      rw [neg_mul, Real.exp_neg, h3, Real.exp_log (by norm_num)]
      norm_num
    rw [upper_log]
    calc
      _ ≤ Real.exp ((N : ℝ) * (-3 * Real.log 2)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
      _ = _ := by rw [Real.exp_nat_mul, he3]
  have hm : (0 : ℝ) ≤ ∑ k ∈ p.support, ‖p.coeff k‖ * (4 : ℝ) ^ k :=
    Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (norm_nonneg _) (by positivity))
  norm_num only [hs, one_div, inv_inv] at h
  norm_num only at he
  apply h.trans
  calc
    _ ≤ (4 : ℝ) ^ N * (1 / 8 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (4 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) hm
    _ = (1 / 2 : ℝ) ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * (4 : ℝ) ^ k := by
      rw [← mul_pow]
      norm_num

/-- Both density-weighted endpoints decay geometrically, uniformly in
the ordinate, for every fixed complex polynomial filter. -/
theorem norm_zetaPrimeBand_endpoints_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖((zetaPrimeBandUpper N : ℝ) : ℂ) *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) (zetaPrimeBandUpper N)‖ +
      ‖((zetaPrimeBandLower N : ℝ) : ℂ) *
        zetaPrimeFilterKernel p N (3 / 2 + I * y) (zetaPrimeBandLower N)‖ ≤
          (1 / 2 : ℝ) ^ N * zetaPrimeBandEndpointConstant p := by
  have h := add_le_add (upper_bound p N y) (lower_bound p N y)
  apply h.trans_eq
  rw [← mul_add, zetaPrimeBandEndpointConstant, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem center_ne_one (y : ℝ) : (3 / 2 + I * (y : ℂ)) ≠ 1 := by
  intro h
  have he := congrArg Complex.re h
  norm_num at he

/-- The continuous-density integral of any pole-annihilating filter
has an independent geometric bound. The exact primitive coefficients
remain visible in the constant. -/
theorem norm_zetaPrimeBand_density_integral_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hp : p.eval ((3 / 2 + I * (y : ℂ)) - 1)⁻¹ = 0) :
    ‖∫ x in Set.Ioc (zetaPrimeBandLower N) (zetaPrimeBandUpper N),
        zetaPrimeFilterKernel p N (3 / 2 + I * y) x‖ ≤
      (1 / 2 : ℝ) ^ N * zetaPrimeBandEndpointConstant
        (Polynomial.X * zetaPrimeFilterPrimitivePolynomial p (3 / 2 + I * y)) := by
  have he (q : Polynomial ℂ) (x : ℝ) :
      zetaPrimeFilterKernel (Polynomial.X * q) N (3 / 2 + I * y) x =
        zetaPrimeFilterKernel q (N + 1) (3 / 2 + I * y) x := by
    simp only [zetaPrimeFilterKernel, zetaFactorialPolynomial_X_mul]
  have hb := norm_zetaPrimeBand_endpoints_le
    (Polynomial.X * zetaPrimeFilterPrimitivePolynomial p (3 / 2 + I * y)) N y
  simp only [he] at hb
  rw [zetaPrimeFilterKernel_integral_eq_primitive p N (center_ne_one y) hp
    (zetaPrimeBandLower_pos N) (zetaPrimeBandLower_le_upper N)]
  exact (norm_sub_le _ _).trans hb

private theorem norm_theta_boundary (v : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖v * ((Chebyshev.theta x - x : ℝ) : ℂ)‖ ≤ (Real.log 4 + 1) * ‖(x : ℂ) * v‖ := by
  have ha : |Chebyshev.theta x - x| ≤ (Real.log 4 + 1) * x := by
    calc
      _ ≤ |Chebyshev.theta x| + |x| := abs_sub _ _
      _ = Chebyshev.theta x + x := by rw [abs_of_nonneg (Chebyshev.theta_nonneg x), abs_of_nonneg hx]
      _ ≤ _ := by nlinarith [Chebyshev.theta_le_log4_mul_x hx]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ‖v‖ * ((Real.log 4 + 1) * x) := mul_le_mul_of_nonneg_left ha (norm_nonneg _)
    _ = _ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]; ring

/-- Both signed Abel boundary terms, retained together as a complex
quantity before taking a norm. -/
def zetaPrimeBandChebyshevBoundary (p : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℂ :=
  zetaPrimeFilterKernel p N (3 / 2 + I * y) (zetaPrimeBandUpper N) *
      ((Chebyshev.theta (zetaPrimeBandUpper N) - zetaPrimeBandUpper N : ℝ) : ℂ) -
    zetaPrimeFilterKernel p N (3 / 2 + I * y) (zetaPrimeBandLower N) *
      ((Chebyshev.theta (zetaPrimeBandLower N) - zetaPrimeBandLower N : ℝ) : ℂ)

/-- Elementary Chebyshev bounds make both Abel boundary terms
geometrically negligible without an RH-strength estimate for `theta`. -/
theorem norm_zetaPrimeBandChebyshevBoundary_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    ‖zetaPrimeBandChebyshevBoundary p N y‖ ≤
      (1 / 2 : ℝ) ^ N * ((Real.log 4 + 1) * zetaPrimeBandEndpointConstant p) := by
  have hc : 0 ≤ Real.log 4 + 1 := by positivity
  rw [zetaPrimeBandChebyshevBoundary]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ (Real.log 4 + 1) *
        ‖((zetaPrimeBandUpper N : ℝ) : ℂ) * zetaPrimeFilterKernel p N (3 / 2 + I * y) (zetaPrimeBandUpper N)‖ +
      (Real.log 4 + 1) *
        ‖((zetaPrimeBandLower N : ℝ) : ℂ) * zetaPrimeFilterKernel p N (3 / 2 + I * y) (zetaPrimeBandLower N)‖ :=
      add_le_add (norm_theta_boundary _ ((zetaPrimeBandLower_pos N).le.trans (zetaPrimeBandLower_le_upper N)))
        (norm_theta_boundary _ (zetaPrimeBandLower_pos N).le)
    _ ≤ (Real.log 4 + 1) * ((1 / 2 : ℝ) ^ N * zetaPrimeBandEndpointConstant p) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_zetaPrimeBand_endpoints_le p N y) hc
    _ = _ := by ring

/-- The remaining signed integral pairs the complete filter derivative
with the ordinary-prime Chebyshev error over the exact retained band. -/
def zetaPrimeBandChebyshevIntegral (p : Polynomial ℂ) (N : ℕ) (y : ℝ) : ℂ :=
  ∫ x in Set.Ioc (zetaPrimeBandLower N) (zetaPrimeBandUpper N),
    deriv (zetaPrimeFilterKernel p N (3 / 2 + I * y)) x * ((x - Chebyshev.theta x : ℝ) : ℂ)

/-- Integrability for the literal signed carrier, not a totalized
improper expression. The interval is finite at each moment order. -/
theorem integrableOn_zetaPrimeBandChebyshevIntegral (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    IntegrableOn
      (fun x ↦ deriv (zetaPrimeFilterKernel p N (3 / 2 + I * y)) x * ((x - Chebyshev.theta x : ℝ) : ℂ))
      (Set.Ioc (zetaPrimeBandLower N) (zetaPrimeBandUpper N)) :=
  (integrableOn_zetaPrimeFilter_chebyshevError p N _ (zetaPrimeBandLower_pos N)).mono_set Set.Ioc_subset_Icc_self

/-- The real signed carrier explicitly couples both phase channels.
The imaginary filter enters with coefficient `y`, so a real-only
replacement would change the arithmetic quantity detecting the zero. -/
theorem zetaPrimeBandChebyshevIntegral_re_lowering (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    (zetaPrimeBandChebyshevIntegral p (N + 1) y).re =
      ∫ x in Set.Ioc (zetaPrimeBandLower (N + 1)) (zetaPrimeBandUpper (N + 1)),
        ((zetaPrimeFilterKernel p N (3 / 2 + I * y) x).re -
            (3 / 2 : ℝ) * (zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * y) x).re +
              y * (zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * y) x).im) / x *
          (x - Chebyshev.theta x) := by
  rw [zetaPrimeBandChebyshevIntegral]
  calc
    _ = ∫ x in Set.Ioc (zetaPrimeBandLower (N + 1)) (zetaPrimeBandUpper (N + 1)),
        (deriv (zetaPrimeFilterKernel p (N + 1) (3 / 2 + I * y)) x * ((x - Chebyshev.theta x : ℝ) : ℂ)).re :=
      (integral_re (integrableOn_zetaPrimeBandChebyshevIntegral p (N + 1) y)).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        deriv_zetaPrimeFilterKernel_re p N _ ((zetaPrimeBandLower_pos (N + 1)).trans hx.1)]
      have hre : (3 / 2 + I * (y : ℂ)).re = (3 / 2 : ℝ) := by norm_num
      have him : (3 / 2 + I * (y : ℂ)).im = y := by norm_num
      rw [hre, him]

/-- Exact comparison with the original finite prime band, keeping the
continuous density and both signed endpoint terms available upstream. -/
theorem zetaOrdinaryPrimeBandFilter_sub_chebyshevIntegral (p : Polynomial ℂ) (N : ℕ) (y : ℝ) :
    zetaOrdinaryPrimeBandFilter p N y - zetaPrimeBandChebyshevIntegral p N y =
      (∫ x in Set.Ioc (zetaPrimeBandLower N) (zetaPrimeBandUpper N),
        zetaPrimeFilterKernel p N (3 / 2 + I * y) x) + zetaPrimeBandChebyshevBoundary p N y := by
  have h := zetaOrdinaryPrimeBandFilter_sub_integral p N y
  change zetaOrdinaryPrimeBandFilter p N y - _ =
    zetaPrimeBandChebyshevBoundary p N y + zetaPrimeBandChebyshevIntegral p N y at h
  linear_combination h

/-- The actual prime band and its signed Chebyshev-error integral differ
by an independently bounded geometric error whenever the pole is killed. -/
theorem norm_zetaOrdinaryPrimeBandFilter_sub_chebyshevIntegral_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (hp : p.eval ((3 / 2 + I * (y : ℂ)) - 1)⁻¹ = 0) :
    ‖zetaOrdinaryPrimeBandFilter p N y - zetaPrimeBandChebyshevIntegral p N y‖ ≤
      (1 / 2 : ℝ) ^ N *
        (zetaPrimeBandEndpointConstant (Polynomial.X * zetaPrimeFilterPrimitivePolynomial p (3 / 2 + I * y)) +
          (Real.log 4 + 1) * zetaPrimeBandEndpointConstant p) := by
  rw [zetaOrdinaryPrimeBandFilter_sub_chebyshevIntegral]
  apply (norm_add_le _ _).trans
  simpa only [mul_add] using add_le_add (norm_zetaPrimeBand_density_integral_le p N y hp)
    (norm_zetaPrimeBandChebyshevBoundary_le p N y)

/-- The entire discrepancy between the actual prime band and its signed
error integral tends to zero even without normalization by a zero source. -/
theorem tendsto_zetaOrdinaryPrimeBandFilter_sub_chebyshevIntegral (p : Polynomial ℂ) (y : ℝ)
    (hp : p.eval ((3 / 2 + I * (y : ℂ)) - 1)⁻¹ = 0) :
    Tendsto (fun N ↦ zetaOrdinaryPrimeBandFilter p N y - zetaPrimeBandChebyshevIntegral p N y) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N ↦ norm_zetaOrdinaryPrimeBandFilter_sub_chebyshevIntegral_le p N y hp)
  simpa only [zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
      (zetaPrimeBandEndpointConstant (Polynomial.X * zetaPrimeFilterPrimitivePolynomial p (3 / 2 + I * y)) +
        (Real.log 4 + 1) * zetaPrimeBandEndpointConstant p)

/-- Every hypothetical right-half zero forces its full negative
multiplicity into the signed Chebyshev-error integral. The continuous
background and both endpoints have been independently proved negligible. -/
theorem tendsto_zetaRightHalfPrimeBandChebyshevIntegral (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      zetaPrimeBandChebyshevIntegral (zetaRightHalfZeroModeFilter rho hrho) N rho.1.im)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have ha : ‖((3 / 2 - rho.1.re : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [NontrivialZetaZero.re_lt_one rho])]
    linarith
  have hpow := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one ha).comp (tendsto_add_atTop_nat 1)
  have ht := hpow.mul (tendsto_zetaOrdinaryPrimeBandFilter_sub_chebyshevIntegral
    (zetaRightHalfZeroModeFilter rho hrho) rho.1.im (zetaRightHalfZeroModeFilter_eval_pole rho hrho))
  have h := (tendsto_zetaRightHalfOrdinaryPrimeBandFilter rho hrho).sub ht
  simp only [zero_mul, sub_zero, Function.comp_apply] at h
  convert h using 1
  funext N
  ring

/-- The real channel retains the selected zero's full signed
multiplicity after both analytic background and finite boundaries vanish. -/
theorem tendsto_zetaRightHalfPrimeBandChebyshevIntegral_re (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ ↦ (3 / 2 - rho.1.re) ^ (N + 1) *
      (zetaPrimeBandChebyshevIntegral (zetaRightHalfZeroModeFilter rho hrho) N rho.1.im).re)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℝ))) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_zetaRightHalfPrimeBandChebyshevIntegral rho hrho)
  simpa only [Function.comp_def, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.neg_re, Complex.natCast_re] using h

/-- The exact signed error integral is eventually more negative than
half the selected zero's source scale. No independent opposite inequality
is asserted; proving one is the remaining arithmetic frontier. -/
theorem zetaRightHalfPrimeBandChebyshevIntegral_eventually_negative (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ N : ℕ in atTop,
      (zetaPrimeBandChebyshevIntegral (zetaRightHalfZeroModeFilter rho hrho) N rho.1.im).re <
        -(analyticZetaZeroMultiplicity rho : ℝ) / (2 * (3 / 2 - rho.1.re) ^ (N + 1)) := by
  have hm : (0 : ℝ) < analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  have hu : 0 < 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (tendsto_zetaRightHalfPrimeBandChebyshevIntegral_re rho hrho).eventually
    (gt_mem_nhds (by linarith : -(analyticZetaZeroMultiplicity rho : ℝ) < -(analyticZetaZeroMultiplicity rho : ℝ) / 2))
  filter_upwards [h] with N hN
  rw [lt_div_iff₀ (mul_pos (by norm_num) (pow_pos hu _))]
  nlinarith

end

end RiemannGaussian
