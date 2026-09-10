/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeBandChebyshev
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Second differences of the complete factorial kernel

An exact second derivative retains all three adjacent moments and their
complex coefficients. A real-variable exponential tilt gives summable
spatial decay for the kernel on real part one quarter after two derivatives.
This is the smooth factor needed after moving a fixed Dirichlet weight
from the arithmetic coefficients into the kernel.
-/

open Complex
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- An exact shift of the spectral parameter transfers a multiplicative
weight without changing any factorial coefficient or complex phase. -/
theorem zetaPrimeFilterKernel_add_parameter (p : Polynomial ℂ) (N : ℕ)
    (s t : ℂ) (x : ℝ) :
    zetaPrimeFilterKernel p N (s + t) x =
      zetaPrimeFilterKernel p N s x * Complex.exp (-t * (Real.log x : ℂ)) := by
  simp only [zetaPrimeFilterKernel, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Division by a positive real power is an exact integer parameter shift. -/
theorem zetaPrimeFilterKernel_div_pow (p : Polynomial ℂ) (N r : ℕ) (s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    zetaPrimeFilterKernel p N s x / (x : ℂ) ^ r =
      zetaPrimeFilterKernel p N (s + r) x := by
  have he : Complex.exp ((r : ℂ) * (Real.log x : ℂ)) = (x : ℂ) ^ r := by
    rw [Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log hx]
  rw [zetaPrimeFilterKernel_add_parameter, neg_mul, Complex.exp_neg, he, div_eq_mul_inv]

/-- A pointwise envelope for the full complex polynomial kernel on the
positive logarithmic axis, with arbitrary positive exponential tilt. -/
theorem norm_zetaPrimeFilterKernel_le_tilt (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {x q : ℝ} (hx : 1 ≤ x) (hq : 0 < q) :
    ‖zetaPrimeFilterKernel p N s x‖ ≤ q⁻¹ ^ N * Real.exp (-(s.re - q) * Real.log x) *
      ∑ k ∈ p.support, ‖p.coeff k‖ * q⁻¹ ^ k := by
  have hx0 := zero_lt_one.trans_le hx
  have h := norm_mul_zetaPrimeFilterKernel_le p N s hx hq
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le] at h
  have he : Real.exp (-((s.re - 1) - q) * Real.log x) =
      x * Real.exp (-(s.re - q) * Real.log x) := by
    conv_rhs => lhs; rw [← Real.exp_log hx0]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  nlinarith [h]

/-- The second differential identity keeps its three adjacent factorial
moments and all complex damping and rotation coefficients. -/
theorem hasDerivAt_zetaPrimeKernel_lowering (p : Polynomial ℂ) (N : ℕ) (s : ℂ)
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦
      (zetaPrimeFilterKernel p (N + 1) s t - s * zetaPrimeFilterKernel p (N + 2) s t) / (t : ℂ))
      ((zetaPrimeFilterKernel p N s x - (2 * s + 1) * zetaPrimeFilterKernel p (N + 1) s x +
        s * (s + 1) * zetaPrimeFilterKernel p (N + 2) s x) / (x : ℂ) ^ 2) x := by
  have h1 := hasDerivAt_zetaPrimeFilterKernel p N s hx
  have h2 := hasDerivAt_zetaPrimeFilterKernel p (N + 1) s hx
  simp only [Nat.add_assoc, show 1 + 1 = 2 by rfl] at h2
  have h := (h1.sub (h2.const_mul s)).fun_div (hasDerivAt_id x).ofReal_comp
    (Complex.ofReal_ne_zero.mpr hx.ne')
  apply h.congr_deriv
  simp only [Complex.ofReal_one, mul_one, id_eq, Pi.sub_apply]
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']
  ring

/-- A unit second difference is controlled by a second derivative bound
on the full two-unit interval. The original signed difference is retained. -/
theorem norm_second_unit_difference_le {f g h : ℝ → ℂ} {a C : ℝ}
    (hf : ∀ x ∈ Set.Icc a (a + 2), HasDerivAt f (g x) x)
    (hg : ∀ x ∈ Set.Icc a (a + 2), HasDerivAt g (h x) x)
    (hb : ∀ x ∈ Set.Icc a (a + 2), ‖h x‖ ≤ C) :
    ‖f (a + 2) - 2 * f (a + 1) + f a‖ ≤ C := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc a (a + 1)) :
      HasDerivAt (fun t ↦ f (t + 1) - f t) (g (x + 1) - g x) x := by
    have hx0 : x ∈ Set.Icc a (a + 2) := ⟨hx.1, by linarith [hx.2]⟩
    have hx1 : x + 1 ∈ Set.Icc a (a + 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hp : HasDerivAt (fun t : ℝ ↦ f (t + 1)) (g (x + 1)) x := by
      simpa only [one_smul, Function.comp_def, id_eq] using
        (hf (x + 1) hx1).scomp x ((hasDerivAt_id x).add_const 1)
    convert! hp.sub (hf x hx0) using 1
  have hd_bound (x : ℝ) (hx : x ∈ Set.Ico a (a + 1)) : ‖g (x + 1) - g x‖ ≤ C := by
    have hi (t : ℝ) (ht : t ∈ Set.Icc x (x + 1)) : t ∈ Set.Icc a (a + 2) :=
      ⟨by linarith [hx.1, ht.1], by linarith [hx.2, ht.2]⟩
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht ↦ (hg t (hi t ht)).hasDerivWithinAt)
      (fun t ht ↦ hb t (hi t ⟨ht.1, ht.2.le⟩)) (x + 1) (by constructor <;> linarith)
    simpa only [add_sub_cancel_left, mul_one] using hh
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x hx ↦ (hd x hx).hasDerivWithinAt) hd_bound (a + 1) (by constructor <;> linarith)
  have he : (f (a + 1 + 1) - f (a + 1)) - (f (a + 1) - f a) =
      f (a + 2) - 2 * f (a + 1) + f a := by rw [show a + 1 + 1 = a + 2 by ring]; ring
  simpa only [he, add_sub_cancel_left, mul_one] using hh

/-- The complete fixed-filter allowance for two derivatives at real
part one quarter, including the ordinate-dependent complex coefficients. -/
def zetaQuarterKernelSecondConstant (p : Polynomial ℂ) (y : ℝ) : ℝ :=
  (∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) *
    (1 + ‖2 * (1 / 4 + I * (y : ℂ)) + 1‖ * (8 / 9 : ℝ) +
      ‖(1 / 4 + I * (y : ℂ)) * (1 / 4 + I * (y : ℂ) + 1)‖ * (8 / 9 : ℝ) ^ 2)

/-- The second-derivative allowance is nonnegative. -/
theorem zetaQuarterKernelSecondConstant_nonneg (p : Polynomial ℂ) (y : ℝ) :
    0 ≤ zetaQuarterKernelSecondConstant p y := by
  unfold zetaQuarterKernelSecondConstant
  exact mul_nonneg (Finset.sum_nonneg (fun _ _ ↦ by positivity)) (by positivity)

/-- Two derivatives give a summable spatial envelope and geometric
moment decay for the full quarter-line kernel. No arithmetic cancellation
or zero-free hypothesis enters this estimate. -/
theorem norm_zetaQuarterKernel_second_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖(zetaPrimeFilterKernel p N (1 / 4 + I * y) x -
      (2 * (1 / 4 + I * y) + 1) * zetaPrimeFilterKernel p (N + 1) (1 / 4 + I * y) x +
      (1 / 4 + I * y) * (1 / 4 + I * y + 1) *
        zetaPrimeFilterKernel p (N + 2) (1 / 4 + I * y) x) / (x : ℂ) ^ 2‖ ≤
      (8 / 9 : ℝ) ^ N * Real.exp (-(9 / 8 : ℝ) * Real.log x) *
        zetaQuarterKernelSecondConstant p y := by
  let s : ℂ := 1 / 4 + I * y
  have hx0 := zero_lt_one.trans_le hx
  have hb (n : ℕ) : ‖zetaPrimeFilterKernel p n s x / (x : ℂ) ^ 2‖ ≤
      (8 / 9 : ℝ) ^ n * Real.exp (-(9 / 8 : ℝ) * Real.log x) *
        ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k := by
    rw [zetaPrimeFilterKernel_div_pow p n 2 s hx0]
    have h := norm_zetaPrimeFilterKernel_le_tilt p n (s + 2) hx (by norm_num : (0 : ℝ) < 9 / 8)
    norm_num [s] at h ⊢
    exact h
  have he : (zetaPrimeFilterKernel p N s x - (2 * s + 1) * zetaPrimeFilterKernel p (N + 1) s x +
        s * (s + 1) * zetaPrimeFilterKernel p (N + 2) s x) / (x : ℂ) ^ 2 =
      zetaPrimeFilterKernel p N s x / (x : ℂ) ^ 2 -
        (2 * s + 1) * (zetaPrimeFilterKernel p (N + 1) s x / (x : ℂ) ^ 2) +
          s * (s + 1) * (zetaPrimeFilterKernel p (N + 2) s x / (x : ℂ) ^ 2) := by ring
  change ‖(zetaPrimeFilterKernel p N s x - _ + _) / (x : ℂ) ^ 2‖ ≤ _
  rw [he]
  apply ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans
  simp only [norm_mul]
  calc
    _ ≤ (8 / 9 : ℝ) ^ N * Real.exp (-(9 / 8 : ℝ) * Real.log x) *
          (∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) +
        ‖2 * s + 1‖ * ((8 / 9 : ℝ) ^ (N + 1) * Real.exp (-(9 / 8 : ℝ) * Real.log x) *
          ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) +
        (‖s‖ * ‖s + 1‖) * ((8 / 9 : ℝ) ^ (N + 2) * Real.exp (-(9 / 8 : ℝ) * Real.log x) *
          ∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) := by
      gcongr
      · exact hb N
      · exact hb (N + 1)
      · exact hb (N + 2)
    _ = _ := by
      simp only [zetaQuarterKernelSecondConstant, ← norm_mul, pow_add, pow_one]
      change _ = (8 / 9 : ℝ) ^ N * _ * ((∑ k ∈ p.support, ‖p.coeff k‖ * (8 / 9 : ℝ) ^ k) *
        (1 + ‖2 * s + 1‖ * (8 / 9 : ℝ) + ‖s * (s + 1)‖ * (8 / 9 : ℝ) ^ 2))
      ring

/-- The entire signed second difference has the same geometric moment
decay and summable spatial envelope, for every positive unit interval. -/
theorem norm_zetaQuarterKernel_second_difference_le (p : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {a : ℝ} (ha : 1 ≤ a) :
    ‖zetaPrimeFilterKernel p (N + 2) (1 / 4 + I * y) (a + 2) -
      2 * zetaPrimeFilterKernel p (N + 2) (1 / 4 + I * y) (a + 1) +
        zetaPrimeFilterKernel p (N + 2) (1 / 4 + I * y) a‖ ≤
      (8 / 9 : ℝ) ^ N * Real.exp (-(9 / 8 : ℝ) * Real.log a) *
        zetaQuarterKernelSecondConstant p y := by
  apply norm_second_unit_difference_le
    (g := fun x ↦ (zetaPrimeFilterKernel p (N + 1) (1 / 4 + I * y) x -
      (1 / 4 + I * y) * zetaPrimeFilterKernel p (N + 2) (1 / 4 + I * y) x) / (x : ℂ))
    (h := fun x ↦ (zetaPrimeFilterKernel p N (1 / 4 + I * y) x -
      (2 * (1 / 4 + I * y) + 1) * zetaPrimeFilterKernel p (N + 1) (1 / 4 + I * y) x +
      (1 / 4 + I * y) * (1 / 4 + I * y + 1) *
        zetaPrimeFilterKernel p (N + 2) (1 / 4 + I * y) x) / (x : ℂ) ^ 2)
  · intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    simpa only [Nat.add_assoc, show 1 + 1 = 2 by rfl] using
      hasDerivAt_zetaPrimeFilterKernel p (N + 1) (1 / 4 + I * y) hx0
  · intro x hx
    exact hasDerivAt_zetaPrimeKernel_lowering p N _ (by linarith [hx.1])
  · intro x hx
    apply (norm_zetaQuarterKernel_second_le p N y (ha.trans hx.1)).trans
    have hl := Real.log_le_log (zero_lt_one.trans_le ha) hx.1
    have he : Real.exp (-(9 / 8 : ℝ) * Real.log x) ≤ Real.exp (-(9 / 8 : ℝ) * Real.log a) :=
      Real.exp_le_exp.mpr (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity))
      (zetaQuarterKernelSecondConstant_nonneg p y)

end
end RiemannGaussian
