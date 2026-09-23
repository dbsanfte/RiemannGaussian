/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerBernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Normalized Bernoulli kernels at every order

The normalized Bernoulli polynomial has derivative equal to the preceding
kernel. Its two endpoints agree from order two onward. These facts give
the exact complex integration-by-parts step used by the higher-order
Euler--Maclaurin evaluator; the coefficient norm gives a finite, rationally
computable bound separately from the signed identity.
-/

namespace RiemannGaussian.ZetaEulerMaclaurinKernel
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped Interval

/-- The literal Bernoulli polynomial divided by its factorial. -/
def polynomial (m : ℕ) : Polynomial ℝ :=
  Polynomial.C ((m.factorial : ℝ)⁻¹) *
    (Polynomial.bernoulli m).map (algebraMap ℚ ℝ)

/-- The normalized real Bernoulli kernel on a translated unit cell. -/
def kernel (m : ℕ) (a x : ℝ) : ℝ := (polynomial m).eval (x - a)

/-- The exact rational boundary coefficient at order `m`. -/
def boundary (m : ℕ) : ℝ := (bernoulli m : ℝ) / m.factorial

/-- A finite explicit coefficient allowance for the normalized polynomial. -/
def allowance (m : ℕ) : ℝ :=
  ∑ j ∈ (polynomial m).support, |(polynomial m).coeff j|

/-- The normalization removes the factor in the Bernoulli derivative. -/
theorem derivative_polynomial (m : ℕ) :
    (polynomial (m + 1)).derivative = polynomial m := by
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  simp only [polynomial, Polynomial.derivative_C_mul, Polynomial.derivative_map,
    Polynomial.derivative_bernoulli_add_one, Polynomial.map_mul, Polynomial.map_add,
    Polynomial.map_natCast, Polynomial.map_one, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc]
  congr 1
  rw [← Polynomial.C_1, ← Polynomial.C_eq_natCast, ← Polynomial.C_add,
    ← Polynomial.C_mul]
  congr 1
  field_simp

/-- The actual real kernel is a primitive of the preceding kernel. -/
theorem kernel_hasDerivAt (m : ℕ) (a x : ℝ) :
    HasDerivAt (kernel (m + 1) a) (kernel m a x) x := by
  have hh := ((polynomial (m + 1)).hasDerivAt (x - a)).comp x
    ((hasDerivAt_id x).sub_const a)
  convert! hh using 1
  simp only [derivative_polynomial, mul_one, kernel]

/-- The left endpoint is the exact Bernoulli number divided by its factorial. -/
theorem kernel_left (m : ℕ) (a : ℝ) : kernel m a a = boundary m := by
  simp only [kernel, sub_self, polynomial, Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (0 : ℝ) = algebraMap ℚ ℝ 0 by simp, Polynomial.eval_map_apply]
  simp [boundary, div_eq_mul_inv, mul_comm]

/-- The right endpoint agrees for all orders except the linear sawtooth. -/
theorem kernel_right {m : ℕ} (hm : m ≠ 1) (a : ℝ) :
    kernel m a (a + 1) = boundary m := by
  simp only [kernel, add_sub_cancel_left, polynomial, Polynomial.eval_mul, Polynomial.eval_C]
  rw [show (1 : ℝ) = algebraMap ℚ ℝ 1 by simp, Polynomial.eval_map_apply]
  simp [boundary, bernoulli_eq_bernoulli'_of_ne_one hm, div_eq_mul_inv, mul_comm]

/-- The finite coefficient allowance is nonnegative. -/
theorem allowance_nonneg (m : ℕ) : 0 ≤ allowance m :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The coefficient allowance is an explicitly bounded finite sum of
rational Bernoulli numbers, suitable for kernel-checked computation. -/
theorem allowance_eq (m : ℕ) :
    allowance m = ∑ j ∈ Finset.range (m + 1),
      |(bernoulli (m - j) : ℝ) * m.choose j| / m.factorial := by
  have hc (j : ℕ) : (polynomial m).coeff j =
      if j ≤ m then (bernoulli (m - j) : ℝ) * m.choose j / m.factorial else 0 := by
    by_cases hj : j ≤ m <;>
      simp [polynomial, Polynomial.coeff_bernoulli, hj, div_eq_mul_inv, mul_comm]
  have hsub : (polynomial m).support ⊆ Finset.range (m + 1) := by
    intro j hj
    have hh := Polynomial.mem_support_iff.mp hj
    rw [hc] at hh
    by_contra hn
    have hj' : ¬j ≤ m := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn
    simp [hj'] at hh
  unfold allowance
  rw [Finset.sum_subset hsub (by
    intro j _ hj
    rw [not_iff_not.mpr Polynomial.mem_support_iff] at hj
    simp only [not_ne_iff] at hj
    simp [hj])]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hc, if_pos (by simpa using hj), abs_div]
  simp only [abs_of_nonneg (Nat.cast_nonneg m.factorial : (0 : ℝ) ≤ m.factorial)]

/-- A checked polynomial bound on the actual closed unit cell. -/
theorem abs_kernel_le (m : ℕ) {a x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    |kernel m a x| ≤ allowance m := by
  rw [kernel, Polynomial.eval_eq_sum, Polynomial.sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_pow, abs_of_nonneg (sub_nonneg.mpr hx.1)]
  have hh : (x - a) ^ j ≤ 1 := pow_le_one₀ (by linarith [hx.1]) (by linarith [hx.2])
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (abs_nonneg _)

/-- A normalized signed Bernoulli integral over one original Euler cell. -/
def block (m : ℕ) (s : ℂ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ),
    (kernel m (n + 1) x : ℂ) * (x : ℂ) ^ (-s - m)

private theorem cell_pos {n : ℕ} {x : ℝ}
    (hx : x ∈ [[(n + 1 : ℝ), (n + 2 : ℝ)]]) : 0 < x := by
  rw [uIcc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)] at hx
  linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]

private theorem power_deriv (r : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ r) (r * (x : ℂ) ^ (r - 1)) x := by
  by_cases hr : r = 0
  · subst r
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hr

private theorem continuous_kernel (m : ℕ) (a : ℝ) : Continuous (kernel m a) := by
  unfold kernel
  fun_prop

/-- Every signed normalized cell is a genuine integrable expression. -/
theorem block_integrable (m : ℕ) (s : ℂ) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦
      (kernel m (n + 1) x : ℂ) * (x : ℂ) ^ (-s - m))
        volume (n + 1 : ℝ) (n + 2 : ℝ) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul ((continuous_ofReal.comp (continuous_kernel m _)).continuousOn)
  apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
  exact fun _ hx ↦ Complex.ofReal_mem_slitPlane.mpr (cell_pos hx)

/-- One exact integration by parts, with both endpoints and the signed
next-order integral retained. -/
theorem block_step {m : ℕ} (hm : 1 ≤ m) (s : ℂ) (n : ℕ) :
    block m s n = (boundary (m + 1) : ℂ) *
      ((n + 2 : ℂ) ^ (-s - m) - (n + 1 : ℂ) ^ (-s - m)) +
        (s + m) * block (m + 1) s n := by
  have hd (x : ℝ) := (kernel_hasDerivAt m (n + 1) x).ofReal_comp
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ hd x) (fun x hx ↦ power_deriv (-s - m) (cell_pos hx))
    ((continuous_ofReal.comp (continuous_kernel m _)).intervalIntegrable _ _)
    (by simpa only [show -(s + (m : ℂ) + 1) = -s - m - 1 by ring] using
      ((ZetaEulerCell.intervalIntegrable_power (s + m + 1) n).const_mul (-s - m)))
  have hright : (n + 2 : ℝ) = (n + 1 : ℝ) + 1 := by ring
  rw [hright, kernel_right (by omega), kernel_left] at hi
  simp only [← hright, show -s - (m : ℂ) - 1 = -(s + m + 1) by ring] at hi
  simp_rw [show ∀ x : ℝ,
    (kernel (m + 1) (n + 1) x : ℂ) * ((-s - m) * (x : ℂ) ^ (-(s + m + 1))) =
      (-s - m) * ((kernel (m + 1) (n + 1) x : ℂ) *
        (x : ℂ) ^ (-s - (m + 1 : ℕ))) by intro x; push_cast; ring_nf] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_ofNat] at hi
  unfold block
  linear_combination hi

/-- The arbitrary-order cell has a telescoping power envelope. -/
theorem norm_block_le {m : ℕ} (hm : 2 ≤ m) {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖block m s n‖ ≤ allowance m *
      ((n + 1 : ℝ) ^ (-s.re - m + 1) - (n + 2 : ℝ) ^ (-s.re - m + 1)) /
        (s.re + m - 1) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hi : IntervalIntegrable (fun x : ℝ ↦ x ^ (-s.re - m))
      volume (n + 1 : ℝ) (n + 2 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    exact fun _ hx ↦ Or.inl (cell_pos hx).ne'
  have hb : ‖block m s n‖ ≤ allowance m *
      ∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ), x ^ (-s.re - m) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · apply Filter.Eventually.of_forall
      intro x hx
      have hxp : 0 < x := by linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hxp]
      simp only [sub_re, neg_re, natCast_re]
      exact mul_le_mul_of_nonneg_right
        (abs_kernel_le m ⟨hx.1.le, by linarith [hx.2]⟩) (Real.rpow_nonneg hxp.le _)
    · exact hi.const_mul _
  rw [integral_rpow (Or.inr ⟨by linarith,
    fun hx ↦ (cell_pos hx).ne' rfl⟩)] at hb
  convert! hb using 1
  field_simp [show s.re + m - 1 ≠ 0 by linarith,
    show -s.re - m + 1 ≠ 0 by linarith]
  ring

/-- Finite absolute cell sums retain the exact terminal power subtraction. -/
theorem sum_norm_block_le {m : ℕ} (hm : 2 ≤ m) {s : ℂ} (hs : 0 < s.re)
    (N M : ℕ) :
    (∑ n ∈ Finset.range M, ‖block m s (n + N)‖) ≤ allowance m *
      ((N + 1 : ℝ) ^ (-s.re - m + 1) - (M + N + 1 : ℝ) ^ (-s.re - m + 1)) /
        (s.re + m - 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hb := norm_block_le hm hs (M + N)
    simp only [Nat.cast_add, Nat.cast_one] at hb ⊢
    apply (add_le_add ih hb).trans_eq
    rw [show (M : ℝ) + 1 + N + 1 = M + N + 2 by ring]
    ring

/-- The complete signed higher-order tail, with no phase removed. -/
def tail (m N : ℕ) (s : ℂ) : ℂ := ∑' n, block m s (n + N)

/-- The full higher-order cell series converges absolutely. -/
theorem summable_block {m : ℕ} (hm : 2 ≤ m) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Summable (fun n ↦ block m s (n + N)) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  apply Summable.of_norm
  apply summable_of_sum_range_le (fun _ ↦ norm_nonneg _)
    (c := allowance m * (N + 1 : ℝ) ^ (-s.re - m + 1) / (s.re + m - 1))
  intro M
  apply (sum_norm_block_le hm hs N M).trans
  apply div_le_div_of_nonneg_right _ (by linarith)
  exact mul_le_mul_of_nonneg_left
    (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) (allowance_nonneg m)

/-- A finite computable coefficient controls the entire signed remainder. -/
theorem norm_tail_le {m : ℕ} (hm : 2 ≤ m) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖tail m N s‖ ≤ allowance m * (N + 1 : ℝ) ^ (-s.re - m + 1) /
      (s.re + m - 1) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  apply (norm_tsum_le_tsum_norm (summable_block hm hs N).norm).trans
  apply Real.tsum_le_of_sum_range_le (fun _ ↦ norm_nonneg _)
  intro M
  apply (sum_norm_block_le hm hs N M).trans
  apply div_le_div_of_nonneg_right _ (by linarith)
  exact mul_le_mul_of_nonneg_left
    (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) (allowance_nonneg m)

/-- The new quadratic normalization agrees with the existing zeta expansion. -/
theorem kernel_two (a x : ℝ) : kernel 2 a x = ZetaEulerBernoulli.kernel a x / 2 := by
  norm_num [kernel, polynomial, Polynomial.bernoulli, Finset.sum_range_succ,
    bernoulli, ZetaEulerBernoulli.kernel]
  ring

/-- The quadratic tail is the old signed tail divided by two. -/
theorem tail_two (N : ℕ) (s : ℂ) : tail 2 N s = ZetaEulerBernoulli.tail N s / 2 := by
  simp only [tail, block, kernel_two, ZetaEulerBernoulli.tail, ZetaEulerBernoulli.block]
  simp_rw [Complex.ofReal_div, Complex.ofReal_ofNat, Nat.cast_ofNat, div_mul_eq_mul_div,
    intervalIntegral.integral_div, tsum_div_const]

end
end RiemannGaussian.ZetaEulerMaclaurinKernel
