/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerBernoulli
import Mathlib.NumberTheory.ZetaValues
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The exact Fourier channels in the actual zeta Euler remainder

The quadratic Bernoulli kernel has an absolutely convergent Fourier
expansion. The zero frequency is absent. Integer cell shifts preserve
each original frequency, so the expansion can be summed across cells
without resetting or discarding their phases.
-/

namespace RiemannGaussian.ZetaEulerFourier
noncomputable section
open Complex Filter MeasureTheory Set Topology ZetaEulerBernoulli
open scoped Interval

/-- The exact nonnegative Bernoulli Fourier coefficient, with the zero
channel equal to zero under the field convention. -/
def weight (n : ℕ) : ℝ := (1 / (n : ℝ) ^ 2) / Real.pi ^ 2

/-- No constant Fourier mode survives the extracted Euler endpoints. -/
theorem weight_zero : weight 0 = 0 := by simp [weight]

/-- Every retained Fourier coefficient is nonnegative. -/
theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

/-- The full absolute Fourier coefficient mass is exactly one sixth. -/
theorem hasSum_weight : HasSum weight (1 / 6) := by
  have h := hasSum_zeta_two.div_const (Real.pi ^ 2)
  have he : (Real.pi ^ 2 / 6) / Real.pi ^ 2 = 1 / 6 := by field_simp
  rw [he] at h
  exact h

/-- The actual quadratic kernel is the complete absolutely convergent
cosine series on each unit cell. -/
theorem hasSum_kernel {a x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    HasSum (fun n : ℕ ↦ weight n * Real.cos (2 * Real.pi * n * (x - a))) (kernel a x) := by
  have h := hasSum_one_div_nat_pow_mul_cos (k := 1) (by omega)
    (show x - a ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hx.1, hx.2])
  change HasSum _ ((-1 : ℝ) ^ 2 * (2 * Real.pi) ^ 2 / 2 / (2 : ℕ).factorial *
    bernoulliFun 2 (x - a)) at h
  rw [bernoulliFun_two] at h
  convert! h.div_const (Real.pi ^ 2) using 1
  · funext n
    unfold weight
    norm_num
    ring
  · unfold kernel
    norm_num
    field_simp

/-- Shifting an original unit cell by its integer base preserves every
global Fourier phase exactly. -/
theorem cosine_cell_shift (n j : ℕ) (x : ℝ) :
    Real.cos (2 * Real.pi * n * (x - (j + 1))) = Real.cos (2 * Real.pi * n * x) := by
  have he : 2 * Real.pi * n * (x - (j + 1)) =
      2 * Real.pi * n * x - (n * (j + 1) : ℕ) * (2 * Real.pi) := by push_cast; ring
  rw [he, Real.cos_sub_nat_mul_two_pi]

/-- The same global frequencies reconstruct the original kernel on
every integer cell; their phases agree across all completion boundaries. -/
theorem hasSum_kernel_global (j : ℕ) {x : ℝ} (hx : x ∈ Icc (j + 1 : ℝ) (j + 2 : ℝ)) :
    HasSum (fun n : ℕ ↦ weight n * Real.cos (2 * Real.pi * n * x)) (kernel (j + 1) x) := by
  have h := hasSum_kernel (show x ∈ Icc (j + 1 : ℝ) ((j + 1 : ℝ) + 1) by
    simpa only [show (j + 1 : ℝ) + 1 = j + 2 by ring] using hx)
  simpa only [cosine_cell_shift] using h

/-- A single original Fourier channel with the full complex power
amplitude and its unshifted global phase. -/
def channel (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (weight n * Real.cos (2 * Real.pi * n * x) : ℝ) * (x : ℂ) ^ (-s - 2)

/-- Each Fourier channel has a summable coefficient envelope while
its complex phase remains available in the exact representation. -/
theorem norm_channel_le (s : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖channel s n x‖ ≤ weight n * x ^ (-s.re - 2) := by
  unfold channel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (weight_nonneg n), norm_cpow_eq_rpow_re_of_pos hx]
  change weight n * |Real.cos _| * x ^ (-s.re - 2) ≤ weight n * x ^ (-s.re - 2)
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (weight_nonneg n) (Real.abs_cos_le_one _))
    (Real.rpow_nonneg hx.le _)

/-- The full complex integrand in the genuine Bernoulli tail is
reconstructed by all its unshifted Fourier channels. -/
theorem hasSum_channel (s : ℂ) (j : ℕ) {x : ℝ}
    (hx : x ∈ Icc (j + 1 : ℝ) (j + 2 : ℝ)) :
    HasSum (fun n ↦ channel s n x) ((kernel (j + 1) x : ℂ) * (x : ℂ) ^ (-s - 2)) :=
  (Complex.hasSum_ofReal.mpr (hasSum_kernel_global j hx)).mul_right _

/-- Every original Fourier channel is genuinely integrable on any
positive compact interval. -/
theorem intervalIntegrable_channel (s : ℂ) (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (channel s n) volume a b := by
  apply ContinuousOn.intervalIntegrable
  unfold channel
  apply ContinuousOn.mul (by fun_prop)
  apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact ofReal_mem_slitPlane.mpr (ha.trans_le hx.1)

/-- Absolute domination justifies the infinite Fourier sum-integral
exchange for each actual Bernoulli cell. -/
theorem hasSum_block (s : ℂ) (j : ℕ) :
    HasSum (fun n ↦ ∫ x : ℝ in (j + 1 : ℝ)..(j + 2 : ℝ), channel s n x) (block s j) := by
  have hj : (j + 1 : ℝ) ≤ j + 2 := by linarith
  have hpos {x : ℝ} (hx : x ∈ Ι (j + 1 : ℝ) (j + 2 : ℝ)) : 0 < x := by
    rw [uIoc_of_le hj] at hx
    linarith [hx.1, Nat.cast_nonneg (α := ℝ) j]
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n x ↦ weight n * x ^ (-s.re - 2))
  · exact fun n ↦ (intervalIntegrable_channel s n (by positivity) hj).aestronglyMeasurable_restrict_uIoc
  · intro n
    exact Filter.Eventually.of_forall fun x hx ↦ norm_channel_le s n (hpos hx)
  · exact Filter.Eventually.of_forall fun x _ ↦ hasSum_weight.summable.mul_right _
  · simp_rw [tsum_mul_right, hasSum_weight.tsum_eq]
    apply IntervalIntegrable.const_mul
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    intro x hx
    rw [uIcc_of_le hj] at hx
    exact Or.inl (by linarith [hx.1, Nat.cast_nonneg (α := ℝ) j] : x ≠ 0)
  · apply Filter.Eventually.of_forall
    intro x hx
    rw [uIoc_of_le hj] at hx
    exact hasSum_channel s j ⟨hx.1.le, hx.2⟩

/-- Whole consecutive blocks have one complete Fourier expansion on
their combined interval. Cell boundaries cost nothing and every cross-cell
phase remains coupled inside the integral. -/
theorem hasSum_blocks (s : ℂ) (N M : ℕ) :
    HasSum (fun n ↦ ∫ x : ℝ in (N + 1 : ℝ)..(M + N + 1 : ℝ), channel s n x)
      (∑ j ∈ Finset.range M, block s (j + N)) := by
  have h := hasSum_sum (s := Finset.range M) (fun j _ ↦ hasSum_block s (j + N))
  apply h.congr_fun
  intro n
  have he := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ ↦ (j + N + 1 : ℝ)) (n := M)
    (fun j _ ↦ intervalIntegrable_channel s n (by positivity) (by push_cast; linarith))
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add,
    show ∀ j : ℝ, j + 1 + N + 1 = j + N + 2 by intro j; ring] using he.symm

end
end RiemannGaussian.ZetaEulerFourier
