/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerTruncation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The signed second Bernoulli remainder of actual zeta

Two integrations by parts extract the half endpoint and the first Euler
derivative correction from every original Euler cell. The remaining
quadratic kernel has zero mean. Its phase is retained in the exact complex
identity, separately from the elementary absolute convergence estimate.
-/

namespace RiemannGaussian.ZetaEulerBernoulli
noncomputable section
open Complex Filter MeasureTheory Set Topology ZetaEulerCell ZetaEulerTruncation
open scoped Interval

/-- The second Bernoulli polynomial on the unit cell based at `a`. -/
def kernel (a x : ℝ) : ℝ := (x - a) ^ 2 - (x - a) + 1 / 6

/-- The signed complex quadratic remainder on one original unit cell. -/
def block (s : ℂ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ),
    (kernel (n + 1) x : ℂ) * (x : ℂ) ^ (-s - 2)

/-- The complete signed Bernoulli tail at an arbitrary integer cutoff. -/
def tail (N : ℕ) (s : ℂ) : ℂ := ∑' n, block s (n + N)

private theorem power_deriv (r : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ r) (r * (x : ℂ) ^ (r - 1)) x := by
  by_cases hr : r = 0
  · subst r
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hr

private theorem power_integrable (r : ℂ) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ (x : ℂ) ^ r) volume (n + 1 : ℝ) (n + 2 : ℝ) := by
  simpa only [neg_neg] using intervalIntegrable_power (-r) n

private theorem linear_deriv (a x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ ((y - a - 1 / 2 : ℝ) : ℂ)) 1 x := by
  simpa using (((hasDerivAt_id x).sub_const a).sub_const (1 / 2)).ofReal_comp

private theorem kernel_deriv (a x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (kernel a y : ℂ))
      (2 * ((x - a - 1 / 2 : ℝ) : ℂ)) x := by
  have h := (((((hasDerivAt_id x).sub_const a).pow 2).sub
    ((hasDerivAt_id x).sub_const a)).add_const (1 / 6)).ofReal_comp
  convert h using 1
  · rfl
  dsimp
  push_cast
  ring

/-- The exact original Euler cell retains both endpoint corrections
and the signed quadratic Bernoulli integral. -/
theorem cell_eq (s : ℂ) (n : ℕ) :
    cell s n = ((n + 1 : ℂ) ^ (-s) - (n + 2 : ℂ) ^ (-s)) / 2 +
      s / 12 * ((n + 1 : ℂ) ^ (-s - 1) - (n + 2 : ℂ) ^ (-s - 1)) -
      s * (s + 1) / 2 * block s n := by
  have hpos {x : ℝ} (hx : x ∈ [[(n + 1 : ℝ), (n + 2 : ℝ)]]) : 0 < x := by
    rw [uIcc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)] at hx
    linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ linear_deriv (n + 1) x)
    (fun x hx ↦ power_deriv (-s) (hpos hx))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℂ))
      volume (n + 1 : ℝ) (n + 2 : ℝ))
    ((power_integrable (-s - 1) n).const_mul (-s))
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ kernel_deriv (n + 1) x)
    (fun x hx ↦ power_deriv (-s - 1) (hpos hx))
    (show IntervalIntegrable (fun x : ℝ ↦ 2 * ((x - (n + 1) - 1 / 2 : ℝ) : ℂ))
      volume (n + 1 : ℝ) (n + 2 : ℝ) from (by fun_prop : Continuous _).intervalIntegrable _ _)
    ((power_integrable (-s - 1 - 1) n).const_mul (-s - 1))
  simp only [one_mul] at h1
  simp only [show -s - 1 - 1 = -s - 2 by ring] at h2
  simp_rw [show ∀ x : ℝ,
    ((x - (n + 1) - 1 / 2 : ℝ) : ℂ) * (-s * (x : ℂ) ^ (-s - 1)) =
      -s * (((x - (n + 1) - 1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) by intro x; ring] at h1
  simp_rw [show ∀ x : ℝ,
    (kernel (n + 1) x : ℂ) * ((-s - 1) * (x : ℂ) ^ (-s - 2)) =
      (-s - 1) * ((kernel (n + 1) x : ℂ) * (x : ℂ) ^ (-s - 2)) by intro x; ring,
    mul_assoc] at h2
  rw [intervalIntegral.integral_const_mul] at h1
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h2
  simp only [kernel, show (n + 2 : ℝ) - (n + 1) = 1 by ring,
    show (n + 1 : ℝ) - (n + 1) = 0 by ring] at h1 h2
  unfold cell block kernel
  push_cast at h1 h2 ⊢
  linear_combination -h1 - s / 2 * h2

/-- The retained quadratic kernel is uniformly small on its actual
unit cell; this estimate is downstream from the signed identity. -/
theorem abs_kernel_le {a x : ℝ} (hx : x ∈ Icc a (a + 1)) :
    |kernel a x| ≤ 1 / 6 := by
  unfold kernel
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg (x - a - 1 / 2)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)]

/-- The quadratic cell has a telescoping integrable envelope. -/
theorem norm_block_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖block s n‖ ≤
      ((n + 1 : ℝ) ^ (-s.re - 1) - (n + 2 : ℝ) ^ (-s.re - 1)) /
        (6 * (s.re + 1)) := by
  have hpos {x : ℝ} (hx : x ∈ [[(n + 1 : ℝ), (n + 2 : ℝ)]]) : 0 < x := by
    rw [uIcc_of_le (by linarith : (n + 1 : ℝ) ≤ n + 2)] at hx
    linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]
  have hi : IntervalIntegrable (fun x : ℝ ↦ x ^ (-s.re - 2))
      volume (n + 1 : ℝ) (n + 2 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.rpow_const
    exact fun x hx ↦ Or.inl (hpos hx).ne'
  have hb : ‖block s n‖ ≤ (1 / 6) *
      ∫ x : ℝ in (n + 1 : ℝ)..(n + 2 : ℝ), x ^ (-s.re - 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · apply Filter.Eventually.of_forall
      intro x hx
      have hxp : 0 < x := by linarith [hx.1, Nat.cast_nonneg (α := ℝ) n]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_cpow_eq_rpow_re_of_pos hxp]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxp.le _)
      exact abs_kernel_le ⟨hx.1.le, by linarith [hx.2]⟩
    · exact hi.const_mul (1 / 6)
  rw [integral_rpow (Or.inr ⟨by linarith,
    fun hx ↦ (hpos hx).ne' rfl⟩)] at hb
  rw [show -s.re - 2 + 1 = -s.re - 1 by ring] at hb
  convert hb using 1
  field_simp [show s.re + 1 ≠ 0 by linarith, show -s.re - 1 ≠ 0 by linarith]
  ring

/-- Every finite sum of the absolute quadratic cells is bounded by
the exact endpoint power difference. -/
theorem sum_norm_block_le {s : ℂ} (hs : 0 < s.re) (N M : ℕ) :
    (∑ n ∈ Finset.range M, ‖block s (n + N)‖) ≤
      ((N + 1 : ℝ) ^ (-s.re - 1) - (M + N + 1 : ℝ) ^ (-s.re - 1)) /
        (6 * (s.re + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hb := norm_block_le hs (M + N)
    simp only [Nat.cast_add, Nat.cast_one] at hb ⊢
    apply (add_le_add ih hb).trans_eq
    rw [show (M : ℝ) + 1 + N + 1 = M + N + 2 by ring]
    ring

/-- The full signed Bernoulli tail converges absolutely for every
positive real part, at every original cutoff. -/
theorem summable_block {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Summable (fun n ↦ block s (n + N)) := by
  apply Summable.of_norm
  apply summable_of_sum_range_le (fun _ ↦ norm_nonneg _)
  intro M
  exact (sum_norm_block_le hs N M).trans
    (div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (by positivity) _))
      (by positivity))

/-- Finite original Euler tails telescope with both complex boundary
corrections and every signed Bernoulli cell retained. -/
theorem sum_cell_eq (s : ℂ) (N M : ℕ) :
    (∑ n ∈ Finset.range M, cell s (n + N)) =
      ((N + 1 : ℂ) ^ (-s) - (M + N + 1 : ℂ) ^ (-s)) / 2 +
      s / 12 * ((N + 1 : ℂ) ^ (-s - 1) - (M + N + 1 : ℂ) ^ (-s - 1)) -
      s * (s + 1) / 2 * ∑ n ∈ Finset.range M, block s (n + N) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, cell_eq]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (M : ℂ) + 1 + N + 1 = M + N + 2 by ring]
    ring

private theorem endpoint_zero {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Tendsto (fun M : ℕ ↦ (M + N + 1 : ℂ) ^ (-s)) atTop (𝓝 0) := by
  have h := (ZetaEulerContinuation.endpoint_tendsto_zero (s := s + 1)
    (by simpa using hs)).comp (tendsto_add_atTop_nat N)
  change Tendsto (fun M : ℕ ↦ ((M + N : ℕ) + 1 : ℂ) ^ (1 - (s + 1))) atTop (𝓝 0) at h
  simpa only [Nat.cast_add, show 1 - (s + 1) = -s by ring] using h

/-- The actual full Euler remainder equals its two genuine complex
endpoint corrections minus the complete signed Bernoulli tail. -/
theorem remainder_eq {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    remainder N s = (N + 1 : ℂ) ^ (-s) / 2 +
      s / 12 * (N + 1 : ℂ) ^ (-s - 1) - s * (s + 1) / 2 * tail N s := by
  have he := (summable_remainder hs N).tendsto_sum_tsum_nat
  simp_rw [sum_cell_eq] at he
  have h0 := endpoint_zero hs N
  have h1 : Tendsto (fun M : ℕ ↦ (M + N + 1 : ℂ) ^ (-s - 1)) atTop (𝓝 0) := by
    simpa only [neg_add_rev, neg_add, sub_eq_add_neg, add_comm] using
      (endpoint_zero (s := s + 1) (by simpa using hs.trans (lt_add_one s.re)) N)
  have ht := ((((tendsto_const_nhds (x := (N + 1 : ℂ) ^ (-s))).sub h0).div_const 2).add
    (((tendsto_const_nhds (x := (N + 1 : ℂ) ^ (-s - 1))).sub h1).const_mul (s / 12))).sub
      (((summable_block hs N).tendsto_sum_tsum_nat).const_mul (s * (s + 1) / 2))
  simpa only [sub_zero, remainder, tail] using tendsto_nhds_unique he ht

/-- Actual zeta has the direct Euler--Maclaurin expansion at every
integer cutoff in the positive half-plane away from its pole. No phase,
endpoint, or remainder is replaced by an estimate in this identity. -/
theorem zeta_eq {s : ℂ} (hs : 0 < s.re) (hsne : s ≠ 1) (N : ℕ) :
    riemannZeta s = partialSum N s + (N + 1 : ℂ) ^ (1 - s) / (s - 1) +
      (N + 1 : ℂ) ^ (-s) / 2 + s / 12 * (N + 1 : ℂ) ^ (-s - 1) -
      s * (s + 1) / 2 * tail N s := by
  rw [zeta_eq_partialSum_add_endpoint_add_remainder hs hsne N, remainder_eq hs]
  ring

/-- Absolute convergence supplies a coarse envelope for the signed
tail; the oscillatory improvement must use its richer integral identity. -/
theorem norm_tail_le {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖tail N s‖ ≤ (N + 1 : ℝ) ^ (-s.re - 1) / (6 * (s.re + 1)) := by
  apply (norm_tsum_le_tsum_norm (summable_block hs N).norm).trans
  apply Real.tsum_le_of_sum_range_le (fun _ ↦ norm_nonneg _)
  intro M
  exact (sum_norm_block_le hs N M).trans
    (div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg (by positivity) _))
      (by positivity))

end
end RiemannGaussian.ZetaEulerBernoulli
