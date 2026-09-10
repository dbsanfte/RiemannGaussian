/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapEulerBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The centered Euler remainder of the actual eta function

The first Euler second difference has a nonzero mean. Extracting that mean
before estimating the remainder retains the next complex endpoint term
`s/4`. The remaining triangular kernel takes values in `[-1/2,1/2]`.
This module preserves the exact complex kernel and bounds its full series
throughout the positive half-plane.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped Classical Interval

private theorem cpow_intervalIntegrable (r : ℂ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact Complex.ofReal_mem_slitPlane.mpr (ha.trans_le hx.1)

private theorem cpow_hasDerivAt (r : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ r)
      (r * (x : ℂ) ^ (r - 1)) x := by
  by_cases hr : r = 0
  · subst r
    simpa using hasDerivAt_const x (1 : ℂ)
  · exact hasDerivAt_ofReal_cpow_const hx.ne' hr

/-- The signed, centered triangular block underlying Euler acceleration.
The two unit intervals keep their opposite orientations. -/
def pairedEtaCenteredEulerBlock (s : ℂ) (x : ℝ) : ℂ :=
  (∫ u : ℝ in x..x + 1,
    ((u - x - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)) -
  ∫ u : ℝ in x + 1..x + 2,
    ((u - (x + 1) - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)

private theorem centered_cpow_integral (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (s + 1) * (∫ u : ℝ in x..x + 1,
      ((u - x - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)) =
    (∫ u : ℝ in x..x + 1, (u : ℂ) ^ (-s - 1)) -
      ((x : ℂ) ^ (-s - 1) + ((x + 1 : ℝ) : ℂ) ^ (-s - 1)) / 2 := by
  have hlin (u : ℝ) :
      HasDerivAt (fun v : ℝ => ((v - x - 1 / 2 : ℝ) : ℂ)) 1 u := by
    simpa using
      (((hasDerivAt_id u).sub_const x).sub_const (1 / 2)).ofReal_comp
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun u _ => hlin u)
    (fun u hu => cpow_hasDerivAt (-s - 1)
      (show 0 < u by rw [uIcc_of_le (by linarith : x ≤ x + 1)] at hu; linarith [hu.1]))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume x (x + 1))
    ((cpow_intervalIntegrable (-s - 1 - 1) hx (by linarith)).const_mul (-s - 1))
  simp only [one_mul] at h
  have he : -s - 1 - 1 = -s - 2 := by ring
  simp only [he] at h
  simp only [show x + 1 - x - 1 / 2 = (1 / 2 : ℝ) by ring,
    show x - x - 1 / 2 = (-1 / 2 : ℝ) by ring] at h
  simp_rw [show ∀ u : ℝ,
      ((u - x - 1 / 2 : ℝ) : ℂ) * ((-s - 1) * (u : ℂ) ^ (-s - 2)) =
      (-s - 1) * (((u - x - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)) by
        intro u; ring] at h
  rw [intervalIntegral.integral_const_mul] at h
  push_cast at h ⊢
  linear_combination -h

/-- The exact second difference consists of the telescoping derivative
mean and the signed centered triangular remainder. -/
theorem cpow_secondDiff_eq_centered_euler (s : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-s) - 2 * ((x + 1 : ℝ) : ℂ) ^ (-s) +
        ((x + 2 : ℝ) : ℂ) ^ (-s) =
      s / 2 * ((x : ℂ) ^ (-s - 1) - ((x + 2 : ℝ) : ℂ) ^ (-s - 1)) +
        s * (s + 1) * pairedEtaCenteredEulerBlock s x := by
  have h1 := cpow_sub_add_one_eq_mul_integral s hx
  have h2 := cpow_sub_add_one_eq_mul_integral s (show 0 < x + 1 by linarith)
  have h3 := centered_cpow_integral s hx
  have h4 := centered_cpow_integral s (show 0 < x + 1 by linarith)
  rw [show x + 1 + 1 = x + 2 by ring] at h2 h4
  unfold pairedEtaCenteredEulerBlock
  linear_combination h1 - h2 - s * h3 + s * h4

private theorem rpow_intervalIntegrable (r : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => x ^ r) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_id.rpow_const
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact Or.inl (ne_of_gt (ha.trans_le hx.1))

private theorem norm_centered_cpow_integral_le (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖∫ u : ℝ in x..x + 1,
      ((u - x - 1 / 2 : ℝ) : ℂ) * (u : ℂ) ^ (-s - 2)‖ ≤
      (1 / 2) * ∫ u : ℝ in x..x + 1, u ^ (-s.re - 2) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
  · apply Filter.Eventually.of_forall
    intro u hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans hu.1)]
    change |u - x - 1 / 2| * u ^ (-s.re - 2) ≤ (1 / 2) * u ^ (-s.re - 2)
    exact mul_le_mul_of_nonneg_right
      (abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩)
      (Real.rpow_nonneg (hx.trans hu.1).le _)
  · exact (rpow_intervalIntegrable (-s.re - 2) hx (by linarith)).const_mul (1 / 2)

/-- Centering the triangular kernel halves its uniform size; its complex
phase is retained in the preceding identity. -/
theorem norm_pairedEtaCenteredEulerBlock_le_integral
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖pairedEtaCenteredEulerBlock s x‖ ≤
      (1 / 2) * ∫ u : ℝ in x..x + 2, u ^ (-s.re - 2) := by
  have h1 := norm_centered_cpow_integral_le s hx
  have h2 := norm_centered_cpow_integral_le s (show 0 < x + 1 by linarith)
  rw [show x + 1 + 1 = x + 2 by ring] at h2
  calc
    ‖pairedEtaCenteredEulerBlock s x‖ ≤ _ := norm_sub_le _ _
    _ ≤ (1 / 2) * (∫ u : ℝ in x..x + 1, u ^ (-s.re - 2)) +
        (1 / 2) * ∫ u : ℝ in x + 1..x + 2, u ^ (-s.re - 2) := add_le_add h1 h2
    _ = (1 / 2) * ∫ u : ℝ in x..x + 2, u ^ (-s.re - 2) := by
      rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals
        (rpow_intervalIntegrable _ hx (by linarith))
        (rpow_intervalIntegrable _ (by linarith) (by linarith))]

/-- Each centered block is controlled by an exact telescoping real power,
with the integrability denominator `Re(s)+1` preserved. -/
theorem norm_pairedEtaCenteredEulerBlock_le_power
    {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    ‖pairedEtaCenteredEulerBlock s x‖ ≤
      (x ^ (-s.re - 1) - (x + 2) ^ (-s.re - 1)) / (2 * (s.re + 1)) := by
  have h := norm_pairedEtaCenteredEulerBlock_le_integral s hx
  rw [integral_rpow (Or.inr ⟨by linarith,
    by rw [uIcc_of_le (by linarith : x ≤ x + 2)]; simp only [mem_Icc, not_and];
       intro h; linarith⟩)] at h
  have he : -s.re - 2 + 1 = -s.re - 1 := by ring
  rw [he] at h
  convert h using 1
  field_simp [show s.re + 1 ≠ 0 by linarith, show -s.re - 1 ≠ 0 by linarith]
  ring

/-- The exact finite eta expansion retains both complex endpoint powers
and the entire signed remainder before any norm is taken. -/
theorem pairedEtaCorePartialSum_eq_centered_euler (N : ℕ) (s : ℂ) :
    pairedEtaCorePartialSum N s =
      (1 - (((2 * N + 1 : ℕ) : ℂ) ^ (-s))) / 2 +
      s / 4 * (1 - (((2 * N + 1 : ℕ) : ℂ) ^ (-s - 1))) +
      s * (s + 1) / 2 *
        ∑ n ∈ Finset.range N, pairedEtaCenteredEulerBlock s ((2 * n + 1 : ℕ) : ℝ) := by
  induction N with
  | zero => simp [pairedEtaCorePartialSum]
  | succ N ih =>
    have h := cpow_secondDiff_eq_centered_euler s
      (x := ((2 * N + 1 : ℕ) : ℝ)) (by positivity)
    have hn : 2 * (N + 1) + 1 = (2 * N + 1) + 2 := by omega
    have hn1 : 2 * N + 2 = (2 * N + 1) + 1 := by omega
    simp only [pairedEtaCorePartialSum, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    simp only [pairedEtaCoreSummand, hn, hn1]
    push_cast at h ⊢
    linear_combination h / 2

/-- The sum of the absolute centered block remainders telescopes, at every
finite cutoff, to a bounded integral over the whole retained range. -/
theorem sum_norm_pairedEtaCenteredEulerBlock_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖pairedEtaCenteredEulerBlock s ((2 * n + 1 : ℕ) : ℝ)‖) ≤
      (1 - (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re - 1))) / (2 * (s.re + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h := norm_pairedEtaCenteredEulerBlock_le_power hs
      (x := ((2 * N + 1 : ℕ) : ℝ)) (by positivity)
    rw [Finset.sum_range_succ]
    have hn : 2 * (N + 1) + 1 = (2 * N + 1) + 2 := by omega
    rw [hn]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at ih h ⊢
    calc
      _ ≤ _ := add_le_add ih h
      _ = _ := by ring

private theorem sum_norm_centered_block_le_const {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    (∑ n ∈ Finset.range N, ‖pairedEtaCenteredEulerBlock s ((2 * n + 1 : ℕ) : ℝ)‖) ≤
      1 / (2 * (s.re + 1)) := by
  apply (sum_norm_pairedEtaCenteredEulerBlock_le hs N).trans
  exact div_le_div_of_nonneg_right
    (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) (by positivity)

/-- The full signed centered remainder is absolutely convergent on the
positive half-plane, independently of any zero hypothesis. -/
theorem summable_pairedEtaCenteredEulerBlock {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => pairedEtaCenteredEulerBlock s ((2 * n + 1 : ℕ) : ℝ)) := by
  apply Summable.of_norm
  exact summable_of_sum_range_le (fun _ => norm_nonneg _)
    (sum_norm_centered_block_le_const hs)

/-- The entire absolute centered remainder has a uniform explicit mass. -/
theorem tsum_norm_pairedEtaCenteredEulerBlock_le {s : ℂ} (hs : 0 < s.re) :
    (∑' n : ℕ, ‖pairedEtaCenteredEulerBlock s ((2 * n + 1 : ℕ) : ℝ)‖) ≤
      1 / (2 * (s.re + 1)) :=
  Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
    (sum_norm_centered_block_le_const hs)

private theorem tendsto_endpoint_cpow_zero {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℂ) ^ (-s)) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  convert tendsto_pairedEtaOddEndpoint_rpow_zero hs using 1
  funext N
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  rfl

/-- The actual infinite eta function, with its complex first Euler
correction extracted and its signed, absolutely convergent remainder intact. -/
theorem pairedEtaCore_eq_centered_euler {s : ℂ} (hs : 0 < s.re) :
    pairedEtaCore s = 1 / 2 + s / 4 + s * (s + 1) / 2 *
      ∑' n : ℕ, pairedEtaCenteredEulerBlock s ((2 * n + 1 : ℕ) : ℝ) := by
  have h0 := tendsto_endpoint_cpow_zero hs
  have h1 : Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℂ) ^ (-s - 1))
      atTop (nhds 0) := by
    simpa only [neg_add_rev, neg_add, neg_one_mul, sub_eq_add_neg, add_comm] using
      (tendsto_endpoint_cpow_zero (s := s + 1) (by simpa using hs.trans (lt_add_one s.re)))
  have he := (summable_pairedEtaCoreSummand hs).tendsto_sum_tsum_nat
  change Tendsto (fun N => pairedEtaCorePartialSum N s) atTop (nhds (pairedEtaCore s)) at he
  simp_rw [pairedEtaCorePartialSum_eq_centered_euler] at he
  have hr := (summable_pairedEtaCenteredEulerBlock hs).tendsto_sum_tsum_nat
  have ht := ((((tendsto_const_nhds (x := (1 : ℂ))).sub h0).div_const 2).add
    (((tendsto_const_nhds (x := (1 : ℂ))).sub h1).const_mul (s / 4))).add
      (hr.const_mul (s * (s + 1) / 2))
  simpa using tendsto_nhds_unique he ht

/-- An explicit analytic error bound after retaining the Euler term `s/4`.
It holds for every complex argument of positive real part. -/
theorem norm_pairedEtaCore_sub_centered_euler_le {s : ℂ} (hs : 0 < s.re) :
    ‖pairedEtaCore s - (1 / 2 + s / 4)‖ ≤
      ‖s‖ * ‖s + 1‖ / (4 * (s.re + 1)) := by
  rw [pairedEtaCore_eq_centered_euler hs, add_sub_cancel_left, norm_mul]
  have h := (norm_tsum_le_tsum_norm (summable_pairedEtaCenteredEulerBlock hs).norm).trans
    (tsum_norm_pairedEtaCenteredEulerBlock_le hs)
  calc
    _ ≤ ‖s * (s + 1) / 2‖ * (1 / (2 * (s.re + 1))) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by rw [norm_div, norm_mul]; norm_num; field_simp; ring

/-- The absolute centered remainder beyond any cutoff keeps the exact
endpoint decay and the integrability denominator. -/
theorem tsum_norm_pairedEtaCenteredEulerBlock_tail_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    (∑' n : ℕ, ‖pairedEtaCenteredEulerBlock s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
      (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re - 1)) / (2 * (s.re + 1)) := by
  have hfinite (M : ℕ) :
      (∑ n ∈ Finset.range M,
        ‖pairedEtaCenteredEulerBlock s ((2 * (n + N) + 1 : ℕ) : ℝ)‖) ≤
        ((((2 * N + 1 : ℕ) : ℝ) ^ (-s.re - 1)) -
          (((2 * (M + N) + 1 : ℕ) : ℝ) ^ (-s.re - 1))) / (2 * (s.re + 1)) := by
    induction M with
    | zero => simp
    | succ M ih =>
      have h := norm_pairedEtaCenteredEulerBlock_le_power hs
        (x := ((2 * (M + N) + 1 : ℕ) : ℝ)) (by positivity)
      rw [Finset.sum_range_succ]
      have hn : 2 * (M + 1 + N) + 1 = (2 * (M + N) + 1) + 2 := by omega
      rw [hn]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at ih h ⊢
      calc
        _ ≤ _ := add_le_add ih h
        _ = _ := by ring
  apply Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _)
  intro M
  apply (hfinite M).trans
  exact div_le_div_of_nonneg_right
    (sub_le_self _ (Real.rpow_nonneg (by positivity) _)) (by positivity)

/-- Every actual eta tail has the same exact two-term complex Euler
expansion, with the complete signed remainder still available. -/
theorem pairedEtaCore_tail_eq_centered_euler {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaCore s - pairedEtaCorePartialSum N s -
        (((2 * N + 1 : ℕ) : ℂ) ^ (-s)) / 2 -
        s / 4 * (((2 * N + 1 : ℕ) : ℂ) ^ (-s - 1)) =
      s * (s + 1) / 2 *
        ∑' n : ℕ, pairedEtaCenteredEulerBlock s ((2 * (n + N) + 1 : ℕ) : ℝ) := by
  rw [pairedEtaCore_eq_centered_euler hs, pairedEtaCorePartialSum_eq_centered_euler]
  rw [← (summable_pairedEtaCenteredEulerBlock hs).sum_add_tsum_nat_add N]
  ring

/-- A quantitative bound for every actual eta tail after extracting both
complex Euler terms; no zero equation or asymptotic cutoff is assumed. -/
theorem norm_pairedEtaCore_tail_sub_centered_euler_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s -
        (((2 * N + 1 : ℕ) : ℂ) ^ (-s)) / 2 -
        s / 4 * (((2 * N + 1 : ℕ) : ℂ) ^ (-s - 1))‖ ≤
      ‖s‖ * ‖s + 1‖ * (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re - 1)) /
        (4 * (s.re + 1)) := by
  rw [pairedEtaCore_tail_eq_centered_euler hs N, norm_mul]
  have hsum : Summable (fun n : ℕ =>
      pairedEtaCenteredEulerBlock s ((2 * (n + N) + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff N).mpr (summable_pairedEtaCenteredEulerBlock hs)
  have h := (norm_tsum_le_tsum_norm hsum.norm).trans
    (tsum_norm_pairedEtaCenteredEulerBlock_tail_le hs N)
  calc
    _ ≤ ‖s * (s + 1) / 2‖ *
        ((((2 * N + 1 : ℕ) : ℝ) ^ (-s.re - 1)) / (2 * (s.re + 1))) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by rw [norm_div, norm_mul]; norm_num; field_simp; ring

end
end RiemannGaussian
