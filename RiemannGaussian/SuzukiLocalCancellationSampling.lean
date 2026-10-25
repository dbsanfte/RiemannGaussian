/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLocalCancellationPhysical
import RiemannGaussian.SuzukiLocalCancellationPrimePowers
import Mathlib.NumberTheory.AbelSummation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Uniform lattice sampling of the actual local Suzuki kernel

The complete signed density-cancelling packet is retained before bounding
its arithmetic lattice sampling error.
-/

set_option warningAsError true

namespace RiemannGaussian
noncomputable section
open MeasureTheory Set
open scoped Topology

private def localSamplingSaw (x : ℝ) : ℝ := (⌊x⌋₊ : ℝ) + 1 - x

private theorem localSamplingSaw_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ localSamplingSaw x ∧ localSamplingSaw x ≤ 1 := by
  dsimp [localSamplingSaw]
  exact ⟨(sub_pos.mpr (Nat.lt_floor_add_one x)).le, by linarith [Nat.floor_le hx]⟩

/-- Exact real-valued Abel sampling, retaining both unrounded endpoints. -/
theorem localCancellation_sampling_identity (f : ℝ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : IntegrableOn (deriv f) (Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n) - (∫ x in a..b, f x) =
      f b * localSamplingSaw b - f a * localSamplingSaw a -
        ∫ x in a..b, deriv f x * localSamplingSaw x := by
  have habs := sum_mul_eq_sub_sub_integral_mul (fun _ : ℕ => (1 : ℝ)) ha hab hf hd
  have hp (x : ℝ) : (∑ _n ∈ Finset.Icc 0 ⌊x⌋₊, (1 : ℝ)) = (⌊x⌋₊ : ℝ) + 1 := by simp
  simp_rw [hp, mul_one] at habs
  have ht := integrableOn_mul_sum_Icc (fun _ : ℕ => (1 : ℝ)) (m := 0) ha hd
  simp_rw [hp] at ht
  have hx : IntegrableOn (fun x : ℝ => deriv f x * x) (Icc a b) := by
    simpa only [id_eq, mul_comm] using
      IntegrableOn.continuousOn_mul continuous_id.continuousOn hd isCompact_Icc
  have hsaw : (∫ x in a..b, deriv f x * localSamplingSaw x) =
      (∫ x in a..b, deriv f x * ((⌊x⌋₊ : ℝ) + 1)) -
        ∫ x in a..b, deriv f x * x := by
    rw [← intervalIntegral.integral_sub
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ht)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hx)]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [localSamplingSaw]
    ring
  have hdint : IntervalIntegrable (deriv f) volume a b := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hd
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => x) (u' := fun _ => (1 : ℝ)) (v := f) (v' := deriv f)
    (fun x _ => hasDerivAt_id x)
    (fun x hx => (hf x (by simpa only [uIcc_of_le hab] using hx)).hasDerivAt)
    (by simp) hdint
  rw [← intervalIntegral.integral_of_le hab] at habs
  rw [hsaw]
  have hxint : (∫ x in a..b, deriv f x * x) =
      b * f b - a * f a - ∫ x in a..b, f x := by
    simpa only [one_mul, mul_one, mul_comm] using hip
  rw [hxint]
  dsimp [localSamplingSaw]
  linarith

/-- A uniform derivative envelope controls each smooth branch's lattice
error, including both real endpoints. -/
theorem localCancellation_sampling_error_le (f : ℝ → ℝ) {a b M D : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : IntegrableOn (deriv f) (Icc a b))
    (hfa : |f a| ≤ M) (hfb : |f b| ≤ M)
    (hderiv : ∀ x ∈ Icc a b, |deriv f x| ≤ D) :
    |(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n) - (∫ x in a..b, f x)| ≤
      2 * M + D * (b - a) := by
  rw [localCancellation_sampling_identity f ha hab hf hd]
  have hbound : |∫ x in a..b, deriv f x * localSamplingSaw x| ≤ D * (b - a) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (f := fun x => deriv f x * localSamplingSaw x) (C := D) (by
        intro x hx
        have hx' : x ∈ Icc a b := (uIoc_of_le hab ▸ hx) |> Ioc_subset_Icc_self
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (localSamplingSaw_bounds (ha.trans hx'.1)).1]
        exact (mul_le_mul_of_nonneg_left (localSamplingSaw_bounds (ha.trans hx'.1)).2
          (abs_nonneg _)).trans (by simpa only [mul_one] using hderiv x hx'))
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hh
  have hleft : |f a * localSamplingSaw a| ≤ M := by
    rw [abs_mul, abs_of_nonneg (localSamplingSaw_bounds ha).1]
    exact (mul_le_mul_of_nonneg_left (localSamplingSaw_bounds ha).2 (abs_nonneg _)).trans
      (by simpa only [mul_one] using hfa)
  have hright : |f b * localSamplingSaw b| ≤ M := by
    rw [abs_mul, abs_of_nonneg (localSamplingSaw_bounds (ha.trans hab)).1]
    exact (mul_le_mul_of_nonneg_left (localSamplingSaw_bounds (ha.trans hab)).2 (abs_nonneg _)).trans
      (by simpa only [mul_one] using hfb)
  calc
    _ ≤ |f b * localSamplingSaw b| + |f a * localSamplingSaw a| +
        |∫ x in a..b, deriv f x * localSamplingSaw x| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ _ := by linarith

/-- A smooth logarithmic branch, before the three real band pieces are
joined. The numerator keeps its actual sign. -/
def suzukiLocalLogBranch (X q A B x : ℝ) : ℝ :=
  (A * Real.log (q * x / X) + B) / Real.sqrt (q * x)

/-- Exact derivative of a smooth scaled branch. -/
theorem suzukiLocalLogBranch_hasDerivAt {X q x : ℝ} (hX : X ≠ 0)
    (hy : 0 < q * x) (A B : ℝ) :
    HasDerivAt (suzukiLocalLogBranch X q A B)
      (q * (A - (A * Real.log (q * x / X) + B) / 2) /
        (q * x * Real.sqrt (q * x))) x := by
  have hy0 : q * x ≠ 0 := hy.ne'
  have hs : Real.sqrt (q * x) ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hh := (((Real.hasDerivAt_log (div_ne_zero hy0 hX)).comp x
    (((hasDerivAt_id x).const_mul q).div_const X)).const_mul A).add_const B
  have hsq := (Real.hasDerivAt_sqrt hy0).comp x ((hasDerivAt_id x).const_mul q)
  convert hh.div hsq hs using 1
  · rfl
  · dsimp only [Function.comp_apply, id_eq]
    have hq : q ≠ 0 := left_ne_zero_of_mul hy0
    have hx : x ≠ 0 := right_ne_zero_of_mul hy0
    field_simp [hX, hq, hx, hs]
    have hss : Real.sqrt (q * x) ^ 2 = q * x := Real.sq_sqrt hy.le
    rw [hss]
    ring

/-- Every actual smooth band has a cutoff-independent Euler error. This
estimate preserves the whole affine numerator before its bound is used. -/
theorem suzukiLocalLogBranch_sampling_error_le {X q a b A B : ℝ}
    (hX : 0 < X) (hq : 0 < q) (hXa : X ≤ a) (hab : a ≤ b)
    (hA : |A| ≤ 3)
    (hnum : ∀ y ∈ Icc a b, |A * Real.log (y / X) + B| ≤ 3) :
    |(∑ n ∈ Finset.Ioc ⌊a / q⌋₊ ⌊b / q⌋₊, suzukiLocalLogBranch X q A B n) -
      (∫ x in a / q..b / q, suzukiLocalLogBranch X q A B x)| ≤
      6 / Real.sqrt X + 5 * (b - a) / (X * Real.sqrt X) := by
  have ha : 0 < a := hX.trans_le hXa
  have hqint : a / q ≤ b / q := (div_le_div_iff_of_pos_right hq).mpr hab
  have hqx : ∀ x ∈ Icc (a / q) (b / q), q * x ∈ Icc a b := by
    intro x hx
    constructor
    · have hh := (div_le_iff₀ hq).mp hx.1
      nlinarith
    · have hh := (le_div_iff₀ hq).mp hx.2
      nlinarith
  have hpos : ∀ x ∈ Icc (a / q) (b / q), 0 < q * x :=
    fun x hx => ha.trans_le (hqx x hx).1
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hcontlog : ContinuousOn (fun x : ℝ => Real.log (q * x / X))
      (Icc (a / q) (b / q)) := by
    apply ((continuous_const.mul continuous_id).div_const X).continuousOn.log
    intro x hx
    exact div_ne_zero (hpos x hx).ne' hX.ne'
  have hcontsqrt : Continuous (fun x : ℝ => Real.sqrt (q * x)) :=
    Real.continuous_sqrt.comp (continuous_const.mul continuous_id)
  have hderiv : ∀ x ∈ Icc (a / q) (b / q),
      deriv (suzukiLocalLogBranch X q A B) x =
        q * (A - (A * Real.log (q * x / X) + B) / 2) /
          (q * x * Real.sqrt (q * x)) := by
    intro x hx
    exact (suzukiLocalLogBranch_hasDerivAt hX.ne' (hpos x hx) A B).deriv
  have hdcont : ContinuousOn (deriv (suzukiLocalLogBranch X q A B))
      (Icc (a / q) (b / q)) := by
    apply ContinuousOn.congr (f := fun x =>
      q * (A - (A * Real.log (q * x / X) + B) / 2) /
        (q * x * Real.sqrt (q * x))) _ (fun x hx => hderiv x hx)
    apply (continuousOn_const.mul
      (continuousOn_const.sub ((continuousOn_const.mul hcontlog |>.add continuousOn_const).div_const 2))).div
      ((continuous_const.mul continuous_id).continuousOn.mul hcontsqrt.continuousOn)
    intro x hx
    exact mul_ne_zero (hpos x hx).ne' (Real.sqrt_pos.mpr (hpos x hx)).ne'
  have hvalue : ∀ x ∈ Icc (a / q) (b / q),
      |suzukiLocalLogBranch X q A B x| ≤ 3 / Real.sqrt X := by
    intro x hx
    have hy := hqx x hx
    have hs := Real.sqrt_le_sqrt (hXa.trans hy.1)
    rw [suzukiLocalLogBranch, abs_div, abs_of_pos (Real.sqrt_pos.mpr (hpos x hx))]
    exact div_le_div₀ (by norm_num) (hnum _ hy) hsX hs
  have hdbound : ∀ x ∈ Icc (a / q) (b / q),
      |deriv (suzukiLocalLogBranch X q A B) x| ≤ 5 * q / (X * Real.sqrt X) := by
    intro x hx
    have hy := hqx x hx
    have hs := Real.sqrt_le_sqrt (hXa.trans hy.1)
    have hn : |A - (A * Real.log (q * x / X) + B) / 2| ≤ 5 := by
      have hn := hnum _ hy
      calc
        _ ≤ |A| + |(A * Real.log (q * x / X) + B) / 2| := abs_sub _ _
        _ ≤ 5 := by rw [abs_div]; norm_num; linarith
    have hdpos : 0 < q * x * Real.sqrt (q * x) :=
      mul_pos (hpos x hx) (Real.sqrt_pos.mpr (hpos x hx))
    have hden : X * Real.sqrt X ≤ q * x * Real.sqrt (q * x) :=
      mul_le_mul (hXa.trans hy.1) hs (Real.sqrt_nonneg _) (hpos x hx).le
    rw [hderiv x hx, abs_div, abs_mul, abs_of_pos hq, abs_of_pos hdpos]
    have hh := div_le_div₀ (by positivity : 0 ≤ q * 5)
      (mul_le_mul_of_nonneg_left hn hq.le) (mul_pos hX hsX) hden
    simpa only [mul_comm q 5] using hh
  have hh := localCancellation_sampling_error_le (suzukiLocalLogBranch X q A B)
    (div_nonneg ha.le hq.le) hqint
    (fun x hx => (suzukiLocalLogBranch_hasDerivAt hX.ne' (hpos x hx) A B).differentiableAt)
    (hdcont.integrableOn_Icc)
    (hvalue _ ⟨le_rfl, hqint⟩) (hvalue _ ⟨hqint, le_rfl⟩) hdbound
  convert hh using 1
  field_simp
  ring

private theorem localSignedKernel_abs_le_three (v : ℝ) :
    |suzukiLocalSignedKernel v| ≤ 3 := by
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hl : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ Real.sqrt 2 + 1)
  exact (abs_suzukiLocalSignedKernel_le v).trans (by nlinarith)

/-- A smooth formula on one physical band gives the same uniform sampling
bound for the literal, unchanged kernel on that band. -/
theorem suzukiLocalPhysicalKernel_band_sampling_error_le {X q a b A B : ℝ}
    (hX : 0 < X) (hq : 0 < q) (hXa : X ≤ a) (hab : a ≤ b)
    (hA : |A| ≤ 3)
    (heq : ∀ y ∈ Icc a b, suzukiLocalPhysicalKernel X y =
      (A * Real.log (y / X) + B) / Real.sqrt y) :
    |(∑ n ∈ Finset.Ioc ⌊a / q⌋₊ ⌊b / q⌋₊, suzukiLocalPhysicalKernel X (q * n)) -
      (∫ x in a / q..b / q, suzukiLocalPhysicalKernel X (q * x))| ≤
      6 / Real.sqrt X + 5 * (b - a) / (X * Real.sqrt X) := by
  have ha : 0 < a := hX.trans_le hXa
  have hb : 0 < b := ha.trans_le hab
  have hqint : a / q ≤ b / q := (div_le_div_iff_of_pos_right hq).mpr hab
  have hnum : ∀ y ∈ Icc a b, |A * Real.log (y / X) + B| ≤ 3 := by
    intro y hy
    have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr (ha.trans_le hy.1)).ne'
    have he := heq y hy
    rw [suzukiLocalPhysicalKernel] at he
    rw [← (div_left_inj' hs).mp he]
    exact localSignedKernel_abs_le_three _
  have hformula : ∀ x ∈ Icc (a / q) (b / q),
      suzukiLocalPhysicalKernel X (q * x) = suzukiLocalLogBranch X q A B x := by
    intro x hx
    have hy : q * x ∈ Icc a b := by
      constructor
      · have hh := (div_le_iff₀ hq).mp hx.1
        nlinarith
      · have hh := (le_div_iff₀ hq).mp hx.2
        nlinarith
    exact heq _ hy
  have hsum : (∑ n ∈ Finset.Ioc ⌊a / q⌋₊ ⌊b / q⌋₊,
      suzukiLocalPhysicalKernel X (q * n)) =
      ∑ n ∈ Finset.Ioc ⌊a / q⌋₊ ⌊b / q⌋₊, suzukiLocalLogBranch X q A B n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    apply hformula
    exact ⟨((Nat.floor_lt (div_nonneg ha.le hq.le)).mp hn'.1).le,
      (Nat.le_floor_iff (div_nonneg hb.le hq.le)).mp hn'.2⟩
  have hint : (∫ x in a / q..b / q, suzukiLocalPhysicalKernel X (q * x)) =
      ∫ x in a / q..b / q, suzukiLocalLogBranch X q A B x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact hformula x (by simpa only [uIcc_of_le hqint] using hx)
  rw [hsum, hint]
  exact suzukiLocalLogBranch_sampling_error_le hX hq hXa hab hA hnum

/-- The complete actual signed packet has a uniform square-root-decaying
lattice sum at every positive spacing. Both packets and all density
cancellation are joined before the bound is applied. -/
theorem suzukiLocalPhysicalKernel_lattice_sum_abs_le {X q : ℝ}
    (hX : 0 < X) (hq : 0 < q) :
    |∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊8 * X / q⌋₊,
      suzukiLocalPhysicalKernel X (q * n)| ≤ 53 / Real.sqrt X := by
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hspos := Real.sqrt_nonneg 2
  have hfirst := suzukiLocalPhysicalKernel_band_sampling_error_le
    (X := X) (q := q) (a := X) (b := 2 * X) (A := Real.sqrt 2) (B := 0)
    hX hq le_rfl (by linarith) (by rw [abs_of_nonneg hspos]; linarith) (by
      intro y hy
      simpa only [add_zero] using suzukiLocalPhysicalKernel_eq_first hX hy.1 hy.2)
  have hmiddle := suzukiLocalPhysicalKernel_band_sampling_error_le
    (X := X) (q := q) (a := 2 * X) (b := 4 * X)
    (A := -(Real.sqrt 2 + 1)) (B := (2 * Real.sqrt 2 + 1) * Real.log 2)
    hX hq (by linarith) (by linarith)
    (by rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2 + 1)]; linarith) (by
      intro y hy
      rw [suzukiLocalPhysicalKernel_eq_middle hX hy.1 hy.2]
      congr 1
      ring)
  have hlast := suzukiLocalPhysicalKernel_band_sampling_error_le
    (X := X) (q := q) (a := 4 * X) (b := 8 * X)
    (A := 1) (B := -(3 * Real.log 2)) hX hq (by linarith) (by linarith) (by norm_num) (by
      intro y hy
      simpa only [one_mul, sub_eq_add_neg] using suzukiLocalPhysicalKernel_eq_last hX hy.1 hy.2)
  let f : ℝ → ℝ := fun x => suzukiLocalPhysicalKernel X (q * x)
  have h01 : X / q ≤ 2 * X / q := (div_le_div_iff_of_pos_right hq).mpr (by linarith)
  have h12 : 2 * X / q ≤ 4 * X / q := (div_le_div_iff_of_pos_right hq).mpr (by linarith)
  have h23 : 4 * X / q ≤ 8 * X / q := (div_le_div_iff_of_pos_right hq).mpr (by linarith)
  have hsum : (∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊2 * X / q⌋₊, f n) +
      (∑ n ∈ Finset.Ioc ⌊2 * X / q⌋₊ ⌊4 * X / q⌋₊, f n) +
      (∑ n ∈ Finset.Ioc ⌊4 * X / q⌋₊ ⌊8 * X / q⌋₊, f n) =
      ∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊8 * X / q⌋₊, f n := by
    rw [Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor h01) (Nat.floor_le_floor h12),
      Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (h01.trans h12)) (Nat.floor_le_floor h23)]
  have hi {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro x hx
    exact ((continuousAt_suzukiLocalPhysicalKernel hX (mul_pos hq (ha.trans_le hx.1))).comp
      (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
  have hint : (∫ x in X / q..2 * X / q, f x) +
      (∫ x in 2 * X / q..4 * X / q, f x) +
      (∫ x in 4 * X / q..8 * X / q, f x) = ∫ x in X / q..8 * X / q, f x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hi (div_pos hX hq) h01) (hi (div_pos (by positivity) hq) h12),
      intervalIntegral.integral_add_adjacent_intervals
        (hi (div_pos hX hq) (h01.trans h12)) (hi (div_pos (by positivity) hq) h23)]
  have hzero : (∫ x in X / q..8 * X / q, f x) = 0 := by
    have hh := intervalIntegral.mul_integral_comp_mul_left
      (f := suzukiLocalPhysicalKernel X) (a := X / q) (b := 8 * X / q) q
    rw [mul_div_cancel₀ X hq.ne', show q * (8 * X / q) = 8 * X by field_simp,
      suzukiLocalPhysicalKernel_integral_eq_zero hX] at hh
    exact (mul_eq_zero.mp hh).resolve_left hq.ne'
  have htri : |(∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊8 * X / q⌋₊, f n) -
      (∫ x in X / q..8 * X / q, f x)| ≤
      |(∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊2 * X / q⌋₊, f n) -
        (∫ x in X / q..2 * X / q, f x)| +
      |(∑ n ∈ Finset.Ioc ⌊2 * X / q⌋₊ ⌊4 * X / q⌋₊, f n) -
        (∫ x in 2 * X / q..4 * X / q, f x)| +
      |(∑ n ∈ Finset.Ioc ⌊4 * X / q⌋₊ ⌊8 * X / q⌋₊, f n) -
        (∫ x in 4 * X / q..8 * X / q, f x)| := by
    rw [← hsum, ← hint]
    let u := (∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊2 * X / q⌋₊, f n) -
      (∫ x in X / q..2 * X / q, f x)
    let v := (∑ n ∈ Finset.Ioc ⌊2 * X / q⌋₊ ⌊4 * X / q⌋₊, f n) -
      (∫ x in 2 * X / q..4 * X / q, f x)
    let w := (∑ n ∈ Finset.Ioc ⌊4 * X / q⌋₊ ⌊8 * X / q⌋₊, f n) -
      (∫ x in 4 * X / q..8 * X / q, f x)
    have he : ((∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊2 * X / q⌋₊, f n) +
        (∑ n ∈ Finset.Ioc ⌊2 * X / q⌋₊ ⌊4 * X / q⌋₊, f n) +
        (∑ n ∈ Finset.Ioc ⌊4 * X / q⌋₊ ⌊8 * X / q⌋₊, f n)) -
        ((∫ x in X / q..2 * X / q, f x) +
        (∫ x in 2 * X / q..4 * X / q, f x) +
        (∫ x in 4 * X / q..8 * X / q, f x)) = u + v + w := by
      dsimp [u, v, w]
      ring
    rw [he]
    exact (abs_add_le (u + v) w).trans (add_le_add (abs_add_le u v) le_rfl)
  rw [hzero, sub_zero] at htri
  change |∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊8 * X / q⌋₊, f n| ≤ _
  have hsumerr := add_le_add (add_le_add hfirst hmiddle) hlast
  have hxden : X * Real.sqrt X ≠ 0 := by positivity
  have hconstant : (6 / Real.sqrt X + 5 * (2 * X - X) / (X * Real.sqrt X)) +
      (6 / Real.sqrt X + 5 * (4 * X - 2 * X) / (X * Real.sqrt X)) +
      (6 / Real.sqrt X + 5 * (8 * X - 4 * X) / (X * Real.sqrt X)) = 53 / Real.sqrt X := by
    field_simp
    ring
  exact htri.trans (hsumerr.trans_eq hconstant)

/-- Equivalently, every positive integer of the complete physical packet
may be summed; all terms before its left endpoint vanish exactly. -/
theorem suzukiLocalPhysicalKernel_prefix_sum_abs_le {X q : ℝ}
    (hX : 0 < X) (hq : 0 < q) :
    |∑ n ∈ Finset.Icc 1 ⌊8 * X / q⌋₊,
      suzukiLocalPhysicalKernel X (q * n)| ≤ 53 / Real.sqrt X := by
  have hAB : ⌊X / q⌋₊ ≤ ⌊8 * X / q⌋₊ :=
    Nat.floor_le_floor ((div_le_div_iff_of_pos_right hq).mpr (by linarith))
  have hz : (∑ n ∈ Finset.Ioc 0 ⌊X / q⌋₊, suzukiLocalPhysicalKernel X (q * n)) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : (n : ℝ) ≤ X / q :=
      (Nat.le_floor_iff (div_nonneg hX.le hq.le)).mp (Finset.mem_Ioc.mp hn).2
    apply suzukiLocalPhysicalKernel_eq_zero_of_le hX
    have hh := (le_div_iff₀ hq).mp hn'
    nlinarith
  have he := Finset.sum_Ioc_consecutive
    (fun n : ℕ => suzukiLocalPhysicalKernel X (q * n)) (Nat.zero_le ⌊X / q⌋₊) hAB
  rw [hz, zero_add] at he
  have hset : Finset.Ioc 0 ⌊8 * X / q⌋₊ = Finset.Icc 1 ⌊8 * X / q⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset] at he
  rw [← he]
  exact suzukiLocalPhysicalKernel_lattice_sum_abs_le hX hq

/-- The actual small-factor cross sector in Vaughan's identity, with all
Möbius signs, proper prime powers and product cutoffs retained. -/
def suzukiLocalVaughanSmallCross (X : ℝ) (U V : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 U, ∑ l ∈ Finset.Ioc 0 V,
    (ArithmeticFunction.moebius d : ℝ) * ArithmeticFunction.vonMangoldt l *
      ∑ m ∈ Finset.Icc 1 ⌊8 * X / ((d : ℝ) * l)⌋₊,
        suzukiLocalPhysicalKernel X ((d : ℝ) * l * m)

/-- Independent arithmetic payment for the complete small-factor cross
sector. At quarter-power factor cutoffs this has a bounded uniform cost.
This does not estimate Vaughan's remaining signed large-factor sector. -/
theorem suzukiLocalVaughanSmallCross_abs_le {X : ℝ} (hX : 0 < X) (U V : ℕ) :
    |suzukiLocalVaughanSmallCross X U V| ≤ 318 * U * V / Real.sqrt X := by
  have hterm : ∀ d ∈ Finset.Ioc 0 U, ∀ l ∈ Finset.Ioc 0 V,
      |(ArithmeticFunction.moebius d : ℝ) * ArithmeticFunction.vonMangoldt l *
        ∑ m ∈ Finset.Icc 1 ⌊8 * X / ((d : ℝ) * l)⌋₊,
          suzukiLocalPhysicalKernel X ((d : ℝ) * l * m)| ≤
        ArithmeticFunction.vonMangoldt l * (53 / Real.sqrt X) := by
    intro d hd l hl
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
    have hlpos : (0 : ℝ) < l := by exact_mod_cast (Finset.mem_Ioc.mp hl).1
    have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hpacket := suzukiLocalPhysicalKernel_prefix_sum_abs_le hX (mul_pos hdpos hlpos)
    rw [abs_mul, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    calc
      _ ≤ 1 * ArithmeticFunction.vonMangoldt l * (53 / Real.sqrt X) := by
        gcongr
      _ = _ := by ring
  have hψ : Chebyshev.psi (V : ℝ) ≤ 6 * V := by
    by_cases hV : V = 0
    · subst V
      simp [Chebyshev.psi]
    · exact chebyshevPsi_le_six_mul_self_of_one_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hV)
  have hsum : |suzukiLocalVaughanSmallCross X U V| ≤
      (U : ℝ) * Chebyshev.psi V * (53 / Real.sqrt X) := by
    unfold suzukiLocalVaughanSmallCross
    calc
      _ ≤ ∑ d ∈ Finset.Ioc 0 U, ∑ l ∈ Finset.Ioc 0 V,
          |(ArithmeticFunction.moebius d : ℝ) * ArithmeticFunction.vonMangoldt l *
            ∑ m ∈ Finset.Icc 1 ⌊8 * X / ((d : ℝ) * l)⌋₊,
              suzukiLocalPhysicalKernel X ((d : ℝ) * l * m)| := by
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum (fun d _ => Finset.abs_sum_le_sum_abs _ _))
      _ ≤ ∑ _d ∈ Finset.Ioc 0 U, ∑ l ∈ Finset.Ioc 0 V,
          ArithmeticFunction.vonMangoldt l * (53 / Real.sqrt X) :=
        Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun l hl => hterm d hd l hl))
      _ = _ := by
        simp only [← Finset.sum_mul, Chebyshev.psi, Nat.floor_natCast,
          Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hψ (Nat.cast_nonneg U)) (by positivity : 0 ≤ 53 / Real.sqrt X)
  exact hsum.trans (hh.trans_eq (by ring))

/-- Every factor-cutoff allocation with product at most `sqrt X` has a
uniform bounded cost in this actual arithmetic sector. -/
theorem suzukiLocalVaughanSmallCross_abs_le_of_product_le_sqrt
    {X : ℝ} (hX : 0 < X) (U V : ℕ)
    (hUV : (U : ℝ) * V ≤ Real.sqrt X) :
    |suzukiLocalVaughanSmallCross X U V| ≤ 318 := by
  apply (suzukiLocalVaughanSmallCross_abs_le hX U V).trans
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hX)).mpr
  nlinarith

end
end RiemannGaussian
