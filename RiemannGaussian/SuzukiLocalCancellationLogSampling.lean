/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiLocalCancellationSampling
import RiemannGaussian.SuzukiLocalCancellationMoment

/-!
# Logarithmic lattice sampling of the exact local Suzuki packet

The logarithmic Type-I weight is retained before estimating the discrete
sampling error. Its nonzero density moment is not dropped.
-/

set_option warningAsError true
namespace RiemannGaussian
noncomputable section
open MeasureTheory Set

/-- Multiplying a smooth sample by a logarithm retains both derivative
terms and the same real sampling endpoints. -/
theorem localCancellation_log_sampling_error_le (f : ℝ → ℝ) {a b M D L R : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hd : IntegrableOn (deriv f) (Icc a b))
    (hvalue : ∀ x ∈ Icc a b, |f x| ≤ M)
    (hderiv : ∀ x ∈ Icc a b, |deriv f x| ≤ D)
    (hlog : ∀ x ∈ Icc a b, Real.log x ≤ L)
    (hinv : ∀ x ∈ Icc a b, x⁻¹ ≤ R) :
    |(∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n * Real.log n) -
      (∫ x in a..b, f x * Real.log x)| ≤
      2 * (M * L) + (D * L + M * R) * (b - a) := by
  have hpos : ∀ x ∈ Icc a b, 0 < x := fun x hx => lt_of_lt_of_le zero_lt_one (ha.trans hx.1)
  have hlog0 : ∀ x ∈ Icc a b, 0 ≤ Real.log x := fun x hx => Real.log_nonneg (ha.trans hx.1)
  have hcont : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hclog : ContinuousOn Real.log (Icc a b) :=
    continuousOn_id.log (fun x hx => (hpos x hx).ne')
  have hcinv : ContinuousOn (fun x : ℝ => x⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun x hx => (hpos x hx).ne')
  have hdf : ∀ x ∈ Icc a b,
      HasDerivAt (fun x => f x * Real.log x) (deriv f x * Real.log x + f x * x⁻¹) x :=
    fun x hx => (hf x hx).hasDerivAt.mul (Real.hasDerivAt_log (hpos x hx).ne')
  have hdi : IntegrableOn (deriv (fun x => f x * Real.log x)) (Icc a b) := by
    have hfirst : IntegrableOn (fun x => deriv f x * Real.log x) (Icc a b) := by
      simpa only [mul_comm] using IntegrableOn.continuousOn_mul hclog hd isCompact_Icc
    apply (hfirst.add (hcont.mul hcinv).integrableOn_Icc).congr_fun _ measurableSet_Icc
    intro x hx
    exact (hdf x hx).deriv.symm
  have hv : ∀ x ∈ Icc a b, |f x * Real.log x| ≤ M * L := by
    intro x hx
    rw [abs_mul, abs_of_nonneg (hlog0 x hx)]
    exact mul_le_mul (hvalue x hx) (hlog x hx) (hlog0 x hx) hM
  have hdv : ∀ x ∈ Icc a b,
      |deriv (fun x => f x * Real.log x) x| ≤ D * L + M * R := by
    intro x hx
    rw [(hdf x hx).deriv]
    calc
      _ ≤ |deriv f x * Real.log x| + |f x * x⁻¹| := abs_add_le _ _
      _ = |deriv f x| * Real.log x + |f x| * x⁻¹ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hlog0 x hx), abs_of_pos (inv_pos.mpr (hpos x hx))]
      _ ≤ _ := add_le_add
        (mul_le_mul (hderiv x hx) (hlog x hx) (hlog0 x hx) hD)
        (mul_le_mul (hvalue x hx) (hinv x hx) (inv_nonneg.mpr (hpos x hx).le) hM)
  exact localCancellation_sampling_error_le _ (zero_le_one.trans ha) hab
    (fun x hx => (hdf x hx).differentiableAt) hdi
    (hv a ⟨le_rfl, hab⟩) (hv b ⟨hab, le_rfl⟩) hdv

/-- A logarithmically weighted smooth branch has a controlled sampling
error uniformly in every divisor spacing between one and the base. -/
theorem suzukiLocalLogBranch_log_sampling_error_le {X q a b A B : ℝ}
    (hX : 1 ≤ X) (hq : 1 ≤ q) (hqX : q ≤ X) (hXa : X ≤ a) (hab : a ≤ b)
    (hbX : b ≤ 8 * X) (hA : |A| ≤ 3)
    (hnum : ∀ y ∈ Icc a b, |A * Real.log (y / X) + B| ≤ 3) :
    |(∑ n ∈ Finset.Ioc ⌊a / q⌋₊ ⌊b / q⌋₊,
      suzukiLocalLogBranch X q A B n * Real.log n) -
      (∫ x in a / q..b / q, suzukiLocalLogBranch X q A B x * Real.log x)| ≤
      6 * Real.log (8 * X) / Real.sqrt X +
        (5 * Real.log (8 * X) + 3) * (b - a) / (X * Real.sqrt X) := by
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have ha : 0 < a := hX0.trans_le hXa
  have hqint : a / q ≤ b / q := (div_le_div_iff_of_pos_right hq0).mpr hab
  have hqx : ∀ x ∈ Icc (a / q) (b / q), q * x ∈ Icc a b := by
    intro x hx
    exact ⟨by have hh := (div_le_iff₀ hq0).mp hx.1; nlinarith,
      by have hh := (le_div_iff₀ hq0).mp hx.2; nlinarith⟩
  have hpos : ∀ x ∈ Icc (a / q) (b / q), 0 < q * x :=
    fun x hx => ha.trans_le (hqx x hx).1
  have hclog : ContinuousOn (fun x : ℝ => Real.log (q * x / X))
      (Icc (a / q) (b / q)) := by
    apply ((continuous_const.mul continuous_id).div_const X).continuousOn.log
    intro x hx
    exact div_ne_zero (hpos x hx).ne' hX0.ne'
  have hcsqrt : Continuous (fun x : ℝ => Real.sqrt (q * x)) :=
    Real.continuous_sqrt.comp (continuous_const.mul continuous_id)
  have hdf : ∀ x ∈ Icc (a / q) (b / q),
      deriv (suzukiLocalLogBranch X q A B) x =
        q * (A - (A * Real.log (q * x / X) + B) / 2) /
          (q * x * Real.sqrt (q * x)) := by
    intro x hx
    exact (suzukiLocalLogBranch_hasDerivAt hX0.ne' (hpos x hx) A B).deriv
  have hdc : ContinuousOn (deriv (suzukiLocalLogBranch X q A B))
      (Icc (a / q) (b / q)) := by
    apply ContinuousOn.congr (f := fun x =>
      q * (A - (A * Real.log (q * x / X) + B) / 2) /
        (q * x * Real.sqrt (q * x))) _ hdf
    apply (continuousOn_const.mul
      (continuousOn_const.sub ((continuousOn_const.mul hclog |>.add continuousOn_const).div_const 2))).div
      ((continuous_const.mul continuous_id).continuousOn.mul hcsqrt.continuousOn)
    intro x hx
    exact mul_ne_zero (hpos x hx).ne' (Real.sqrt_pos.mpr (hpos x hx)).ne'
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hv : ∀ x ∈ Icc (a / q) (b / q),
      |suzukiLocalLogBranch X q A B x| ≤ 3 / Real.sqrt X := by
    intro x hx
    rw [suzukiLocalLogBranch, abs_div, abs_of_pos (Real.sqrt_pos.mpr (hpos x hx))]
    exact div_le_div₀ (by norm_num) (hnum _ (hqx x hx)) hsX
      (Real.sqrt_le_sqrt (hXa.trans (hqx x hx).1))
  have hdv : ∀ x ∈ Icc (a / q) (b / q),
      |deriv (suzukiLocalLogBranch X q A B) x| ≤ 5 * q / (X * Real.sqrt X) := by
    intro x hx
    have hy := hqx x hx
    have hn : |A - (A * Real.log (q * x / X) + B) / 2| ≤ 5 := by
      have hh := hnum _ hy
      calc
        _ ≤ |A| + |(A * Real.log (q * x / X) + B) / 2| := abs_sub _ _
        _ ≤ 5 := by rw [abs_div]; norm_num; linarith
    have hdpos : 0 < q * x * Real.sqrt (q * x) :=
      mul_pos (hpos x hx) (Real.sqrt_pos.mpr (hpos x hx))
    have hden : X * Real.sqrt X ≤ q * x * Real.sqrt (q * x) :=
      mul_le_mul (hXa.trans hy.1) (Real.sqrt_le_sqrt (hXa.trans hy.1))
        (Real.sqrt_nonneg _) (hpos x hx).le
    rw [hdf x hx, abs_div, abs_mul, abs_of_pos hq0, abs_of_pos hdpos]
    simpa only [mul_comm q 5] using div_le_div₀ (by positivity : 0 ≤ q * 5)
      (mul_le_mul_of_nonneg_left hn hq0.le) (mul_pos hX0 hsX) hden
  have hlow : 1 ≤ a / q := (one_le_div hq0).mpr (hqX.trans hXa)
  have hlog : ∀ x ∈ Icc (a / q) (b / q), Real.log x ≤ Real.log (8 * X) := by
    intro x hx
    have hxpos : 0 < x := zero_lt_one.trans_le (hlow.trans hx.1)
    apply Real.log_le_log hxpos
    have hh := (le_div_iff₀ hq0).mp hx.2
    nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ x)]
  have hinv : ∀ x ∈ Icc (a / q) (b / q), x⁻¹ ≤ q / X := by
    intro x hx
    have hlo : X / q ≤ x := ((div_le_div_iff_of_pos_right hq0).mpr hXa).trans hx.1
    have hh := one_div_le_one_div_of_le (div_pos hX0 hq0) hlo
    simpa only [one_div, inv_div] using hh
  have hh := localCancellation_log_sampling_error_le (suzukiLocalLogBranch X q A B)
    hlow hqint (by positivity) (by positivity)
    (fun x hx => (suzukiLocalLogBranch_hasDerivAt hX0.ne' (hpos x hx) A B).differentiableAt)
    hdc.integrableOn_Icc hv hdv hlog hinv
  convert hh using 1
  field_simp
  ring

private theorem localLogSignedKernel_abs_le_three (v : ℝ) :
    |suzukiLocalSignedKernel v| ≤ 3 := by
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hl : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ Real.sqrt 2 + 1)
  exact (abs_suzukiLocalSignedKernel_le v).trans (by nlinarith)


/-- The unchanged physical branch, with its logarithmic arithmetic weight,
has the uniform discretization error supplied by its actual smooth formula. -/
theorem suzukiLocalPhysicalKernel_band_log_sampling_error_le {X q a b A B : ℝ}
    (hX : 1 ≤ X) (hq : 1 ≤ q) (hqX : q ≤ X) (hXa : X ≤ a) (hab : a ≤ b)
    (hbX : b ≤ 8 * X) (hA : |A| ≤ 3)
    (heq : ∀ y ∈ Icc a b, suzukiLocalPhysicalKernel X y =
      (A * Real.log (y / X) + B) / Real.sqrt y) :
    |(∑ n ∈ Finset.Ioc ⌊a / q⌋₊ ⌊b / q⌋₊,
      suzukiLocalPhysicalKernel X (q * n) * Real.log n) -
      (∫ x in a / q..b / q, suzukiLocalPhysicalKernel X (q * x) * Real.log x)| ≤
      6 * Real.log (8 * X) / Real.sqrt X +
        (5 * Real.log (8 * X) + 3) * (b - a) / (X * Real.sqrt X) := by
  have hX0 := zero_lt_one.trans_le hX
  have hq0 := zero_lt_one.trans_le hq
  have ha : 0 < a := hX0.trans_le hXa
  have hb : 0 < b := ha.trans_le hab
  have hqint : a / q ≤ b / q := (div_le_div_iff_of_pos_right hq0).mpr hab
  have hnum : ∀ y ∈ Icc a b, |A * Real.log (y / X) + B| ≤ 3 := by
    intro y hy
    have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr (ha.trans_le hy.1)).ne'
    have he := heq y hy
    rw [suzukiLocalPhysicalKernel] at he
    rw [← (div_left_inj' hs).mp he]
    exact localLogSignedKernel_abs_le_three _
  have hformula : ∀ x ∈ Icc (a / q) (b / q),
      suzukiLocalPhysicalKernel X (q * x) = suzukiLocalLogBranch X q A B x := by
    intro x hx
    have hy : q * x ∈ Icc a b := by
      exact ⟨by have hh := (div_le_iff₀ hq0).mp hx.1; nlinarith,
        by have hh := (le_div_iff₀ hq0).mp hx.2; nlinarith⟩
    exact heq _ hy
  have hsum : (∑ n ∈ Finset.Ioc ⌊a / q⌋₊ ⌊b / q⌋₊,
      suzukiLocalPhysicalKernel X (q * n) * Real.log n) =
      ∑ n ∈ Finset.Ioc ⌊a / q⌋₊ ⌊b / q⌋₊,
        suzukiLocalLogBranch X q A B n * Real.log n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    rw [hformula n ⟨((Nat.floor_lt (div_nonneg ha.le hq0.le)).mp hn'.1).le,
      (Nat.le_floor_iff (div_nonneg hb.le hq0.le)).mp hn'.2⟩]
  have hint : (∫ x in a / q..b / q, suzukiLocalPhysicalKernel X (q * x) * Real.log x) =
      ∫ x in a / q..b / q, suzukiLocalLogBranch X q A B x * Real.log x := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [hformula x (by simpa only [uIcc_of_le hqint] using hx)]
  rw [hsum, hint]
  exact suzukiLocalLogBranch_log_sampling_error_le hX hq hqX hXa hab hbX hA hnum

/-- The complete logarithmically weighted physical packet has a uniform
sampling-error bound at every divisor spacing between one and the base.
The density moment remains in the displayed integral. -/
theorem suzukiLocalPhysicalKernel_log_lattice_sampling_error_le {X q : ℝ}
    (hX : 1 ≤ X) (hq : 1 ≤ q) (hqX : q ≤ X) :
    |(∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊8 * X / q⌋₊,
      suzukiLocalPhysicalKernel X (q * n) * Real.log n) -
      (∫ x in X / q..8 * X / q, suzukiLocalPhysicalKernel X (q * x) * Real.log x)| ≤
      (53 * Real.log (8 * X) + 21) / Real.sqrt X := by
  have hX0 := zero_lt_one.trans_le hX
  have hq0 := zero_lt_one.trans_le hq
  have hs : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hspos := Real.sqrt_nonneg 2
  have hfirst := suzukiLocalPhysicalKernel_band_log_sampling_error_le
    (X := X) (q := q) (a := X) (b := 2 * X) (A := Real.sqrt 2) (B := 0)
    hX hq hqX le_rfl (by linarith) (by linarith)
    (by rw [abs_of_nonneg hspos]; linarith) (by
      intro y hy
      simpa only [add_zero] using suzukiLocalPhysicalKernel_eq_first hX0 hy.1 hy.2)
  have hmiddle := suzukiLocalPhysicalKernel_band_log_sampling_error_le
    (X := X) (q := q) (a := 2 * X) (b := 4 * X)
    (A := -(Real.sqrt 2 + 1)) (B := (2 * Real.sqrt 2 + 1) * Real.log 2)
    hX hq hqX (by linarith) (by linarith) (by linarith)
    (by rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2 + 1)]; linarith) (by
      intro y hy
      rw [suzukiLocalPhysicalKernel_eq_middle hX0 hy.1 hy.2]
      congr 1
      ring)
  have hlast := suzukiLocalPhysicalKernel_band_log_sampling_error_le
    (X := X) (q := q) (a := 4 * X) (b := 8 * X)
    (A := 1) (B := -(3 * Real.log 2)) hX hq hqX (by linarith) (by linarith)
    le_rfl (by norm_num) (by
      intro y hy
      simpa only [one_mul, sub_eq_add_neg] using suzukiLocalPhysicalKernel_eq_last hX0 hy.1 hy.2)
  let f : ℝ → ℝ := fun x => suzukiLocalPhysicalKernel X (q * x) * Real.log x
  have h01 : X / q ≤ 2 * X / q := (div_le_div_iff_of_pos_right hq0).mpr (by linarith)
  have h12 : 2 * X / q ≤ 4 * X / q := (div_le_div_iff_of_pos_right hq0).mpr (by linarith)
  have h23 : 4 * X / q ≤ 8 * X / q := (div_le_div_iff_of_pos_right hq0).mpr (by linarith)
  have hsum : (∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊2 * X / q⌋₊, f n) +
      (∑ n ∈ Finset.Ioc ⌊2 * X / q⌋₊ ⌊4 * X / q⌋₊, f n) +
      (∑ n ∈ Finset.Ioc ⌊4 * X / q⌋₊ ⌊8 * X / q⌋₊, f n) =
      ∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊8 * X / q⌋₊, f n := by
    rw [Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor h01) (Nat.floor_le_floor h12),
      Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor (h01.trans h12)) (Nat.floor_le_floor h23)]
  have hi {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro x hx
    exact (((continuousAt_suzukiLocalPhysicalKernel hX0 (mul_pos hq0 (ha.trans_le hx.1))).comp
      (continuous_const.mul continuous_id).continuousAt).mul
        (Real.continuousAt_log (ha.trans_le hx.1).ne')).continuousWithinAt
  have hint : (∫ x in X / q..2 * X / q, f x) +
      (∫ x in 2 * X / q..4 * X / q, f x) +
      (∫ x in 4 * X / q..8 * X / q, f x) = ∫ x in X / q..8 * X / q, f x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hi (div_pos hX0 hq0) h01) (hi (div_pos (by positivity) hq0) h12),
      intervalIntegral.integral_add_adjacent_intervals
        (hi (div_pos hX0 hq0) (h01.trans h12)) (hi (div_pos (by positivity) hq0) h23)]
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

  change |(∑ n ∈ Finset.Ioc ⌊X / q⌋₊ ⌊8 * X / q⌋₊, f n) -
    (∫ x in X / q..8 * X / q, f x)| ≤ _
  have hsumerr := add_le_add (add_le_add hfirst hmiddle) hlast
  have hxden : X * Real.sqrt X ≠ 0 := by positivity
  have hconstant :
      (6 * Real.log (8 * X) / Real.sqrt X +
        (5 * Real.log (8 * X) + 3) * (2 * X - X) / (X * Real.sqrt X)) +
      (6 * Real.log (8 * X) / Real.sqrt X +
        (5 * Real.log (8 * X) + 3) * (4 * X - 2 * X) / (X * Real.sqrt X)) +
      (6 * Real.log (8 * X) / Real.sqrt X +
        (5 * Real.log (8 * X) + 3) * (8 * X - 4 * X) / (X * Real.sqrt X)) =
      (53 * Real.log (8 * X) + 21) / Real.sqrt X := by
    field_simp
    ring
  exact htri.trans (hsumerr.trans_eq hconstant)

/-- The logarithmically weighted packet can equivalently be summed over
its full positive prefix, keeping the continuous density moment explicit. -/
theorem suzukiLocalPhysicalKernel_log_prefix_sampling_error_le {X q : ℝ}
    (hX : 1 ≤ X) (hq : 1 ≤ q) (hqX : q ≤ X) :
    |(∑ n ∈ Finset.Icc 1 ⌊8 * X / q⌋₊,
      suzukiLocalPhysicalKernel X (q * n) * Real.log n) -
      (∫ x in X / q..8 * X / q, suzukiLocalPhysicalKernel X (q * x) * Real.log x)| ≤
      (53 * Real.log (8 * X) + 21) / Real.sqrt X := by
  have hX0 := zero_lt_one.trans_le hX
  have hq0 := zero_lt_one.trans_le hq
  have hAB : ⌊X / q⌋₊ ≤ ⌊8 * X / q⌋₊ :=
    Nat.floor_le_floor ((div_le_div_iff_of_pos_right hq0).mpr (by linarith))
  have hz : (∑ n ∈ Finset.Ioc 0 ⌊X / q⌋₊,
      suzukiLocalPhysicalKernel X (q * n) * Real.log n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' : (n : ℝ) ≤ X / q :=
      (Nat.le_floor_iff (div_nonneg hX0.le hq0.le)).mp (Finset.mem_Ioc.mp hn).2
    have hy : q * n ≤ X := by
      have hh := (le_div_iff₀ hq0).mp hn'
      nlinarith
    rw [suzukiLocalPhysicalKernel_eq_zero_of_le hX0 hy, zero_mul]
  have he := Finset.sum_Ioc_consecutive
    (fun n : ℕ => suzukiLocalPhysicalKernel X (q * n) * Real.log n)
    (Nat.zero_le ⌊X / q⌋₊) hAB
  rw [hz, zero_add] at he
  have hset : Finset.Ioc 0 ⌊8 * X / q⌋₊ = Finset.Icc 1 ⌊8 * X / q⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset] at he
  rw [← he]
  exact suzukiLocalPhysicalKernel_log_lattice_sampling_error_le hX hq hqX

/-- The actual logarithmic Type-I sector of Vaughan's identity. Both
integer factors and the complete compact product cutoff are literal. -/
def suzukiLocalVaughanSmallLog (X : ℝ) (U : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioc 0 U, (ArithmeticFunction.moebius d : ℝ) *
    ∑ m ∈ Finset.Icc 1 ⌊8 * X / d⌋₊,
      suzukiLocalPhysicalKernel X ((d : ℝ) * m) * Real.log m

/-- The complete logarithmic Type-I sector differs from its genuine,
nonzero signed density moment by a controlled arithmetic error. The
Möbius reciprocal prefix in that main term is retained exactly. -/
theorem suzukiLocalVaughanSmallLog_sub_main_abs_le {X : ℝ} (hX : 1 ≤ X) (U : ℕ)
    (hUX : (U : ℝ) ≤ X) :
    |suzukiLocalVaughanSmallLog X U -
      (-4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2 - 1) ^ 2) * Real.sqrt X *
        ∑ d ∈ Finset.Ioc 0 U, (ArithmeticFunction.moebius d : ℝ) / d| ≤
      U * (53 * Real.log (8 * X) + 21) / Real.sqrt X := by
  let J := -4 * Real.log 2 * Real.sqrt 2 * (Real.sqrt 2 - 1) ^ 2
  let E := (53 * Real.log (8 * X) + 21) / Real.sqrt X
  have hX0 := zero_lt_one.trans_le hX
  have hterm : ∀ d ∈ Finset.Ioc 0 U,
      |(ArithmeticFunction.moebius d : ℝ) *
        ((∑ m ∈ Finset.Icc 1 ⌊8 * X / d⌋₊,
          suzukiLocalPhysicalKernel X ((d : ℝ) * m) * Real.log m) - J * Real.sqrt X / d)| ≤ E := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_Ioc.mp hd).1
    have hdX : (d : ℝ) ≤ X := (by exact_mod_cast (Finset.mem_Ioc.mp hd).2 : (d : ℝ) ≤ U).trans hUX
    have hs := suzukiLocalPhysicalKernel_log_prefix_sampling_error_le hX hd1 hdX
    rw [suzukiLocalPhysicalKernel_scaled_log_integral hX0 hd0] at hs
    have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [abs_mul]
    exact (mul_le_mul hμ hs (abs_nonneg _) (by norm_num)).trans_eq (one_mul E)
  have he : suzukiLocalVaughanSmallLog X U - J * Real.sqrt X *
      (∑ d ∈ Finset.Ioc 0 U, (ArithmeticFunction.moebius d : ℝ) / d) =
      ∑ d ∈ Finset.Ioc 0 U, (ArithmeticFunction.moebius d : ℝ) *
        ((∑ m ∈ Finset.Icc 1 ⌊8 * X / d⌋₊,
          suzukiLocalPhysicalKernel X ((d : ℝ) * m) * Real.log m) - J * Real.sqrt X / d) := by
    unfold suzukiLocalVaughanSmallLog
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  change |suzukiLocalVaughanSmallLog X U - J * Real.sqrt X *
      (∑ d ∈ Finset.Ioc 0 U, (ArithmeticFunction.moebius d : ℝ) / d)| ≤ _
  rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 U,
        |(ArithmeticFunction.moebius d : ℝ) *
          ((∑ m ∈ Finset.Icc 1 ⌊8 * X / d⌋₊,
            suzukiLocalPhysicalKernel X ((d : ℝ) * m) * Real.log m) - J * Real.sqrt X / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Ioc 0 U, E := Finset.sum_le_sum hterm
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      dsimp [E]
      ring

end
end RiemannGaussian
