import RiemannGaussian.SuzukiLocalCancellationExplicitBound
import RiemannGaussian.SuzukiLocalCancellationSampling
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Fine-lattice cancellation for the local Suzuki packet

The logarithmic hinge primitive of the integer lattice is a log factorial.
Robbins' bound controls its drift across the whole packet. Removing the
affine and density terms before applying the twice-Abel estimate gains a
factor of the lattice spacing divided by the cutoff.
-/

namespace RiemannGaussian
noncomputable section
open Set

private theorem logFactorialSum (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, Real.log m = Real.log (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : insert (n+1) (Finset.Icc 1 n) = Finset.Icc 1 (n+1) := by
      ext k
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [← he]
    rw [Finset.sum_insert (by simp), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]

private theorem gridHinge_eq {y : ℝ} (hy : 1 ≤ y) {N : ℕ} (hN : ⌊y⌋₊ ≤ N) :
    (∑ m ∈ Finset.Icc 1 N, max (Real.log y - Real.log m) 0) =
      (⌊y⌋₊ : ℝ) * Real.log y - Real.log (⌊y⌋₊.factorial : ℝ) := by
  have hcut : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_right hN
  rw [← Finset.sum_subset hcut (fun m hm hsmall => ?_)]
  · calc
      _ = ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (Real.log y - Real.log m) := by
        apply Finset.sum_congr rfl
        intro m hm
        obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
        have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
        exact max_eq_left (sub_nonneg.mpr (Real.log_le_log hmpos
          ((Nat.le_floor_iff (by linarith)).mp hm2)))
      _ = _ := by
        rw [Finset.sum_sub_distrib, logFactorialSum]
        simp
  · have hlt : ⌊y⌋₊ < m := by
      have hm1 := (Finset.mem_Icc.mp hm).1
      exact lt_of_not_ge (fun hh => hsmall (Finset.mem_Icc.mpr ⟨hm1, hh⟩))
    exact max_eq_right (sub_nonpos.mpr (Real.log_le_log (by linarith)
      (lt_of_not_ge (fun h => (not_le_of_gt hlt) ((Nat.le_floor_iff (by linarith)).mpr h))).le))

private theorem stirling_drift {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    0 ≤ Real.log (Stirling.stirlingSeq m) - Real.log (Stirling.stirlingSeq n) ∧
      Real.log (Stirling.stirlingSeq m) - Real.log (Stirling.stirlingSeq n) ≤
        1 / (12 * (m : ℝ)) - 1 / (12 * (n : ℝ)) := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hstep := Stirling.log_stirlingSeq_sdiff_le n
    have hdec : Real.log (Stirling.stirlingSeq (n + 1)) ≤
        Real.log (Stirling.stirlingSeq n) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact Stirling.log_stirlingSeq'_antitone (show k ≤ k + 1 by omega)
    have hid : 1 / (12 * (n : ℝ) * (n + 1)) =
        1 / (12 * (n : ℝ)) - 1 / (12 * (n + 1 : ℝ)) := by
      field_simp
      ring
    rw [hid] at hstep
    push_cast
    constructor <;> linarith [ih.1, ih.2]

/-- Uniform error for the logarithmic lattice primitive on any interval
starting at an integer m. The same affine normalization works at every y. -/
private theorem gridHinge_remainder {m N : ℕ} (hm : 1 ≤ m) {y : ℝ}
    (hmy : (m : ℝ) ≤ y) (hN : ⌊y⌋₊ ≤ N) :
    |(∑ k ∈ Finset.Icc 1 N, max (Real.log y - Real.log k) 0) -
      (y - (Real.log 2 / 2 + Real.log (Stirling.stirlingSeq m)) - Real.log y / 2)| ≤
      2 / (m : ℝ) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hy : 1 ≤ y := hm1.trans hmy
  let n := ⌊y⌋₊
  have hmn : m ≤ n := (Nat.le_floor_iff (by linarith)).mpr hmy
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hm.trans hmn
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0 : 0 < y := by linarith
  have hny : (n : ℝ) ≤ y := Nat.floor_le hy0.le
  have hyn : y < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hratio : 0 ≤ Real.log y - Real.log n := sub_nonneg.mpr (Real.log_le_log hn0 hny)
  have hup := Real.log_le_sub_one_of_pos (div_pos hy0 hn0)
  rw [Real.log_div hy0.ne' hn0.ne'] at hup
  have hlo := Real.log_le_sub_one_of_pos (div_pos hn0 hy0)
  rw [Real.log_div hn0.ne' hy0.ne'] at hlo
  have h1 : (n : ℝ) * (Real.log y - Real.log n) ≤ y - n := by
    have h := mul_le_mul_of_nonneg_right hup hn0.le
    simp only [sub_mul, div_mul_cancel₀ _ hn0.ne', one_mul] at h
    linarith
  have h2 : y - n ≤ y * (Real.log y - Real.log n) := by
    have h := mul_le_mul_of_nonneg_right hlo hy0.le
    simp only [sub_mul, div_mul_cancel₀ _ hy0.ne', one_mul] at h
    linarith
  have hlog : Real.log y - Real.log n ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hn0).mpr
    linarith
  have hround : |((n : ℝ) + 1 / 2) * (Real.log y - Real.log n) - (y - n)| ≤ 1 / (n : ℝ) := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ) + 1 - y) hratio]
  have hst := Stirling.log_stirlingSeq_formula n
  rw [Real.log_div hn0.ne' (Real.exp_pos _).ne', Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne'] at hst
  have hd := stirling_drift hm hmn
  have hnm : 1 / (n : ℝ) ≤ 1 / (m : ℝ) := by
    exact one_div_le_one_div_of_le (by linarith) (by exact_mod_cast hmn)
  rw [gridHinge_eq hy hN]
  change |(n : ℝ) * Real.log y - Real.log (n.factorial : ℝ) - _| ≤ _
  rw [abs_le] at hround ⊢
  have h12 : 1 / (12 * (m : ℝ)) ≤ 1 / (m : ℝ) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have h12n : 0 ≤ 1 / (12 * (n : ℝ)) := by positivity
  rw [show (2 : ℝ) / m = 1 / m + 1 / m by ring]
  constructor <;> linarith [hd.1, hd.2, hround.1, hround.2]

private theorem unit_grid_estimate {Y : ℝ} (hY : 1 ≤ Y) :
    |∑ k ∈ Finset.Icc 1 ⌊8 * Y⌋₊, suzukiLocalPhysicalKernel Y k| ≤
      96 / (Y * Real.sqrt Y) := by
  let m := ⌊Y⌋₊
  have hY0 : 0 < Y := by linarith
  have hm : 1 ≤ m := (Nat.le_floor_iff hY0.le).mpr (by simpa using hY)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb := abs_suzukiLocal_atomic_sum_le
    (Finset.Icc 1 ⌊8 * Y⌋₊) (fun k : ℕ => Real.log k)
    (t := Real.log Y) (a := -(Real.log 2 / 2 + Real.log (Stirling.stirlingSeq m)))
    (b := -1/2) (B := 2 / (m : ℝ)) (by positivity) (by
      intro s hs
      have hy : Y ≤ Real.exp s := (Real.log_le_iff_le_exp hY0).mp hs.1
      have hy8 : Real.exp s ≤ 8 * Y := by
        have hh := Real.exp_le_exp.mpr hs.2
        rw [Real.exp_add, Real.exp_log hY0, show 3 * Real.log 2 = Real.log 2 + Real.log 2 + Real.log 2 by ring,
          Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
        linarith
      have hh := gridHinge_remainder hm ((Nat.floor_le hY0.le).trans hy) (Nat.floor_le_floor hy8)
      rw [Real.log_exp] at hh
      convert hh using 2
      ring)
  have hid (k : ℕ) (hk : k ∈ Finset.Icc 1 ⌊8 * Y⌋₊) :
      suzukiLocalPhysicalKernel Y k = Real.exp (-(Real.log k) / 2) *
        suzukiLocalSignedKernel (Real.log k - Real.log Y) := by
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    rw [suzukiLocalPhysicalKernel, Real.log_div hk0.ne' hY0.ne', neg_div, Real.exp_neg,
      Real.exp_half, Real.exp_log hk0]
    ring
  rw [Finset.sum_congr rfl hid]
  rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log hY0] at hb
  apply hb.trans
  have hYm : Y ≤ 2 * (m : ℝ) := by linarith [Nat.lt_floor_add_one Y]
  have hm0 : (0 : ℝ) < m := by linarith
  have hs0 := Real.sqrt_pos.mpr hY0
  field_simp
  linarith

/-- Dilation in the physical variable changes the base and the square-root weight. -/
theorem suzukiLocalPhysicalKernel_mul_eq {X q : ℝ} (hX : 0 < X) (hq : 0 < q) (y : ℝ) :
    suzukiLocalPhysicalKernel X (q * y) =
      (Real.sqrt q)⁻¹ * suzukiLocalPhysicalKernel (X / q) y := by
  unfold suzukiLocalPhysicalKernel
  rw [Real.sqrt_mul hq.le, show q * y / X = y / (X / q) by field]
  ring

/-- The complete signed lattice packet gains a factor q/X on a fine grid.
The bound holds for every positive real spacing, including q above X. -/
theorem suzukiLocalPhysicalKernel_prefix_sum_abs_le_spacing {X q : ℝ}
    (hX : 0 < X) (hq : 0 < q) :
    |∑ k ∈ Finset.Icc 1 ⌊8 * X / q⌋₊, suzukiLocalPhysicalKernel X (q * k)| ≤
      96 * q / (X * Real.sqrt X) := by
  have hsX := Real.sqrt_pos.mpr hX
  by_cases hqX : q ≤ X
  · have hY : 1 ≤ X / q := (one_le_div hq).mpr hqX
    have hh := unit_grid_estimate hY
    rw [← mul_div_assoc] at hh
    simp_rw [suzukiLocalPhysicalKernel_mul_eq hX hq]
    rw [← Finset.mul_sum, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt q)⁻¹)]
    refine (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq ?_
    rw [Real.sqrt_div hX.le]
    field_simp
  · apply (suzukiLocalPhysicalKernel_prefix_sum_abs_le hX hq).trans
    field_simp
    linarith

/-- A spacing-sensitive estimate for the complete small-factor Vaughan cross term. -/
theorem suzukiLocalVaughanSmallCross_abs_le_squared_product {X : ℝ}
    (hX : 0 < X) (U V : ℕ) :
    |suzukiLocalVaughanSmallCross X U V| ≤
      576 * ((U : ℝ) * V) ^ 2 / (X * Real.sqrt X) := by
  let E := 96 * ((U : ℝ) * V) / (X * Real.sqrt X)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have ht (d : ℕ) (hd : d ∈ Finset.Ioc 0 U) (l : ℕ) (hl : l ∈ Finset.Ioc 0 V) :
      |(ArithmeticFunction.moebius d : ℝ) * ArithmeticFunction.vonMangoldt l *
        (∑ k ∈ Finset.Icc 1 ⌊8 * X / ((d : ℝ) * l)⌋₊,
          suzukiLocalPhysicalKernel X ((d : ℝ) * l * k))| ≤
        ArithmeticFunction.vonMangoldt l * E := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Ioc.mp hd).1
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (Finset.mem_Ioc.mp hl).1
    have hprod : (d : ℝ) * l ≤ (U : ℝ) * V := by
      gcongr <;> exact_mod_cast (Finset.mem_Ioc.mp ‹_›).2
    have hgrid := suzukiLocalPhysicalKernel_prefix_sum_abs_le_spacing hX (mul_pos hd0 hl0)
    have hcost : 96 * ((d : ℝ) * l) / (X * Real.sqrt X) ≤ E := by
      dsimp [E]
      gcongr
    have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    rw [abs_mul, abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    calc
      _ ≤ 1 * ArithmeticFunction.vonMangoldt l * E := by gcongr; exact hgrid.trans hcost
      _ = _ := by rw [one_mul]
  have hψ : Chebyshev.psi (V : ℝ) ≤ 6 * V := by
    rcases eq_or_ne V 0 with rfl | h
    · simp [Chebyshev.psi]
    · exact chebyshevPsi_le_six_mul_self_of_one_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 U, ∑ l ∈ Finset.Ioc 0 V,
        ArithmeticFunction.vonMangoldt l * E := by
      unfold suzukiLocalVaughanSmallCross
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (ht d hd))
    _ = (U : ℝ) * Chebyshev.psi V * E := by
      simp only [← Finset.sum_mul, Chebyshev.psi, Nat.floor_natCast,
        Finset.sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_assoc]
    _ ≤ (U : ℝ) * (6 * V) * E := by gcongr
    _ = _ := by dsimp [E]; ring

/-- Uniform cost whenever the product of the two integer cutoffs is at
most the three-quarter power of the physical scale. -/
theorem suzukiLocalVaughanSmallCross_abs_le_of_product_le_three_quarters
    {X : ℝ} (hX : 0 < X) (U V : ℕ) (hUV : (U : ℝ) * V ≤ X ^ (3/4 : ℝ)) :
    |suzukiLocalVaughanSmallCross X U V| ≤ 576 := by
  apply (suzukiLocalVaughanSmallCross_abs_le_squared_product hX U V).trans
  have hh := pow_le_pow_left₀ (by positivity) hUV 2
  rw [← Real.rpow_mul_natCast hX.le, Nat.cast_ofNat,
    show (3/4 : ℝ) * 2 = 1 + 1/2 by norm_num, Real.rpow_add hX,
    Real.rpow_one, ← Real.sqrt_eq_rpow] at hh
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

end
end RiemannGaussian
