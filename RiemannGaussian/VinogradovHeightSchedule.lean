/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNearOneBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A joint height schedule for the actual Vinogradov estimate

At logarithmic height L, use floor((L/log L)^(1/3)). The same natural
index pays the cubic growth exponent, reciprocal analytic radius and
original degree-dependent height threshold. No fixed-index limit is
substituted at the moving index.
-/

namespace RiemannGaussian.VinogradovHeightSchedule
noncomputable section
open Filter VinogradovNearOneBudget VinogradovScaleSelection
open scoped Topology

/-- The continuous balanced degree at logarithmic height L. -/
def size (L : ℝ) : ℝ := (L / Real.log L) ^ (1 / 3 : ℝ)

/-- The actual natural degree used in every downstream estimate. -/
def index (L : ℝ) : ℕ := ⌊size L⌋₊

/-- The balanced degree grows without bound. -/
theorem size_atTop : Tendsto size atTop atTop := by
  have hratio : Tendsto (fun L : ℝ ↦ L / Real.log L) atTop atTop := by
    have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hpos : ∀ᶠ L : ℝ in atTop, 0 < Real.log L / L := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
      exact div_pos (Real.log_pos hL) (by linarith)
    have hinv := tendsto_inv_nhdsGT_zero.comp
      ((tendsto_nhdsWithin_iff.mpr ⟨h, hpos⟩) :
        Tendsto (fun L : ℝ ↦ Real.log L / L) atTop (𝓝[>] 0))
    simpa only [Function.comp_def, inv_div] using hinv
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hratio

/-- The actual rounded degree grows without bound. -/
theorem index_atTop : Tendsto index atTop atTop := tendsto_nat_floor_atTop.comp size_atTop

/-- The defining cubic balance is exact on the positive-log range. -/
theorem size_cube {L : ℝ} (hL : 1 < L) : size L ^ 3 = L / Real.log L := by
  unfold size
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity [Real.log_pos hL])]
  norm_num

/-- Natural rounding loses at most a factor two once the size is at least two. -/
theorem rounding {L : ℝ} (hL : 2 ≤ size L) :
    1 ≤ index L ∧ (index L : ℝ) ≤ size L ∧ size L ≤ 2 * (index L : ℝ) := by
  have hi : 1 ≤ index L := (Nat.le_floor_iff (by linarith : 0 ≤ size L)).mpr
    (by norm_num; linarith)
  have hf := Nat.floor_le (show 0 ≤ size L by linarith)
  have hlt := Nat.lt_floor_add_one (size L)
  change size L < (index L : ℝ) + 1 at hlt
  have hir : (1 : ℝ) ≤ index L := by exact_mod_cast hi
  exact ⟨hi, hf, by linarith⟩

/-- Above a unit second logarithm, the degree is below both the cube root
and the full logarithmic height. -/
theorem size_upper {L : ℝ} (hL : 1 ≤ L) (hl : 1 ≤ Real.log L) :
    size L ≤ L ^ (1 / 3 : ℝ) ∧ size L ≤ L := by
  have hdiv : L / Real.log L ≤ L := (div_le_iff₀ (by linarith)).mpr (by nlinarith)
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ L / Real.log L) hdiv
    (by norm_num : (0 : ℝ) ≤ 1 / 3)
  refine ⟨h, h.trans ?_⟩
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
    (by norm_num : (1 / 3 : ℝ) ≤ 1)

/-- A convenient cubic majorant for the actual height exponent. -/
theorem growth_cubic_bound {n : ℕ} (hn : 1 ≤ n) :
    growth n * (8 * (n : ℝ) ^ 3) ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : growth n * (8 * (n : ℝ) ^ 3) =
      (n : ℝ) ^ 2 / (4096 * (2 * (n : ℝ) + 1) ^ 2) := by
    unfold growth delta
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < 4096 * (2 * (n : ℝ) + 1) ^ 2)).mpr
  nlinarith [sq_nonneg (n : ℝ)]

/-- The scheduled height-growth cost is bounded by one second logarithm. -/
theorem growth_mul_le {L : ℝ} (hL : 1 < L) (hs : 2 ≤ size L) :
    growth (index L) * L ≤ Real.log L := by
  obtain ⟨hi, _, hr⟩ := rounding hs
  have hg := growth_pos hi
  have hp : size L ^ 3 ≤ 8 * (index L : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ size L) hr 3
    nlinarith only [h]
  have h := (mul_le_mul_of_nonneg_left hp hg.le).trans (growth_cubic_bound hi)
  rw [size_cube hL] at h
  have hl := Real.log_pos hL
  calc
    growth (index L) * L = (growth (index L) * (L / Real.log L)) * Real.log L := by
      field_simp
    _ ≤ 1 * Real.log L := mul_le_mul_of_nonneg_right h hl.le
    _ = _ := one_mul _

/-- The full reciprocal radius is paid by the square of the balanced degree. -/
theorem inverse_delta_le {L : ℝ} (hs : 2 ≤ size L) :
    1 / delta (index L) ≤ 589824 * size L ^ 2 := by
  obtain ⟨hi, hf, _⟩ := rounding hs
  have hir : (1 : ℝ) ≤ index L := by exact_mod_cast hi
  have hsq : (2 * (index L : ℝ) + 1) ^ 2 ≤ 9 * size L ^ 2 := by
    have h : 2 * (index L : ℝ) + 1 ≤ 3 * size L := by linarith
    nlinarith [sq_nonneg (3 * size L - (2 * (index L : ℝ) + 1))]
  simp only [delta, one_div_one_div]
  nlinarith

/-- The complete logarithmic radius cost is at most two second logarithms
plus a fixed numerical constant. -/
theorem log_inverse_delta_le {L : ℝ} (hL : 1 ≤ L) (hl : 1 ≤ Real.log L)
    (hs : 2 ≤ size L) :
    Real.log (1 / delta (index L)) ≤ Real.log 589824 + 2 * Real.log L := by
  have hsize := (size_upper hL hl).2
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ size L) hsize 2
  have h := (inverse_delta_le hs).trans
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 589824))
  have hh := Real.log_le_log (by positivity [delta_pos (index L)]) h
  rw [Real.log_mul (by norm_num : (589824 : ℝ) ≠ 0)
    (pow_pos (by linarith : 0 < L) 2).ne', Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

/-- The logarithm of the original height threshold is bounded along the
same moving index, including its full polynomial base and exponent. -/
theorem log_threshold_le {L : ℝ} (hL : 1 ≤ L) (hl : 1 ≤ Real.log L)
    (hs : 2 ≤ size L) :
    Real.log (heightThreshold (index L)) ≤
      2 * L ^ (1 / 3 : ℝ) * (Real.log 144 + 2 * Real.log L) := by
  obtain ⟨_, hf, _⟩ := rounding hs
  obtain ⟨hcube, hsize⟩ := size_upper hL hl
  have hbpos : (0 : ℝ) < rootBase (index L) := by
    have h : (16 : ℝ) ≤ rootBase (index L) := by exact_mod_cast rootBase_ge_sixteen _
    linarith
  have hb : (rootBase (index L) : ℝ) ≤ 144 * L ^ 2 := by
    have hi := hf.trans hsize
    have h : 2 * (index L : ℝ) + 1 ≤ 3 * L := by linarith
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (index L : ℝ) + 1) h 2
    simp only [rootBase, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one]
    nlinarith
  have hbLog := Real.log_le_log hbpos hb
  rw [Real.log_mul (by norm_num : (144 : ℝ) ≠ 0)
    (pow_pos (by linarith : 0 < L) 2).ne', Real.log_pow] at hbLog
  norm_num only [Nat.cast_ofNat] at hbLog
  have hlog0 : 0 ≤ Real.log (rootBase (index L)) := Real.log_nonneg (by
    have h : (16 : ℝ) ≤ rootBase (index L) := by exact_mod_cast rootBase_ge_sixteen _
    linarith)
  simp only [heightThreshold, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  exact mul_le_mul (by linarith [hf.trans hcube]) hbLog hlog0 (by positivity)

/-- The complete logarithmic threshold is sublinear in logarithmic height.
This limit controls the actual moving index, rather than a fixed degree. -/
theorem threshold_envelope_tendsto :
    Tendsto (fun L : ℝ ↦
      2 * L ^ (1 / 3 : ℝ) * (Real.log 144 + 2 * Real.log L) / L) atTop (𝓝 0) := by
  have hc := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).const_div_atTop
    (Real.log 144)
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
  have h := (hc.add (hl.const_mul 2)).const_mul 2
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  simp only [show (2 / 3 : ℝ) = 1 - 1 / 3 by norm_num, Real.rpow_sub hL,
    Real.rpow_one]
  field_simp

/-- Eventually every original degree condition is available and its
height threshold is at most exp(L/2), on the single balanced schedule. -/
theorem eventually_threshold : ∀ᶠ L : ℝ in atTop,
    12 ≤ index L ∧ 1 ≤ Real.log L ∧ 2 ≤ size L ∧
      (heightThreshold (index L) : ℝ) ≤ Real.exp (L / 2) := by
  filter_upwards [index_atTop.eventually (eventually_ge_atTop 12),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    size_atTop.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_gt_atTop (1 : ℝ),
    threshold_envelope_tendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with L hi hl hs hL hc
  refine ⟨hi, hl, hs, ?_⟩
  have henv : 2 * L ^ (1 / 3 : ℝ) * (Real.log 144 + 2 * Real.log L) ≤ L / 2 := by
    have h := (div_lt_iff₀ (by linarith : 0 < L)).mp hc
    linarith
  have ht := (log_threshold_le hL.le hl hs).trans henv
  have hpos : (0 : ℝ) < heightThreshold (index L) := by
    have hbase : (0 : ℝ) < rootBase (index L) := by
      have h : (16 : ℝ) ≤ rootBase (index L) := by exact_mod_cast rootBase_ge_sixteen _
      linarith
    simpa only [heightThreshold, Nat.cast_pow] using pow_pos hbase (2 * index L)
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr ht

/-- The balanced radius cost has exactly the classical two-thirds and
one-third logarithmic powers. -/
theorem balanced_identity {L : ℝ} (hL : 1 < L) :
    size L ^ 2 * Real.log L = L ^ (2 / 3 : ℝ) * Real.log L ^ (1 / 3 : ℝ) := by
  have hLp : 0 < L := by linarith
  have hl := Real.log_pos hL
  unfold size
  rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hLp.le hl.le)]
  norm_num only [Nat.cast_ofNat, show (1 / 3 : ℝ) * 2 = 2 / 3 by norm_num]
  rw [Real.div_rpow hLp.le hl.le]
  have he : Real.log L = Real.log L ^ (2 / 3 : ℝ) * Real.log L ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hl]
    norm_num
  calc
    _ = (L ^ (2 / 3 : ℝ) / Real.log L ^ (2 / 3 : ℝ)) *
        (Real.log L ^ (2 / 3 : ℝ) * Real.log L ^ (1 / 3 : ℝ)) := by rw [← he]
    _ = _ := by field_simp

end
end RiemannGaussian.VinogradovHeightSchedule
