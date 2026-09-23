/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDyadic

/-!
# Explicit degree and root-scale selection for the middle blocks

The degree is the integer part of log(t)/(2log(M)), plus one. A fixed
polynomial base and its displayed height power pay the original moment
order. Every parameter belongs to the existing actual Dirichlet estimate;
no degree-selection or moment hypothesis is hidden in the result.
-/

namespace RiemannGaussian.VinogradovScaleSelection
noncomputable section
open VinogradovDyadic

/-- A polynomial root scale pays every degree through 2n+1. -/
def rootBase (n : ℕ) : ℕ := 16 * (2 * n + 1) ^ 2

/-- The explicit physical height beyond which the middle-scale selection works. -/
def heightThreshold (n : ℕ) : ℕ := rootBase n ^ (2 * n)

/-- The root base is at least sixteen, including the unused zero index. -/
theorem rootBase_ge_sixteen (n : ℕ) : 16 ≤ rootBase n := by
  have h : 1 ≤ (2 * n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold rootBase
  omega

/-- Every positive target index has a height threshold above its root base. -/
theorem rootBase_le_heightThreshold {n : ℕ} (hn : 1 ≤ n) : rootBase n ≤ heightThreshold n :=
  Nat.le_self_pow (by omega : 2 * n ≠ 0) _

/-- The floor-defined degree lies in the required original time
rectangle and pays its actual tuple order, with no selection premise. -/
theorem exists_degree {n M : ℕ} {t : ℝ} (hM : 1 < M)
    (hsize : (7 * (2 * n + 1) + 1) * (2 * n + 1) ≤ M)
    (ht : 0 < t) (hlo : (M : ℝ) ^ 22 ≤ t)
    (hlog : Real.log t ≤ 4 * (n : ℝ) * Real.log M) :
    ∃ k : ℕ, 12 ≤ k ∧ k ≤ 2 * n + 1 ∧ (7 * k + 1) * k ≤ M ∧
      (M : ℝ) ^ (2 * k - 2) ≤ t ∧ t ≤ (M : ℝ) ^ (2 * k) := by
  have hMr : (1 : ℝ) < M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlM : 0 < Real.log M := Real.log_pos hMr
  let a := Real.log t / (2 * Real.log M)
  have halower : 11 ≤ a := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Real.log (M : ℝ))).mpr
    have h := Real.log_le_log (pow_pos hM0 22) hlo
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith
  have haupper : a ≤ 2 * (n : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log (M : ℝ))).mpr
    nlinarith only [hlog]
  let k := ⌊a⌋₊ + 1
  have hklo : 12 ≤ k := by
    have h : 11 ≤ ⌊a⌋₊ := (Nat.le_floor_iff (by linarith : 0 ≤ a)).mpr (by exact_mod_cast halower)
    omega
  have hfloor := Nat.floor_le (show 0 ≤ a by linarith)
  have hkup : k ≤ 2 * n + 1 := by
    have h : ⌊a⌋₊ ≤ 2 * n := by exact_mod_cast hfloor.trans haupper
    omega
  have hsize' : (7 * k + 1) * k ≤ M := by
    apply le_trans _ hsize
    exact Nat.mul_le_mul (by omega) hkup
  refine ⟨k, hklo, hkup, hsize', ?_, ?_⟩
  · apply (Real.log_le_log_iff (pow_pos hM0 _) ht).mp
    rw [Real.log_pow]
    have h := (le_div_iff₀ (by positivity : 0 < 2 * Real.log (M : ℝ))).mp hfloor
    have he : ((2 * k - 2 : ℕ) : ℝ) = 2 * (⌊a⌋₊ : ℝ) := by
      dsimp only [k]
      have hn : 2 * (⌊a⌋₊ + 1) - 2 = 2 * ⌊a⌋₊ := by omega
      rw [hn]
      push_cast
      rfl
    rw [he]
    linarith
  · apply (Real.log_le_log_iff ht (pow_pos hM0 _)).mp
    rw [Real.log_pow]
    have ha : a < (k : ℝ) := by
      simpa only [k, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one a
    have hh := (div_lt_iff₀ (by positivity : 0 < 2 * Real.log (M : ℝ))).mp ha
    push_cast
    nlinarith only [hh]

/-- Every physical block in the middle window has an eligible integer
fourth root and degree, beyond one explicit height threshold. -/
theorem exists_window_parameters (n X : ℕ) (hn : 12 ≤ n) {t : ℝ}
    (ht : (heightThreshold n : ℝ) ≤ t)
    (hlo : t ^ (2 / (n : ℝ)) ≤ X) (hhi : (X : ℝ) ≤ t ^ (2 / 11 : ℝ)) :
    ∃ k M : ℕ, 12 ≤ k ∧ k ≤ 2 * n + 1 ∧ (7 * k + 1) * k ≤ M ∧
      M ^ 4 ≤ X ∧ X ≤ 2 * M ^ 4 ∧
      (M : ℝ) ^ (2 * k - 2) ≤ t ∧ t ≤ (M : ℝ) ^ (2 * k) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb : (16 : ℝ) ≤ rootBase n := by exact_mod_cast rootBase_ge_sixteen n
  have hbt : (rootBase n : ℝ) ≤ t := by
    have hbT : (rootBase n : ℝ) ≤ heightThreshold n := by
      exact_mod_cast rootBase_le_heightThreshold (show 1 ≤ n by omega)
    exact hbT.trans ht
  have htpos : 0 < t := by linarith
  have hbpos : (0 : ℝ) < rootBase n := by linarith
  have hroot : (rootBase n : ℝ) ^ 4 ≤ X := by
    have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ heightThreshold n)
      ht (by positivity : 0 ≤ 2 / (n : ℝ))
    have he : (heightThreshold n : ℝ) ^ (2 / (n : ℝ)) = (rootBase n : ℝ) ^ 4 := by
      simp only [heightThreshold, Nat.cast_pow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbpos.le]
      have hex : ((2 * n : ℕ) : ℝ) * (2 / (n : ℝ)) = (4 : ℕ) := by
        push_cast
        field_simp
        norm_num
      rw [hex, Real.rpow_natCast]
    rw [he] at hp
    exact hp.trans hlo
  let M := Nat.nthRoot 4 X
  have hbM : rootBase n ≤ M := by
    apply (Nat.le_nthRoot_iff (by norm_num : (4 : ℕ) ≠ 0)).mpr
    exact_mod_cast hroot
  have hM16 : 16 ≤ M := (rootBase_ge_sixteen n).trans hbM
  have hMr : (16 : ℝ) ≤ M := by exact_mod_cast hM16
  have hMpos : (0 : ℝ) < M := by linarith
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  obtain ⟨hMX, hXM⟩ := fourth_root_window X (by change 6 ≤ M; omega)
  have hMXr : (M : ℝ) ^ 4 ≤ X := by exact_mod_cast hMX
  have hXMr : (X : ℝ) ≤ 2 * (M : ℝ) ^ 4 := by exact_mod_cast hXM
  have hXpos : (0 : ℝ) < X := (pow_pos hMpos 4).trans_le hMXr
  have hsize : (7 * (2 * n + 1) + 1) * (2 * n + 1) ≤ M := by
    apply le_trans _ hbM
    unfold rootBase
    nlinarith
  have htime : (M : ℝ) ^ 22 ≤ t := by
    apply (Real.log_le_log_iff (pow_pos hMpos _) htpos).mp
    have hl := Real.log_le_log (pow_pos hMpos 4) (hMXr.trans hhi)
    rw [Real.log_pow, Real.log_rpow htpos] at hl
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat] at hl ⊢
    linarith
  have hlog : Real.log t ≤ 4 * (n : ℝ) * Real.log M := by
    have hl := Real.log_le_log (Real.rpow_pos_of_pos htpos _) hlo
    rw [Real.log_rpow htpos] at hl
    have hu := Real.log_le_log hXpos hXMr
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 4 hMpos.ne'),
      Real.log_pow] at hu
    have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ M by linarith)
    have hh : (2 * Real.log t) / (n : ℝ) ≤ 8 * Real.log M := by
      norm_num only [Nat.cast_ofNat] at hu
      rw [show 2 * Real.log t / (n : ℝ) = 2 / (n : ℝ) * Real.log t by ring]
      linarith
    have hh' := (div_le_iff₀ hnpos).mp hh
    nlinarith
  obtain ⟨k, hk, hkn, hkr, hkt, htk⟩ :=
    exists_degree (by omega : 1 < M) hsize htpos htime hlog
  exact ⟨k, M, hk, hkn, hkr, hMX, hXM, hkt, htk⟩

end
end RiemannGaussian.VinogradovScaleSelection
