/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovRosserPrimeSupply
import RiemannGaussian.RosserSchoenfeldLargePrimeCounting

/-!
# Actual Ford prime packets in the proved large range

The large-range count theorem supplies literal prime packets whenever the
original published base is at least exp(5100). In particular, the unchanged
ShortPrimeSupply statement is proved throughout the original width range
when log(k) >= 1700. This does not assert the all-degree literature target.
The remaining global count premise is confined to (16000,exp(5100)).
-/

namespace RiemannGaussian.VinogradovRosserLargeSupply
noncomputable section
open Real RosserSchoenfeldComparison VinogradovFordGlobalStep
open VinogradovFordTailThreshold VinogradovRosserPrimeSupply

/-- Only the bounded intermediate count interval remains for the full original
prime-supply target. Both outside ranges have been proved independently. -/
theorem shortPrimeSupply_of_intermediate_counts (k : ℕ) {w : ℝ} (hk : 26 ≤ k)
    (hw : 0 < w) (hw' : w ≤ 1/2) (hwLower : 1/(3*log k) ≤ w)
    (hupper : ∀ x ∈ Set.Ioo (16000 : ℝ) (exp 5100),
      (Nat.primeCounting ⌊x⌋₊ : ℝ) < upper x)
    (hlower : ∀ x ∈ Set.Ioo (16000 : ℝ) (exp 5100),
      lower x < (Nat.primeCounting ⌊x⌋₊ : ℝ)) : ShortPrimeSupply k w := by
  apply shortPrimeSupply_of_primeCounting_above_sixteen_thousand k hk hw hw' hwLower
  · intro x hx
    by_cases h : x < exp 5100
    · exact hupper x ⟨hx,h⟩
    · exact (RosserSchoenfeldLargePrimeCounting.bounds_above_exp_5100 (le_of_not_gt h)).2
  · intro x hx
    by_cases h : x < exp 5100
    · exact hlower x ⟨hx,h⟩
    · exact (RosserSchoenfeldLargePrimeCounting.bounds_above_exp_5100 (le_of_not_gt h)).1

/-- The original packet statement holds without a count premise whenever its
unchanged published base lies in the independently proved large range. -/
theorem shortPrimeSupply_of_large_base (k : ℕ) {w : ℝ} (hk : 26 ≤ k)
    (hw : 0 < w) (hw' : w ≤ 1/2) (hwLower : 1/(3*log k) ≤ w)
    (hbase : exp 5100 ≤ publishedBase k w) : ShortPrimeSupply k w := by
  intro M hM
  have hlarge := hbase.trans hM
  have hM0 := (exp_pos 5100).trans_le hlarge
  have hMw : M ≤ (1+w)*M := by nlinarith
  apply exists_prime_packet (N := k^3) (by nlinarith [Nat.pow_le_pow_left hk 3])
    hw hw' (cubic_density hk hw hwLower)
    ((le_max_left _ _).trans hM) _
    (RosserSchoenfeldLargePrimeCounting.bounds_above_exp_5100 hlarge).2
    (RosserSchoenfeldLargePrimeCounting.bounds_above_exp_5100 (hlarge.trans hMw)).1
  have hh := (le_max_right _ _).trans hM
  change 18/w*(k : ℝ)^3*log k ≤ M at hh
  push_cast
  rw [log_pow]
  norm_num only [Nat.cast_ofNat]
  convert! hh using 1
  ring

/-- The explicit logarithmic cutoff implies every numerical degree condition used here. -/
theorem degree_ge_of_log_ge {k : ℕ} (hk : (1700 : ℝ) ≤ log k) : 1701 ≤ k := by
  have hk0 : k ≠ 0 := by intro h; norm_num [h] at hk
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
  have hh := log_le_sub_one_of_pos hkR
  have h : (1701 : ℝ) ≤ k := by linarith
  exact_mod_cast h

/-- The original base is above the proved count threshold at this explicit
large-degree cutoff, throughout Ford's original admissible width range. -/
theorem publishedBase_large_of_log_ge {k : ℕ} (hk : (1700 : ℝ) ≤ log k)
    {w : ℝ} (hw : 0 < w) (hw' : w ≤ 1/2) : exp 5100 ≤ publishedBase k w := by
  have hkN := degree_ge_of_log_ge hk
  have hk0 : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hpow : exp 5100 ≤ (k : ℝ)^3 := by
    rw [← exp_log hk0, ← exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    exact exp_le_exp.mpr (by linarith)
  apply hpow.trans
  apply le_trans _ (publishedBase_ge (by omega : 26 ≤ k) hw hw')
  nlinarith [pow_nonneg hk0.le 3]

/-- Unconditional actual prime supply at large degree, retaining every
original packet constant, physical endpoint and admissible width. -/
theorem shortPrimeSupply_of_log_ge {k : ℕ} (hk : (1700 : ℝ) ≤ log k)
    {w : ℝ} (hw : 0 < w) (hw' : w ≤ 1/2) (hwLower : 1/(3*log k) ≤ w) :
    ShortPrimeSupply k w :=
  shortPrimeSupply_of_large_base k (by have := degree_ge_of_log_ge hk; omega)
    hw hw' hwLower (publishedBase_large_of_log_ge hk hw hw')

/-- The literal fixed width used by the selected Ford moment chain is supplied
without an arithmetic premise on the explicit large-degree range. -/
theorem fixedWidth_shortPrimeSupply {k : ℕ} (hk : (1700 : ℝ) ≤ log k) :
    ShortPrimeSupply k (3/50) := by
  apply shortPrimeSupply_of_log_ge hk (by norm_num) (by norm_num)
  apply (div_le_iff₀ (show 0 < 3*log k by linarith)).mpr
  linarith

end
end RiemannGaussian.VinogradovRosserLargeSupply
