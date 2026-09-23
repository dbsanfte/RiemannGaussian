/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDiagonalThreshold
import RiemannGaussian.VinogradovShortPacket

/-!+# All-endpoint diagonal descent with a fixed-width prime packet

The actual packet now lies in (M,8M]. A polynomial root-scale threshold
pays its cardinality, discriminant product, repeated tuples and original
tail endpoint. The exact defect contraction is unchanged. Small endpoints
again cost an independent maximum, not a repeated multiplicative loss.
-/

namespace RiemannGaussian.VinogradovNarrowThreshold
noncomputable section
open scoped BigOperators Classical
open VinogradovMeanValue VinogradovDiagonalExponent

/-- A polynomial root-scale threshold pays every fixed-width packet condition. -/
def base (k s : ℕ) : ℕ :=
  max 4096 (max (36 * k ^ 6) (max (128 * s ^ 2) (max (4 * k ^ 4) (k + 1))))

/-- The original endpoint threshold is the actual k-th power of the root threshold. -/
def threshold (k s : ℕ) : ℕ := base k s ^ k

/-- The packet has 2k cubed primes, each at most eight times the root scale. -/
def packetCoefficient (k : ℕ) : ℕ := 8 * k ^ 3 * k.factorial * 8 ^ (k ^ 2)

/-- The small-endpoint allowance remains independent of the preceding coefficient. -/
def nextCoefficient (k s C : ℕ) : ℕ :=
  max (threshold k s ^ degreeWeight k) (packetCoefficient k * C)

/-- Twice the cubic packet cardinality removes the exponential root-scale
condition from the full two-block discriminant budget. -/
theorem root_packet_budget {k M P : ℕ} (hk : 2 ≤ k) (hM : 2 ≤ M)
    (hroot : P < (M + 1) ^ k) : P ^ (2 * k.choose 2) < M ^ (2 * k ^ 3) := by
  have hupper : P < M ^ (2 * k) := by
    apply hroot.trans_le
    calc
      _ ≤ (M ^ 2) ^ k := Nat.pow_le_pow_left (by nlinarith : M + 1 ≤ M ^ 2) k
      _ = _ := (pow_mul _ _ _).symm
  have he : (2 * k) * (2 * k.choose 2) ≤ 2 * k ^ 3 := by
    rw [twice_choose_two]
    calc
      _ ≤ (2 * k) * (k * k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left k (Nat.sub_le k 1))
      _ = _ := by ring
  calc
    _ < (M ^ (2 * k)) ^ (2 * k.choose 2) := Nat.pow_lt_pow_left hupper
      (by have h := Nat.choose_pos hk; omega)
    _ = M ^ ((2 * k) * (2 * k.choose 2)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) he

/-- At every endpoint above the displayed threshold, the literal integer
root pays the numerical prime supply and every conditioning size condition. -/
theorem exists_root_parameters {k s P : ℕ} (hk : 2 ≤ k) (hP : threshold k s ≤ P) :
    ∃ M : ℕ, 4096 ≤ M ∧ 9 * (2 * k ^ 3) ^ 2 ≤ M ∧
      4 * k ^ 4 ≤ P ∧ k ≤ M ∧
      P ^ (2 * k.choose 2) < M ^ (2 * k ^ 3) ∧
      P < (M + 1) ^ k ∧ M ^ k ≤ P ∧ 16 * s ^ 2 * (8 * M) ≤ P := by
  let M := Nat.nthRoot k P
  have hk0 : k ≠ 0 := by omega
  have hbM : base k s ≤ M := (Nat.le_nthRoot_iff hk0).mpr hP
  have hbnum : 4096 ≤ base k s := le_max_left _ _
  have hbR : 36 * k ^ 6 ≤ base k s := (le_max_left _ _).trans (le_max_right _ _)
  have hbQ : 128 * s ^ 2 ≤ base k s :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbsize : 4 * k ^ 4 ≤ base k s :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hbk : k ≤ base k s := (Nat.le_succ k).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))
  have hMnum := hbnum.trans hbM
  have hMP : M ^ k ≤ P := Nat.pow_nthRoot_le (Or.inl hk0)
  have hroot : P < (M + 1) ^ k := Nat.lt_pow_nthRoot_add_one hk0 P
  have hbaseP : base k s ≤ P := hbM.trans ((Nat.le_self_pow hk0 M).trans hMP)
  have hR : 9 * (2 * k ^ 3) ^ 2 ≤ M := by
    calc
      _ = 36 * k ^ 6 := by ring
      _ ≤ M := hbR.trans hbM
  refine ⟨M, hMnum, hR, hbsize.trans hbaseP, hbk.trans hbM,
    root_packet_budget hk (by omega) hroot, hroot, hMP, ?_⟩
  calc
    _ = (128 * s ^ 2) * M := by ring
    _ ≤ M * M := Nat.mul_le_mul_right M (hbQ.trans hbM)
    _ = M ^ 2 := (pow_two M).symm
    _ ≤ M ^ k := Nat.pow_le_pow_right (by omega) hk
    _ ≤ P := hMP

/-- The actual homogeneous moment contracts its defect at every positive
endpoint, with the full fixed-width packet and small-endpoint costs paid. -/
theorem all_endpoint_defect_step {k s C : ℕ} (hk : 2 ≤ k) (hs : 1 ≤ s)
    {delta : ℝ} (hd : 0 ≤ delta) (hdk : delta ≤ (k : ℝ) ^ 2)
    (hexp : 0 ≤ exponent k s delta)
    (hJ : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤ (C : ℝ) * (X : ℝ) ^ exponent k s delta)
    (P : ℕ) (hP : 1 ≤ P) :
    meanValue (s + k) k P ≤ (nextCoefficient k s C : ℝ) *
      (P : ℝ) ^ exponent k (s + k) (delta * (1 - 1 / (k : ℝ))) := by
  by_cases hlarge : threshold k s ≤ P
  · obtain ⟨M, hMnum, hR, hsize, hM, hbudget, hroot, hMP, hQ⟩ :=
      exists_root_parameters hk hlarge
    obtain ⟨π, hcard, hπ⟩ := VinogradovShortPacket.exists_short_packet M (2 * k ^ 3) hMnum hR
    have hprod : M ^ (2 * k ^ 3) ≤ ∏ p ∈ π, p := by
      rw [← hcard, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => (hπ p hp).2.1.le)
    have h := moment_defect_step_of_packet hk hsize hM (by norm_num) π hπ
      (hbudget.trans_le hprod) hroot hMP hs hQ (Nat.cast_nonneg C) hd hdk hexp hJ
    have hc : 4 * π.card * k.factorial * 8 ^ (k ^ 2) = packetCoefficient k := by
      rw [hcard, packetCoefficient]
      ring
    rw [hc] at h
    have hnext : (packetCoefficient k : ℝ) * C ≤ (nextCoefficient k s C : ℝ) := by
      exact_mod_cast (le_max_right (threshold k s ^ degreeWeight k) (packetCoefficient k * C))
    exact h.trans (mul_le_mul_of_nonneg_right hnext (Real.rpow_nonneg (Nat.cast_nonneg P) _))
  · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have ht : 0 ≤ 1 - 1 / (k : ℝ) :=
      sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
    have h := VinogradovDiagonalThreshold.small_endpoint_bound hP
      (by omega : P ≤ threshold k s) k (s + k) (mul_nonneg hd ht)
    have hc : (threshold k s : ℝ) ^ degreeWeight k ≤ (nextCoefficient k s C : ℝ) := by
      exact_mod_cast (le_max_left (threshold k s ^ degreeWeight k) (packetCoefficient k * C))
    exact h.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg P) _))

end
end RiemannGaussian.VinogradovNarrowThreshold
