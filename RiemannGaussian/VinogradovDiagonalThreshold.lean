/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDiagonalExponent
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# All-endpoint quantitative diagonal descent

The integer k-th root supplies an actual packet scale at every sufficiently
large endpoint. Every packet, repetition and quotient hypothesis is paid
by one defined threshold. Below it the literal tuple count pays a separate
small-endpoint allowance. Taking a maximum keeps this allowance from
artificially multiplying the preceding moment coefficient.
-/

namespace RiemannGaussian.VinogradovDiagonalThreshold
noncomputable section
open scoped BigOperators Classical
open VinogradovMeanValue VinogradovDiagonalExponent

/-- One explicit root-scale threshold pays all conditions for R=k^3 primes. -/
def base (k s : ℕ) : ℕ :=
  max (2 ^ k) (max (4 * k ^ 4) (max (16 * s ^ 2 * 2 ^ (k ^ 3)) (k + 1)))

/-- The physical endpoint threshold is an actual integer power. -/
def threshold (k s : ℕ) : ℕ := base k s ^ k

/-- The diagonal prime-packet multiplier is independent of the moment order and defect. -/
def packetCoefficient (k : ℕ) : ℕ := 4 * k ^ 3 * k.factorial * 2 ^ (k ^ 3 * k ^ 2)

/-- Keep the small-endpoint allowance separate from the previous coefficient. -/
def nextCoefficient (k s C : ℕ) : ℕ :=
  max (threshold k s ^ degreeWeight k) (packetCoefficient k * C)

/-- The unordered pair budget fits in k^3 primes at the literal root scale. -/
theorem root_packet_budget {k M P : ℕ} (hk : 2 ≤ k) (hM : 2 ^ k ≤ M)
    (hroot : P < (M + 1) ^ k) : P ^ (2 * k.choose 2) < M ^ (k ^ 3) := by
  have hM0 : 0 < M := (pow_pos (by omega : 0 < 2) k).trans_le hM
  have hupper : P < M ^ (k + 1) := by
    calc
      P < (M + 1) ^ k := hroot
      _ ≤ (2 * M) ^ k := Nat.pow_le_pow_left (by omega) k
      _ = 2 ^ k * M ^ k := mul_pow _ _ _
      _ ≤ M * M ^ k := Nat.mul_le_mul_right _ hM
      _ = M ^ (k + 1) := (pow_succ' _ _).symm
  have he : (k + 1) * (2 * k.choose 2) ≤ k ^ 3 := by
    rw [twice_choose_two]
    have h := congrArg (fun a : ℕ => (k + 1) * k * a) (Nat.sub_add_cancel (by omega : 1 ≤ k))
    simp only [Nat.mul_add, Nat.mul_one] at h
    nlinarith
  have hchoose : 0 < 2 * k.choose 2 := Nat.mul_pos (by omega) (Nat.choose_pos hk)
  calc
    _ < (M ^ (k + 1)) ^ (2 * k.choose 2) := Nat.pow_lt_pow_left hupper (by omega)
    _ = M ^ ((k + 1) * (2 * k.choose 2)) := (pow_mul _ _ _).symm
    _ ≤ M ^ (k ^ 3) := Nat.pow_le_pow_right hM0 he

/-- The actual integer root discharges every hypothesis of the diagonal
moment step, including the original quotient endpoint threshold. -/
theorem exists_root_parameters {k s P : ℕ} (hk : 2 ≤ k) (hP : threshold k s ≤ P) :
    ∃ M : ℕ, 4 * k ^ 4 ≤ P ∧ k ≤ M ∧
      P ^ (2 * k.choose 2) < M ^ (k ^ 3) ∧
      P < (M + 1) ^ k ∧ M ^ k ≤ P ∧
      16 * s ^ 2 * (2 ^ (k ^ 3) * M) ≤ P := by
  let M := Nat.nthRoot k P
  have hk0 : k ≠ 0 := by omega
  have hbM : base k s ≤ M := (Nat.le_nthRoot_iff hk0).mpr hP
  have hbpow : 2 ^ k ≤ base k s := le_max_left _ _
  have hbsize : 4 * k ^ 4 ≤ base k s := (le_max_left _ _).trans (le_max_right _ _)
  have hbQ : 16 * s ^ 2 * 2 ^ (k ^ 3) ≤ base k s :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hbk : k ≤ base k s := (Nat.le_succ k).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hM0 : 0 < M := (pow_pos (by omega : 0 < 2) k).trans_le (hbpow.trans hbM)
  have hMP : M ^ k ≤ P := Nat.pow_nthRoot_le (Or.inl hk0)
  have hroot : P < (M + 1) ^ k := Nat.lt_pow_nthRoot_add_one hk0 P
  have hbaseP : base k s ≤ P :=
    hbM.trans ((Nat.le_self_pow hk0 M).trans hMP)
  refine ⟨M, hbsize.trans hbaseP, hbk.trans hbM,
    root_packet_budget hk (hbpow.trans hbM) hroot, hroot, hMP, ?_⟩
  calc
    _ = (16 * s ^ 2 * 2 ^ (k ^ 3)) * M := by ring
    _ ≤ M * M := Nat.mul_le_mul_right M (hbQ.trans hbM)
    _ = M ^ 2 := (pow_two M).symm
    _ ≤ M ^ k := Nat.pow_le_pow_right hM0 hk
    _ ≤ P := hMP

/-- The full moment is bounded by the complete number of original tuple pairs. -/
theorem meanValue_le_trivial (s k P : ℕ) : meanValue s k P ≤ (P : ℝ) ^ (2 * s) := by
  rw [meanValue_eq_count]
  have hn : collisionCount s (fun n : Fin P => monomialFrequency k (n.val + 1)) ≤ P ^ (2 * s) := by
    unfold collisionCount
    calc
      _ ≤ Fintype.card ((Fin s → Fin P) × (Fin s → Fin P)) := Finset.card_le_univ _
      _ = _ := by
        simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
        rw [← pow_add, two_mul]
  exact_mod_cast hn

/-- A small original endpoint is paid independently of the preceding
moment coefficient, even when the target exponent exceeds the trivial one. -/
theorem small_endpoint_bound {P U : ℕ} (hP : 1 ≤ P) (hPU : P ≤ U)
    (k s : ℕ) {delta : ℝ} (hd : 0 ≤ delta) :
    meanValue s k P ≤ (U : ℝ) ^ degreeWeight k * (P : ℝ) ^ exponent k s delta := by
  have hPR : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hgap := Real.rpow_le_rpow_of_exponent_le hP1
    (show (degreeWeight k : ℝ) - delta ≤ degreeWeight k by linarith)
  rw [Real.rpow_natCast] at hgap
  have hpow : (P : ℝ) ^ degreeWeight k ≤ (U : ℝ) ^ degreeWeight k := by
    exact_mod_cast Nat.pow_le_pow_left hPU (degreeWeight k)
  apply (meanValue_le_trivial s k P).trans
  rw [← Real.rpow_natCast]
  have he : ((2 * s : ℕ) : ℝ) = (degreeWeight k : ℝ) - delta + exponent k s delta := by
    unfold exponent
    push_cast
    ring
  rw [he, Real.rpow_add hPR]
  exact mul_le_mul_of_nonneg_right (hgap.trans hpow) (Real.rpow_nonneg hPR.le _)

/-- The quantitative defect step holds at every positive integer
endpoint. Its new coefficient is the maximum of the actual packet cost
times the old coefficient and an independent small-endpoint allowance. -/
theorem all_endpoint_defect_step {k s C : ℕ} (hk : 2 ≤ k) (hs : 1 ≤ s)
    {delta : ℝ} (hd : 0 ≤ delta) (hdk : delta ≤ (k : ℝ) ^ 2)
    (hexp : 0 ≤ exponent k s delta)
    (hJ : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤ (C : ℝ) * (X : ℝ) ^ exponent k s delta)
    (P : ℕ) (hP : 1 ≤ P) :
    meanValue (s + k) k P ≤ (nextCoefficient k s C : ℝ) *
      (P : ℝ) ^ exponent k (s + k) (delta * (1 - 1 / (k : ℝ))) := by
  by_cases hlarge : threshold k s ≤ P
  · obtain ⟨M, hsize, hM, hbudget, hroot, hMP, hQ⟩ := exists_root_parameters hk hlarge
    have h := moment_defect_step hk hsize hM hbudget hroot hMP hs hQ
      (Nat.cast_nonneg C) hd hdk hexp hJ
    have hc : ((packetCoefficient k * C : ℕ) : ℝ) ≤ (nextCoefficient k s C : ℝ) := by
      exact_mod_cast (le_max_right (threshold k s ^ degreeWeight k) (packetCoefficient k * C))
    have he : ((packetCoefficient k * C : ℕ) : ℝ) =
        ((4 * k ^ 3 * k.factorial * 2 ^ (k ^ 3 * k ^ 2) : ℕ) : ℝ) * C := by
      simp only [packetCoefficient, Nat.cast_mul]
    rw [he] at hc
    exact h.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg P) _))
  · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have ht : 0 ≤ 1 - 1 / (k : ℝ) :=
      sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
    have h := small_endpoint_bound hP (by omega : P ≤ threshold k s)
      k (s + k) (mul_nonneg hd ht)
    have hc : (threshold k s : ℝ) ^ degreeWeight k ≤ (nextCoefficient k s C : ℝ) := by
      exact_mod_cast (le_max_left (threshold k s ^ degreeWeight k) (packetCoefficient k * C))
    exact h.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg P) _))

end
end RiemannGaussian.VinogradovDiagonalThreshold
