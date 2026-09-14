/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovProductEnergy
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.ModEq

/-!
# One finite prime packet separates every original distinct block

Iterated Bertrand supplies R distinct primes in (M,2^R*M]. Their product
cannot divide a positive integer smaller than M^R. Apply this to the full
ordered product of pairwise distances: if X^(k*(k-1))<M^R, the same packet
contains a separating prime for every distinct block in the original
interval. The induced conditioned block preserves all signed frequencies.
-/

namespace RiemannGaussian.VinogradovPrimePacket
noncomputable section
open scoped BigOperators

/-- Iterated Bertrand constructs any prescribed number of distinct primes in an explicit finite interval. -/
theorem exists_prime_packet (M R : ℕ) (hM : 0 < M) :
    ∃ P : Finset ℕ, P.card = R ∧ ∀ p ∈ P, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M := by
  classical
  induction R with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ R ih =>
    obtain ⟨P, hcard, hP⟩ := ih
    obtain ⟨q, hq, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ R * M) (by positivity)
    have hn : q ∉ P := by
      intro hqP
      exact (not_lt_of_ge (hP q hqP).2.2) hlo
    refine ⟨insert q P, by simp [hn, hcard], ?_⟩
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · refine ⟨hq, ?_, ?_⟩
      · have hpow : 1 ≤ 2 ^ R := Nat.one_le_two_pow
        nlinarith
      · simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hhi
    · obtain ⟨hprime, hMlt, hle⟩ := hP p hp
      refine ⟨hprime, hMlt, hle.trans ?_⟩
      rw [pow_succ]
      nlinarith

/-- Distinct prime divisors contribute their full product, without a prime-counting estimate. -/
theorem prime_product_dvd {P : Finset ℕ} {D : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hD : ∀ p ∈ P, p ∣ D) : (∏ p ∈ P, p) ∣ D := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hpp := hP p (Finset.mem_insert_self p P)
    have hprime : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hc : p.Coprime (∏ q ∈ P, q) := by
      apply Nat.Coprime.prod_right
      intro q hq
      apply hpp.coprime_iff_not_dvd.mpr
      intro hd
      have he := (Nat.prime_dvd_prime_iff_eq hpp (hprime q hq)).mp hd
      exact hp (he ▸ hq)
    rw [Finset.prod_insert hp]
    exact hc.mul_dvd_of_dvd_of_dvd (hD p (Finset.mem_insert_self p P))
      (ih hprime (fun q hq => hD q (Finset.mem_insert_of_mem hq)))

/-- A positive discriminant smaller than a complete prime product is avoided by at least one prime in that packet. -/
theorem exists_prime_not_dvd {P : Finset ℕ} {D : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hD : 0 < D) (hprod : D < ∏ p ∈ P, p) :
    ∃ p ∈ P, ¬p ∣ D := by
  by_contra hn
  push Not at hn
  have hd := prime_product_dvd hP hn
  exact (not_lt_of_ge (Nat.le_of_dvd hD hd)) hprod

/-- The same finite prime packet avoids every positive integer below the explicit power budget. -/
theorem exists_uniform_avoiding_packet (M R : ℕ) (hM : 0 < M) :
    ∃ P : Finset ℕ, P.card = R ∧
      (∀ p ∈ P, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M) ∧
      ∀ D : ℕ, 0 < D → D < M ^ R → ∃ p ∈ P, ¬p ∣ D := by
  obtain ⟨P, hcard, hP⟩ := exists_prime_packet M R hM
  refine ⟨P, hcard, hP, ?_⟩
  intro D hD hbound
  apply exists_prime_not_dvd (fun p hp => (hP p hp).1) hD
  have hprod : M ^ R ≤ ∏ p ∈ P, p := by
    rw [← hcard, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun p hp => (hP p hp).2.1.le)
  exact hbound.trans_le hprod

/-- The full ordered product of pairwise integer distances; no zero diagonal factors are inserted. -/
def separationProduct {k : ℕ} (x : Fin k → ℕ) : ℕ :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, Nat.dist (x i) (x j)

/-- Distinct original entries give a strictly positive separation product. -/
theorem separationProduct_pos {k : ℕ} {x : Fin k → ℕ} (hx : Function.Injective x) :
    0 < separationProduct x := by
  unfold separationProduct
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  exact Nat.dist_pos_of_ne (fun h => (Finset.mem_erase.mp hj).1 (hx h).symm)

/-- The complete ordered discriminant has the explicit original-window power bound. -/
theorem separationProduct_le {k X : ℕ} (x : Fin k → ℕ) (hx : ∀ i, x i ≤ X) :
    separationProduct x ≤ X ^ (k * (k - 1)) := by
  unfold separationProduct
  calc
    _ ≤ ∏ _i : Fin k, X ^ (k - 1) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i hi
      calc
        _ ≤ ∏ _j ∈ (Finset.univ.erase i), X := by
          apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          intro j hj
          unfold Nat.dist
          have hiX := hx i
          have hjX := hx j
          omega
        _ = _ := by simp
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      congr 1
      ring

/-- Every off-diagonal distance divides the retained full separation product. -/
theorem dist_dvd_separationProduct {k : ℕ} (x : Fin k → ℕ) {i j : Fin k} (hij : i ≠ j) :
    Nat.dist (x i) (x j) ∣ separationProduct x := by
  have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
  exact (Finset.dvd_prod_of_mem (fun l : Fin k => Nat.dist (x i) (x l)) hj).trans
    (Finset.dvd_prod_of_mem (fun l : Fin k => ∏ j ∈ Finset.univ.erase l, Nat.dist (x l) (x j))
      (Finset.mem_univ i))

/-- Avoiding the exact separation product preserves every pairwise distinction modulo the chosen base. -/
theorem mod_injective_of_not_dvd {k p : ℕ} (x : Fin k → ℕ)
    (hp : ¬p ∣ separationProduct x) : Function.Injective (fun i => x i % p) := by
  intro i j hij
  by_contra hne
  apply hp
  have hm : Nat.ModEq p (x i) (x j) := hij
  have hd : p ∣ Nat.dist (x i) (x j) := by
    unfold Nat.dist
    exact dvd_add hm.symm.dvd' hm.dvd'
  exact hd.trans (dist_dvd_separationProduct x hne)

/-- One uniformly bounded finite prime packet separates every distinct tuple from the original window. -/
theorem exists_uniform_separating_packet (M R k X : ℕ) (hM : 0 < M)
    (hbudget : X ^ (k * (k - 1)) < M ^ R) :
    ∃ P : Finset ℕ, P.card = R ∧
      (∀ p ∈ P, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M) ∧
      ∀ x : Fin k → ℕ, Function.Injective x → (∀ i, x i ≤ X) →
        ∃ p ∈ P, Function.Injective (fun i => x i % p) := by
  obtain ⟨P, hcard, hP, havoid⟩ := exists_uniform_avoiding_packet M R hM
  refine ⟨P, hcard, hP, ?_⟩
  intro x hx hX
  obtain ⟨p, hp, hnot⟩ := havoid (separationProduct x) (separationProduct_pos hx)
    ((separationProduct_le x hX).trans_lt hbudget)
  exact ⟨p, hp, mod_injective_of_not_dvd x hnot⟩

/-- The selected prime constructs an actual original conditioned block, retaining every entry. -/
def packetBlock {p k X : ℕ} (x : Fin k → Fin X)
    (hx : Function.Injective (fun j => ((x j).val + 1) % p)) :
    VinogradovResidueEnergy.ConditionedWindow p k 0 0 X := by
  refine ⟨x, ?_, ?_⟩
  · intro j
    change ((x j).val + 1) % 1 = 0
    exact Nat.mod_one _
  · simp only [pow_zero, Nat.div_one]
    intro i j hij
    apply hx
    simpa only [ZMod.val_natCast] using congrArg ZMod.val hij

/-- Every original signed degree frequency survives the prime selection without an approximation. -/
theorem packetBlock_frequency {p k X : ℕ} (x : Fin k → Fin X)
    (hx : Function.Injective (fun j => ((x j).val + 1) % p)) (colour : Fin k → Bool) :
    VinogradovProductEnergy.blockFrequency colour (packetBlock x hx) =
      fun i : Fin k => ∑ j, VinogradovSignedCongruence.sign (colour j) *
        ((x j).val + 1 : ℤ) ^ (i.val + 1) := rfl

/-- A single finite prime packet covers every distinct original positive block by actual conditioned blocks with exactly the same entries. -/
theorem exists_uniform_conditioned_packet (M R k X : ℕ) (hM : 0 < M)
    (hbudget : X ^ (k * (k - 1)) < M ^ R) :
    ∃ P : Finset ℕ, P.card = R ∧
      (∀ p ∈ P, p.Prime ∧ M < p ∧ p ≤ 2 ^ R * M) ∧
      ∀ x : Fin k → Fin X, Function.Injective x →
        ∃ p ∈ P, ∃ z : VinogradovResidueEnergy.ConditionedWindow p k 0 0 X, z.val = x := by
  obtain ⟨P, hcard, hP, hsep⟩ := exists_uniform_separating_packet M R k X hM hbudget
  refine ⟨P, hcard, hP, ?_⟩
  intro x hx
  have hn : Function.Injective (fun i => (x i).val + 1) := by
    intro i j hij
    apply hx
    apply Fin.ext
    change (x i).val + 1 = (x j).val + 1 at hij
    exact Nat.add_right_cancel hij
  obtain ⟨p, hp, hmod⟩ := hsep (fun i => (x i).val + 1) hn (fun i => by have hi := (x i).isLt; omega)
  exact ⟨p, hp, packetBlock x hmod, rfl⟩

end
end RiemannGaussian.VinogradovPrimePacket
