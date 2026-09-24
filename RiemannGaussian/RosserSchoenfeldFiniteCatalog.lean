/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldFiniteBounds

/-!
# The complete reusable prime catalog through 16000

The checked block lists give every prime through the finite cutoff. Filtering
this same catalog computes the actual prime count at any smaller natural
endpoint; completeness is proved, not inferred from a list of prime examples.
-/

namespace RiemannGaussian.RosserSchoenfeldFiniteBounds

/-- A complete consecutive prime block contains no repeated labels. -/
theorem primeBlock_nodup (a n : ℕ) : (primeBlock a n).Nodup := by
  exact (List.nodup_range' (s := a) (n := n)).filter _

/-- Membership in the actual block retains its exact interval and primality. -/
theorem mem_primeBlock {a n p : ℕ} :
    p ∈ primeBlock a n ↔ a ≤ p ∧ p < a+n ∧ p.Prime := by
  simp only [primeBlock, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  tauto

/-- Filtering a complete catalog gives every prime through the smaller endpoint. -/
theorem primesLE_eq_filtered_catalog {B : ℕ} {ps : List ℕ}
    (hc : primeBlock 0 (B+1) = ps) {n : ℕ} (hn : n ≤ B) :
    Nat.primesLE n = (ps.filter (fun p => decide (p ≤ n))).toFinset := by
  ext p
  rw [List.mem_toFinset, List.mem_filter, ← hc, mem_primeBlock]
  simp only [Nat.mem_primesLE, decide_eq_true_eq, Nat.zero_le, Nat.zero_add, true_and]
  constructor
  · rintro ⟨hpn, hp⟩
    exact ⟨⟨by omega, hp⟩, hpn⟩
  · rintro ⟨⟨_, hp⟩, hpn⟩
    exact ⟨hpn, hp⟩

/-- The filtered catalog length is the actual prime count, not an approximation. -/
theorem count_eq_filtered_catalog {B : ℕ} {ps : List ℕ}
    (hc : primeBlock 0 (B+1) = ps) {n : ℕ} (hn : n ≤ B) :
    Nat.primeCounting n = (ps.filter (fun p => decide (p ≤ n))).length := by
  rw [← Nat.primesLE_card_eq_primeCounting, primesLE_eq_filtered_catalog hc hn]
  apply List.toFinset_card_of_nodup
  apply List.Nodup.filter
  rw [← hc]
  exact primeBlock_nodup 0 (B+1)

/-- The checked finite catalog contains exactly the primes through 16000. -/
theorem catalog_mem_iff {p : ℕ} : p ∈ catalog16000 ↔ p ≤ 16000 ∧ p.Prime := by
  rw [← catalog_complete_16000, mem_primeBlock]
  simp only [Nat.zero_le, Nat.zero_add, true_and]
  constructor
  · intro h
    exact ⟨by omega, h.2⟩
  · intro h
    exact ⟨by omega, h.2⟩

/-- The reusable catalog has no duplicates. -/
theorem catalog_nodup : catalog16000.Nodup := by
  rw [← catalog_complete_16000]
  exact primeBlock_nodup 0 16001

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The complete catalog is strictly increasing, so its initial segments
retain exact prime-prefix information for subsequent sieve recurrences. -/
theorem catalog_sorted : catalog16000.Pairwise (· < ·) := by
  have h : catalog16000.IsChain (· < ·) := by decide +kernel
  exact List.isChain_iff_pairwise.mp h

/-- A finite executable lookup using the proved complete prime catalog. -/
def smallPrimeCount (n : ℕ) : ℕ :=
  (catalog16000.filter (fun p => decide (p ≤ n))).length

/-- Every lookup through 16000 agrees with the actual prime-counting function. -/
theorem smallPrimeCount_eq {n : ℕ} (hn : n ≤ 16000) :
    smallPrimeCount n = Nat.primeCounting n :=
  (count_eq_filtered_catalog catalog_complete_16000 hn).symm

end RiemannGaussian.RosserSchoenfeldFiniteBounds
