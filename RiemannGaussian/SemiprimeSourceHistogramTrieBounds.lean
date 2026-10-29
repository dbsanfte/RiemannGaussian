/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramTrie

/-! # Key-linear trie reports and logarithmic physical counters
Numeric tally bounds concern the existing input state and are discharged by the
actual update/count invariant, never by supplied encoded output or Fits answers.
Persistent child references retain their explicit native-machine join boundary.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramTrieBounds
open SemiprimeSourceHistogramTrie SemiprimeBitArithmetic

/-- Every stored frequency is bounded by an original update-count cap. -/
def CountCap (t : Trie) (M : ℕ) : Prop := ∀ key,value t key ≤ M

/-- Empty dictionary starts with actual zero counters everywhere. -/
theorem empty_cap (M : ℕ) : CountCap .empty M := by
  intro key
  simp only [value,stored_empty,bitValue,Nat.zero_le]

/-- One actual update increases the global tally cap by at most one. -/
theorem bump_cap (t : Trie) (key : List Bool) (M : ℕ) (ht : CountCap t M) :
    CountCap (bump t key).trie (M+1) := by
  intro query
  rw [bump_value]
  split_ifs <;> have h := ht query <;> omega

/-- Compact existing counters fit the logarithmic original tally cap. -/
theorem stored_length (t : Trie) (key : List Bool) (M : ℕ)
    (hc : CompactCounters t) (hv : value t key ≤ M) :
    (stored t key).length ≤ Nat.clog 2 (M+1) := by
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ (hc key)
  have hp := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (M+1)
  change bitValue (stored t key) ≤ M at hv
  omega

/-- The actual selected old payload is copied at logarithmic width. -/
theorem bump_old_length (t : Trie) (key : List Bool) (M : ℕ)
    (hc : CompactCounters t) (hv : value t key ≤ M) :
    (bump t key).old.length ≤ Nat.clog 2 (M+1) := by
  rw [bump_old]
  exact stored_length t key M hc hv

/-- Lookup produces the same compact logarithmic counter, including absent zero. -/
theorem lookup_length (t : Trie) (key : List Bool) (M : ℕ)
    (hc : CompactCounters t) (hv : value t key ≤ M) :
    (lookup t key).bits.length ≤ Nat.clog 2 (M+1) := by
  rw [lookup_bits]
  exact stored_length t key M hc hv

/-- Exact clock shape shows a single key-path and one copied/incremented terminal. -/
theorem bump_clock_shape (t : Trie) (key : List Bool) :
    (bump t key).clock=20*(key.length+1)+
      (SemiprimeSourceCompactBits.copy (stored t key)).clock+
      (SemiprimeSourceCompactBits.increment (stored t key)).clock := by
  induction key generalizing t with
  | nil => simp only [bump,stored,List.length_nil];omega
  | cons b bs ih => simp only [bump,stored,List.length_cons,ih];omega

/-- Single-path update work is linear in key length and existing physical counter width. -/
theorem bump_clock (t : Trie) (key : List Bool) (B : ℕ) (hB : 1 ≤ B)
    (ht : (stored t key).length ≤ B) :
    (bump t key).clock ≤ 20*key.length+30*(B+1)+30 := by
  have hc := SemiprimeSourceCompactBits.copy_clock (stored t key)
  have hi := SemiprimeSourceCompactBits.increment_clock (stored t key) B hB ht
  rw [bump_clock_shape]
  omega

/-- Selected-payload lookup reads one key path; absent branches stop immediately. -/
theorem lookup_clock (t : Trie) (key : List Bool) (B : ℕ)
    (ht : (stored t key).length ≤ B) :
    (lookup t key).clock ≤ 8*key.length+3*B+12 := by
  induction key generalizing t with
  | nil =>
    cases t with
    | empty => simp only [lookup,List.length_nil];omega
    | node v l r =>
      have h := SemiprimeSourceCompactBits.copy_clock (v.getD [])
      change (v.getD []).length ≤ B at ht
      simp only [lookup,List.length_nil]
      omega
  | cons b bs ih =>
    cases t with
    | empty => simp only [lookup,List.length_cons];omega
    | node v l r =>
      cases b
      · have h := ih l ht
        simp only [lookup,List.length_cons,Bool.false_eq_true,ite_false]
        omega
      · have h := ih r ht
        simp only [lookup,List.length_cons,ite_true]
        omega

/-- Positive counter width with space for the next tally. -/
def clockWidth (M : ℕ) : ℕ := Nat.clog 2 (M+2)

/-- This width is positive even before the first insertion. -/
theorem clockWidth_pos (M : ℕ) : 1 ≤ clockWidth M := by
  have hp := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (M+2)
  by_contra h
  have hz : Nat.clog 2 (M+2)=0 := by unfold clockWidth at h;omega
  rw [hz,pow_zero] at hp
  omega

/-- Existing actual counter bounds derive the update template width internally. -/
theorem stored_clockWidth (t : Trie) (key : List Bool) (M : ℕ)
    (hc : CompactCounters t) (hv : value t key ≤ M) :
    (stored t key).length ≤ clockWidth M := by
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ (hc key)
  have hp := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (M+2)
  change bitValue (stored t key) ≤ M at hv
  change bitValue (stored t key)<2^(Nat.clog 2 (M+2))
  omega

/-- Actual update report with logarithmic frequency width and no encoded-count advice. -/
theorem bump_clock_of_count (t : Trie) (key : List Bool) (M : ℕ)
    (hc : CompactCounters t) (hv : value t key ≤ M) :
    (bump t key).clock ≤ 20*key.length+30*(clockWidth M+1)+30 :=
  bump_clock t key (clockWidth M) (clockWidth_pos M) (stored_clockWidth t key M hc hv)

/-- Actual lookup report with a derived logarithmic frequency width. -/
theorem lookup_clock_of_count (t : Trie) (key : List Bool) (M : ℕ)
    (hc : CompactCounters t) (hv : value t key ≤ M) :
    (lookup t key).clock ≤ 8*key.length+3*(Nat.clog 2 (M+1))+12 :=
  lookup_clock t key _ (stored_length t key M hc hv)

end RiemannGaussian.SemiprimeSourceHistogramTrieBounds
