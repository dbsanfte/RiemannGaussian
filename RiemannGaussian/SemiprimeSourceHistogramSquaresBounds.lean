/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramSquares
import RiemannGaussian.SemiprimeSourceHistogramTrieBounds

/-! # Original-key-list widths, inventory and complete streaming reports
Every numeric cap is derived from actual occurrence counts and loop invariants.
There is no supplied encoded counter, frequency, output fit or callback clock.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramSquaresBounds
open SemiprimeBitArithmetic SemiprimeSourceHistogramSquares
open SemiprimeSourceHistogramTrie (Trie)
open SemiprimeSourceCompactBits (Compact)

/-- A literal list sum with bounded acquired entries has the actual length cap. -/
theorem list_sum_cap {A : Type*} (xs : List A) (f : A → ℕ) (M : ℕ)
    (hf : ∀a∈xs,f a ≤ M) : (xs.map f).sum ≤ xs.length*M := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hf a List.mem_cons_self
    have ht := ih (fun b hb => hf b (List.mem_cons_of_mem a hb))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- The proof-view pair count is also the sum of its acquired occurrence frequencies. -/
theorem collisions_counts (keys : List (List Bool)) :
    collisions keys=(keys.map (fun key => keys.count key)).sum := by
  have hr (key : List Bool) :
      (keys.map (fun a => if key=a then (1:ℕ) else 0)).sum=keys.count key := by
    simpa only [eq_comm] using row_count keys key
  unfold collisions SemiprimeSourceHistogramGrouping.pairs
  simp_rw [hr]

/-- Actual accumulated collision count never exceeds the original occurrence square. -/
theorem collisions_le (keys : List (List Bool)) : collisions keys ≤ keys.length^2 := by
  rw [collisions_counts,pow_two]
  exact list_sum_cap keys (fun key => keys.count key) keys.length (fun _ _ => List.count_le_length)

/-- Every final dictionary counter has intrinsic logarithmic physical width. -/
theorem frequency_width (keys : List (List Bool)) (key : List Bool) :
    (SemiprimeSourceHistogramTrie.stored (acquire keys).trie key).length ≤
      Nat.clog 2 (keys.length+1) := by
  apply SemiprimeSourceHistogramTrieBounds.stored_length _ key keys.length
    (acquire_good keys).2.2.1
  rw [(acquire_good keys).1 key]
  exact List.count_le_length

/-- The actual total output has logarithmic width in the original pair cap. -/
theorem square_width (keys : List (List Bool)) :
    (acquire keys).bits.length ≤ Nat.clog 2 (keys.length^2+1) := by
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ (acquire_good keys).2.2.2
  rw [acquire_value]
  have hc := collisions_le keys
  have hp := Nat.le_pow_clog (by decide : 1<(2:ℕ)) (keys.length^2+1)
  omega

/-- Common logarithmic arithmetic width including the doubled old counter. -/
def width (M : ℕ) : ℕ := Nat.clog 2 ((M+1)^2+1)+2

/-- Its numerical envelope follows the original length, not an advised word. -/
theorem width_envelope (M : ℕ) : (M+1)^2+1 ≤ 2^(width M) := by
  apply (Nat.le_pow_clog (by decide : 1<(2:ℕ)) ((M+1)^2+1)).trans
  apply Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
  unfold width
  omega

/-- Every actual current stored frequency fits the internally selected common width. -/
theorem good_stored_width (processed : List (List Bool)) (state : State) (M : ℕ)
    (hs : Good processed state) (hlen : processed.length ≤ M) (key : List Bool) :
    (SemiprimeSourceHistogramTrie.stored state.trie key).length ≤ width M := by
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ (hs.2.2.1 key)
  have hc : SemiprimeSourceHistogramTrie.value state.trie key ≤ M :=
    (hs.1 key ▸ List.count_le_length).trans hlen
  have hp := width_envelope M
  change bitValue (SemiprimeSourceHistogramTrie.stored state.trie key) ≤ M at hc
  nlinarith

/-- Every actual accumulated prefix fits the same original-length envelope. -/
theorem good_total_width (processed : List (List Bool)) (state : State) (M : ℕ)
    (hs : Good processed state) (hlen : processed.length ≤ M) : state.bits.length ≤ width M := by
  apply SemiprimeSourceCompactBits.compact_length_of_lt _ hs.2.2.2
  have hc : bitValue state.bits ≤ M^2 := by
    rw [hs.2.1]
    exact (collisions_le processed).trans (Nat.pow_le_pow_left hlen 2)
  have hp := width_envelope M
  nlinarith

/-- Single-step budget is linear in actual key width and logarithmic tally width. -/
def stepBudget (B M : ℕ) : ℕ := 100*(B+width M+2)+100

/-- Complete executed update work from the proven actual prefix invariant. -/
theorem step_clock (processed : List (List Bool)) (state : State) (key : List Bool) (B M : ℕ)
    (hs : Good processed state) (hlen : processed.length ≤ M) (hk : key.length ≤ B) :
    (step state key).clock ≤ state.clock+stepBudget B M := by
  have hW : 1 ≤ width M := by unfold width;omega
  have hold := good_stored_width processed state M hs hlen key
  have htotal := good_total_width processed state M hs hlen
  have hBump := SemiprimeSourceHistogramTrieBounds.bump_clock state.trie key (width M) hW hold
  have hOld : (SemiprimeSourceHistogramTrie.bump state.trie key).old.length ≤ width M := by
    rw [SemiprimeSourceHistogramTrie.bump_old]
    exact hold
  have hi := SemiprimeSourceCompactBits.increment_clock
    (false::(SemiprimeSourceHistogramTrie.bump state.trie key).old) (width M+1)
    (by omega) (by simp only [List.length_cons];omega)
  have hterm : (SemiprimeSourceCompactBits.increment
      (false::(SemiprimeSourceHistogramTrie.bump state.trie key).old)).bits.length ≤ width M := by
    apply SemiprimeSourceCompactBits.compact_length_of_lt _
      (SemiprimeSourceCompactBits.increment_compact _)
    rw [SemiprimeSourceCompactBits.increment_value,SemiprimeSourceHistogramTrie.bump_old]
    have hcount : SemiprimeSourceHistogramTrie.value state.trie key ≤ M := by
      rw [hs.1 key]
      exact List.count_le_length.trans hlen
    have hp := width_envelope M
    change bitValue (SemiprimeSourceHistogramTrie.stored state.trie key) ≤ M at hcount
    simp only [bitValue,bitNat,Bool.false_eq_true,ite_false]
    nlinarith
  have ha := SemiprimeSourceCompactBits.add_clock state.bits
    (SemiprimeSourceCompactBits.increment
      (false::(SemiprimeSourceHistogramTrie.bump state.trie key).old)).bits (width M) htotal hterm
  unfold step stepBudget
  dsimp only
  omega

/-- Final bound retains every step and loop branch, with no final bin scan. -/
def budget (B M : ℕ) : ℕ := M*(stepBudget B M+3)+2

/-- Actual remaining-key recursion preserves a fixed original-prefix cap. -/
theorem fold_clock (keys processed : List (List Bool)) (state : State) (B M : ℕ)
    (hs : Good processed state) (hlen : processed.length+keys.length ≤ M)
    (hk : ∀key∈keys,key.length ≤ B) :
    (fold keys state).clock ≤ state.clock+keys.length*(stepBudget B M+3)+1 := by
  induction keys generalizing processed state with
  | nil => simp [fold]
  | cons key keys ih =>
    have hkey := hk key List.mem_cons_self
    have hstep := step_clock processed state key B M hs (by simp only [List.length_cons] at hlen;omega) hkey
    have hnext := step_good processed state key hs
    have hlen' : (processed++[key]).length+keys.length ≤ M := by
      simp only [List.length_append,List.length_cons,List.length_nil] at hlen ⊢
      omega
    have hr := ih (processed++[key]) (step state key) hnext hlen'
      (fun k h => hk k (List.mem_cons_of_mem key h))
    simp only [fold,List.length_cons]
    nlinarith

/-- Original input length and key widths discharge the entire acquisition clock. -/
theorem acquire_clock (keys : List (List Bool)) (B : ℕ)
    (hk : ∀key∈keys,key.length ≤ B) : (acquire keys).clock ≤ budget B keys.length := by
  have h := fold_clock keys [] initial B keys.length initial_good (by simp) hk
  change (fold keys initial).clock ≤ keys.length*(stepBudget B keys.length+3)+2
  change (fold keys initial).clock ≤ 1+keys.length*(stepBudget B keys.length+3)+1 at h
  omega

/-- Actual persistent trie nodes grow only on the visited original key path. -/
theorem fold_nodes (keys : List (List Bool)) (state : State) :
    SemiprimeSourceHistogramTrie.nodes (fold keys state).trie ≤
      SemiprimeSourceHistogramTrie.nodes state.trie+(keys.map (fun key => key.length+1)).sum := by
  induction keys generalizing state with
  | nil => simp [fold]
  | cons key keys ih =>
    have h := ih (step state key)
    have hb := SemiprimeSourceHistogramTrie.bump_nodes state.trie key
    simp only [fold,step,List.map_cons,List.sum_cons] at h ⊢
    omega

/-- Node inventory of the actual acquired trie is bounded by the original key cells. -/
theorem acquire_nodes (keys : List (List Bool)) (B : ℕ)
    (hk : ∀key∈keys,key.length ≤ B) :
    SemiprimeSourceHistogramTrie.nodes (acquire keys).trie ≤ keys.length*(B+1) := by
  have h := fold_nodes keys initial
  have hb := list_sum_cap keys (fun key => key.length+1) (B+1)
    (fun key h => Nat.add_le_add_right (hk key h) 1)
  simp only [initial,SemiprimeSourceHistogramTrie.nodes,Nat.zero_add] at h
  exact h.trans hb

/-- The internally derived common width is monotone in the original key count. -/
theorem width_mono {M M' : ℕ} (h : M ≤ M') : width M ≤ width M' := by
  unfold width
  apply Nat.add_le_add_right
  apply Nat.clog_mono_right 2
  gcongr

/-- Original key-width/count caps may be enlarged without a resource oracle. -/
theorem budget_mono {B M B' M' : ℕ} (hB : B ≤ B') (hM : M ≤ M') :
    budget B M ≤ budget B' M' := by
  have hw := width_mono hM
  unfold budget stepBudget
  gcongr

end RiemannGaussian.SemiprimeSourceHistogramSquaresBounds
