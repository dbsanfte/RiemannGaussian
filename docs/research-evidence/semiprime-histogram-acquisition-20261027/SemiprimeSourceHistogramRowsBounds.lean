/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramRows

/-! # Original-dimension row-dictionary acquisition and query bounds
The bank is acquired once and every row is encoded and inserted once. Bounds
include actual zip traversal, frame/counter work, copies and dictionary visits.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramRowsBounds
open SemiprimeSourceHistogramRows SemiprimeSourceHistogramTrie SemiprimeRationalBits

/-- Original bounds on literal paired IDs and physical coordinate rows. -/
def Good (pairs : List (List Bool × Row)) (B Q R : ℕ) : Prop :=
  ∀ p ∈ pairs, p.1.length ≤ B ∧ p.2.length ≤ Q ∧
    ∀ x ∈ p.2, x.numerator.magnitude.length ≤ R

/-- Every stored raw encoded row has the same original payload-width cap. -/
theorem build_width (pairs : List (List Bool × Row)) (B Q R : ℕ)
    (hg : Good pairs B Q R) (key : List Bool) :
    (stored (build pairs).trie key).length ≤ Q*(2*R+1) := by
  induction pairs generalizing key with
  | nil => simp [build,stored_empty]
  | cons p ps ih =>
    have hp := hg p (by simp)
    apply SemiprimeSourceHistogramTrieStore.put_width
    · exact fun query => ih (fun x hx => hg x (List.mem_cons_of_mem p hx)) query
    · rw [encodeRow_bits]
      exact (layout_length p.2 R hp.2.2).trans (Nat.mul_le_mul_right _ hp.2.1)

/-- Each actual encoded original row has a linear one-time construction ledger. -/
def rowStage (B Q R : ℕ) : ℕ := Q*(18*R+13)+20*B+28

/-- No acquisition step repeats an earlier bank lookup or row encoding. -/
theorem build_clock (pairs : List (List Bool × Row)) (B Q R : ℕ)
    (hg : Good pairs B Q R) :
    (build pairs).clock ≤ pairs.length*rowStage B Q R+1 := by
  induction pairs with
  | nil => simp [build]
  | cons p ps ih =>
    have hp := hg p (by simp)
    have ht := ih (fun x hx => hg x (List.mem_cons_of_mem p hx))
    have he := encodeRow_clock p.2 R hp.2.2
    have hl := layout_length p.2 R hp.2.2
    have hu := SemiprimeSourceHistogramTrieStore.put_clock (build ps).trie p.1
      (encodeRow p.2).bits
    rw [encodeRow_bits] at hu
    change (build ps).clock+_+_+6 ≤ _
    rw [encodeRow_bits]
    simp only [List.length_cons]
    unfold rowStage at ht ⊢
    nlinarith

/-- Dictionary inventory grows only by the inserted original ID path. -/
theorem build_nodes (pairs : List (List Bool × Row)) (B Q R : ℕ)
    (hg : Good pairs B Q R) : nodes (build pairs).trie ≤ pairs.length*(B+1) := by
  induction pairs with
  | nil => simp [build,nodes]
  | cons p ps ih =>
    have hp := hg p (by simp)
    have ht := ih (fun x hx => hg x (List.mem_cons_of_mem p hx))
    have hu := SemiprimeSourceHistogramTrieStore.put_nodes (build ps).trie p.1
      (encodeRow p.2).bits
    change nodes (SemiprimeSourceHistogramTrieStore.put _ _ _).trie ≤ _
    simp only [List.length_cons]
    nlinarith

/-- Actual acquired bank bounds discharge all original row-dictionary input caps. -/
theorem original_good (r Q : ℕ) : Good
    ((SemiprimeSourceCompactWordBank.acquire r Q).ids.zip
      (SemiprimeSourceCompactWordBank.acquire r Q).rows)
    (Nat.clog 2 (r^Q+1)) Q (r+1) := by
  intro p hp
  have ha : p.1 ∈ (SemiprimeSourceCompactWordBank.acquire r Q).ids := by
    have h : p.1 ∈ (((SemiprimeSourceCompactWordBank.acquire r Q).ids.zip
      (SemiprimeSourceCompactWordBank.acquire r Q).rows).map Prod.fst) :=
      List.mem_map.mpr ⟨p,hp,rfl⟩
    rwa [List.map_fst_zip (SemiprimeSourceCompactWordBank.ids_length r Q).le] at h
  have hb : p.2 ∈ (SemiprimeSourceCompactWordBank.acquire r Q).rows := by
    have h : p.2 ∈ (((SemiprimeSourceCompactWordBank.acquire r Q).ids.zip
      (SemiprimeSourceCompactWordBank.acquire r Q).rows).map Prod.snd) :=
      List.mem_map.mpr ⟨p,hp,rfl⟩
    rw [List.map_snd_zip (SemiprimeSourceCompactWordBank.ids_length r Q).symm.le] at h
    exact h
  refine ⟨SemiprimeSourceCompactWordBank.ids_bounded r Q p.1 ha,?_,?_⟩
  · exact (SemiprimeSourceWordBankBounds.acquire_row_length r Q p.2 hb).le
  · intro x hx
    exact (SemiprimeSourceWordBankBounds.acquire_good r Q p.2 hb x hx).2.1

/-- Original candidate IDs and rows are zipped with exactly original cardinality. -/
theorem original_pair_length (r Q : ℕ) :
    ((SemiprimeSourceCompactWordBank.acquire r Q).ids.zip
      (SemiprimeSourceCompactWordBank.acquire r Q).rows).length=r^Q := by
  rw [List.length_zip,SemiprimeSourceCompactWordBank.ids_length,Nat.min_self,
    SemiprimeSourceCompactWordBank.acquire_length]

/-- Complete original input construction, including the original bank producer. -/
def budget (r Q L : ℕ) : ℕ := SemiprimeSourceCompactWordBank.budget r Q L+
  4*L+1+L*rowStage (Nat.clog 2 (L+1)) Q (r+1)+1+4

/-- No external bank, row, ID-width or producer-clock advice remains. -/
theorem acquire_clock (r Q : ℕ) (hr : 0 < r) :
    (acquire r Q).clock ≤ budget r Q (r^Q) := by
  have hb := SemiprimeSourceCompactWordBank.acquire_clock r Q hr
  have hz := zipRows_clock (SemiprimeSourceCompactWordBank.acquire r Q).ids
    (SemiprimeSourceCompactWordBank.acquire r Q).rows
  have ht := build_clock _ _ _ _ (original_good r Q)
  simp only [original_pair_length] at hz ht
  unfold acquire budget
  dsimp only
  rw [zipRows_value]
  omega

/-- Every stored actual original row fits its original coordinate payload size. -/
theorem acquire_width (r Q : ℕ) (key : List Bool) :
    (stored (acquire r Q).trie key).length ≤ Q*(2*(r+1)+1) := by
  change (stored (build (zipRows _ _).value).trie key).length ≤ _
  rw [zipRows_value]
  exact build_width _ _ _ _ (original_good r Q) key

/-- Actual original dictionary inventory is linear-count times compact-ID width. -/
theorem acquire_nodes (r Q : ℕ) : nodes (acquire r Q).trie ≤
    r^Q*(Nat.clog 2 (r^Q+1)+1) := by
  change nodes (build (zipRows _ _).value).trie ≤ _
  rw [zipRows_value]
  have h := build_nodes _ _ _ _ (original_good r Q)
  rwa [original_pair_length] at h

/-- Each subsequent row query pays only its compact key and selected row payload. -/
theorem readRow_clock (r Q : ℕ) (id : List Bool)
    (hi : id ∈ (SemiprimeSourceCompactWordBank.acquire r Q).ids) :
    (readRow (acquire r Q) id).clock ≤
      8*Nat.clog 2 (r^Q+1)+3*(Q*(2*(r+1)+1))+12 := by
  have h := SemiprimeSourceHistogramTrieBounds.lookup_clock
    (acquire r Q).trie id _ (acquire_width r Q id)
  have hl := SemiprimeSourceCompactWordBank.ids_bounded r Q id hi
  exact h.trans (by omega)

end RiemannGaussian.SemiprimeSourceHistogramRowsBounds
