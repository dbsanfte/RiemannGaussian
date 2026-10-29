/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecordsCanonical

/-! # Linear full-jet grouping work -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsGroupBounds
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsBounds
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1JetAxes (Context)

/-- Key-width property, independent of the number of stored assignments. -/
def Keys (K : Nat) (es : List Entry) : Prop := ∀e∈es,e.key.length≤K

/-- Sum of actual coefficient bytes under the current per-coordinate width. -/
theorem payload_length (ws : List (List Bool)) (p : Nat) (h : ∀w∈ws,w.length≤p) :
    (ws.map List.length).sum≤ws.length*p := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have hw:=h w List.mem_cons_self
    have ht:=ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Full record capacity pays rank delimiters even when precision is zero. -/
def recordBudget (ctx : Context) (K : Nat) : Nat := K+ctx.rank*(ctx.precision+1)+2

/-- Canonicality plus actual address width bounds every byte in a record. -/
theorem size_le (ctx : Context) (K : Nat) (e : Entry)
    (hg : SemiprimeD1TensorTables.GoodWords ctx e.words) (hk : e.key.length≤K) :
    size e≤recordBudget ctx K := by
  have hp:=payload_length e.words ctx.precision (fun w hw => (hg.2 w hw).2)
  rw [hg.1] at hp
  unfold size recordBudget
  rw [hg.1]
  nlinarith

/-- The grouped sum keeps the actual key attached to its combined payload. -/
theorem group_keys (ctx : Context) (K : Nat) : (es : List Entry) → Keys K es → Keys K (group ctx es).value
  | [],_ => by simp [group,Keys]
  | [a],h => by simpa only [group] using h
  | a::b::rest,h => by
    rw [group]
    split
    · apply group_keys ctx K
      intro e he
      rcases List.mem_cons.mp he with he | he
      · rw [he]
        exact h a List.mem_cons_self
      · exact h e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
    · have ha:=h a List.mem_cons_self
      intro e he
      rcases List.mem_cons.mp he with he | he
      · simpa only [he] using ha
      · exact group_keys ctx K (b::rest) (fun e he => h e (List.mem_cons_of_mem _ he)) e he
termination_by es _ => es.length

/-- Per-record sum work explicitly depends on the whole current context. -/
def sumBudget (ctx : Context) (K : Nat) : Nat :=
  ctx.rank*(6*ctx.rank+20*ctx.precision+17)+10*ctx.rank+5+
    20*(recordBudget ctx K+1)

/-- Real dense addition cost under the actually derived canonical input facts. -/
theorem add_clock (ctx : Context) (a b : Entry)
    (ha : SemiprimeD1TensorTables.GoodWords ctx a.words)
    (hb : SemiprimeD1TensorTables.GoodWords ctx b.words) :
    (SemiprimeD1JetRingBits.add ctx a.words b.words).clock≤
      ctx.rank*(6*ctx.rank+20*ctx.precision+17)+10*ctx.rank+5 := by
  have h:=SemiprimeD1JetRingBounds.add_clock ctx a.words b.words ctx.precision ha.1.le hb.1.le
    (fun w hw => (ha.2 w hw).2) (fun w hw => (hb.2 w hw).2)
  convert h using 1; ring

/-- The actual consecutive-key reduction is linear in record count, while
retaining every coefficient operation and full record-copy allowance. -/
theorem group_clock (ctx : Context) (K : Nat) :
    (es : List Entry) → GoodEntries ctx es → Keys K es →
    (group ctx es).clock≤ sumBudget ctx K*(es.length+1)
  | [],_,_ => by simp [group,sumBudget,recordBudget]; omega
  | [a],hg,hk => by
    have ha:=size_le ctx K a (hg a List.mem_cons_self) (hk a List.mem_cons_self)
    simp only [group,List.length_cons,List.length_nil]
    unfold sumBudget
    nlinarith
  | a::b::rest,hg,hk => by
    have hga:=hg a List.mem_cons_self
    have hgb:=hg b (by simp)
    have hka:=hk a List.mem_cons_self
    have hkb:=hk b (by simp)
    have hsa:=size_le ctx K a hga hka
    have hsb:=size_le ctx K b hgb hkb
    have cmp:=compare_clock a.key b.key
    have hadd:=add_clock ctx a b hga hgb
    have hkB : K≤recordBudget ctx K := by unfold recordBudget;omega
    rw [group]
    split
    · have hgood : GoodEntries ctx
          (⟨a.key,(SemiprimeD1JetRingBits.add ctx a.words b.words).words⟩::rest) := by
        apply SemiprimeD1BoundaryRecordsCanonical.good_cons ctx _ _ |>.mpr
        exact ⟨SemiprimeD1LeafCounterBounds.add_good ctx _ _,
          fun e he => hg e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))⟩
      have hkey : Keys K
          (⟨a.key,(SemiprimeD1JetRingBits.add ctx a.words b.words).words⟩::rest) := by
        intro e he
        rcases List.mem_cons.mp he with he | he
        · rw [he]; exact hka
        · exact hk e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
      have tail:=group_clock ctx K _ hgood hkey
      simp only [List.length_cons] at tail ⊢
      unfold sumBudget at tail ⊢
      nlinarith
    · have tail:=group_clock ctx K (b::rest)
        (fun e he => hg e (List.mem_cons_of_mem _ he))
        (fun e he => hk e (List.mem_cons_of_mem _ he))
      simp only [List.length_cons] at tail ⊢
      unfold sumBudget at tail ⊢
      nlinarith
termination_by es _ _ => es.length

end RiemannGaussian.SemiprimeD1BoundaryRecordsGroupBounds
