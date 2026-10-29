/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecords

/-! # Exact full-jet reduction of consecutive equal-key records -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1BoundaryRecords
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorTables (GoodWords)
open SemiprimeD1JetInterpretation (interpret Carrier)

/-- Weighted key semantics sums all actual matching records. It is proof-side
only; the runtime still uses concrete sorted sequential records. -/
noncomputable def weighted (ctx : Context) (es : List Entry) (key : List Bool) : Carrier ctx :=
  (es.map (fun e => if e.key=key then interpret ctx e.words else 0)).sum

/-- Comparator equality means literal byte equality, including padding/EOF. -/
private theorem compare_eq (xs ys : List Bool) :
    (compareKey xs ys).value=Ordering.eq ↔ xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [compareKey]
  | cons a as ih =>
    cases ys with
    | nil => simp [compareKey]
    | cons b bs => cases a <;> cases b <;> simp [compareKey,ih]

/-- A concrete record permutation preserves all full-jet key sums. -/
theorem weighted_perm (ctx : Context) {xs ys : List Entry} (h : xs.Perm ys) (key : List Bool) :
    weighted ctx xs key=weighted ctx ys key := by
  exact (h.map (fun e => if e.key=key then interpret ctx e.words else 0)).sum_eq

/-- Actual adjacent grouping preserves every key's complete jet value, without
field/nonzero/unit assumptions or a moment-only projection. -/
theorem group_weighted (ctx : Context) (hp : ctx.Positive) :
    (es : List Entry) → (key : List Bool) →
      weighted ctx (group ctx es).value key=weighted ctx es key
  | [],key => by simp [group,weighted]
  | [a],key => by simp [group,weighted]
  | a::b::rest,key => by
    by_cases hc : (compareKey a.key b.key).value=Ordering.eq
    · have he:= (compare_eq a.key b.key).mp hc
      rw [group]
      simp only [hc,beq_self_eq_true,ite_true]
      rw [group_weighted ctx hp (⟨a.key,(SemiprimeD1JetRingBits.add ctx a.words b.words).words⟩::rest) key]
      by_cases ha : a.key=key
      · simp [weighted,ha,←he,SemiprimeD1JetOperations.interpret_add ctx _ _ hp,add_assoc]
      · simp [weighted,ha,←he]
    · rw [group]
      have hn : ((compareKey a.key b.key).value==Ordering.eq)=false := by
        cases he : (compareKey a.key b.key).value <;> simp_all
      simp only [hn,Bool.false_eq_true,ite_false]
      change (if a.key=key then interpret ctx a.words else 0)+
        weighted ctx (group ctx (b::rest)).value key=weighted ctx (a::b::rest) key
      rw [group_weighted ctx hp (b::rest) key]
      rfl
termination_by es _ => es.length

/-- Every actual entry has the required canonical coefficient data. -/
def GoodEntries (ctx : Context) (es : List Entry) : Prop :=
  ∀ e∈es,GoodWords ctx e.words

/-- Grouping preserves canonical shape, compactness and current precision. -/
theorem group_good (ctx : Context) : (es : List Entry) → GoodEntries ctx es →
    GoodEntries ctx (group ctx es).value
  | [],_ => by simp [group,GoodEntries]
  | [a],ha => by simpa only [group] using ha
  | a::b::rest,hab => by
    by_cases hc : (compareKey a.key b.key).value=Ordering.eq
    · rw [group]
      simp only [hc,beq_self_eq_true,ite_true]
      apply group_good ctx
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact SemiprimeD1LeafCounterBounds.add_good ctx a.words b.words
      · exact hab e (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ he))
    · rw [group]
      have hn : ((compareKey a.key b.key).value==Ordering.eq)=false := by
        cases he : (compareKey a.key b.key).value <;> simp_all
      simp only [hn,Bool.false_eq_true,ite_false]
      have ha:=hab a List.mem_cons_self
      intro e he
      rcases List.mem_cons.mp he with he | he
      · simpa only [he] using ha
      · exact group_good ctx (b::rest)
          (fun e he => hab e (List.mem_cons_of_mem _ he)) e he
termination_by es _ => es.length

/-- The grouping loop never loses the scalar entry of a nonempty tensor. -/
theorem group_nonempty (ctx : Context) : (es : List Entry) → es≠[] → (group ctx es).value≠[]
  | [],h => False.elim (h rfl)
  | [a],_ => by simp [group]
  | a::b::rest,_ => by
    rw [group]
    split
    · exact group_nonempty ctx _ (by simp)
    · simp
termination_by es _ => es.length

end RiemannGaussian.SemiprimeD1BoundaryRecordsReduction
