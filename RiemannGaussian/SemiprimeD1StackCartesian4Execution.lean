/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCartesian4Loop

/-! # Closed four-level physical Cartesian execution
All lower-procedure premises are discharged here from actual included Frame
calls. This internal primitive still requires its physical limits/tag; the
original-input catalogue wrapper acquires those from the real public data.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackCartesian4Execution
open SemiprimeD1StackCartesian4 SemiprimeD1StackCartesian4Components SemiprimeD1StackCartesian4Body
open SemiprimeD1StackCartesian4Loop
open SemiprimeD1StackProcedureFragments (Runs)

/-- Actual remaining level counters are empty between physical calls. -/
def ReadyFrom (level:ℕ) (indices:Fin 4→List Bool) : Prop := ∀j,level≤j.val→indices j=[]
/-- Common finite word-width bound for actual current indices. -/
def IndexBound (D:ℕ) (indices:Fin 4→List Bool) : Prop := ∀j,(indices j).length≤D

/-- A bounded physically visited index preserves the actual index-length bound. -/
theorem update_bound (indices:Fin 4→List Bool) (level:Fin 4) (i D:ℕ)
    (hb:IndexBound D indices) (hi:i≤D) :
    IndexBound D (Function.update indices level (List.replicate i true)) := by
  intro j
  by_cases h:j=level
  · subst j;simpa only [Function.update_self,List.length_replicate] using hi
  · simpa only [Function.update_of_ne h] using hb j

/-- A real outer index never changes any lower-level empty work counter. -/
theorem update_ready (indices:Fin 4→List Bool) (level:Fin 4) (word:List Bool)
    (hr:ReadyFrom level.val indices) : ReadyFrom (level.val+1) (Function.update indices level word) := by
  intro j hj
  have hn:j≠level:=by intro h;subst j;omega
  rw [Function.update_of_ne hn]
  exact hr j (by omega)

/-- Exact innermost record fold. -/
def box3 (dims:Fin 4→ℕ) (indices:Fin 4→List Bool) (tag output:List Bool) : List Bool :=
  rangeFold (dims 3) (fun i out=>record tag (Function.update indices 3 (List.replicate i true)) out) output
/-- Exact third-level product fold. -/
def box2 (dims:Fin 4→ℕ) (indices:Fin 4→List Bool) (tag output:List Bool) : List Bool :=
  rangeFold (dims 2) (fun i out=>box3 dims (Function.update indices 2 (List.replicate i true)) tag out) output
/-- Exact second-level product fold. -/
def box1 (dims:Fin 4→ℕ) (indices:Fin 4→List Bool) (tag output:List Bool) : List Bool :=
  rangeFold (dims 1) (fun i out=>box2 dims (Function.update indices 1 (List.replicate i true)) tag out) output
/-- Exact whole four-axis product fold, in original ascending lexicographic order. -/
def box0 (dims:Fin 4→ℕ) (indices:Fin 4→List Bool) (tag output:List Bool) : List Bool :=
  rangeFold (dims 0) (fun i out=>box1 dims (Function.update indices 0 (List.replicate i true)) tag out) output

/-- Fixed-degree polynomial clock, with the number of loop levels fixed to four. -/
def stageBudget (D T:ℕ) : ℕ→ℕ
  | 0 => 6*(4*D+T)+25
  | n+1 => D*(stageBudget D T n+8)+5

/-- Actual closed physical level3, retaining all child calls and original counter copies. -/
theorem level3_run (dims:Fin 4→ℕ) (limits indices:Fin 4→List Bool) (tag output:List Bool) (D:ℕ)
    (hl:∀j,limits j=List.replicate (dims j) true) (hd:∀j,dims j≤D)
    (hb:IndexBound D indices) (hc:ReadyFrom 3 indices) :
    ∃m≤stageBudget D tag.length 1,Runs program m (.inl (.entry 3)) (store limits indices tag output)
      (.inl .ret) (store limits indices tag (box3 dims indices tag output)) := by
  have hchild:∀i<dims 3,∀out,∃m≤stageBudget D tag.length 0,
      Runs program m (childEntry 3)
        (store limits (Function.update indices 3 (List.replicate i true)) tag out)
        (.inl .ret) (store limits (Function.update indices 3 (List.replicate i true)) tag
          (record tag (Function.update indices 3 (List.replicate i true)) out)):=by
    intro i hi out
    let current:=Function.update indices 3 (List.replicate i true)
    have hbi:IndexBound D current:=update_bound indices 3 i D hb ((Nat.le_of_lt hi).trans (hd 3))
    refine ⟨bodyClock current tag,bodyClock_le current tag D hbi,?_⟩
    change Runs program _ (.inl (.fields 0)) _ (.inl .ret) _
    exact body_run limits current tag out
  obtain ⟨m,hm,ht⟩:=entry_run (dims 3) 3 limits indices tag (hl 3) (hc 3 (le_refl _))
    (fun i out=>record tag (Function.update indices 3 (List.replicate i true)) out) (stageBudget D tag.length 0) hchild output
  refine ⟨m,hm.trans ?_,ht⟩
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hd 3)) 5

/-- Actual closed physical level2, retaining all child calls and original counter copies. -/
theorem level2_run (dims:Fin 4→ℕ) (limits indices:Fin 4→List Bool) (tag output:List Bool) (D:ℕ)
    (hl:∀j,limits j=List.replicate (dims j) true) (hd:∀j,dims j≤D)
    (hb:IndexBound D indices) (hc:ReadyFrom 2 indices) :
    ∃m≤stageBudget D tag.length 2,Runs program m (.inl (.entry 2)) (store limits indices tag output)
      (.inl .ret) (store limits indices tag (box2 dims indices tag output)) := by
  have hchild:∀i<dims 2,∀out,∃m≤stageBudget D tag.length 1,
      Runs program m (childEntry 2)
        (store limits (Function.update indices 2 (List.replicate i true)) tag out)
        (.inl .ret) (store limits (Function.update indices 2 (List.replicate i true)) tag
          (box3 dims (Function.update indices 2 (List.replicate i true)) tag out)):=by
    intro i hi out
    let current:=Function.update indices 2 (List.replicate i true)
    have hbi:IndexBound D current:=update_bound indices 2 i D hb ((Nat.le_of_lt hi).trans (hd 2))
    have hci:ReadyFrom 3 current:=update_ready indices 2 (List.replicate i true) hc
    obtain ⟨m,hm,ht⟩:=level3_run dims limits current tag out D hl hd hbi hci
    refine ⟨m,hm,?_⟩
    change Runs program m (.inl (.entry 3)) _ (.inl .ret) _
    exact ht
  obtain ⟨m,hm,ht⟩:=entry_run (dims 2) 2 limits indices tag (hl 2) (hc 2 (le_refl _))
    (fun i out=>box3 dims (Function.update indices 2 (List.replicate i true)) tag out) (stageBudget D tag.length 1) hchild output
  refine ⟨m,hm.trans ?_,ht⟩
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hd 2)) 5

/-- Actual closed physical level1, retaining all child calls and original counter copies. -/
theorem level1_run (dims:Fin 4→ℕ) (limits indices:Fin 4→List Bool) (tag output:List Bool) (D:ℕ)
    (hl:∀j,limits j=List.replicate (dims j) true) (hd:∀j,dims j≤D)
    (hb:IndexBound D indices) (hc:ReadyFrom 1 indices) :
    ∃m≤stageBudget D tag.length 3,Runs program m (.inl (.entry 1)) (store limits indices tag output)
      (.inl .ret) (store limits indices tag (box1 dims indices tag output)) := by
  have hchild:∀i<dims 1,∀out,∃m≤stageBudget D tag.length 2,
      Runs program m (childEntry 1)
        (store limits (Function.update indices 1 (List.replicate i true)) tag out)
        (.inl .ret) (store limits (Function.update indices 1 (List.replicate i true)) tag
          (box2 dims (Function.update indices 1 (List.replicate i true)) tag out)):=by
    intro i hi out
    let current:=Function.update indices 1 (List.replicate i true)
    have hbi:IndexBound D current:=update_bound indices 1 i D hb ((Nat.le_of_lt hi).trans (hd 1))
    have hci:ReadyFrom 2 current:=update_ready indices 1 (List.replicate i true) hc
    obtain ⟨m,hm,ht⟩:=level2_run dims limits current tag out D hl hd hbi hci
    refine ⟨m,hm,?_⟩
    change Runs program m (.inl (.entry 2)) _ (.inl .ret) _
    exact ht
  obtain ⟨m,hm,ht⟩:=entry_run (dims 1) 1 limits indices tag (hl 1) (hc 1 (le_refl _))
    (fun i out=>box2 dims (Function.update indices 1 (List.replicate i true)) tag out) (stageBudget D tag.length 2) hchild output
  refine ⟨m,hm.trans ?_,ht⟩
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hd 1)) 5

/-- Actual closed physical level0, retaining all child calls and original counter copies. -/
theorem level0_run (dims:Fin 4→ℕ) (limits indices:Fin 4→List Bool) (tag output:List Bool) (D:ℕ)
    (hl:∀j,limits j=List.replicate (dims j) true) (hd:∀j,dims j≤D)
    (hb:IndexBound D indices) (hc:ReadyFrom 0 indices) :
    ∃m≤stageBudget D tag.length 4,Runs program m (.inl (.entry 0)) (store limits indices tag output)
      (.inl .ret) (store limits indices tag (box0 dims indices tag output)) := by
  have hchild:∀i<dims 0,∀out,∃m≤stageBudget D tag.length 3,
      Runs program m (childEntry 0)
        (store limits (Function.update indices 0 (List.replicate i true)) tag out)
        (.inl .ret) (store limits (Function.update indices 0 (List.replicate i true)) tag
          (box1 dims (Function.update indices 0 (List.replicate i true)) tag out)):=by
    intro i hi out
    let current:=Function.update indices 0 (List.replicate i true)
    have hbi:IndexBound D current:=update_bound indices 0 i D hb ((Nat.le_of_lt hi).trans (hd 0))
    have hci:ReadyFrom 1 current:=update_ready indices 0 (List.replicate i true) hc
    obtain ⟨m,hm,ht⟩:=level1_run dims limits current tag out D hl hd hbi hci
    refine ⟨m,hm,?_⟩
    change Runs program m (.inl (.entry 1)) _ (.inl .ret) _
    exact ht
  obtain ⟨m,hm,ht⟩:=entry_run (dims 0) 0 limits indices tag (hl 0) (hc 0 (le_refl _))
    (fun i out=>box1 dims (Function.update indices 0 (List.replicate i true)) tag out) (stageBudget D tag.length 3) hchild output
  refine ⟨m,hm.trans ?_,ht⟩
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hd 0)) 5

/-- A complete actual finite range fold has the literal original ascending list order. -/
theorem rangeFold_range (n:ℕ) (F:ℕ→List Bool→List Bool) (tail:List Bool) :
    rangeFold n F tail=(List.range n).foldr F tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih => simp only [rangeFold,ih,List.range_succ,List.foldr_append,List.foldr_cons,List.foldr_nil]
end RiemannGaussian.SemiprimeD1StackCartesian4Execution
