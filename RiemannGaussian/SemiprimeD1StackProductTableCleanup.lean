/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableSpec
import RiemannGaussian.SemiprimeD1StackProductTablePrimitives
/-! # Physical full checker cleanup between product-table leaves -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableCleanup
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableSpec
open SemiprimeD1StackProductTablePrimitives SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
/-- Fixed finite-role equality used only to prove the static cleanup inventory. -/
local instance : BEq P.Stack := ⟨fun a b=>decide (a=b)⟩
/-- Static cleanup-role Boolean equality agrees with actual role identity. -/
local instance : LawfulBEq P.Stack where
  eq_of_beq := by intro a b h;exact of_decide_eq_true h
  rfl := by intro a;exact decide_eq_true rfl
attribute [local irreducible] checkerRoles
/-- Proof view of exactly the already visited static cleanup roles. -/
def cleanPrefix (data : Stack→List Bool) (n : ℕ) : Stack→List Bool
  | .inl k=>if k∈checkerRoles.take n then [] else data (.inl k)
  | .inr k=>data (.inr k)
/-- Exact clean reusable checker state; every private caller cell is preserved. -/
def clean (data : Stack→List Bool) : Stack→List Bool
  | .inl _=>[]
  | .inr k=>data (.inr k)
/-- Proof-side spelling of a position in the fixed76-role cleanup control. -/
def clearStart (n : ℕ) : Label := if h : n<76 then .clear ⟨n,h⟩ else .clearDone
/-- An empty visited prefix has changed no physical cell. -/
theorem cleanPrefix_zero (data : Stack→List Bool) : cleanPrefix data 0=data := by
  funext k;cases k <;> simp only [cleanPrefix,List.take_zero,List.not_mem_nil,ite_false]
/-- Full coverage proves actual cleanup resets ALL76 roles, not only live fields. -/
theorem cleanPrefix_full (data : Stack→List Bool) : cleanPrefix data 76=clean data := by
  have ht : checkerRoles.take 76=checkerRoles := by rw [←checkerRoles_length,List.take_length]
  funext k;cases k with
  | inl k=>simp only [cleanPrefix,ht,checkerRoles_complete k,ite_true,clean]
  | inr k=>rfl
/-- The actual register update matches precisely the next visited static role. -/
theorem cleanPrefix_step (data : Stack→List Bool) (pos : Fin 76) :
    Function.update (cleanPrefix data pos.val) (clearRole pos) []=cleanPrefix data (pos.val+1) := by
  have hp : pos.val<checkerRoles.length := by rw [checkerRoles_length];exact pos.isLt
  rw [clearRole_eq]
  funext k
  cases k with
  | inl k=>
    by_cases he : k=checkerRoles[pos.val]
    · subst k
      rw [Function.update_same]
      simp only [cleanPrefix,List.take_succ_eq_append_getElem hp,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,or_true,ite_true]
    · rw [Function.update_of_ne (by intro h;exact he (Sum.inl.inj h))]
      simp only [cleanPrefix,List.take_succ_eq_append_getElem hp,List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false,he,or_false]
  | inr k=>rw [Function.update_of_ne (by intro h;cases h)];rfl
/-- Every prefix clear can only shrink an original cell. -/
theorem cleanPrefix_length (data : Stack→List Bool) (n : ℕ) (k : Stack) :
    (cleanPrefix data n k).length ≤ (data k).length := by
  cases k with
  | inl k=>
    change (if k∈checkerRoles.take n then [] else data (.inl k)).length ≤ (data (.inl k)).length
    split
    · exact Nat.zero_le _
    · exact le_rfl
  | inr k=>exact le_rfl
/-- Actual bounded-cell inventory before clearing, used solely in this proof. -/
def inventory (data : Stack→List Bool) : ℕ :=∑k : P.Stack,(data (.inl k)).length
private theorem single_sum {α : Type} [Fintype α] (f : α→ℕ) (a : α) : f a ≤ ∑k,f k :=
  Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ a)
/-- Each actually visited cell is included in the whole checker inventory. -/
theorem role_length_le (data : Stack→List Bool) (pos : Fin 76) (n : ℕ) :
    (cleanPrefix data n (clearRole pos)).length ≤ inventory data := by
  rw [clearRole_eq]
  have hi:=single_sum (fun k : P.Stack=>(data (.inl k)).length)
    (checkerRoles[pos.val]'(by rw [checkerRoles_length];exact pos.isLt))
  change (data (.inl (checkerRoles[pos.val]'(by rw [checkerRoles_length];exact pos.isLt)))).length ≤ inventory data at hi
  exact (cleanPrefix_length data n _).trans hi
/-- Static finite control advances without any data/address lookup oracle. -/
theorem next_eq (pos : Fin 76) : clearNext pos=clearStart (pos.val+1) := by
  unfold clearNext clearStart
  split
  · next h=>rw [dite_eq_left (by omega : pos.val+1<76)]
  · next h=>rw [dite_eq_right (by omega : ¬pos.val+1<76)]
/-- Every cleanup role is physically drained; no full-store reset operation is
introduced. The bound counts original payloads and every actual EOF visit. -/
theorem clear_runs (data : Stack→List Bool) (n left : ℕ) (h : n+left=76) :
    ∃t ≤ left*(inventory data+1),Runs program t (clearStart n) (cleanPrefix data n) .clearDone (clean data) := by
  induction left generalizing n with
  | zero=>
    have hn : n=76 := by omega
    subst n
    rw [cleanPrefix_full]
    refine ⟨0,by omega,?_⟩
    exact runs_refl program .clearDone (clean data)
  | succ left ih=>
    have hn : n<76 := by omega
    let pos : Fin 76:=⟨n,hn⟩
    have hd:=drain (.clear pos) (clearNext pos) (clearRole pos) rfl (cleanPrefix data n)
    have hs : Function.update (cleanPrefix data n) (clearRole pos) []=cleanPrefix data (n+1) := cleanPrefix_step data pos
    rw [next_eq,hs] at hd
    obtain ⟨t,ht,hr⟩:=ih (n+1) (by omega)
    have hb:=role_length_le data pos n
    have hout:=runs_trans program _ _ _ _ _ _ _ _ hd hr
    refine ⟨(cleanPrefix data n (clearRole pos)).length+1+t,?_,?_⟩
    · rw [Nat.succ_mul];omega
    · simpa only [clearStart,dite_eq_left hn] using hout
/-- Real recursive-procedure return after complete checker clearing. -/
theorem clear_returns (data : Stack→List Bool) :
    ∃t ≤ 76*(inventory data+1)+1,Returns program t (.clear 0) data (clean data) := by
  obtain ⟨t,ht,hr⟩:=clear_runs data 0 76 rfl
  rw [cleanPrefix_zero] at hr
  refine ⟨t+1,by omega,?_⟩
  exact of_runs program t (.clear 0) .clearDone data (clean data) hr rfl
end RiemannGaussian.SemiprimeD1StackProductTableCleanup
