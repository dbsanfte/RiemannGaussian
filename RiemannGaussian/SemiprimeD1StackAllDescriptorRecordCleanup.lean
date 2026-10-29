/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordPrimitives
/-! # Actual exhaustive private-word cleanup, charged cell by cell -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordCleanup
open SemiprimeD1StackAllDescriptorRecord SemiprimeD1StackAllDescriptorRecordInventory
open SemiprimeD1StackAllDescriptorRecordPrimitives SemiprimeD1StackProcedureTrace
/-- Mathematical physical-store size used only to bound an actual trace. -/
def mass (d : Stack→List Bool) : Nat :=∑k,(d k).length
/-- Every physical word is charged to the total initial physical data. -/
theorem word_le_mass (d : Stack→List Bool) (k : Stack) : (d k).length≤ mass d :=by
  unfold mass
  exact Finset.single_le_sum (f:=fun k:Stack=>(d k).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
/-- Exact store after the first n literal private-word drains; common data is retained. -/
noncomputable def cleared (d : Stack→List Bool) (n : Nat) : Stack→List Bool :=by
  classical
  exact Sum.elim (fun c=>d (.inl c)) (fun p : Private=>if p∈privateRoles.take n then [] else d (.inr p))
/-- Entering cleanup has not modified any acquired or private word. -/
theorem cleared_zero (d : Stack→List Bool) : cleared d 0=d :=by
  funext k;cases k <;> simp [cleared]
/-- An actual physical drain is exactly the next literal inventory prefix. -/
theorem cleared_succ (d : Stack→List Bool) (n : Fin 1252) :
    Function.update (cleared d n.val) (privateStack (privateAt n)) []=cleared d (n.val+1) :=by
  classical
  have hn:n.val<privateRoles.length:=by rw [privateRoles_length];exact n.isLt
  have ht:=List.take_succ_eq_append_getElem hn
  change privateRoles.take (n.val+1)=privateRoles.take n.val++[privateAt n] at ht
  funext k
  cases k with
  | inl c=>rfl
  | inr p=>
    by_cases hp:p=privateAt n
    · subst p
      simp only [privateStack,Function.update_same,cleared,Sum.elim_inr,ht,List.mem_append,List.mem_singleton,or_true,ite_true]
    · have he:Sum.inr p≠privateStack (privateAt n):=by intro h;exact hp (Sum.inr.inj h)
      rw [Function.update_of_ne he]
      change (if p∈privateRoles.take n.val then [] else d (.inr p))=
        (if p∈privateRoles.take (n.val+1) then [] else d (.inr p))
      rw [ht]
      simp only [List.mem_append,List.mem_singleton,hp,or_false]
/-- Cleanup never increases a word's physical cell count. -/
theorem cleared_word_le (d : Stack→List Bool) (n : Nat) (k : Stack) :
    ((cleared d n) k).length≤ mass d :=by
  cases k with
  | inl c=>exact word_le_mass d (.inl c)
  | inr p=>
    simp only [cleared,Sum.elim_inr]
    split
    · exact Nat.zero_le _
    · exact word_le_mass d (.inr p)
/-- After all1252 physical positions, every private/shadow word is empty,
while all eleven common/caller words retain their actual bytes. -/
theorem cleared_all (d : Stack→List Bool) :
    cleared d 1252=Sum.elim (fun c=>d (.inl c)) (fun _=>[]) :=by
  funext k
  cases k with
  | inl c=>rfl
  | inr p=>
    simp only [cleared,Sum.elim_inr,List.take_of_length_le (by rw [privateRoles_length]),privateRoles_complete p,ite_true]
/-- Every actual cell of every allocated private word is popped; every EOF,
including empty aliases and inactive families, is charged to this same program. -/
theorem sweep (remaining position : Nat) (h:position+remaining=1252) (d : Stack→List Bool) :
    ∃t≤remaining*(mass d+1)+1,
      Runs program t (.inl (.clear ⟨position,by omega⟩)) (cleared d position)
        (.inl .done) (cleared d 1252) :=by
  induction remaining generalizing position with
  | zero=>
    have hp:position=1252:=by omega
    subst position
    refine ⟨1,by omega,?_⟩
    apply one_base program _ _ (.jump (.inl .done)) _ _ ?_
    · rfl
    · rfl
    · simp only [program,show ¬1252<1252 by omega,dite_false]
  | succ remaining ih=>
    have hp:position<1252:=by omega
    let slot : Fin 1252:=⟨position,hp⟩
    let pc : Label:=.inl (.clear ⟨position,by omega⟩)
    let next : Label:=.inl (.clear ⟨position+1,by omega⟩)
    have hc:program pc=.base (.pop (privateStack (privateAt slot)) next pc pc):=by
      simp only [pc,next,slot,program,dite_eq_left hp]
    have hd:=SemiprimeD1StackPhysicalLoops.drain program pc next (privateStack (privateAt slot)) hc
      (cleared d position) ((cleared d position) (privateStack (privateAt slot)))
    rw [Function.update_eq_self] at hd
    have he:=cleared_succ d slot
    change Function.update (cleared d position) (privateStack (privateAt slot)) []=cleared d (position+1) at he
    rw [he] at hd
    obtain ⟨t,ht,hr⟩:=ih (position+1) (by omega)
    refine ⟨((cleared d position) (privateStack (privateAt slot))).length+1+t,?_,compose hd hr⟩
    have hw:=cleared_word_le d position (privateStack (privateAt slot))
    · nlinarith
/-- Complete prepared cleanup trace, through all actual private pops and the
final jump; only the subsequent literal halt remains to the caller. -/
theorem cleanup_run (d : Stack→List Bool) :
    ∃t≤1252*(mass d+1)+1,
      Runs program t (.inl (.clear 0)) d (.inl .done)
        (Sum.elim (fun c=>d (.inl c)) (fun _=>[])) :=by
  have h:=sweep 1252 0 rfl d
  have hz:(⟨0,by omega⟩:Fin 1253)=0:=Fin.ext rfl
  simpa only [cleared_zero,cleared_all,hz] using h
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordCleanup
