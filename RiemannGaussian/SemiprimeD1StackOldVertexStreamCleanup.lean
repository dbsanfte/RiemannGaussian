/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOldVertexStreamPrimitives
/-! # Every literal vertex-workspace word is physically drained
All169 source/private/shadow locations are visited. The four immutable caller
headers lie outside that raw work bank. No subtree elapsed clock is an operand
width: the cleanup clock uses only actual stopped workspace bytes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOldVertexStreamCleanup
open SemiprimeD1StackOldVertexStream SemiprimeD1StackOldVertexStreamRoles
open SemiprimeD1StackProcedureTrace
namespace P
export SemiprimeD1StackOldVertexStreamPrimitives (drain_loop join)
end P
/-- Total physically present raw work bytes, including all displaced shadows. -/
def mass (data : Stack→List Bool) : ℕ:=∑i : Fin 169,(data (work (role i))).length
/-- Each physically allocated word is paid by the complete workspace mass. -/
theorem word_le_mass (data : Stack→List Bool) (i : Fin 169) : (data (work (role i))).length≤ mass data:=
  Finset.single_le_sum (f:=fun j : Fin 169=>(data (work (role j))).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
/-- Proof-side exact store after a prefix of the literal drain sites. -/
noncomputable def cleared (data : Stack→List Bool) (position : ℕ) : Stack→List Bool:=by
  classical
  exact fun k=>if ∃i : Fin 169,i.val<position ∧ work (role i)=k then [] else data k
/-- The empty physical sweep changes nothing. -/
theorem cleared_zero (data : Stack→List Bool) : cleared data 0=data:=by
  funext k
  simp [cleared]
/-- One completed drain advances exactly one fixed cleanup label. -/
theorem cleared_succ (data : Stack→List Bool) (i : Fin 169) :
    Function.update (cleared data i.val) (work (role i)) []=cleared data (i.val+1):=by
  classical
  funext k
  by_cases he : k=work (role i)
  · subst k
    rw [Function.update_self]
    exact (ite_eq_left ⟨i,by omega,rfl⟩).symm
  · rw [Function.update_of_ne he]
    have hh : (∃j : Fin 169,j.val < i.val+1 ∧ work (role j)=k) ↔
        (∃j : Fin 169,j.val < i.val ∧ work (role j)=k):=by
      constructor
      · rintro ⟨j,hj,hk⟩
        have hn : j.val≠i.val:=by
          intro h
          have hji : j=i:=Fin.ext h
          subst j
          exact he hk.symm
        exact ⟨j,by omega,hk⟩
      · rintro ⟨j,hj,hk⟩
        exact ⟨j,by omega,hk⟩
    simp only [cleared,hh]
/-- Draining earlier roles never enlarges a later word. -/
theorem cleared_word_le (data : Stack→List Bool) (position : ℕ) (i : Fin 169) :
    (cleared data position (work (role i))).length≤ mass data:=by
  unfold cleared
  split
  · exact Nat.zero_le _
  · exact word_le_mass data i
/-- Fixed finite successor, independent of every input word. -/
def next (i : Fin 169) : Label:=
  if h:i.val<168 then .local (.clearWork ⟨i.val+1,by omega⟩) else .local .recordTag
/-- The actual instruction at each of the169 drain sites. -/
theorem drain_code (i : Fin 169) : program (.local (.clearWork i))=
    .base (.pop (work (role i)) (next i) (.local (.clearWork i)) (.local (.clearWork i))):=rfl
/-- Every remaining literal work role is drained, including its true empty branch. -/
theorem sweep (remaining position : ℕ) (hp : position+remaining=168) (data : Stack→List Bool) :
    ∃t≤(remaining+1)*(mass data+1),
      Runs program t (.local (.clearWork ⟨position,by omega⟩)) (cleared data position)
        (.local .recordTag) (cleared data 169):=by
  induction remaining generalizing position with
  | zero=>
    have hpos : position=168:=by omega
    let i : Fin 169:=⟨position,by omega⟩
    have hn : next i=.local .recordTag:=by simp only [next,i,hpos,Nat.lt_irrefl,dite_false]
    have h0:=P.drain_loop (.local (.clearWork i)) (.local .recordTag) (work (role i))
      (cleared data position) (cleared data position (work (role i))) (by rw [drain_code,hn]) rfl
    have hc:=cleared_succ data i
    change Function.update (cleared data position) (work (role i)) []=cleared data (position+1) at hc
    rw [hc,show position+1=169 by omega] at h0
    refine ⟨_,?_,h0⟩
    have hw:=cleared_word_le data position i
    omega
  | succ remaining ih=>
    have hpos : position<168:=by omega
    let i : Fin 169:=⟨position,by omega⟩
    have hn : next i=.local (.clearWork ⟨position+1,by omega⟩):=by simp only [next,i,dite_eq_left hpos]
    have h0:=P.drain_loop (.local (.clearWork i)) (.local (.clearWork ⟨position+1,by omega⟩)) (work (role i))
      (cleared data position) (cleared data position (work (role i))) (by rw [drain_code,hn]) rfl
    have hc:=cleared_succ data i
    change Function.update (cleared data position) (work (role i)) []=cleared data (position+1) at hc
    rw [hc] at h0
    obtain ⟨t,ht,h1⟩:=ih (position+1) (by omega)
    refine ⟨_,?_,P.join h0 h1⟩
    have hw:=cleared_word_le data position i
    nlinarith
/-- All169 physical work words are zero after the whole literal sweep. -/
theorem cleared_work (data : Stack→List Bool) (k : ChoiceStack) : cleared data 169 (work k)=[]:=by
  obtain ⟨i,hi⟩:=role_complete k
  apply ite_eq_left
  exact ⟨i,i.isLt,congrArg work hi⟩
/-- Every physical parser, input header, reader and history word is retained by the work sweep. -/
theorem cleared_foreign (data : Stack→List Bool) (k : F.Stack⊕Aux) : cleared data 169 (.inr k)=data (.inr k):=by
  apply ite_eq_right
  rintro ⟨i,_,hi⟩
  cases hi
/-- Complete actual sweep from position zero, with semantic stopped bytes as its only resource. -/
theorem source_run (data : Stack→List Bool) :
    ∃t≤169*(mass data+1),Runs program t (.local (.clearWork 0)) data (.local .recordTag) (cleared data 169):=by
  obtain ⟨t,ht,hr⟩:=sweep 168 0 rfl data
  have hz : (⟨0,by decide⟩ : Fin 169)=0:=Fin.ext rfl
  exact ⟨t,ht,by simpa only [cleared_zero,hz] using hr⟩
end RiemannGaussian.SemiprimeD1StackOldVertexStreamCleanup
