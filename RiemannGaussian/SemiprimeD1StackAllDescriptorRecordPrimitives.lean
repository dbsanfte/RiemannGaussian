/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordWiring
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecordInventory
/-! # Paid tag copy and literal eighteen-state physical constructor decoder -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordPrimitives
open SemiprimeD1StackAllDescriptorRecord SemiprimeD1StackAllDescriptorRecordWiring
open SemiprimeD1StackProcedureTrace
/-- Consecutive fragments execute the same fixed physical source and retain outer returns. -/
theorem compose {m n : Nat} {pc mid next : Label} {before middle after : Stack→List Bool}
    (h : Runs program m pc before mid middle) (g : Runs program n mid middle next after) :
    Runs program (m+n) pc before next after :=runs_trans program _ _ _ _ _ _ _ _ h g
/-- Actual preserving tag copy reads the original field and fills only the private reader. -/
theorem copy_tag (d : Stack→List Bool) (hr : d tagReader=[]) (hs : d copyScratch=[]) :
    Runs program (5*(d (source 1)).length+4) (.inl .start) d (.inl (.decode 0))
      (Function.update d tagReader (d (source 1))) :=by
  apply included_call program copyStack (fun pc=>.inr (.inl pc)) copyStack_injective
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (.inl .start) (.inl (.decode 0)) rfl (5*(d (source 1)).length+3)
    (SemiprimeD1StackCopy.state 0 none (d (source 1)) [] [])
    (SemiprimeD1StackCopy.done (d (source 1)) (d (source 1)++[]))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words (d (source 1)) [] none
  · constructor
    · intro k;fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,hr,hs]
    · intro k _;rfl
  · constructor
    · intro k
      fin_cases k
      · change Function.update d tagReader (d (source 1)) (source 1)=d (source 1)
        exact Function.update_of_ne (by decide) _ _
      · change Function.update d tagReader (d (source 1)) tagReader=d (source 1)++[]
        simp only [Function.update_same,List.append_nil]
      · change Function.update d tagReader (d (source 1)) copyScratch=[]
        rw [Function.update_of_ne (by decide : copyScratch≠tagReader)]
        exact hs
    · intro k hk
      have hne:tagReader≠k:=hk 1
      exact Function.update_of_ne (Ne.symm hne) _ _
/-- Each copied true marker is physically consumed by one actual transition. -/
theorem tag_prefix (n i : Nat) (hi:i+n<18) (d : Stack→List Bool) (tail : List Bool) :
    Runs program n (.inl (.decode ⟨i,by omega⟩))
      (Function.update d tagReader (List.replicate n true++tail))
      (.inl (.decode ⟨i+n,hi⟩)) (Function.update d tagReader tail) :=by
  induction n generalizing i with
  | zero=>simpa only [List.replicate_zero,List.nil_append,Nat.add_zero] using
      runs_refl program (.inl (.decode ⟨i,hi⟩)) (Function.update d tagReader tail)
  | succ n ih=>
    have hit:i<17:=by omega
    have hc:program (.inl (.decode ⟨i,by omega⟩))=.base (.pop tagReader (dispatch ⟨i,by omega⟩)
      (.inl .abort) (.inl (.decode ⟨i+1,by omega⟩))):=by simp only [program,nextDecode,dite_eq_left hit]
    have h0:Runs program 1 (.inl (.decode ⟨i,by omega⟩))
        (Function.update d tagReader (List.replicate (n+1) true++tail))
        (.inl (.decode ⟨i+1,by omega⟩)) (Function.update d tagReader (List.replicate n true++tail)):=by
      apply one_base program _ _ _ _ _ hc
      · rfl
      · change Function.update (Function.update d tagReader (List.replicate (n+1) true++tail)) tagReader
          (List.replicate (n+1) true++tail).tail=_
        simp only [List.replicate_succ,List.cons_append,List.tail_cons,Function.update_idem]
    have h1:=ih (i+1) (by omega)
    have he:(⟨i+1+n,by omega⟩:Fin 18)=⟨i+(n+1),hi⟩:=by apply Fin.ext;change i+1+n=i+(n+1);omega
    rw [he] at h1
    simpa only [show 1+n=n+1 by omega] using compose h0 h1
/-- Physical EOF dispatch occurs only after the complete copied original tag is consumed. -/
theorem tag_decode (code : Fin 18) (d : Stack→List Bool) :
    Runs program (code.val+1) (.inl (.decode 0)) (Function.update d tagReader (List.replicate code.val true))
      (dispatch code) (Function.update d tagReader []) :=by
  have h0:=tag_prefix code.val 0 (by omega) d []
  simp only [List.append_nil,Nat.zero_add] at h0
  have h1:Runs program 1 (.inl (.decode code)) (Function.update d tagReader [])
      (dispatch code) (Function.update d tagReader []):=by
    apply one_base program _ _ (.pop tagReader (dispatch code) (.inl .abort) (nextDecode code)) _ _ rfl
    · rfl
    · change Function.update (Function.update d tagReader []) tagReader []=_
      simp only [Function.update_idem]
  exact compose h0 h1
/-- Real acquisition-free frontend trace: copy actual raw tag, consume every marker,
then select exactly one literal family entry, preserving all original fields. -/
theorem dispatch_run (raw : Fin 6→List Bool) (bank hist out : List Bool) (code : Fin 18)
    (htag:raw 1=List.replicate code.val true) :
    Runs program (6*code.val+5) (.inl .start) (cleanData raw bank hist out)
      (dispatch code) (cleanData raw bank hist out) :=by
  have h0:=copy_tag (cleanData raw bank hist out) rfl rfl
  change Runs program (5*(raw 1).length+4) _ _ _ (Function.update (cleanData raw bank hist out) tagReader (raw 1)) at h0
  rw [htag,List.length_replicate] at h0
  have h1:=tag_decode code (cleanData raw bank hist out)
  have he:Function.update (cleanData raw bank hist out) tagReader []=cleanData raw bank hist out:=by
    funext k
    by_cases hk:k=tagReader
    · subst k;rfl
    · exact Function.update_of_ne hk _ _
  rw [he] at h1
  convert compose h0 h1 using 1;omega
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordPrimitives
