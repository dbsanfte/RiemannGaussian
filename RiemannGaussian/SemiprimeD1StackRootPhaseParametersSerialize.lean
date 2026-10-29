/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseParametersPrimitives
/-! # All forty-eight actual stopped words are framed in the original fixed order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseParametersSerialize
open SemiprimeD1StackRootPhaseParameters SemiprimeD1StackRootPhaseParametersEncoding
open SemiprimeD1StackRootPhaseParametersPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Total physical cell mass of the actual forty-eight stopped phase words. -/
def phaseMass (bank:Stack→List Bool) : Nat :=∑k:P.Stack,(bank (phaseStack k)).length
/-- Every framed input word is charged to the actual stopped-bank cell mass. -/
theorem word_le_mass (bank:Stack→List Bool) (k:P.Stack) : (bank (phaseStack k)).length≤phaseMass bank :=by
  exact Finset.single_le_sum (f:=fun k:P.Stack=>(bank (phaseStack k)).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
/-- Writing record bytes cannot change any actual stopped phase word. -/
theorem record_phase (bank:Stack→List Bool) (word:List Bool) (k:P.Stack) :
    Function.update bank (aux .record) word (phaseStack k)=bank (phaseStack k) :=
  Function.update_of_ne (by simp [phaseStack,aux]) _ _
/-- Record framing retains exactly the same stopped-bank mass. -/
theorem phaseMass_update (bank:Stack→List Bool) (word:List Bool) :
    phaseMass (Function.update bank (aux .record) word)=phaseMass bank :=by
  rfl
/-- Proof-side finite framedPrefix of the declared complete physical record order. -/
def framedPrefix (n:Nat) (bank:Stack→List Bool) (tail:List Bool) : List Bool :=
  (I.roles.take n).foldr (fun k rest=>frame (bank (phaseStack k)) rest) tail
/-- One further finite role contributes its frame at the end of that framedPrefix. -/
theorem prefix_succ (n:Nat) (hn:n<48) (bank:Stack→List Bool) (tail:List Bool) :
    framedPrefix (n+1) bank tail=framedPrefix n bank (frame (bank (phaseStack (I.role ⟨n,hn⟩))) tail) :=by
  have hlen:n<I.roles.length:=by simpa only [SemiprimeD1StackRootPhaseParametersInventory.roles_length] using hn
  unfold framedPrefix
  rw [List.take_succ_eq_append_getElem hlen,List.foldr_append]
  rfl
/-- A paid record write retains all words used by the remaining fixed frame sites. -/
theorem prefix_update (n:Nat) (bank:Stack→List Bool) (word tail:List Bool) :
    framedPrefix n (Function.update bank (aux .record) word) tail=framedPrefix n bank tail :=by
  rfl
/-- Exact actual reverse-position framing loop. Each source word is physically
copied/restored by Frame; there is one real call/return per role and one final jump. -/
theorem prefix_run (n:Nat) (hn:n≤48) (bank:Stack→List Bool) (hs:bank (aux .copyScratch)=[]) :
    ∃t≤n*(6*phaseMass bank+5)+1,
      Runs program t (.serialize ⟨48-n,by omega⟩) bank .allocate
        (Function.update bank (aux .record) (framedPrefix n bank (bank (aux .record)))) :=by
  induction n generalizing bank with
  | zero=>
    refine ⟨1,by omega,?_⟩
    have hz:(⟨48-0,by omega⟩:Fin 49)=48:=Fin.ext rfl
    simpa only [hz,framedPrefix,List.take_zero,List.foldr_nil,Function.update_eq_self] using serialization_end bank
  | succ n ih=>
    have hlt:n<48:=by omega
    let position:Fin 49:=⟨48-(n+1),by omega⟩
    let i:Fin 48:=⟨n,hlt⟩
    let word:=frame (bank (phaseStack (I.role i))) (bank (aux .record))
    let next:=Function.update bank (aux .record) word
    have hc:=frame_call position (by dsimp [position];omega) bank hs
    have hi:(⟨47-position.val,by dsimp [position];omega⟩:Fin 48)=i:=by apply Fin.ext;dsimp [position,i];omega
    have hp:(⟨position.val+1,by dsimp [position];omega⟩:Fin 49)=⟨48-n,by omega⟩:=by apply Fin.ext;dsimp [position];omega
    dsimp only at hc
    rw [hi,hp] at hc
    change Runs program (6*(bank (phaseStack (I.role i))).length+5) (.serialize position) bank
      (.serialize ⟨48-n,by omega⟩) next at hc
    have hs':next (aux .copyScratch)=[]:=by dsimp [next];rw [Function.update_of_ne (by decide : aux .copyScratch≠aux .record),hs]
    obtain ⟨t,ht,hr⟩:=ih (by omega) next hs'
    have hm:phaseMass next=phaseMass bank:=phaseMass_update bank word
    rw [hm] at ht
    have he:Function.update next (aux .record) (framedPrefix n next (next (aux .record)))=
        Function.update bank (aux .record) (framedPrefix (n+1) bank (bank (aux .record))):=by
      dsimp only [next]
      rw [Function.update_same,prefix_update,Function.update_idem,prefix_succ n hlt]
    rw [he] at hr
    refine ⟨(6*(bank (phaseStack (I.role i))).length+5)+t,?_,compose hc hr⟩
    have hw:=word_le_mass bank (I.role i)
    nlinarith
/-- Actual complete serialization has EXACTLY the entire stopped bank in the
fixed forward role order, including all empty and rejected output fields. -/
theorem serialize_run (bank:Stack→List Bool) (hs:bank (aux .copyScratch)=[]) (hr:bank (aux .record)=[]) :
    ∃t≤48*(6*phaseMass bank+5)+1,Runs program t (.serialize 0) bank .allocate
      (Function.update bank (aux .record) (phaseRecord (fun k=>bank (phaseStack k)))) :=by
  have h:=prefix_run 48 (by omega) bank hs
  have hz:(⟨48-48,by omega⟩:Fin 49)=0:=Fin.ext rfl
  simpa only [hz,framedPrefix,hr,List.take_of_length_le (by rw [SemiprimeD1StackRootPhaseParametersInventory.roles_length]),
    phaseRecord] using h
end RiemannGaussian.SemiprimeD1StackRootPhaseParametersSerialize
