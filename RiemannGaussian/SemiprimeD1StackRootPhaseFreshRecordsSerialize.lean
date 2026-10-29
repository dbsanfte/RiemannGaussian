/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsPrimitives
/-! # All eighty-five actual stopped words are framed in the original fixed order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsSerialize
open SemiprimeD1StackRootPhaseFreshRecords SemiprimeD1StackRootPhaseFreshRecordsEncoding
open SemiprimeD1StackRootPhaseFreshRecordsPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Total physical cell mass of the actual eighty-five stopped Fresh words. -/
def freshMass (bank:Stack→List Bool) : Nat :=∑k:F.Stack,(bank (freshStack k)).length
/-- Every framed input word is charged to the actual stopped-bank cell mass. -/
theorem word_le_mass (bank:Stack→List Bool) (k:F.Stack) : (bank (freshStack k)).length≤freshMass bank :=by
  exact Finset.single_le_sum (f:=fun k:F.Stack=>(bank (freshStack k)).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
/-- Writing record bytes cannot change any actual stopped Fresh word. -/
theorem record_fresh (bank:Stack→List Bool) (word:List Bool) (k:F.Stack) :
    Function.update bank (aux .record) word (freshStack k)=bank (freshStack k) :=
  Function.update_of_ne (by rw [fresh_private];simp [cachePrivate,aux]) _ _
/-- Record framing retains exactly the same stopped-bank mass. -/
theorem freshMass_update (bank:Stack→List Bool) (word:List Bool) :
    freshMass (Function.update bank (aux .record) word)=freshMass bank :=by
  unfold freshMass
  apply Finset.sum_congr rfl
  intro k _
  rw [record_fresh]
/-- Proof-side finite framedPrefix of the declared complete physical record order. -/
def framedPrefix (n:Nat) (bank:Stack→List Bool) (tail:List Bool) : List Bool :=
  (SemiprimeD1StackRootPhaseFreshRecordsInventory.roles.take n).foldr (fun k rest=>frame (bank (freshStack k)) rest) tail
/-- One further finite role contributes its frame at the end of that framedPrefix. -/
theorem prefix_succ (n:Nat) (hn:n<85) (bank:Stack→List Bool) (tail:List Bool) :
    framedPrefix (n+1) bank tail=framedPrefix n bank (frame (bank (freshStack (I.role ⟨n,hn⟩))) tail) :=by
  have hlen:n<SemiprimeD1StackRootPhaseFreshRecordsInventory.roles.length:=by simpa only [SemiprimeD1StackRootPhaseFreshRecordsInventory.roles_length] using hn
  unfold framedPrefix
  rw [List.take_succ_eq_append_getElem hlen,List.foldr_append]
  rfl
/-- A paid record write retains all words used by the remaining fixed frame sites. -/
theorem prefix_update (n:Nat) (bank:Stack→List Bool) (word tail:List Bool) :
    framedPrefix n (Function.update bank (aux .record) word) tail=framedPrefix n bank tail :=by
  unfold framedPrefix
  congr 1
  funext k rest
  rw [record_fresh]
/-- Exact actual reverse-position framing loop. Each source word is physically
copied/restored by Frame; there is one real call/return per role and one final jump. -/
theorem prefix_run (n:Nat) (hn:n≤85) (bank:Stack→List Bool) (hs:bank (aux .copyScratch)=[]) :
    ∃t≤n*(6*freshMass bank+5)+1,
      Runs program t (.serialize ⟨85-n,by omega⟩) bank .allocate
        (Function.update bank (aux .record) (framedPrefix n bank (bank (aux .record)))) :=by
  induction n generalizing bank with
  | zero=>
    refine ⟨1,by omega,?_⟩
    have hz:(⟨85-0,by omega⟩:Fin 86)=85:=Fin.ext rfl
    simpa only [hz,framedPrefix,List.take_zero,List.foldr_nil,Function.update_eq_self] using serialization_end bank
  | succ n ih=>
    have hlt:n<85:=by omega
    let position:Fin 86:=⟨85-(n+1),by omega⟩
    let i:Fin 85:=⟨n,hlt⟩
    let word:=frame (bank (freshStack (I.role i))) (bank (aux .record))
    let next:=Function.update bank (aux .record) word
    have hc:=frame_call position (by dsimp [position];omega) bank hs
    have hi:(⟨84-position.val,by dsimp [position];omega⟩:Fin 85)=i:=by apply Fin.ext;dsimp [position,i];omega
    have hp:(⟨position.val+1,by dsimp [position];omega⟩:Fin 86)=⟨85-n,by omega⟩:=by apply Fin.ext;dsimp [position];omega
    dsimp only at hc
    rw [hi,hp] at hc
    change Runs program (6*(bank (freshStack (I.role i))).length+5) (.serialize position) bank
      (.serialize ⟨85-n,by omega⟩) next at hc
    have hs':next (aux .copyScratch)=[]:=by dsimp [next];rw [Function.update_of_ne (by decide : aux .copyScratch≠aux .record),hs]
    obtain ⟨t,ht,hr⟩:=ih (by omega) next hs'
    have hm:freshMass next=freshMass bank:=freshMass_update bank word
    rw [hm] at ht
    have he:Function.update next (aux .record) (framedPrefix n next (next (aux .record)))=
        Function.update bank (aux .record) (framedPrefix (n+1) bank (bank (aux .record))):=by
      dsimp only [next]
      rw [Function.update_same,prefix_update,Function.update_idem,prefix_succ n hlt]
    rw [he] at hr
    refine ⟨(6*(bank (freshStack (I.role i))).length+5)+t,?_,compose hc hr⟩
    have hw:=word_le_mass bank (I.role i)
    nlinarith
/-- Actual complete serialization has EXACTLY the entire stopped bank in the
fixed forward role order, including all empty and rejected output fields. -/
theorem serialize_run (bank:Stack→List Bool) (hs:bank (aux .copyScratch)=[]) (hr:bank (aux .record)=[]) :
    ∃t≤85*(6*freshMass bank+5)+1,Runs program t (.serialize 0) bank .allocate
      (Function.update bank (aux .record) (freshRecord (fun k=>bank (freshStack k)))) :=by
  have h:=prefix_run 85 (by omega) bank hs
  have hz:(⟨85-85,by omega⟩:Fin 86)=0:=Fin.ext rfl
  simpa only [hz,framedPrefix,hr,List.take_of_length_le (by rw [SemiprimeD1StackRootPhaseFreshRecordsInventory.roles_length]),
    freshRecord] using h
end RiemannGaussian.SemiprimeD1StackRootPhaseFreshRecordsSerialize
