/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueView
import RiemannGaussian.SemiprimeD1StackProcedureFragments
/-! # Actual five-field catalogue parser into the real raw descriptor operands -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueFields
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueView
open SemiprimeD1StackProcedureFragments (Runs included_call one_base)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Actual one-field parser call, including every parse/reverse bit and the real return. -/
theorem field_call (part:Fin 5) (store:Stack→List Bool) (word tail:List Bool)
    (hi:store descriptorReader=frame word tail) (ho:store (cache part)=[])
    (hs:store scratch=[]) (hv:store valid=[]) :
    Runs program (8*word.length+7) (.local (.field part)) store (.local (.valid part))
      (Function.update (Function.update (Function.update store descriptorReader tail) (cache part) word) valid [true]):=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State Field.Stack Field.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack part) store before.store store:=by
    constructor
    · intro k;rcases k with k|k
      · cases k <;> simp [fieldStack,before,SemiprimeD1TensorTapeFieldBytecode.initial,
          SemiprimeD1TensorTapeFieldMachine.contents,hi,ho,hs]
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program (fieldStack part) (Label.field part) (field_injective part) Field.code
    (Field.active .tagPop (none,false)) (fun _=>rfl) (.local (.field part)) (.local (.valid part))
    rfl (8*word.length+6) before after _ _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update (fieldStack part) (field_injective part) store before.store store hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack part) (field_injective part) store _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack part) (field_injective part) store _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
      (.inl .output) word) (.inr ()) [true]=after.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  simpa only [he,fieldStack] using h2
/-- Proof-side prefix of fields ALREADY physically parsed, with every later cache empty. -/
def parsed (n:Nat) (words:Fin 5→List Bool) :Fin 5→List Bool:=
  fun k=>if k.val<n then words k else []
/-- Actual next-field suffix of the five-frame input record. -/
def suffix (words:Fin 5→List Bool) (n:Nat) (tail:List Bool) :List Bool:=
  if n=0 then frame (words 0) (frame (words 1) (frame (words 2) (frame (words 3) (frame (words 4) tail))))
  else if n=1 then frame (words 1) (frame (words 2) (frame (words 3) (frame (words 4) tail)))
  else if n=2 then frame (words 2) (frame (words 3) (frame (words 4) tail))
  else if n=3 then frame (words 3) (frame (words 4) tail)
  else if n=4 then frame (words 4) tail else tail
/-- One physically written field advances the exact five-field partial cache. -/
theorem parsed_step (part:Fin 5) (words:Fin 5→List Bool) :
    Function.update (parsed part.val words) part (words part)=parsed (part.val+1) words:=by
  funext k;fin_cases part <;> fin_cases k <;> rfl
/-- The actual parser can start only with its not-yet-written output empty. -/
theorem parsed_current (part:Fin 5) (words:Fin 5→List Bool) :parsed part.val words part=[]:=by
  simp only [parsed,Nat.lt_irrefl,ite_false]
/-- Actual field input has exactly the next framed source payload and its real remaining suffix. -/
theorem suffix_step (part:Fin 5) (words:Fin 5→List Bool) (tail:List Bool) :
    suffix words part.val tail=frame (words part) (suffix words (part.val+1) tail):=by fin_cases part <;> rfl
/-- Every partial parse uses a real catalogue projection and physically consumes the written valid bit. -/
theorem parse_one (part:Fin 5) (f:F.Stack→List Bool) (v:V.Stack→List Bool)
    (words:Fin 5→List Bool) (tail hist out:List Bool)
    (hr:v catalogueOutput=suffix words part.val tail) :
    Runs program (8*(words part).length+8) (.local (.field part))
      (data f v (parsed part.val words) hist out) (nextField part)
      (data f (Function.update v catalogueOutput (suffix words (part.val+1) tail))
        (parsed (part.val+1) words) hist out):=by
  let nextV:=Function.update v catalogueOutput (suffix words (part.val+1) tail)
  let nextW:=parsed (part.val+1) words
  have h0:=field_call part (data f v (parsed part.val words) hist out) (words part)
    (suffix words (part.val+1) tail)
    (by change v catalogueOutput=_;rw [hr,suffix_step])
    (by rw [data_cache,parsed_current]) (data_scratch _ _ _ _ _ _) (data_valid _ _ _ _ _ _)
  have he:Function.update (Function.update (Function.update (data f v (parsed part.val words) hist out)
      descriptorReader (suffix words (part.val+1) tail)) (cache part) (words part)) valid [true]=
      data f nextV nextW hist out [true]:=by
    change Function.update (Function.update (Function.update _ (catalogueStack catalogueOutput) _) _ _) _ _=_
    rw [update_catalogue,update_cache,parsed_step,update_valid]
  rw [he] at h0
  have h1:Runs program 1 (.local (.valid part)) (data f nextV nextW hist out [true])
      (nextField part) (data f nextV nextW hist out):=by
    apply one_base program _ _ (.pop valid (.local .abort) (.local .abort) (nextField part)) _ _ rfl rfl
    exact update_valid _ _ _ _ _ _ _
  have h:=h0.trans h1
  simpa only [show (8*(words part).length+7)+1=8*(words part).length+8 by omega] using h
/-- All five original raw field bytes, proof-side sum only. -/
def mass (words:Fin 5→List Bool) :Nat:=∑i:Fin 5,(words i).length
/-- Physical parser chain writes ALL five actual fields and consumes exactly their complete record. -/
theorem parse_run (f:F.Stack→List Bool) (v:V.Stack→List Bool) (words:Fin 5→List Bool)
    (tail hist out:List Bool) (hr:v catalogueOutput=suffix words 0 tail) :
    Runs program (8*mass words+40) (.local (.field 0)) (data f v (fun _=>[]) hist out)
      (.local .row) (data f (Function.update v catalogueOutput tail) words hist out):=by
  let view (n:Nat):V.Stack→List Bool:=Function.update v catalogueOutput (suffix words n tail)
  have h0:=parse_one 0 f v words tail hist out hr
  have h1:=parse_one 1 f (view 1) words tail hist out (Function.update_self _ _ _)
  have h2:=parse_one 2 f (view 2) words tail hist out (Function.update_self _ _ _)
  have h3:=parse_one 3 f (view 3) words tail hist out (Function.update_self _ _ _)
  have h4:=parse_one 4 f (view 4) words tail hist out (Function.update_self _ _ _)
  simp only [view,Function.update_idem] at h1 h2 h3 h4
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  have hp0:parsed 0 words=fun _=>[]:=by funext k;exact ite_eq_right (Nat.not_lt_zero _)
  have hp5:parsed 5 words=words:=by funext k;exact ite_eq_left k.isLt
  have hs:suffix words 5 tail=tail:=rfl
  have ht:(8*(words 0).length+8)+((8*(words 1).length+8)+((8*(words 2).length+8)+
      ((8*(words 3).length+8)+(8*(words 4).length+8))))=8*mass words+40:=by
    unfold mass
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero,Nat.add_zero]
    change _=8*((words 0).length+((words 1).length+((words 2).length+((words 3).length+(words 4).length))))+40
    omega
  rw [ht] at h
  change Runs program (8*mass words+40) (.local (.field 0)) (data f v (parsed 0 words) hist out)
    (.local .row) (data f (Function.update v catalogueOutput (suffix words 5 tail)) (parsed 5 words) hist out) at h
  simpa only [hp0,hp5,hs] using h
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueFields
