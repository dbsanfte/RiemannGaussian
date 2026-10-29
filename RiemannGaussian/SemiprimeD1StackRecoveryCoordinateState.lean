/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinate
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedState
/-! # Full physical21-role source boundaries
Eleven mathematical field names describe actual retained/parser/logger words.
The actual binary coordinate and all nine private reader roles are represented.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateState
open SemiprimeD1StackRecoveryCoordinate
namespace IX
export SemiprimeD1StackRecoveryEntriesIndexedState (view)
end IX
/-- Proof-only names for11 actual non-query boundary words, never runtime operands. -/
inductive Role where
  | cache | value | phases | reader | blocks | valid | rowHistory | rowOutput | history | buffer | output
  deriving DecidableEq,Repr
instance :Fintype Role:=Fintype.ofList [.cache,.value,.phases,.reader,.blocks,.valid,.rowHistory,.rowOutput,.history,.buffer,.output]
  (by intro k;cases k <;> simp)
/-- Literal physical address of each mathematical boundary field. -/
def address:Role→Stack
  | .cache=>block | .value=>selected | .phases=>aux .phases | .reader=>aux .reader | .blocks=>aux .blocks
  | .valid=>aux .valid | .rowHistory=>aux .rowHistory | .rowOutput=>aux .rowOutput
  | .history=>aux .history | .buffer=>aux .buffer | .output=>output
/-- Auxiliary role conversion is fixed and has no data-dependent address operation. -/
def external:Aux→Role
  | .phases=>.phases | .reader=>.reader | .blocks=>.blocks | .valid=>.valid
  | .rowHistory=>.rowHistory | .rowOutput=>.rowOutput | .history=>.history | .buffer=>.buffer | .output=>.output
/-- Full physical bank: raw binary query retained, all actual private reader roles empty. -/
def data (key:List Bool) (w:Role→List Bool):Stack→List Bool:=
  Sum.elim (IX.view (w .cache) key [] [] (w .value)) (fun a=>w (external a))
/-- Every named actual boundary word is literal. -/
theorem data_get (key:List Bool) (w:Role→List Bool) (r:Role):data key w (address r)=w r:=by cases r <;> rfl
/-- The original binary coordinate, including all high-zero padding, is retained. -/
theorem data_coordinate (key:List Bool) (w:Role→List Bool):data key w coordinate=key:=rfl
/-- The genuine shared copy/parser scratch is empty between component calls. -/
theorem data_scratch (key:List Bool) (w:Role→List Bool):data key w scratch=[]:=rfl
/-- Logical single-field updates coincide exactly with the actual physical21-role bank. -/
theorem data_update (key:List Bool) (w:Role→List Bool) (r:Role) (word:List Bool):
    data key (Function.update w r word)=Function.update (data key w) (address r) word:=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> cases r <;> rfl
    · cases k <;> cases r <;> rfl
  · cases k <;> cases r <;> rfl
/-- All mathematical boundary names refer to distinct actual tapes. -/
theorem address_injective:Function.Injective address:=by decide
/-- Proof-side full boundary record, never a runtime object. -/
structure Words where
  /-- Actual cache boundary payload. -/
  cache:List Bool:=[]
  /-- Actual value boundary payload. -/
  value:List Bool:=[]
  /-- Actual phases boundary payload. -/
  phases:List Bool:=[]
  /-- Actual reader boundary payload. -/
  reader:List Bool:=[]
  /-- Actual blocks boundary payload. -/
  blocks:List Bool:=[]
  /-- Actual valid boundary payload. -/
  valid:List Bool:=[]
  /-- Actual rowHistory boundary payload. -/
  rowHistory:List Bool:=[]
  /-- Actual rowOutput boundary payload. -/
  rowOutput:List Bool:=[]
  /-- Actual history boundary payload. -/
  history:List Bool:=[]
  /-- Actual buffer boundary payload. -/
  buffer:List Bool:=[]
  /-- Actual output boundary payload. -/
  output:List Bool:=[]
/-- Literal11-word projection into the all21-role bank. -/
def words (v:Words):Role→List Bool
  | .cache=>v.cache | .value=>v.value | .phases=>v.phases | .reader=>v.reader | .blocks=>v.blocks
  | .valid=>v.valid | .rowHistory=>v.rowHistory | .rowOutput=>v.rowOutput | .history=>v.history
  | .buffer=>v.buffer | .output=>v.output
/-- Literal record update describes a real single physical word replacement. -/
def setWord (v:Words) (r:Role) (word:List Bool):Words:=match r with
  | .cache=>{v with cache:=word} | .value=>{v with value:=word} | .phases=>{v with phases:=word}
  | .reader=>{v with reader:=word} | .blocks=>{v with blocks:=word} | .valid=>{v with valid:=word}
  | .rowHistory=>{v with rowHistory:=word} | .rowOutput=>{v with rowOutput:=word}
  | .history=>{v with history:=word} | .buffer=>{v with buffer:=word} | .output=>{v with output:=word}
/-- Every real physical update is exactly its11-word mathematical view. -/
theorem words_update (v:Words) (r:Role) (word:List Bool):Function.update (words v) r word=words (setWord v r word):=by
  funext k;cases r <;> cases k <;> rfl
/-- The actual two-input source boundary contains no prepared coordinate cache. -/
theorem initial_data (phases key:List Bool):(initial phases key).data=data key (words {phases:=phases}):=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> rfl
    · cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateState
