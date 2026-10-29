/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesPrimitives
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedExecution
/-! # Two real binary indexed calls on actual parsed node/index words
Every source cache and parsed payload is physically retained. The full12-role
callee executes twice through fixed outer/inner inclusions; unused allocated
query/value shadows remain counted and genuinely empty throughout.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesCalls
open SemiprimeD1StackRecoveryEntries SemiprimeD1StackRecoveryEntriesState
open SemiprimeD1StackRecoveryEntriesPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace IX
export SemiprimeD1StackRecoveryEntriesIndexedExecution (source_run timeBound done result_bank)
end IX
/-- Actual acquired cache word for one of the two finite lookup sites. -/
def cacheWord (inner:Bool) (children:List Bool) (w:Aux → List Bool):List Bool:=if inner then w .selectedRow else children
/-- Actual binary query is the corresponding real parsed source field. -/
def queryWord (inner:Bool) (w:Aux → List Bool):List Bool:=if inner then w .index else w .node
/-- Actual outer row-cache or inner coefficient-result destination. -/
def resultAux (inner:Bool):Aux:=if inner then .child else .selectedRow
/-- Static actual source-call site. -/
def callPC (inner:Bool):Label:=if inner then .local .inner else .local .outer
/-- Static actual continuation after the full selected-field/EOF cleanup. -/
def callNext (inner:Bool):Label:=if inner then .local (.frame 0) else .local .normalize
/-- Every declared actual indexed result address is exact. -/
theorem result_address (inner:Bool):indexStack inner (I.aux .value)=aux (resultAux inner):=by cases inner <;> rfl
/-- Actual incoming alias bank is the honest two-word source entry, with no ordinal or selected-word advice. -/
theorem initial_projection (inner:Bool) (children:List Bool) (w:Aux → List Bool) (he:w (resultAux inner)=[]) (k:I.Stack):
    data children w (indexStack inner k)=(I.initial (cacheWord inner children w) (queryWord inner w)).data k:=by
  cases inner <;> rcases k with k|k
  · cases k <;> rfl
  · cases k with
    | value=>exact he
    | cache|query|counter|reader|parser|valid|copy=>rfl
  · cases k <;> rfl
  · cases k with
    | value=>exact he
    | cache|query|counter|reader|parser|valid|copy=>rfl
/-- Complete actual nested-call source; every address scan, parser, increment, copy, cleanup and real return is paid. -/
theorem index_call (inner:Bool) (children:List Bool) (w:Aux → List Bool) (words:List (List Bool))
    (hc:cacheWord inner children w=vectorBits words) (he:w (resultAux inner)=[]):
    Runs program (IX.timeBound words (queryWord inner w)+1) (callPC inner) (data children w) (callNext inner)
      (data children (Function.update w (resultAux inner) ((words[SemiprimeBitArithmetic.bitValue (queryWord inner w)]?).getD []))):=by
  let query:=queryWord inner w
  let answer:=(words[SemiprimeBitArithmetic.bitValue query]?).getD []
  have hin:SemiprimeD1StackMultiplierLink.DataRel (indexStack inner) (data children w)
      (I.initial (vectorBits words) query).data (data children w):=by
    constructor
    · intro k
      have h:=initial_projection inner children w he k
      rw [hc] at h
      exact h
    · intro k _;rfl
  have ho:=SemiprimeD1StackMultiplierLink.data_update (indexStack inner) (index_injective inner)
    (data children w) (I.initial (vectorBits words) query).data (data children w) hin (I.aux .value) answer
  have hfinal:Function.update (I.initial (vectorBits words) query).data (I.aux .value) answer=(IX.done words query).data:=
    (IX.result_bank words query).symm
  rw [hfinal,result_address,←data_update] at ho
  apply SemiprimeD1StackProcedureCallsTrace.included_call program (indexStack inner) (Label.indexed inner)
    (index_injective inner) I.program (.local .start) (fun _=>rfl) (callPC inner) (callNext inner)
    (by cases inner <;> rfl) (IX.timeBound words query) (I.initial (vectorBits words) query) (IX.done words query)
    _ _ rfl rfl rfl rfl (IX.source_run words query) hin ho
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesCalls
