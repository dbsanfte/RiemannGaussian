/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinatePrimitives
/-! # Real binary reader call on each actual parsed block
The raw binary coordinate is retained. Numeric equality handles padding and
physical EOF bounds every scan, without any unary decoded address acquisition.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateCalls
open SemiprimeD1StackRecoveryCoordinate SemiprimeD1StackRecoveryCoordinateState
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace X
export SemiprimeD1StackRecoveryEntriesIndexedExecution (source_run timeBound done result_bank)
end X
/-- Initial actual full12-role reader bank, derived from this21-role caller's real fields. -/
theorem initial_projection (key:List Bool) (w:Role→List Bool) (he:w .value=[]):
    (data key w) ∘ indexed=(I.initial (w .cache) key).data:=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k with
    | value=>exact he
    | cache|query|counter|reader|parser|valid|copy=>rfl
/-- Each actual block lookup includes all12 real reader roles and its genuine call/return. -/
theorem index_call (key:List Bool) (w:Role→List Bool) (words:List (List Bool))
    (hc:w .cache=vectorBits words) (he:w .value=[]):
    Runs program (X.timeBound words key+1) (.local .lookup) (data key w) (.local .coefficientFrame)
      (data key (Function.update w .value ((words[SemiprimeBitArithmetic.bitValue key]?).getD []))):=by
  let answer:=(words[SemiprimeBitArithmetic.bitValue key]?).getD []
  have hin:SemiprimeD1StackMultiplierLink.DataRel indexed (data key w)
      (I.initial (vectorBits words) key).data (data key w):=by
    constructor
    · intro k
      have h:=congrFun (initial_projection key w he) k
      rw [hc] at h
      exact h
    · intro k _;rfl
  have ho:=SemiprimeD1StackMultiplierLink.data_update indexed indexed_injective
    (data key w) (I.initial (vectorBits words) key).data (data key w) hin (I.aux .value) answer
  have hfinal:Function.update (I.initial (vectorBits words) key).data (I.aux .value) answer=(X.done words key).data:=
    (X.result_bank words key).symm
  rw [hfinal] at ho
  change SemiprimeD1StackMultiplierLink.DataRel indexed (data key w)
    (X.done words key).data (Function.update (data key w) (address .value) answer) at ho
  rw [←data_update] at ho
  exact SemiprimeD1StackProcedureCallsTrace.included_call program indexed Label.indexed indexed_injective I.program
    (.local .start) (fun _=>rfl) (.local .lookup) (.local .coefficientFrame) rfl
    (X.timeBound words key) (I.initial (vectorBits words) key) (X.done words key)
    _ _ rfl rfl rfl rfl (X.source_run words key) hin ho
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateCalls
