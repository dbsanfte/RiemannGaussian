/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftVertexPrimitives
/-! # Both actual preserving frames acquire the exact singleton-vertex stream -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftVertexFrames
open SemiprimeD1StackChildLiftVertex SemiprimeD1StackChildLiftVertexPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Literal singleton-record codec, with both actual fields and the stream's FALSE terminator. -/
def record (ports tableBytes : List Bool) : List Bool := true::frame ports (frame tableBytes [false])
/-- The entire framing continuation preserves ALL134 whole-table fields and clears its only new scratch. -/
theorem frames_run (data : T.Stack→List Bool) (ports tableBytes : List Bool)
    (hp : data (SemiprimeD1StackVectorTable.counter .bank)=ports)
    (ht : data (SemiprimeD1StackVectorTable.aux .output)=tableBytes) :
    Runs program (6*tableBytes.length+6*ports.length+12) (.local .seed) (bank data [] [])
      (.local .done) (bank data (record ports tableBytes) []) := by
  have h0:=push_run .seed .tableFrame false data [] [] rfl
  have h1:=frame_call false .tableFrame .scopeFrame (bank data [false] []) tableBytes [false] rfl
    (by intro i;fin_cases i <;> first | exact ht | rfl)
  rw [update_record] at h1
  have h2:=frame_call true .scopeFrame .tag (bank data (frame tableBytes [false]) []) ports (frame tableBytes [false]) rfl
    (by intro i;fin_cases i <;> first | exact hp | rfl)
  rw [update_record] at h2
  have h3:=push_run .tag .done true data (frame ports (frame tableBytes [false])) [] rfl
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0
    (runs_trans program _ _ _ _ _ _ _ _ h1 (runs_trans program _ _ _ _ _ _ _ _ h2 h3))
  convert h using 1 <;> first | rfl | omega
/-- Both framed fields coincide with the EXISTING full vertex-stream ABI, not a new codec. -/
theorem record_original (v : SemiprimeD1LeafCounter.Vertex) :
    record (SemiprimeD1StackVertexReadExecution.portTape v.ports) (SemiprimeD1TensorTapeCodec.tape v.table)=
      SemiprimeD1StackVertexProduct.records [v] := rfl
end RiemannGaussian.SemiprimeD1StackChildLiftVertexFrames
