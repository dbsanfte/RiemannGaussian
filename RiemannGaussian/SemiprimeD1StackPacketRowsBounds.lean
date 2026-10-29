/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsClock
/-! # Genuine compiled packet-row source time certificate
The prepared front door takes exactly the physical joint key and catalogue.
Both lookups, presence peeks, paired EOF loop and output logging use the same
fixed nineteen-role source that witnesses this polynomial certificate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsBounds
open SemiprimeD1StackPacketRows SemiprimeD1StackPacketRowsExecution SemiprimeD1StackPacketRowsClock
open SemiprimeD1StackPacketRowsAcquire SemiprimeD1StackPacketRowsEncoding
open SemiprimeSourceHistogramKeyBits (frame)
namespace Map
export SemiprimeD1StackOwnerLookup (records)
end Map
/-- Actual source certificate using the whole literal trace, including its final halt. -/
noncomputable def sourceRead (owner factor:List Bool) (rows:List (List Bool×List Bool)) (left right:List (List Bool))
    (hl:present owner rows=true) (hr:present factor rows=true)
    (hleft:payload owner rows=SemiprimeD1PacketRows.serialize left)
    (hright:payload factor rows=SemiprimeD1PacketRows.serialize right) (hlen:left.length=right.length) :
    StateTransition.EvalsToInTime (SemiprimeD1StackCalls.step program)
      (initial (frame owner factor) (Map.records rows []))
      (some (done (frame owner factor) (Map.records rows []) left right))
      (polynomial (frame owner factor) (Map.records rows [])) :=by
  let h:=source_run_bounded owner factor rows left right hl hr hleft hright hlen
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- SAME fixed finite Boolean-stack machine, actual execution, and own physical-input polynomial. -/
noncomputable def machineRead (owner factor:List Bool) (rows:List (List Bool×List Bool)) (left right:List (List Bool))
    (hl:present owner rows=true) (hr:present factor rows=true)
    (hleft:payload owner rows=SemiprimeD1PacketRows.serialize left)
    (hright:payload factor rows=SemiprimeD1PacketRows.serialize right) (hlen:left.length=right.length) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (frame owner factor) (Map.records rows [])))
      (some (SemiprimeD1StackCalls.configuration (done (frame owner factor) (Map.records rows []) left right)))
      (polynomial (frame owner factor) (Map.records rows [])) :=
  SemiprimeD1StackCalls.evalsCorrect (aux .key) (output false) (SemiprimeD1StackPacketRows.Label.local .start) program _ _ _
    (sourceRead owner factor rows left right hl hr hleft hright hlen)
end RiemannGaussian.SemiprimeD1StackPacketRowsBounds
