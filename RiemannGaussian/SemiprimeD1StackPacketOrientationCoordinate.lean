/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationCompare
import RiemannGaussian.SemiprimeD1StackPacketOrientationLog
/-! # Actual numeric classification and equal-coordinate binary index consumption -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationCoordinate
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationPrimitives
open SemiprimeD1StackPacketOrientationRowView SemiprimeD1StackPacketOrientationLog
open SemiprimeD1StackProcedureTrace
namespace Compare
export SemiprimeD1StackPacketOrientationCompare (compare_run view_empty)
end Compare
namespace Spec
export SemiprimeD1StackPacketOrientationEncoding (ordered equal field chunk slot next)
end Spec
local notation "ctl"=>Label.local
/-- A real comparison consumes actual copies, physically pops its answer and preserves the complete loop bank. -/
theorem compare_row (backward:Bool) (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (kh sh ko so hi:List Bool):
    Runs program (5*(colours backward).length+5*(colours (!backward)).length+
      SemiprimeD1StackWordLessExecution.totalTime (colours backward) (colours (!backward))+10)
      (ctl (.copyOperand backward false)) (rowView originals readers cursor colours kh sh ko so hi)
      (ctl (if SemiprimeD1StackWordLessExecution.answer (colours backward) (colours (!backward)) then
        (if backward then .slot false true else .slot true false) else (if backward then .padding else .copyOperand true false)))
      (rowView originals readers cursor colours kh sh ko so hi) :=by
  have h:=Compare.compare_run backward (rowView originals readers cursor colours kh sh ko so hi)
    (colours backward) (colours (!backward)) (by cases backward <;> rfl) (by cases backward <;> rfl) rfl rfl rfl
  rw [Compare.view_empty _ rfl rfl rfl] at h
  exact h
/-- A computed slot bit is really pushed before the actual nested field logger; no supplied verdict enters the program. -/
theorem slot_run (ordered bit:Bool) (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (kh sh ko so hi:List Bool):
    Runs program (1+emitTime ordered colours) (ctl (.slot ordered bit))
      (rowView originals readers cursor colours kh sh ko so hi) (ctl .leftTag)
      (rowView originals readers cursor (fun _=>[]) ((SemiprimeSourceHistogramKeyBits.frame (pairField ordered colours) []).reverse++kh)
        (bit::sh) ko so hi) :=by
  have h0:=push_run (.slot ordered bit) (ctl (.copyHigh ordered)) (aux .slotHistory) bit
    (rowView originals readers cursor colours kh sh ko so hi) rfl
  rw [update_slotHistory] at h0
  exact join h0 (emit_run ordered originals readers cursor colours kh (bit::sh) ko so hi)
/-- Physically pop one actual low index bit only on the equality branch; missing bits become literal false. -/
theorem padding_run (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (kh sh ko so hi:List Bool):
    Runs program 1 (ctl .padding) (rowView originals readers cursor colours kh sh ko so hi)
      (ctl (.slot true (cursor.headD false)))
      (rowView originals readers cursor.tail colours kh sh ko so hi) :=by
  have h:=pop_run .padding (ctl (.slot true false)) (ctl (.slot true false)) (ctl (.slot true true))
    (aux .indexCursor) (rowView originals readers cursor colours kh sh ko so hi) cursor rfl rfl
  rw [update_cursor] at h
  cases cursor with
  | nil=>exact h
  | cons b bs=>cases b <;> exact h
end RiemannGaussian.SemiprimeD1StackPacketOrientationCoordinate
