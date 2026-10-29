/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationView
/-! # Clean loop-boundary banks of the actual packet orientation source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationRowView
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationView
/-- All physical loop words with all real comparison/parser/frame/restoration work clear. -/
def rowView (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (keyHistory slotHistory keyOutput slotOutput highOutput:List Bool):Stack→List Bool:=
  view (originals 0) (originals 1) (originals 2) (readers false) (readers true) cursor
    (colours false) (colours true) [] [] [] [] [] [] keyHistory slotHistory keyOutput slotOutput highOutput
/-- Actual colour-reader projection at either fixed finite side. -/
theorem reader_get (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (kh sh ko so hi:List Bool) (side:Bool):
    rowView originals readers cursor colours kh sh ko so hi (reader side)=readers side:=by cases side <;> rfl
/-- Actual copied-colour projection at either fixed finite side. -/
theorem colour_get (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (kh sh ko so hi:List Bool) (side:Bool):
    rowView originals readers cursor colours kh sh ko so hi (colour side)=colours side:=by cases side <;> rfl
/-- One real parser-source update preserves every other actual word. -/
theorem update_reader (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (kh sh ko so hi:List Bool) (side:Bool) (word:List Bool):
    Function.update (rowView originals readers cursor colours kh sh ko so hi) (reader side) word=
      rowView originals (Function.update readers side word) cursor colours kh sh ko so hi:=by
  cases side <;> funext k <;> rcases k with k|k
  all_goals first | (rcases k with k|k <;> cases k <;> rfl) | (cases k <;> rfl)
/-- One real parsed-colour update preserves every other actual word. -/
theorem update_colour (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (kh sh ko so hi:List Bool) (side:Bool) (word:List Bool):
    Function.update (rowView originals readers cursor colours kh sh ko so hi) (colour side) word=
      rowView originals readers cursor (Function.update colours side word) kh sh ko so hi:=by
  cases side <;> funext k <;> rcases k with k|k
  all_goals first | (rcases k with k|k <;> cases k <;> rfl) | (cases k <;> rfl)
/-- A physically consumed equal-coordinate index head changes only its actual cursor word. -/
theorem update_cursor (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (kh sh ko so hi word:List Bool):
    Function.update (rowView originals readers cursor colours kh sh ko so hi) (aux .indexCursor) word=
      rowView originals readers word colours kh sh ko so hi:=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Actual acquired slot logging changes only the reversed slot history. -/
theorem update_slotHistory (originals:Fin 3→List Bool) (readers:Bool→List Bool) (cursor:List Bool)
    (colours:Bool→List Bool) (kh sh ko so hi word:List Bool):
    Function.update (rowView originals readers cursor colours kh sh ko so hi) (aux .slotHistory) word=
      rowView originals readers cursor colours kh word ko so hi:=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackPacketOrientationRowView
