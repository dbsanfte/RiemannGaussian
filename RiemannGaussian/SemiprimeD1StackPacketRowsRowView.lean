/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketRowsView
/-! # Complete nineteen-role banks during paired colour parsing and logging
The Bool-indexed functions name the two fixed physical row/word/history/output
roles only. They are proof-side tape-bank views, absent from runtime control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketRowsRowView
open SemiprimeD1StackPacketRows
/-- All row-stage words, after actual query/key-reader cleanup and before the final computed flag. -/
def rowView (key catalogue:List Bool) (streams words histories outputs:Bool→List Bool)
    (buffer:List Bool) :Stack→List Bool :=
  SemiprimeD1StackPacketRowsView.view key catalogue [] (streams false) (streams true) []
    (words false) (words true) [] [] [] buffer (histories false) (histories true) (outputs false) (outputs true)
/-- Actual physical raw-stream projection for either fixed side. -/
theorem stream_get (key catalogue:List Bool) (streams words histories outputs:Bool→List Bool)
    (buffer:List Bool) (side:Bool) :rowView key catalogue streams words histories outputs buffer (rowBytes side)=streams side :=by
  cases side <;> rfl
/-- Actual physical parsed-colour projection for either fixed side. -/
theorem word_get (key catalogue:List Bool) (streams words histories outputs:Bool→List Bool)
    (buffer:List Bool) (side:Bool) :rowView key catalogue streams words histories outputs buffer (colourWord side)=words side :=by
  cases side <;> rfl
/-- Actual physical history projection for either fixed side. -/
theorem history_get (key catalogue:List Bool) (streams words histories outputs:Bool→List Bool)
    (buffer:List Bool) (side:Bool) :rowView key catalogue streams words histories outputs buffer (history side)=histories side :=by
  cases side <;> rfl
/-- Actual physical chronological-output projection for either fixed side. -/
theorem output_get (key catalogue:List Bool) (streams words histories outputs:Bool→List Bool)
    (buffer:List Bool) (side:Bool) :rowView key catalogue streams words histories outputs buffer (output side)=outputs side :=by
  cases side <;> rfl
/-- One actual streams update touches only the selected fixed physical side. -/
theorem update_streams (key catalogue:List Bool) (streams words histories outputs:Bool→List Bool)
    (buffer word:List Bool) (side:Bool) :
    Function.update (rowView key catalogue streams words histories outputs buffer) (rowBytes side) word=
      rowView key catalogue (Function.update streams side word) words histories outputs buffer :=by
  cases side <;> funext k
  all_goals rcases k with k|k
  all_goals first | (rcases k with k|k <;> cases k <;> rfl) | (cases k <;> rfl)
/-- One actual words update touches only the selected fixed physical side. -/
theorem update_words (key catalogue:List Bool) (streams words histories outputs:Bool→List Bool)
    (buffer word:List Bool) (side:Bool) :
    Function.update (rowView key catalogue streams words histories outputs buffer) (colourWord side) word=
      rowView key catalogue streams (Function.update words side word) histories outputs buffer :=by
  cases side <;> funext k
  all_goals rcases k with k|k
  all_goals first | (rcases k with k|k <;> cases k <;> rfl) | (cases k <;> rfl)
/-- One actual histories update touches only the selected fixed physical side. -/
theorem update_histories (key catalogue:List Bool) (streams words histories outputs:Bool→List Bool)
    (buffer word:List Bool) (side:Bool) :
    Function.update (rowView key catalogue streams words histories outputs buffer) (history side) word=
      rowView key catalogue streams words (Function.update histories side word) outputs buffer :=by
  cases side <;> funext k
  all_goals rcases k with k|k
  all_goals first | (rcases k with k|k <;> cases k <;> rfl) | (cases k <;> rfl)
/-- One actual outputs update touches only the selected fixed physical side. -/
theorem update_outputs (key catalogue:List Bool) (streams words histories outputs:Bool→List Bool)
    (buffer word:List Bool) (side:Bool) :
    Function.update (rowView key catalogue streams words histories outputs buffer) (output side) word=
      rowView key catalogue streams words histories (Function.update outputs side word) buffer :=by
  cases side <;> funext k
  all_goals rcases k with k|k
  all_goals first | (rcases k with k|k <;> cases k <;> rfl) | (cases k <;> rfl)
/-- The shared empty frame buffer changes without touching either raw stream, parsed colour or logger word. -/
theorem update_buffer (key catalogue:List Bool) (streams words histories outputs:Bool→List Bool)
    (buffer word:List Bool) :
    Function.update (rowView key catalogue streams words histories outputs buffer) frameBuffer word=
      rowView key catalogue streams words histories outputs word :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackPacketRowsRowView
