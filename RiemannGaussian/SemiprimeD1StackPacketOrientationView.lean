/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationPrimitives
/-! # Complete actual nineteen-word banks between packet-orientation calls
These are proof notations for fixed physical words, never runtime functions.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationView
open SemiprimeD1StackPacketOrientation
/-- Every actual original input, cursor, comparator/logger word and output is explicit. -/
def view (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput:List Bool):Stack→List Bool:=
  Sum.elim (Less.store leftOperand rightOperand scratchWord bufferWord answerWord)
    (fun k=>match k with
      | .leftInput=>leftInput
      | .rightInput=>rightInput
      | .indexInput=>indexInput
      | .leftReader=>leftReader
      | .rightReader=>rightReader
      | .indexCursor=>indexCursor
      | .leftColour=>leftColour
      | .rightColour=>rightColour
      | .copyScratch=>copyScratch
      | .keyHistory=>keyHistory
      | .slotHistory=>slotHistory
      | .keyOutput=>keyOutput
      | .slotOutput=>slotOutput
      | .highOutput=>highOutput
)
/-- One real leftInput update preserves all other eighteen physical words. -/
theorem update_leftInput (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .leftInput) word=
      view word rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real rightInput update preserves all other eighteen physical words. -/
theorem update_rightInput (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .rightInput) word=
      view leftInput word indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real indexInput update preserves all other eighteen physical words. -/
theorem update_indexInput (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .indexInput) word=
      view leftInput rightInput word leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real leftReader update preserves all other eighteen physical words. -/
theorem update_leftReader (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .leftReader) word=
      view leftInput rightInput indexInput word rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real rightReader update preserves all other eighteen physical words. -/
theorem update_rightReader (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .rightReader) word=
      view leftInput rightInput indexInput leftReader word indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real indexCursor update preserves all other eighteen physical words. -/
theorem update_indexCursor (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .indexCursor) word=
      view leftInput rightInput indexInput leftReader rightReader word leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real leftColour update preserves all other eighteen physical words. -/
theorem update_leftColour (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .leftColour) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor word rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real rightColour update preserves all other eighteen physical words. -/
theorem update_rightColour (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .rightColour) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour word leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real leftOperand update preserves all other eighteen physical words. -/
theorem update_leftOperand (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (operand false) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour word rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real rightOperand update preserves all other eighteen physical words. -/
theorem update_rightOperand (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (operand true) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand word scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real scratchWord update preserves all other eighteen physical words. -/
theorem update_scratchWord (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (scratch) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand word bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real bufferWord update preserves all other eighteen physical words. -/
theorem update_bufferWord (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (buffer) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord word answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real answerWord update preserves all other eighteen physical words. -/
theorem update_answerWord (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (answer) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord word copyScratch keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real copyScratch update preserves all other eighteen physical words. -/
theorem update_copyScratch (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .copyScratch) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord word keyHistory slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real keyHistory update preserves all other eighteen physical words. -/
theorem update_keyHistory (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .keyHistory) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch word slotHistory keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real slotHistory update preserves all other eighteen physical words. -/
theorem update_slotHistory (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .slotHistory) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory word keyOutput slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real keyOutput update preserves all other eighteen physical words. -/
theorem update_keyOutput (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .keyOutput) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory word slotOutput highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real slotOutput update preserves all other eighteen physical words. -/
theorem update_slotOutput (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .slotOutput) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput word highOutput :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One real highOutput update preserves all other eighteen physical words. -/
theorem update_highOutput (leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput word:List Bool):
    Function.update (view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput highOutput) (aux .highOutput) word=
      view leftInput rightInput indexInput leftReader rightReader indexCursor leftColour rightColour leftOperand rightOperand scratchWord bufferWord answerWord copyScratch keyHistory slotHistory keyOutput slotOutput word :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackPacketOrientationView
