/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientation
import RiemannGaussian.SemiprimeD1OrientationBits
/-! # Numeric orientation flags and literal packet-key logger bytes
Raw colour words are preserved. Numeric equality never substitutes one padded
colour encoding for another; ties retain the old left/right copy direction.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationEncoding
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceHistogramKeyBits (frame)
namespace Less
export SemiprimeD1StackWordLessExecution (answer answer_true)
end Less
namespace Native
export SemiprimeD1OrientationBits (coordinate coordinate_flags coordinate_fields coordinate_field coordinate_slot coordinate_next acquire)
end Native
/-- Proof-side finite branch order acquired by the two actual strict numeric comparisons. -/
def ordered (left right:List Bool):Bool:=if Less.answer left right then true else !Less.answer right left
/-- Both actual strict comparisons are false exactly on numeric equality. -/
def equal (left right:List Bool):Bool:= !Less.answer left right && !Less.answer right left
/-- The physical branch agrees with the old non-strict numeric order, including arbitrary high-zero padding. -/
theorem ordered_original (left right index:List Bool):ordered left right=(Native.coordinate left right index).ordered :=by
  apply Bool.eq_iff_iff.mpr
  rw [(Native.coordinate_flags left right index).2]
  unfold ordered
  by_cases hl:Less.answer left right=true
  · simp only [hl,ite_true]
    constructor
    · intro _;exact Nat.le_of_lt ((Less.answer_true left right).mp hl)
    · intro _;trivial
  · have hf:=Bool.eq_false_of_not_eq_true hl
    simp only [hf,Bool.false_eq_true,ite_false,Bool.not_eq,ne_eq,Less.answer_true]
    omega
/-- The physically computed tie predicate has the exact old numeric meaning, without raw-byte equality assumptions. -/
theorem equal_original (left right index:List Bool):equal left right=(Native.coordinate left right index).equal :=by
  apply Bool.eq_iff_iff.mpr
  rw [(Native.coordinate_flags left right index).1]
  simp only [equal,Bool.and_eq_true,Bool.not_eq,ne_eq,Less.answer_true]
  omega
/-- Actual low colour copy direction on numeric ties is left, preserving its literal padding. -/
def low (left right:List Bool):List Bool:=if ordered left right then left else right
/-- Actual high colour copy direction on numeric ties is right, preserving its literal padding. -/
def high (left right:List Bool):List Bool:=if ordered left right then right else left
/-- Exact inner raw-tail colour-pair field. -/
def field (left right:List Bool):List Bool:=frame (low left right) (high left right)
/-- Exact outer frame logged for one acquired coordinate; no vector tag is introduced. -/
def chunk (left right:List Bool):List Bool:=frame (field left right) []
/-- Physical slot branch: only ties read an actual index head, with EOF interpreted as false. -/
def slot (left right index:List Bool):Bool:=if equal left right then index.headD false else !ordered left right
/-- Actual remaining index cursor: only ties consume one low bit. -/
def next (left right index:List Bool):List Bool:=if equal left right then index.tail else index
/-- Exact coordinate field bytes of the original routine, retaining both literal colour encodings. -/
theorem field_original (left right index:List Bool):field left right=(Native.coordinate left right index).field :=by
  rw [Native.coordinate_field,(Native.coordinate_fields left right index).1,(Native.coordinate_fields left right index).2]
  unfold field low high
  rw [ordered_original left right index]
  rfl
/-- Actual acquired orientation/equal-coordinate bit has exactly the original value. -/
theorem slot_original (left right index:List Bool):slot left right index=(Native.coordinate left right index).slot :=by
  rw [Native.coordinate_slot]
  unfold slot
  rw [equal_original left right index,ordered_original left right index]
/-- Exact raw remaining high-index word, including original high-zero padding. -/
theorem next_original (left right index:List Bool):next left right index=(Native.coordinate left right index).next :=by
  rw [Native.coordinate_next]
  unfold next
  rw [equal_original left right index]
/-- One acquired outer-key fragment has its full literal bit cost. -/
theorem chunk_length (left right:List Bool):
    (chunk left right).length ≤ 4*(left.length+right.length)+3 :=by
  unfold chunk field low high
  rw [SemiprimeSourceHistogramKeyBits.frame_length,SemiprimeSourceHistogramKeyBits.frame_length]
  cases ordered left right <;> simp only [Bool.false_eq_true,ite_false,ite_true,List.length_nil] <;> omega
/-- Literal append to a framed key retains its supplied physical tail. -/
theorem frame_append (word tail suffix:List Bool):frame word tail++suffix=frame word (tail++suffix) :=by
  induction word with
  | nil=>rfl
  | cons b word ih=>simp only [frame,List.cons_append,ih]
end RiemannGaussian.SemiprimeD1StackPacketOrientationEncoding
