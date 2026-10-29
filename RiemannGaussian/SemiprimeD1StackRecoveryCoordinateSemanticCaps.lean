/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateEncoding
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesChildCaps
/-! # Semantic phase/block/rank/precision input and output byte caps
These caps use actual finite shapes and coefficient widths, never a recursive
subtree's execution budget. Old rank and child working precision are distinct.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateSemanticCaps
open SemiprimeD1StackRecoveryCoordinateEncoding
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace E
export SemiprimeD1StackRecoveryEntriesChildCaps (vector_length child_tape_length)
end E
/-- Original phase/block/old-rank/working-precision envelope for the actual input bank. -/
def bankByteBound (Q B R P:Nat):Nat:=8*Q*B*R*(P+1)+8*Q*B+4*Q+1
/-- All three real nesting levels have a semantic fixed-polynomial byte cap. -/
theorem bank_bytes (phases:Phases) (Q B R P:Nat) (hq:phases.length ≤Q)
    (hb:∀blocks∈phases,blocks.length ≤B) (hr:∀blocks∈phases,∀words∈blocks,words.length ≤R)
    (hp:∀blocks∈phases,∀words∈blocks,∀word∈words,word.length ≤P):
    (tape phases).length ≤bankByteBound Q B R P:=by
  have h:=E.vector_length (phases.map (fun blocks=>vectorBits (blocks.map vectorBits))) Q
    (4*B*R*(P+1)+4*B+1) (by simpa only [List.length_map] using hq) (by
      intro encoded he
      obtain ⟨blocks,hblocks,rfl⟩:=List.mem_map.mp he
      exact E.child_tape_length blocks B R P (hb blocks hblocks) (hr blocks hblocks) (hp blocks hblocks))
  change (tape phases).length ≤_ at h
  unfold bankByteBound
  nlinarith only [h]
/-- Selected/default actual coefficient widths derive from semantic source widths. -/
theorem coefficient_width (key:List Bool) (words:List (List Bool)) (P:Nat)
    (hp:∀word∈words,word.length ≤P):((words[SemiprimeBitArithmetic.bitValue key]?).getD []).length ≤P:=by
  cases he:words[SemiprimeBitArithmetic.bitValue key]? with
  | none=>simp
  | some word=>exact hp word (List.mem_of_getElem? he)
/-- The output has one row per actual phase and one coefficient per actual block, including empty phases. -/
theorem columns_shape (phases:Phases) (key:List Bool) (B P:Nat)
    (hb:∀blocks∈phases,blocks.length ≤B)
    (hp:∀blocks∈phases,∀words∈blocks,∀word∈words,word.length ≤P):
    (columns phases key).length=phases.length ∧
      ∀outputRow∈columns phases key,outputRow.length ≤B ∧∀word∈outputRow,word.length ≤P:=by
  constructor
  · exact List.length_map _
  · intro outputRow ho
    obtain ⟨blocks,hblocks,rfl⟩:=List.mem_map.mp ho
    constructor
    · simpa only [row,List.length_map] using hb blocks hblocks
    · intro word hw
      obtain ⟨words,hwords,rfl⟩:=List.mem_map.mp hw
      exact coefficient_width key words P (hp blocks hblocks words hwords)
/-- Actual two-level child-coordinate tape cap, independent of every child runtime. -/
theorem result_bytes (phases:Phases) (key:List Bool) (Q B P:Nat) (hq:phases.length ≤Q)
    (hb:∀blocks∈phases,blocks.length ≤B)
    (hp:∀blocks∈phases,∀words∈blocks,∀word∈words,word.length ≤P):
    (result phases key).length ≤4*Q*B*(P+1)+4*Q+1:=by
  have hs:=columns_shape phases key B P hb hp
  exact E.child_tape_length (columns phases key) Q B P (hs.1.le.trans hq)
    (fun outputRow ho=>(hs.2 outputRow ho).1) (fun outputRow ho=>(hs.2 outputRow ho).2)
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateSemanticCaps
