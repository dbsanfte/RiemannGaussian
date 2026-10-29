/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinate
import RiemannGaussian.SemiprimeD1TensorTapeCodec
/-! # Actual phase/block/word input ABI and original-order column output
These lists describe literal bytes in proofs only. The runtime program has
exactly two words and never receives these lists or a coordinate-cache answer.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateEncoding
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeBitArithmetic (bitValue)
/-- Proof-side actual original-order phase/block/word inventory. -/
abbrev Phases:=List (List (List (List Bool)))
/-- Each actual CachePhase block tape is one framed outer payload, including empty rejected phases. -/
def tape (phases:Phases):List Bool:=vectorBits (phases.map (fun blocks=>vectorBits (blocks.map vectorBits)))
/-- Defaulting literal column of one phase, without changing coefficient padding. -/
def row (key:List Bool) (blocks:List (List (List Bool))):List (List Bool):=
  blocks.map (fun words=>(words[bitValue key]?).getD [])
/-- Original phase/block order is preserved, including every empty/rejected row. -/
def columns (phases:Phases) (key:List Bool):List (List (List Bool)):=phases.map (row key)
/-- Exact two-level child tape consumed by the frozen RecoveryEntries source. -/
def result (phases:Phases) (key:List Bool):List Bool:=vectorBits ((columns phases key).map vectorBits)
/-- One actual vector element chunk, before any output sentinel. -/
def chunk (word:List Bool):List Bool:=true::frame word []
/-- Original-order vector prefix without its one final false sentinel. -/
def chunks (words:List (List Bool)):List Bool:=words.foldr (fun word rest=>chunk word++rest) []
/-- Actual frame composition, retaining all payload bytes. -/
theorem frame_append (word left right:List Bool):frame word left++right=frame word (left++right):=by
  induction word with
  | nil=>rfl
  | cons b word ih=>change (true::b::frame word left)++right=true::b::frame word (left++right);rw [List.cons_append,List.cons_append,ih]
/-- Chunk sequence plus one physical false is the exact vector codec. -/
theorem chunks_vector (words:List (List Bool)):chunks words++[false]=vectorBits words:=by
  induction words with
  | nil=>rfl
  | cons word words ih=>
    change (chunk word++chunks words)++[false]=true::frame word (vectorBits words)
    rw [List.append_assoc,ih]
    change (true::frame word [])++vectorBits words=_
    rw [List.cons_append,frame_append,List.nil_append]
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateEncoding
