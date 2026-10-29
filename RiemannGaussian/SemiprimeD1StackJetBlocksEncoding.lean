/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocks
import RiemannGaussian.SemiprimeD1StackNetworkRowsEncoding
/-! # Exact contiguous blocks and original offset-read interpretation
The lists and natural indices below specify physically streamed coefficient
bytes. None occurs in the source instruction table or finite control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksEncoding
namespace Codec
export SemiprimeD1StackNetworkRowsEncoding (payload payload_vector payload_length chunk chunk_length)
end Codec
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Sequentially read exactly rank actual/default-empty coefficient words. -/
def padded :Nat→List (List Bool)→List (List Bool)
  | 0,_=>[]
  | rank+1,words=>words.headD []::padded rank words.tail
/-- Exactly one real/default coefficient field per actual rank marker. -/
theorem padded_length (rank:Nat) (words:List (List Bool)) :(padded rank words).length=rank :=by
  induction rank generalizing words with
  | zero=>rfl
  | succ rank ih=>simp only [padded,List.length_cons,ih]
/-- Actual EOF padding preserves the original empty-word zero convention, without trimming any input coefficient. -/
theorem padded_nil (rank:Nat) :padded rank []=List.replicate rank [] :=by
  induction rank with
  | zero=>rfl
  | succ rank ih=>simp only [padded,List.headD_nil,List.tail_nil,ih,List.replicate_succ]
/-- Literal sequential reads equal all original offset-free finite reads/defaults. -/
theorem padded_range (rank:Nat) (words:List (List Bool)) :
    padded rank words=(List.range rank).map (fun i=>(words[i]?).getD []) :=by
  induction rank generalizing words with
  | zero=>rfl
  | succ rank ih=>
    rw [padded,List.range_succ_eq_map,List.map_cons,List.map_map]
    congr 1
    · cases words <;> rfl
    · rw [ih]
      apply List.map_congr_left
      intro i _
      cases words <;> rfl
/-- Sequential whole-block bytes are EXACTthe original JetBlockBits.extract cached-offset reads. -/
theorem padded_native (old:SemiprimeD1JetAxes.Context) (j:Nat) (words:List (List Bool)) :
    padded old.rank (words.drop (j*old.rank))=(SemiprimeD1JetBlockBits.extract old j words).words :=by
  rw [padded_range]
  simp only [SemiprimeD1JetBlockBits.extract,List.map_map,Function.comp_def,
    SemiprimeD1JetBlockBits.readCopy_bits,List.getElem?_drop]
/-- Actual chronological block list, consuming each earlier field only once. -/
def chunks (rank:Nat) :Nat→List (List Bool)→List (List (List Bool))
  | 0,_=>[]
  | q+1,words=>padded rank words::chunks rank q (words.drop rank)
/-- The number of actual emitted blocks is the actual q marker count, even with source EOF. -/
theorem chunks_length (rank q:Nat) (words:List (List Bool)) :(chunks rank q words).length=q :=by
  induction q generalizing words with
  | zero=>rfl
  | succ q ih=>simp only [chunks,List.length_cons,ih]
/-- Complete sequential traversal matches all original ascending block offsets. -/
theorem chunks_range (rank q:Nat) (words:List (List Bool)) :
    chunks rank q words=(List.range q).map (fun j=>padded rank (words.drop (j*rank))) :=by
  induction q generalizing words with
  | zero=>rfl
  | succ q ih=>
    rw [chunks,List.range_succ_eq_map,List.map_cons,List.map_map,ih]
    simp only [Nat.zero_mul,List.drop_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    rw [List.drop_drop]
    congr 2
    rw [Nat.succ_mul]
    omega
/-- Exact original native phase-block order and every unchanged raw binary coefficient word. -/
theorem chunks_native (old:SemiprimeD1JetAxes.Context) (q:Nat) (words:List (List Bool)) :
    chunks old.rank q words=(List.range q).map (fun j=>(SemiprimeD1JetBlockBits.extract old j words).words) :=by
  rw [chunks_range]
  apply List.map_congr_left
  intro j _
  exact padded_native old j words
/-- Literal nested block output ABI, with actual coefficient padding and block order preserved. -/
def tape (rank q:Nat) (words:List (List Bool)) :List Bool :=vectorBits ((chunks rank q words).map vectorBits)
end RiemannGaussian.SemiprimeD1StackJetBlocksEncoding
