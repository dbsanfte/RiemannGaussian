/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateBlock
/-! # Intrinsic physical byte and actual binary-reader step bounds
Source/output lengths and lookup costs are derived from actual physical fields.
No numeric coordinate magnitude or subtree clock is a work parameter.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateCapacities
open SemiprimeD1StackRecoveryCoordinateEncoding SemiprimeD1StackRecoveryCoordinateBlock
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace I
export SemiprimeD1StackRecoveryEntriesIndexedBounds (vector_cons_length member_length result_length timeBound_le runBound)
end I
/-- Physical vector row count is bounded by its actual tagged/framed byte tape. -/
theorem vector_count (words:List (List Bool)):words.length ≤(vectorBits words).length:=by
  have h:=SemiprimeD1TensorTapeCodec.vectorBits_length words
  omega
/-- Replacing each physical field by a no-longer payload cannot enlarge its literal vector tape. -/
theorem vector_map_mono {K:Type} (xs:List K) (f g:K→List Bool)
    (h:∀x∈xs,(f x).length ≤(g x).length):
    (vectorBits (xs.map f)).length ≤(vectorBits (xs.map g)).length:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    have h0:=h x (List.mem_cons_self)
    have h1:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons,I.vector_cons_length]
    omega
/-- Actual selected/default word is paid by its physical block-vector bytes. -/
theorem coefficient_length (key:List Bool) (words:List (List Bool)):
    (coefficient key words).length ≤(vectorBits words).length:=I.result_length words key
/-- Actual phase coordinate row cannot exceed the already acquired phase block tape. -/
theorem row_length (key:List Bool) (blocks:List (List (List Bool))):
    (vectorBits (row key blocks)).length ≤(vectorBits (blocks.map vectorBits)).length:=
  vector_map_mono blocks _ _ (fun words _=>coefficient_length key words)
/-- Literal tagged-frame chunk length. -/
theorem chunk_length (word:List Bool):(chunk word).length=2*word.length+2:=by
  simp only [chunk,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
/-- Only one physical false sentinel separates vector length from the chunk-history length. -/
theorem chunks_length (words:List (List Bool)):(chunks words).length+1=(vectorBits words).length:=by
  have h:=congrArg List.length (chunks_vector words)
  simpa only [List.length_append,List.length_singleton] using h
/-- Original phase count is paid by the actual full retained input-bank bytes. -/
theorem phase_count (phases:Phases):phases.length ≤(tape phases).length:=by
  simpa only [tape,List.length_map] using vector_count (phases.map (fun blocks=>vectorBits (blocks.map vectorBits)))
/-- Original retained blocks of every actual phase are paid by that phase's byte payload. -/
theorem block_count (blocks:List (List (List Bool))):blocks.length ≤(vectorBits (blocks.map vectorBits)).length:=by
  simpa only [List.length_map] using vector_count (blocks.map vectorBits)
/-- Every actual phase payload is paid by the original acquired outer tape. -/
theorem phase_length (phases:Phases) (blocks:List (List (List Bool))) (hb:blocks∈phases):
    (vectorBits (blocks.map vectorBits)).length ≤(tape phases).length:=
  I.member_length _ _ (List.mem_map.mpr ⟨blocks,hb,rfl⟩)
/-- Every actual block payload is paid by its acquired phase tape. -/
theorem block_length (blocks:List (List (List Bool))) (words:List (List Bool)) (hw:words∈blocks):
    (vectorBits words).length ≤(vectorBits (blocks.map vectorBits)).length:=
  I.member_length _ _ (List.mem_map.mpr ⟨words,hw,rfl⟩)
/-- Entire actual output column bank cannot exceed its original phase-block input tape. -/
theorem result_length (phases:Phases) (key:List Bool):(result phases key).length ≤(tape phases).length:=by
  simp only [result,columns,List.map_map,Function.comp_def,tape]
  exact vector_map_mono phases _ _ (fun blocks _=>row_length key blocks)
/-- All actual one-block copies/parser/lookup/frame/reverse/drains fit the same physical-byte quadratic. -/
theorem block_time (key:List Bool) (words:List (List Bool)) (L:Nat) (hl:(vectorBits words).length ≤L):
    blockTime key words ≤10000000*(L+key.length+1)^2:=by
  have hlookup:=I.timeBound_le words key
  have hp:=Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_right hl key.length) 1) 2
  have hs:=coefficient_length key words
  have he:SemiprimeD1StackRecoveryEntriesIndexedExecution.timeBound words key ≤1000000*(L+key.length+1)^2:=
    hlookup.trans (Nat.mul_le_mul_left 1000000 hp)
  have hlin:L+key.length+1 ≤(L+key.length+1)^2:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤L+key.length+1) (by decide:1 ≤2)
  unfold blockTime
  rw [chunk_length]
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateCapacities
