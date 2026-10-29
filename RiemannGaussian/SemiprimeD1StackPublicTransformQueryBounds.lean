/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformInventory
/-! # Original-derived per-output transform transition budget -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformQueryBounds
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformWords
open SemiprimeD1StackPublicTransformLoopState SemiprimeD1StackPublicTransformQuery
open SemiprimeD1StackPublicTransformRead SemiprimeD1StackPublicTransformQueryClosure
open SemiprimeD1StackPublicTransformInventory SemiprimeBitArithmetic
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Even an absent word has a derived width bound; no canonicality is assumed. -/
theorem default_length (width raw : List Bool) (n k : ℕ) :
    (SemiprimeD1StackExprDotSpec.wordAt (SemiprimeD1StackWordVectorSpec.blocks width n raw) k).length ≤ width.length := by
  by_cases hk : k<n
  · rw [SemiprimeD1StackExprDotSpec.wordAt,SemiprimeD1StackWordVectorSpec.blocks_get width n raw k hk,Option.getD_some]
    exact (SemiprimeD1StackWordBlockExecution.result_length _ _).le
  · have hn : (SemiprimeD1StackWordVectorSpec.blocks width n raw).length ≤ k := by
      rw [SemiprimeD1StackWordVectorSpec.blocks_length];omega
    rw [SemiprimeD1StackExprDotSpec.wordAt,List.getElem?_eq_none hn,Option.getD_none,List.length_nil]
    exact Nat.zero_le _
/-- Actual output bytes are always at most the acquired width. -/
theorem output_length (bits raw : List Bool) (second : Bool) (k : ℕ) :
    (outputWord bits raw second k).length ≤ (cached bits).length :=
  default_length _ _ _ _
/-- Complete actual dot input inventory is quadratic in original acquired caches. -/
theorem dot_inventory (bits raw : List Bool) (second inverse : Bool) (k : ℕ)
    (hk : k ≤ size bits second) :
    SemiprimeD1StackDotEvaluateBounds.inputSize (queryCache bits raw second inverse k) (cached bits)+1 ≤
      10*(inputSize bits raw second inverse)^2 := by
  obtain ⟨_,_,hm,hb,_,hn,hs,hS⟩:=caps bits raw second inverse
  have hv:=(vector_caps bits raw second inverse).1
  unfold SemiprimeD1StackDotEvaluateBounds.inputSize SemiprimeD1StackExprDotBounds.inputSize queryCache
  rw [stride_unary,count_unary]
  simp only [unary,List.length_replicate]
  nlinarith
private theorem dot_poly (t x S : ℕ) (ht : t ≤ 10000000000*x^8) (hx : x ≤ 10*S^2) :
    t ≤ 10^18*S^16 := by
  have h:=Nat.mul_le_mul_left 10000000000 (Nat.pow_le_pow_left hx 8)
  rw [mul_pow,←pow_mul,←Nat.mul_assoc] at h
  norm_num only [Nat.reducePow,Nat.reduceMul] at h ⊢
  exact ht.trans h
attribute [local irreducible] SemiprimeD1StackRootSourceExecution.done
  SemiprimeD1BinaryPublicAcquisitionComponents.result
/-- Every ACTUALLY executed query has a fixed degree-sixteen budget; validity
is derived locally from the computed input guard, not supplied at the endpoint. -/
theorem query_le (bits raw : List Bool) (second inverse : Bool) (k : ℕ)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (hg : SemiprimeD1StackPublicTransformGuards.inputFlag (rootData bits) raw second=true)
    (hk : k ≤ size bits second) :
    queryBudget bits raw second inverse k ≤ 10^21*(inputSize bits raw second inverse)^16 := by
  let S:=inputSize bits raw second inverse
  obtain ⟨_,_,hm,hb,hNorm,hn,hs,hS⟩:=caps bits raw second inverse
  have hv:=dot_valid bits raw second inverse k hc hN hg
  have hmpos : 0<bitValue (cached bits) := by have h:=(original_valid bits hc hN inverse).1;omega
  have hdlen : (dotWord bits raw second inverse k).length ≤ (cached bits).length :=
    (SemiprimeMacroEntryBitPrimitives.execute_bounds (cached bits) hmpos _ hv).1.le
  have hplen : (productWord bits raw second inverse k).length=(cached bits).length :=
    SemiprimeD1StackResidueMulBounds.residue_width _ _ _
  have holen:=output_length bits raw second k
  have hdot:=SemiprimeD1StackDotEvaluateBounds.timeBound_le (queryCache bits raw second inverse k) (cached bits)
    (expression bits inverse) (source_code bits inverse) (inputs (rootData bits) raw second)
    (size bits (!second)) k (size bits second) (stride_unary bits second) rfl (count_unary bits second) rfl hmpos hv
  have hdot' : SemiprimeD1StackDotEvaluateExecution.timeBound (queryCache bits raw second inverse k) (cached bits)
      (expression bits inverse) (inputs (rootData bits) raw second) (size bits (!second)) k (size bits second) ≤ 10^18*S^16 :=
    dot_poly _ _ _ hdot (dot_inventory bits raw second inverse k hk)
  have hmul:= (SemiprimeD1StackResidueMulBounds.totalTime_le (normalizer bits second inverse)
    (dotWord bits raw second inverse k) (cached bits)).trans
      (SemiprimeD1StackResidueMulBounds.timeBound_le_cube _ _ _)
  have hsum : (normalizer bits second inverse).length+(dotWord bits raw second inverse k).length+(cached bits).length+3 ≤ 5*S := by
    change _ ≤ 5*inputSize bits raw second inverse;omega
  have hcube:=Nat.pow_le_pow_left hsum 3
  rw [mul_pow] at hcube
  norm_num only [Nat.reducePow] at hcube
  have hmul' : SemiprimeD1StackResidueMulExecution.totalTime (normalizer bits second inverse)
      (dotWord bits raw second inverse k) (cached bits) ≤ 1250000*S^3 := by
    have h:=Nat.mul_le_mul_left 10000 hcube
    rw [←Nat.mul_assoc] at h
    norm_num only [Nat.reduceMul] at h
    exact hmul.trans h
  have hread:=SemiprimeD1StackJetReadExecution.totalTime_le (unary k) (outputs (rootData bits) raw second)
  have hvec:=(vector_caps bits raw second inverse).2
  have heq:=SemiprimeD1StackWordEqualExecution.executionTime_le (productWord bits raw second inverse k) (outputWord bits raw second k)
  have h1 : S ≤ S^16 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ S) (by decide : 1 ≤ 16)
  have h2 : S^2 ≤ S^16 := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 16)
  have h3 : S^3 ≤ S^16 := Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 16)
  have hp : 0<S^16 := Nat.pow_pos (by omega)
  unfold queryBudget
  unfold SemiprimeD1StackJetReadExecution.timeBound at hread
  simp only [unary,List.length_replicate] at hread ⊢
  change _ ≤ 10^21*S^16
  norm_num only [Nat.reducePow]
  change (vectorBits (outputs (rootData bits) raw second)).length ≤ 5*S^2 at hvec
  change (cached bits).length ≤ S at hm
  change (normalizer bits second inverse).length ≤ S at hNorm
  change size bits second ≤ S at hn
  omega
end RiemannGaussian.SemiprimeD1StackPublicTransformQueryBounds
