/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformExecution
/-! # Actual query verdicts and original normalization semantics -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformMeaning
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformWords
open SemiprimeD1StackPublicTransformGuards SemiprimeD1StackPublicTransformQuery
open SemiprimeD1StackPublicTransformRead SemiprimeBitArithmetic SemiprimeMacroEntryBitPrimitives
/-- Actual physical multiplication and comparison are precisely the normalized
ring equation, under guards already computed by the executed frontend. -/
theorem query_true (bits raw : List Bool) (second inverse : Bool) (k : ℕ)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (hi : inputFlag (rootData bits) raw second=true)
    (ho : outputFlag (rootData bits) raw second=true) :
    queryAnswer bits raw second inverse k=true ↔
      meaning (cached bits) (if second then SemiprimeMacroEntryBitCheck.normalizationExpr
        (SemiprimePublicFactorCount.publicConfig (bitValue bits) hN) (transform inverse)
        else oneExpr)*meaning (cached bits) (dotExpression bits raw second inverse k)=
      (bitValue (outputWord bits raw second k) : ZMod (bitValue (cached bits))) := by
  obtain ⟨hm,_⟩:=original_valid bits hc hN inverse
  have hp : 0<bitValue (cached bits) := by omega
  have hd:=dot_valid bits raw second inverse k hc hN hi
  have he:=execute_correct (cached bits) hp _ hd
  have hv:=SemiprimeD1StackGuardedDotExecution.defaulted_canonical (cached bits)
    (outputs (rootData bits) raw second) hp ho k
  change bitValue (outputWord bits raw second k)<bitValue (cached bits) at hv
  have hr:=SemiprimeD1StackResidueMulBounds.residue_value
    (normalizer bits second inverse) (dotWord bits raw second inverse k) (cached bits) hp
  have hb : bitValue (productWord bits raw second inverse k)<bitValue (cached bits) := by
    change bitValue (SemiprimeD1StackResidueMulExecution.residue _ _ _)<_
    rw [hr];exact Nat.mod_lt _ hp
  have hcast : (bitValue (productWord bits raw second inverse k) : ZMod (bitValue (cached bits)))=
      meaning (cached bits) (.literal (normalizer bits second inverse))*meaning (cached bits) (dotExpression bits raw second inverse k) := by
    change ((bitValue (SemiprimeD1StackResidueMulExecution.residue _ _ _) : ℕ) : ZMod (bitValue (cached bits)))=_
    rw [hr,ZMod.natCast_mod,Nat.cast_mul]
    change (bitValue (normalizer bits second inverse) : ZMod (bitValue (cached bits)))*
      (bitValue (execute (cached bits) (dotExpression bits raw second inverse k)).bits : ZMod (bitValue (cached bits)))=_
    rw [he];rfl
  rw [normalizer_meaning bits hc hN second inverse] at hcast
  change decide (bitValue (productWord bits raw second inverse k)=bitValue (outputWord bits raw second k))=true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · intro h;rw [←hcast,h]
  · intro h
    have hh:=congrArg ZMod.val (hcast.trans h)
    simpa only [ZMod.val_natCast_of_lt hb,ZMod.val_natCast_of_lt hv] using hh
/-- The physical descending loop checks each original frequency exactly once. -/
theorem loop_answer_true (bits raw : List Bool) (second inverse : Bool) (n : ℕ) :
    SemiprimeD1StackPublicTransformLoop.answer bits raw second inverse n=true ↔
      ∀k<n,queryAnswer bits raw second inverse k=true := by
  induction n with
  | zero=>simp only [SemiprimeD1StackPublicTransformLoop.answer,forall_prop_of_false (Nat.not_lt_zero _),implies_true]
  | succ n ih=>
    rw [SemiprimeD1StackPublicTransformLoop.answer,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨hn,hs⟩ k hk
      by_cases he : k=n
      · subst k;exact hn
      · exact hs k (by omega)
    · intro h;exact ⟨h n (by omega),fun k hk=>h k (by omega)⟩
end RiemannGaussian.SemiprimeD1StackPublicTransformMeaning
