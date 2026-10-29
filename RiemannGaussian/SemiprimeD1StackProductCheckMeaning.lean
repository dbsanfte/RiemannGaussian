/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductCheckBounds
import RiemannGaussian.SemiprimeMacroEntryBitCheck

/-! # Exact original guarded product semantics
The actual computed Boolean has the original canonicality and modular product
meaning for all raw words. The original expression evaluator occurs only in
the specification; the actual checker uses its paid direct arithmetic trace.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProductCheckMeaning
open SemiprimeD1StackProductCheck SemiprimeD1StackProductCheckGuard
open SemiprimeD1StackProductCheckParse SemiprimeD1StackProductCheckExecution
open SemiprimeBitArithmetic SemiprimeMacroEntryBitPrimitives

/-- Exact computed vector guard, without assuming canonicality of any word. -/
theorem accepted_true (raw cached : List Bool) :
    accepted raw cached=true ↔
      bitValue (first raw cached)<bitValue cached ∧ bitValue (second raw cached)<bitValue cached ∧
      bitValue (third raw cached)<bitValue cached := by
  rw [accepted,SemiprimeD1StackVectorCanonicalExecution.answer_true,
    SemiprimeD1StackProductCheckBounds.words_three]
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]

/-- Integer characterization of the actually computed guarded verdict. It is
valid even for a zero modulus, because actual canonicality then rejects. -/
theorem answer_true (raw cached : List Bool) :
    answer raw cached=true ↔
      bitValue (first raw cached)<bitValue cached ∧ bitValue (second raw cached)<bitValue cached ∧
      bitValue (third raw cached)<bitValue cached ∧
      (bitValue (first raw cached)*bitValue (second raw cached))%bitValue cached=bitValue (third raw cached) := by
  cases ha:accepted raw cached with
  | false =>
    simp only [answer,ha,Bool.false_eq_true,ite_false]
    constructor
    · intro h;cases h
    · rintro ⟨h0,h1,h2,_⟩
      have ht:accepted raw cached=true := (accepted_true raw cached).mpr ⟨h0,h1,h2⟩
      rw [ha] at ht
      cases ht
  | true =>
    obtain ⟨h0,h1,h2⟩:=(accepted_true raw cached).mp ha
    have hm:=accepted_modulus_pos raw cached ha
    simp only [answer,ha,ite_true,SemiprimeD1StackProductCheckCompute.verdict,decide_eq_true_eq,
      SemiprimeD1StackProductCheckCompute.residue,
      SemiprimeD1StackResidueMulBounds.residue_value _ _ cached hm,h0,h1,h2,true_and]

/-- Original two input words, specified in the same physical order as parsing. -/
def inputWords (raw cached : List Bool) (i : Fin 2) : List Bool :=
  if i=0 then first raw cached else second raw cached

/-- The actual direct product checker returns EXACTLY the old original
guarded expression-check verdict, on all raw words and original configs. -/
theorem old_product (p : SemiprimeMacroGraphSemantics.Config) (raw : List Bool) :
    answer raw (SemiprimeMacroEntryBitCheck.modulus p)=
      (SemiprimeMacroEntryBitCheck.equationRun p (inputWords raw (SemiprimeMacroEntryBitCheck.modulus p))
        (third raw (SemiprimeMacroEntryBitCheck.modulus p))
        (.mul (.literal (first raw (SemiprimeMacroEntryBitCheck.modulus p)))
          (.literal (second raw (SemiprimeMacroEntryBitCheck.modulus p))))).accepted := by
  let cached:=SemiprimeMacroEntryBitCheck.modulus p
  have hm : 0<bitValue cached := by
    have h:=SemiprimeMacroEntryBitCheck.modulus_gt_four p
    change 4<bitValue cached at h
    omega
  apply Bool.eq_iff_iff.mpr
  rw [answer_true]
  simp only [SemiprimeMacroEntryBitCheck.equationRun,SemiprimeMacroEntryBitCheck.guardRun_correct,
    SemiprimeMacroEntryBitCheck.andRun,Bool.and_eq_true,SemiprimeMacroEntryBitCheck.canonicalRun_correct,
    lessBits_correct]
  constructor
  · rintro ⟨ha,hb,ho,he⟩
    refine ⟨⟨?_,ho⟩,?_⟩
    · intro i;fin_cases i
      · exact ha
      · exact hb
    · rw [residueEqualityBits_correct cached hm (.literal (third raw cached))
        (.mul (.literal (first raw cached)) (.literal (second raw cached))) ho ⟨ha,hb⟩]
      change (bitValue (third raw cached) : ZMod (bitValue cached))=
        (bitValue (first raw cached) : ZMod (bitValue cached))*(bitValue (second raw cached) : ZMod (bitValue cached))
      rw [←Nat.cast_mul,←he,ZMod.natCast_mod]
  · rintro ⟨⟨hi,ho⟩,he⟩
    have ha : bitValue (first raw cached)<bitValue cached := hi 0
    have hb : bitValue (second raw cached)<bitValue cached := hi 1
    refine ⟨ha,hb,ho,?_⟩
    rw [residueEqualityBits_correct cached hm (.literal (third raw cached))
      (.mul (.literal (first raw cached)) (.literal (second raw cached))) ho ⟨ha,hb⟩] at he
    change (bitValue (third raw cached) : ZMod (bitValue cached))=
      (bitValue (first raw cached) : ZMod (bitValue cached))*(bitValue (second raw cached) : ZMod (bitValue cached)) at he
    rw [←Nat.cast_mul] at he
    have hv:=congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt ho,ZMod.val_natCast] at hv
    exact hv.symm

end RiemannGaussian.SemiprimeD1StackProductCheckMeaning
