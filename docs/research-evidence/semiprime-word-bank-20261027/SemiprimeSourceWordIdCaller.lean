/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdSearch
import RiemannGaussian.SemiprimeSourceWordIdMetadata
import RiemannGaussian.SemiprimeSourceScorePhysicalCaller

/-! # Original indexed source inputs to physically stored selected label IDs
Metadata is constructed from original dimensions/arities, descriptors are
actually compiled, and the acquired bank/ID controller supplies the labels.
No native source word, decoded prefix, advised menu or score is a runtime input.
Native original arity/owner/index/descriptor operations retain their own ledger.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceWordIdCaller
open SemiprimeMaterializedWords SemiprimeSourceWordBankSemantics

/-- Construct original metadata and score descriptors before the actual acquired-ID search. -/
def indexed (n F r Q lam : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) : Run (List (List Bool)) :=
  let metadata := SemiprimeSourceWordIdMetadata.acquire n F Q arity
  let compiled := SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst metadata.indices metadata.terms
  let result := SemiprimeSourceWordIdSearch.run metadata.incidences.length n r Q lam compiled.value metadata.indices.length
  ⟨result.value,metadata.clock+compiled.work+result.work+3⟩

/-- All actual stored labels remain acquired candidate IDs, without a decoder on runtime. -/
theorem indexed_valid (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    SemiprimeSourceWordIdControl.InMenu (SemiprimeSourceWordBank.acquire r Q).ids
      (indexed n F r Q lam arity owner).value := by
  exact SemiprimeSourceWordIdSearch.run_valid _ n r Q lam _ _

/-- Physically selected IDs decode to the EXACT previously proved original source
caller result; both candidate order and every left-on-tie decision are retained. -/
theorem indexed_refines (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (hlam : 0 < lam) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    (indexed n F r Q lam arity owner).value.map (decode r Q)=
      (SemiprimeSourceScorePhysicalCaller.computed owner Sigma.fst en lam).value := by
  let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
  have fields := SemiprimeSourceWordIdMetadata.indexed_fields n F r Q arity
  change (SemiprimeSourceWordIdSearch.run
      (SemiprimeSourceWordIdMetadata.acquire n F Q arity).incidences.length n r Q lam
      (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst
        (SemiprimeSourceWordIdMetadata.acquire n F Q arity).indices
        (SemiprimeSourceWordIdMetadata.acquire n F Q arity).terms).value
      (SemiprimeSourceWordIdMetadata.acquire n F Q arity).indices.length).value.map (decode r Q)=_
  rw [fields.1,fields.2.1,fields.2.2]
  let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst en.indices.values en.terms.values).value
  have hnew := SemiprimeSourceWordIdSearch.run_refines en.incidences.values.length n F r Q lam arity
    programs en.indices.values.length 0 hlam
  have hcard := SemiprimeSourceScoreCountOrder.caller_cardinality en
  rw [SemiprimeSourceOffsetHeight.caller_universal_length] at hcard
  have hold := SemiprimeSourceScorePhysicalSearch.run_refines en.incidences.values.length n lam
    en.wordFirst en.wordTail programs en.indices.values.length 0 (NeZero.pos r) hlam hcard
  exact hnew.trans hold.symm

/-- Direct original scalar-source comparison, with any shared offset appearing only in proof. -/
theorem indexed_original (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (hlam : 0 < lam) (offset : ℚ) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    (indexed n F r Q lam arity owner).value.map (decode r Q)=
      (SemiprimeMaterializedSourceWords.computedList owner Sigma.fst en.wordFirst en.wordTail
        en.terms.values en.indices.values (SemiprimeSourceScorePhysicalCaller.originalX en lam)
        ((n:ℚ)/(2*(r:ℚ))) offset).value :=
  (indexed_refines n F r Q lam arity owner hlam).trans
    (SemiprimeSourceScorePhysicalCaller.computed_refines owner Sigma.fst
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value lam hlam offset)

end RiemannGaussian.SemiprimeSourceWordIdCaller
