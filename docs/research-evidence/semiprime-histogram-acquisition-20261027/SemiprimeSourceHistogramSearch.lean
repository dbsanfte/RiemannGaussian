/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramQueryCorrectness
import RiemannGaussian.SemiprimeSourceWordIdControl
import RiemannGaussian.SemiprimeSourceScoreCountOrder
import RiemannGaussian.SemiprimeSourceScorePhysicalCaller

/-! # Actual original source selection from one acquired histogram cache
The executed selector uses compact bank IDs and the concrete physical histogram
query. Original quadratic term lists and native word functions occur only in
refinement specifications. No score callback is supplied by the caller.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeSourceHistogramSearch
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeRationalBits
open SemiprimeSourceWordIdControl
open SemiprimeSourceWordBankSemantics (decode)

/-- Compact acquired candidate IDs have the exact old first/tail menu ordering. -/
theorem tail_decode (n F r Q : ℕ) [NeZero r] (arity : Fin F→ℕ) :
    ((SemiprimeSourceCompactWordBank.acquire r Q).ids.tail.map (decode r Q))=
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordTail := by
  have h:=SemiprimeSourceCompactWordBank.ids_indexed n F r Q arity
  rw [SemiprimeSourceCompactWordBank.default_head,List.map_cons] at h
  exact (List.cons.inj h).2

/-- The literal compact-zero candidate is the original first source word. -/
theorem first_decode (n F r Q : ℕ) [NeZero r] (arity : Fin F→ℕ) :
    decode r Q []=(SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordFirst := by
  rw [SemiprimeSourceCompactWordBank.decode_default]
  rfl

/-- Actual canonical candidate membership, with no advised menu coverage. -/
theorem candidates_valid (r Q : ℕ) [NeZero r] :
    InMenu (SemiprimeSourceCompactWordBank.acquire r Q).ids
      ([]::(SemiprimeSourceCompactWordBank.acquire r Q).ids.tail) := by
  intro id hi
  simpa only [←SemiprimeSourceCompactWordBank.default_head r Q] using hi

/-- The original count specification is exactly the old indexed sequential
count, not merely a proportional score or a permuted source term list. -/
theorem counts_indexed (n F r Q : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool)) (s : ℕ) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst
      en.indices.values en.terms.values).value
    SemiprimeSourceHistogramQueryCorrectness.originalCounts n F r Q arity owner fixed s=
      (SemiprimeSourceScoreCountsObjective.sequentialCounts en.wordFirst en.wordTail programs s
        (fixed.map (decode r Q))).value := by
  dsimp only
  have hfields:=SemiprimeSourceWordIdMetadata.indexed_fields n F r Q arity
  have hmenu : (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordFirst::
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value.wordTail=
      (SemiprimeFiniteEnumerations.words r Q).values :=
    (SemiprimeSourceCompactWordBank.ids_indexed n F r Q arity).symm.trans
      (SemiprimeSourceCompactWordBank.ids_decode r Q)
  unfold SemiprimeSourceHistogramQueryCorrectness.originalCounts
    SemiprimeSourceScoreCountsObjective.sequentialCounts
  dsimp only
  simp only [SemiprimeSourceHistogramHeadOriginal.originalEnv,List.length_map]
  rw [hfields.2.1,hfields.2.2,←hmenu,first_decode n F r Q arity]

/-- The concrete acquired query has exactly the original integer count objective
on every actual compact-menu prefix. No score/count oracle is supplied. -/
theorem query_integerValue (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool)) (s : ℕ)
    (hf : InMenu (SemiprimeSourceCompactWordBank.acquire r Q).ids fixed) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst
      en.indices.values en.terms.values).value
    (SemiprimeSourceHistogramQuery.score
      (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner) fixed s).word.value=
      (SemiprimeSourceScoreCountOrder.integerValue (∑ e,arity e) n lam (r^(2*Q))
        en.wordFirst en.wordTail programs s (fixed.map (decode r Q)):ℚ) := by
  dsimp only
  rw [SemiprimeSourceHistogramQueryCorrectness.score_original n F r Q lam arity owner fixed s hf]
  simp only [counts_indexed]
  rfl

/-- Actual histogram queries preserve every original comparison, including ties. -/
theorem query_order (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (fixed : List (List Bool)) (v w : List Bool) (s : ℕ) (offset : ℚ)
    (hf : InMenu (SemiprimeSourceCompactWordBank.acquire r Q).ids fixed)
    (hv : v∈(SemiprimeSourceCompactWordBank.acquire r Q).ids)
    (hw : w∈(SemiprimeSourceCompactWordBank.acquire r Q).ids) (hlam : 0<lam) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst
      en.indices.values en.terms.values).value
    let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
    (SemiprimeSourceHistogramQuery.score cache (v::fixed) s).word.value ≤
      (SemiprimeSourceHistogramQuery.score cache (w::fixed) s).word.value ↔
    (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs
      (((∑ e,arity e : ℕ):ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ)))
      offset s (decode r Q v::fixed.map (decode r Q))).value ≤
    (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs
      (((∑ e,arity e : ℕ):ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ)))
      offset s (decode r Q w::fixed.map (decode r Q))).value := by
  dsimp only
  rw [query_integerValue n F r Q lam arity owner (v::fixed) s (inMenu_cons _ fixed v hv hf),
    query_integerValue n F r Q lam arity owner (w::fixed) s (inMenu_cons _ fixed w hw hf)]
  let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
  let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst
    en.indices.values en.terms.values).value
  have hcard : (en.wordFirst::en.wordTail).length^4=(r^(2*Q))^2 := by
    simpa only [SemiprimeSourceOffsetHeight.caller_universal_length] using
      SemiprimeSourceScoreCountOrder.caller_cardinality en
  have hc:=SemiprimeSourceScoreCountOrder.integer_le_iff (∑ e,arity e) n lam (r^(2*Q))
    en.wordFirst en.wordTail programs offset s s
    ((v::fixed).map (decode r Q)) ((w::fixed).map (decode r Q))
    (NeZero.pos r) hlam (pow_pos (NeZero.pos r) _) hcard
  exact (show ((SemiprimeSourceScoreCountOrder.integerValue (∑ e,arity e) n lam (r^(2*Q))
      en.wordFirst en.wordTail programs s ((v::fixed).map (decode r Q)):ℚ) ≤
      (SemiprimeSourceScoreCountOrder.integerValue (∑ e,arity e) n lam (r^(2*Q))
        en.wordFirst en.wordTail programs s ((w::fixed).map (decode r Q)):ℚ)) ↔
      SemiprimeSourceScoreCountOrder.integerValue (∑ e,arity e) n lam (r^(2*Q))
        en.wordFirst en.wordTail programs s ((v::fixed).map (decode r Q)) ≤
      SemiprimeSourceScoreCountOrder.integerValue (∑ e,arity e) n lam (r^(2*Q))
        en.wordFirst en.wordTail programs s ((w::fixed).map (decode r Q)) from by exact_mod_cast Iff.rfl).trans hc

/-- Acquire setup ONCE, then use only the shared compact bank and concrete
histogram query for every original prefix/candidate score. -/
def run (n F r Q lam : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) : Run (List (List Bool)) :=
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  let bank := cache.rows.source.bank
  let N := cache.data.metadata.indices.length
  let result := SemiprimeSourceChoiceBits.run [] bank.ids.tail
    (fun tokens fixed => SemiprimeSourceHistogramQuery.score cache fixed tokens.length) N []
  ⟨result.value,cache.clock+result.work+N+4⟩

/-- The setup acquisition report and every executed query/controller report remain paid. -/
theorem run_retains_setup (n F r Q lam : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).clock ≤
      (run n F r Q lam arity owner).work := by
  unfold run
  dsimp only
  omega

/-- Every selected output remains an actual compact candidate ID. -/
theorem run_valid (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    InMenu (SemiprimeSourceCompactWordBank.acquire r Q).ids (run n F r Q lam arity owner).value := by
  change InMenu _ (SemiprimeSourceChoiceBits.run []
    (SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner).rows.source.bank.ids.tail
    _ _ []).value
  rw [SemiprimeSourceHistogramSetup.bank_actual]
  exact assign_inMenu _ [] (SemiprimeSourceCompactWordBank.acquire r Q).ids.tail _ _ []
    (candidates_valid r Q) (by simp [InMenu])


/-- The actual selector returns one acquired ID for every original variable. -/
theorem run_length (n F r Q lam : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (run n F r Q lam arity owner).value.length=n+F := by
  simp only [run,SemiprimeSourceChoiceBits.run,SemiprimeSourceChoiceBits.assign_length,
    List.length_nil,Nat.zero_add,SemiprimeSourceChoiceBits.acquireTokens_value,List.length_replicate,
    SemiprimeSourceHistogramSetup.metadata_actual]
  exact (SemiprimeSourceHistogramMetadata.sizes n F Q arity).2.2.2.2

/-- The concrete one-setup histogram selector returns exactly the old indexed
source search labels, including every original left-on-tie decision. -/
theorem run_refines (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (offset : ℚ) (hlam : 0<lam) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst
      en.indices.values en.terms.values).value
    (run n F r Q lam arity owner).value.map (decode r Q)=
      (SemiprimeMaterializedScoreSearch.search en.wordFirst en.wordTail programs
        (((∑ e,arity e : ℕ):ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ)))
        offset en.indices.values.length).value := by
  let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
  let cache := SemiprimeSourceHistogramSetup.acquire n F r Q lam arity owner
  let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst
    en.indices.values en.terms.values).value
  have hn : cache.data.metadata.indices.length=en.indices.values.length := by
    rw [SemiprimeSourceHistogramSetup.metadata_actual,
      (SemiprimeSourceHistogramMetadata.original_fields n F Q arity).2,
      (SemiprimeSourceWordIdMetadata.indexed_fields n F r Q arity).2.2]
  have h:=SemiprimeSourceWordIdControl.run_decode
    (SemiprimeSourceCompactWordBank.acquire r Q).ids (decode r Q) []
    (SemiprimeSourceCompactWordBank.acquire r Q).ids.tail
    (fun tokens fixed => SemiprimeSourceHistogramQuery.score cache fixed tokens.length)
    (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs
      (((∑ e,arity e : ℕ):ℚ)/((r:ℚ)*(lam:ℚ)*(r^(2*Q):ℕ))) ((n:ℚ)/(2*(r:ℚ))) offset)
    (fun tokens fixed _ => SemiprimeSourceHistogramQuery.score_valid _ _ _)
    (fun tokens fixed hf v hv w hw => query_order n F r Q lam arity owner fixed v w
      tokens.length offset hf hv hw hlam)
    en.indices.values.length [] (candidates_valid r Q) (by simp [InMenu])
  rw [first_decode n F r Q arity,tail_decode n F r Q arity] at h
  change (SemiprimeSourceChoiceBits.run [] cache.rows.source.bank.ids.tail
    (fun tokens fixed => SemiprimeSourceHistogramQuery.score cache fixed tokens.length)
    cache.data.metadata.indices.length []).value.map (decode r Q)=_
  rw [SemiprimeSourceHistogramSetup.bank_actual,hn]
  exact h


/-- Exact old original source-caller labels from the new physical histogram
selector, with no old descriptor list or old score callback on the runtime path. -/
theorem indexed_refines (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (hlam : 0<lam) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    (run n F r Q lam arity owner).value.map (decode r Q)=
      (SemiprimeSourceScorePhysicalCaller.computed owner Sigma.fst en lam).value := by
  let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
  let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst
    en.indices.values en.terms.values).value
  have hnew:=run_refines n F r Q lam arity owner 0 hlam
  have hcard : (en.wordFirst::en.wordTail).length^4=(r^(2*Q))^2 := by
    simpa only [SemiprimeSourceOffsetHeight.caller_universal_length] using
      SemiprimeSourceScoreCountOrder.caller_cardinality en
  have hold:=SemiprimeSourceScorePhysicalSearch.run_refines en.incidences.values.length n lam
    en.wordFirst en.wordTail programs en.indices.values.length 0 (NeZero.pos r) hlam hcard
  have hM : en.incidences.values.length=∑ e,arity e :=
    SemiprimePaidFiniteEnumerations.indexed_incidence_length n F r Q arity
  rw [←hM] at hnew
  exact hnew.trans hold.symm

/-- Exact ORIGINAL computed source labels for any shared proof-side offset.
Candidate order, output order and all left-on-tie decisions are unchanged. -/
theorem indexed_original (n F r Q lam : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (hlam : 0<lam) (offset : ℚ) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value
    (run n F r Q lam arity owner).value.map (decode r Q)=
      (SemiprimeMaterializedSourceWords.computedList owner Sigma.fst en.wordFirst en.wordTail
        en.terms.values en.indices.values (SemiprimeSourceScorePhysicalCaller.originalX en lam)
        ((n:ℚ)/(2*(r:ℚ))) offset).value :=
  (indexed_refines n F r Q lam arity owner hlam).trans
    (SemiprimeSourceScorePhysicalCaller.computed_refines owner Sigma.fst
      (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value lam hlam offset)

end RiemannGaussian.SemiprimeSourceHistogramSearch
