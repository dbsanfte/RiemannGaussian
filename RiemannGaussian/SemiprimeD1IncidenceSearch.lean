/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramSearch
import RiemannGaussian.SemiprimeSourceHistogramSearchBudget

/-! # Actual incidence-only original-graph selector for D1 packet construction
One cache feeds the existing physical ID controller. Only the incidence query
executes at candidates; no head penalty or original quadratic term list executes.
Palette cardinality r^a is distinct from the future packet length 2^a.
-/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace RiemannGaussian.SemiprimeD1IncidenceSearch
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation MulticolorTypes
open SemiprimeMaterializedWords SemiprimeRationalBits
open SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceWordIdControl
open SemiprimeSourceWordBankSemantics (decode)

/-- Actual incidence lane after one acquired prefix dictionary; no head query. -/
def query {n F a : ℕ} {arity : Fin F→ℕ}
    (cache : SemiprimeSourceHistogramSetup.Cache n F a arity)
    (fixed : List (List Bool)) (s : ℕ) : RationalReport :=
  let dict :=  SemiprimeSourceHistogramPrefix.acquire fixed
  let out := SemiprimeSourceHistogramQuery.incidenceWith cache dict.trie fixed.length s
  ⟨out.word,dict.clock+out.clock+fixed.length+7⟩

/-- The concrete incidence output is valid physical denominator-one arithmetic. -/
theorem query_valid {n F a : ℕ} {arity : Fin F→ℕ}
    (cache : SemiprimeSourceHistogramSetup.Cache n F a arity)
    (fixed : List (List Bool)) (s : ℕ) : (query cache fixed s).word.Valid :=
  SemiprimeSourceHistogramArithmetic.den_valid _
    (SemiprimeSourceHistogramQuery.incidence_den cache _ _ _)

/-- All original prefixes have the exact padded incidence count. -/
theorem query_value (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool)) (s : ℕ)
    (hf : InMenu (SemiprimeSourceCompactWordBank.acquire r a).ids fixed) :
    (query (SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner) fixed s).word.value=
      ((SemiprimeSourceHistogramQueryCorrectness.originalCounts n F r a arity owner fixed s).incidence:ℚ) :=
  SemiprimeSourceHistogramQueryCorrectness.incidence_original n F r a 0 arity owner fixed s hf

/-- Incidence count scaling is the same positive Lword^4 at every prefix. -/
theorem query_order (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (fixed : List (List Bool))
    (v w : List Bool) (s : ℕ)
    (hf : InMenu (SemiprimeSourceCompactWordBank.acquire r a).ids fixed)
    (hv : v∈(SemiprimeSourceCompactWordBank.acquire r a).ids)
    (hw : w∈(SemiprimeSourceCompactWordBank.acquire r a).ids) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r a arity).value
    let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst
      en.indices.values en.terms.values).value
    let cache := SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner
    (query cache (v::fixed) s).word.value≤(query cache (w::fixed) s).word.value ↔
      (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs 0 1 0 s
        (decode r a v::fixed.map (decode r a))).value≤
      (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs 0 1 0 s
        (decode r a w::fixed.map (decode r a))).value := by
  dsimp only
  rw [query_value n F r a arity owner (v::fixed) s (inMenu_cons _ fixed v hv hf),
    query_value n F r a arity owner (w::fixed) s (inMenu_cons _ fixed w hw hf)]
  simp only [SemiprimeSourceHistogramSearch.counts_indexed,
    SemiprimeSourceScoreCountsObjective.sequential_counts,one_pow,zero_pow (by decide : (2:ℕ)≠0),
    one_mul,zero_mul,add_zero,sub_zero,List.map_cons]
  have hd : (0:ℚ)<(((SemiprimePaidFiniteEnumerations.indexed n F r a arity).value.wordFirst::
      (SemiprimePaidFiniteEnumerations.indexed n F r a arity).value.wordTail).length:ℚ)^4 := by
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    positivity
  exact (div_le_div_iff_of_pos_right hd).symm

/-- Setup is acquired once; every candidate executes the concrete incidence query.
The full reusable cache has some unused once-paid fields, never a head penalty. -/
def run (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) : Run (List (List Bool)) :=
  let cache := SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner
  let N := cache.data.metadata.indices.length
  let result := SemiprimeSourceChoiceBits.run [] cache.rows.source.bank.ids.tail
    (fun tokens fixed => query cache fixed tokens.length) N []
  ⟨result.value,cache.clock+result.work+N+4⟩

/-- Every selected byte ID is an actually acquired original candidate. -/
theorem run_valid (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    InMenu (SemiprimeSourceCompactWordBank.acquire r a).ids (run n F r a arity owner).value := by
  change InMenu _ (SemiprimeSourceChoiceBits.run []
    (SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner).rows.source.bank.ids.tail _ _ []).value
  rw [SemiprimeSourceHistogramSetup.bank_actual]
  exact assign_inMenu _ [] _ _ _ [] (SemiprimeSourceHistogramSearch.candidates_valid r a) (by simp [InMenu])

/-- One original compact ID is returned for each original vertex on both sides. -/
theorem run_length (n F r a : ℕ) (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (run n F r a arity owner).value.length=n+F := by
  simp only [run,SemiprimeSourceChoiceBits.run,SemiprimeSourceChoiceBits.assign_length,
    List.length_nil,Nat.zero_add,SemiprimeSourceChoiceBits.acquireTokens_value,List.length_replicate,
    SemiprimeSourceHistogramSetup.metadata_actual]
  exact (SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.2.2

/-- Exact original x=0,y=1 conditional-expectation search, with every tie preserved. -/
theorem run_refines (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    let en := (SemiprimePaidFiniteEnumerations.indexed n F r a arity).value
    let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst
      en.indices.values en.terms.values).value
    (run n F r a arity owner).value.map (decode r a)=
      (SemiprimeMaterializedScoreSearch.search en.wordFirst en.wordTail programs 0 1 0 en.indices.values.length).value := by
  let en := (SemiprimePaidFiniteEnumerations.indexed n F r a arity).value
  let cache := SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner
  let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst en.indices.values en.terms.values).value
  have hn : cache.data.metadata.indices.length=en.indices.values.length := by
    rw [SemiprimeSourceHistogramSetup.metadata_actual,
      (SemiprimeSourceHistogramMetadata.original_fields n F a arity).2,
      (SemiprimeSourceWordIdMetadata.indexed_fields n F r a arity).2.2]
  have h := SemiprimeSourceWordIdControl.run_decode
    (SemiprimeSourceCompactWordBank.acquire r a).ids (decode r a) []
    (SemiprimeSourceCompactWordBank.acquire r a).ids.tail
    (fun tokens fixed => query cache fixed tokens.length)
    (SemiprimeMaterializedScoreSearch.sequential en.wordFirst en.wordTail programs 0 1 0)
    (fun tokens fixed _ => query_valid _ _ _)
    (fun tokens fixed hf v hv w hw => query_order n F r a arity owner fixed v w tokens.length hf hv hw)
    en.indices.values.length [] (SemiprimeSourceHistogramSearch.candidates_valid r a) (by simp [InMenu])
  rw [SemiprimeSourceHistogramSearch.first_decode n F r a arity,
    SemiprimeSourceHistogramSearch.tail_decode n F r a arity] at h
  change (SemiprimeSourceChoiceBits.run [] cache.rows.source.bank.ids.tail
    (fun tokens fixed => query cache fixed tokens.length) cache.data.metadata.indices.length []).value.map _=_
  rw [SemiprimeSourceHistogramSetup.bank_actual,hn]
  exact h

/-- Original terminal score depends only on its literal support, for every program. -/
theorem program_depends {r a : ℕ} (p : ScoreProgram a) :
    DependsOn (support p).toFinset (programValue (r:=r) 0 1 p) := by
  intro x y h
  cases p with
  | incidence aa b c d =>
    have ha := h aa (by simp [support])
    have hb := h b (by simp [support])
    have hc := h c (by simp [support])
    have hd := h d (by simp [support])
    simp only [programValue,ha,hb,hc,hd]
  | head t aa b => simp [programValue]

/-- Generic original scalar search never increases its initial exact mean.
The supplied programs are concrete old specifications, not a runtime oracle. -/
theorem original_search_le {r a : ℕ} (first : Word r a) (tail : List (Word r a))
    (programs : List (ScoreProgram a)) (N : ℕ) :
    (SemiprimeMaterializedScoreSearch.sequential first tail programs 0 1 0 0
      (SemiprimeMaterializedScoreSearch.search first tail programs 0 1 0 N).value).value≤
    (SemiprimeMaterializedScoreSearch.sequential first tail programs 0 1 0 N []).value := by
  rw [SemiprimeMaterializedScoreSearch.sequential_value,SemiprimeMaterializedScoreSearch.sequential_value,
    SemiprimeMaterializedScoreSearch.search_value,
    sequentialEvaluator_zero _ (by simp) _ _ _ program_depends]
  exact localAssign_le_initial first tail programs (fun p => (support p).toFinset)
    (programValue 0 1) program_depends 0 first N

/-- Actual physical selected IDs have no larger padded original incidence count
than the all-free initial assignment, for every original graph and palette. -/
theorem counts_le_initial (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    (SemiprimeSourceHistogramQueryCorrectness.originalCounts n F r a arity owner
      (run n F r a arity owner).value 0).incidence≤
    (SemiprimeSourceHistogramQueryCorrectness.originalCounts n F r a arity owner [] (n+F)).incidence := by
  let en := (SemiprimePaidFiniteEnumerations.indexed n F r a arity).value
  let programs := (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst en.indices.values en.terms.values).value
  have h := original_search_le en.wordFirst en.wordTail programs en.indices.values.length
  rw [←run_refines n F r a arity owner] at h
  rw [SemiprimeSourceScoreCountsObjective.sequential_counts,
    SemiprimeSourceScoreCountsObjective.sequential_counts] at h
  simp only [one_pow,zero_pow (by decide : (2:ℕ)≠0),one_mul,zero_mul,add_zero,sub_zero] at h
  have hn : en.indices.values.length=n+F := by
    exact SemiprimePaidFiniteEnumerations.indexed_indices_length n F r a arity
  rw [hn] at h
  have hf := SemiprimeSourceHistogramSearch.counts_indexed n F r a arity owner (run n F r a arity owner).value 0
  have hi := SemiprimeSourceHistogramSearch.counts_indexed n F r a arity owner [] (n+F)
  simp only [List.map_nil] at hi
  rw [←hf,←hi] at h
  have hd : (0:ℚ)<((en.wordFirst::en.wordTail).length:ℚ)^4 := by
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    positivity
  exact_mod_cast (div_le_div_iff_of_pos_right hd).mp h

end RiemannGaussian.SemiprimeD1IncidenceSearch
