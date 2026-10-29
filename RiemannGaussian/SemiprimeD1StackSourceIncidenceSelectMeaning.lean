/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectSpec
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentOriginal
import RiemannGaussian.SemiprimeSourceHistogramDictRefinement
import RiemannGaussian.SemiprimeSourceHistogramAcquiredSums
/-! # Original incidence-only query meaning for the prepared selector
These mathematical identities bind actual compact owner/factor keys and actual
prefix IDs to the OLDoriginal D1 query, retaining every ordered incidence pair.
No histogram, graph function, score function or environment getter is an operand
of the literal controller. The physical47source will supply its own trace and
binary-result identity, once its source group is FINAL.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectMeaning
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceIncidenceCountFormula (classifiedCount)
namespace Keys
export SemiprimeSourceHistogramHeadRefinement (numberKey numberKey_value numberKey_compact)
end Keys
/-- Mathematical original prefix ID label; code reads its actual marked dictionary payload instead. -/
def idLabel (ids:List (List Bool)) (i:Nat) :Nat :=bitValue (SemiprimeSourceHistogramPrefix.expected ids i)
/-- Every actual original prefix/default payload remains an acquired candidate ID. -/
theorem expected_mem (r a:Nat) [NeZero r] (ids:List (List Bool))
    (hf:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) (i:Nat) :
    SemiprimeSourceHistogramPrefix.expected ids i∈(SemiprimeSourceCompactWordBank.acquire r a).ids :=by
  have h:=SemiprimeSourceHistogramDictRefinement.stored_mem r a ids hf (Keys.numberKey i)
  rw [SemiprimeSourceHistogramPrefix.stored_eq ids _ (Keys.numberKey_compact i),Keys.numberKey_value] at h
  exact h
/-- Every expected original/default ID is canonical, including zero[]. -/
theorem expected_compact (ids:List (List Bool)) (i:Nat) :
    SemiprimeSourceCompactBits.Compact (SemiprimeSourceHistogramPrefix.expected ids i) :=
  SemiprimeSourceCompactBits.trim_compact _
/-- Actual compact payload decode equals the exact original finite environment label. -/
theorem expected_decode (r a:Nat) [NeZero r] (ids:List (List Bool)) (i:Nat) :
    SemiprimeSourceWordBankSemantics.decode r a (SemiprimeSourceHistogramPrefix.expected ids i)=
      SemiprimeSourceHistogramDictRefinement.labels r a ids i :=by
  have h:=SemiprimeSourceHistogramDictRefinement.stored_decode r a ids (Keys.numberKey i) (Keys.numberKey_compact i)
  rw [SemiprimeSourceHistogramPrefix.stored_eq ids _ (Keys.numberKey_compact i),Keys.numberKey_value] at h
  exact h
/-- Numeric actual candidate ID equality is EXACToriginal whole-word equality for every valid selected prefix. -/
theorem label_eq_iff (r a:Nat) [NeZero r] (ids:List (List Bool))
    (hf:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) (i j:Nat) :
    idLabel ids i=idLabel ids j ↔
      SemiprimeSourceHistogramDictRefinement.labels r a ids i=SemiprimeSourceHistogramDictRefinement.labels r a ids j :=by
  constructor
  · intro h
    have he:=SemiprimeSourceCompactWordIds.compact_value_injective _ _ (expected_compact ids i) (expected_compact ids j) h
    exact (expected_decode r a ids i).symm.trans ((congrArg (SemiprimeSourceWordBankSemantics.decode r a) he).trans (expected_decode r a ids j))
  · intro h
    have he:=SemiprimeSourceCompactWordBank.decode_injective r a (expected_mem r a ids hf i) (expected_mem r a ids hf j)
      ((expected_decode r a ids i).trans (h.trans (expected_decode r a ids j).symm))
    exact congrArg bitValue he
/-- The two original labels can be replaced by their actual compact numeric IDs, without changing a single lane. -/
theorem classified_original (r a L:Nat) [NeZero r] (ids:List (List Bool))
    (hf:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire r a).ids)
    (remaining:List Nat) (u v w z:Nat) :
    classifiedCount L remaining (idLabel ids) u v w z=
      classifiedCount L remaining (SemiprimeSourceHistogramDictRefinement.labels r a ids) u v w z :=by
  unfold classifiedCount SemiprimeSourceIncidenceCountFormula.pairOK
  simp only [label_eq_iff r a ids hf u w,label_eq_iff r a ids hf v z]
/-- Exact ordered physical key list in the old acquired original incidence order. -/
def originalKeys (n F a:Nat) (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :List (List Bool×List Bool) :=
  (SemiprimeSourceHistogramMetadata.acquire n F a arity).incidences.map
    (fun i=>(Keys.numberKey (owner i).val,Keys.numberKey (n+i.1.val)))
/-- Mathematical scalar sum represented by the actual ordered-pair source; no such sum opcode occurs at runtime. -/
def codeScore (L:Nat) (remaining:List Nat) (ids:List (List Bool)) (rows:List (List Bool×List Bool)) :Nat :=
  (rows.map (fun left=>(rows.map (fun right=>classifiedCount L remaining (idLabel ids)
    (bitValue left.1) (bitValue left.2) (bitValue right.1) (bitValue right.2))).sum)).sum
/-- Actual compact numeric keys encode the exact OLDordered incidence count, including every duplicate pair. -/
theorem counts_original (n F r a:Nat) [NeZero r] (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (ids:List (List Bool)) (s:Nat)
    (hf:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) :
    (SemiprimeSourceHistogramQueryCorrectness.originalCounts n F r a arity owner ids s).incidence=
      codeScore (r^a) (List.range' ids.length s) ids (originalKeys n F a arity owner) :=by
  unfold SemiprimeSourceHistogramQueryCorrectness.originalCounts
  dsimp only
  rw [SemiprimeSourceHistogramAcquiredSums.original_terms,
    ←(SemiprimeSourceHistogramMetadata.original_fields n F a arity).2,
    SemiprimeSourceHistogramOriginalSums.compiled_incidence_sum]
  unfold codeScore originalKeys SemiprimeSourceHistogramGrouping.pairs
  simp only [List.map_map,Function.comp_def,Keys.numberKey_value,
    SemiprimeSourceHistogramPortKeys.indexCode_inl,SemiprimeSourceHistogramPortKeys.indexCode_inr]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  have hi: (owner i).val < n:=(owner i).isLt
  have hj: (owner j).val < n:=(owner j).isLt
  have hp:=SemiprimeSourceIncidenceCountFormula.paddedLocal_formula r a (NeZero.pos r)
    (owner i).val (n+i.1.val) (owner j).val (n+j.1.val) (List.range' ids.length s)
    (SemiprimeSourceHistogramHeadOriginal.originalEnv r a ids) (List.nodup_range')
    (by omega) (by omega) (by omega) (by omega)
  simp only [SemiprimeSourceHeadCountFormula.alphabet] at hp
  rw [hp]
  change classifiedCount (r^a) (List.range' ids.length s)
      (SemiprimeMaterializedScoreEnvironment.denote
        (SemiprimeMaterializedScoreEnvironment.baseEnvironment (SemiprimeSourceWordBankSemantics.decode r a [])
          (ids.map (SemiprimeSourceWordBankSemantics.decode r a)))) _ _ _ _=_
  rw [SemiprimeSourceHistogramDictRefinement.labels_original]
  exact (classified_original r a (r^a) ids hf (List.range' ids.length s) _ _ _ _).symm
/-- Exact incidence-only ORIGINALquery scalar; no head query or generic weight is introduced. -/
theorem query_value_original (n F r a:Nat) [NeZero r] (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (ids:List (List Bool)) (s:Nat)
    (hf:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) :
    (SemiprimeD1IncidenceSearch.query (SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner) ids s).word.value=
      (codeScore (r^a) (List.range' ids.length s) ids (originalKeys n F a arity owner):Rat) :=by
  rw [SemiprimeD1IncidenceSearch.query_value n F r a arity owner ids s hf,
    counts_original n F r a arity owner ids s hf]
/-- Exact mathematical next winner of the physical forward catalogue scan. -/
def stepChoice (L:Nat) (rows:List (List Bool×List Bool)) (s:Nat)
    (ids:List (List Bool)) (first:List Bool) (rest:List (List Bool)) :List Bool :=
  SemiprimeD1StackSourceIncidenceSelectSpec.tailChoice
    (fun id=>codeScore L (List.range' (ids.length+1) s) (id::ids) rows) first rest
/-- The concrete numeric scan returns the exact original query choice, including every equality. -/
theorem stepChoice_original (n F r a:Nat) [NeZero r] (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (ids:List (List Bool)) (s:Nat)
    (first:List Bool) (rest:List (List Bool))
    (hf:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire r a).ids)
    (hm:∀id∈first::rest,id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) :
    stepChoice (r^a) (originalKeys n F a arity owner) s ids first rest=
      (SemiprimeSourceChoiceBits.choose
        (fun id=>SemiprimeD1IncidenceSearch.query
          (SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner) (id::ids) s) first rest).value :=by
  apply SemiprimeD1StackSourceIncidenceSelectSpec.tailChoice_reports
  · intro id _
    exact SemiprimeD1IncidenceSearch.query_valid _ _ _
  · intro id hid
    simpa only [List.length_cons] using query_value_original n F r a arity owner (id::ids) s
      (SemiprimeSourceWordIdControl.inMenu_cons _ ids id (hm id hid) hf)
/-- Exact selected-ID specification controlled by the physically consumed marker list. -/
def select (L:Nat) (rows:List (List Bool×List Bool)) (first:List Bool) (rest:List (List Bool)) :
    List Bool→List (List Bool)→List (List Bool)
  | [],ids=>ids
  | _::tokens,ids=>
    let id:=stepChoice L rows tokens.length ids first rest
    select L rows first rest tokens (id::ids)
/-- The physical scan specification preserves exact original assignment at every selected prefix. -/
theorem select_original (n F r a:Nat) [NeZero r] (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) (first:List Bool) (rest:List (List Bool))
    (tokens:List Bool) (ids:List (List Bool))
    (hf:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire r a).ids)
    (hm:∀id∈first::rest,id∈(SemiprimeSourceCompactWordBank.acquire r a).ids) :
    select (r^a) (originalKeys n F a arity owner) first rest tokens ids=
      (SemiprimeSourceChoiceBits.assign first rest
        (fun todo fixed=>SemiprimeD1IncidenceSearch.query
          (SemiprimeSourceHistogramSetup.acquire n F r a 0 arity owner) fixed todo.length) tokens ids).value :=by
  induction tokens generalizing ids with
  | nil=>simp only [select,SemiprimeSourceChoiceBits.assign,SemiprimeSourceChoiceBits.copyIDs_value]
  | cons token tokens ih=>
    have hw:=stepChoice_original n F r a arity owner ids tokens.length first rest hf hm
    have hmem:=SemiprimeD1StackSourceIncidenceSelectSpec.tailChoice_mem
      (fun id=>codeScore (r^a) (List.range' (ids.length+1) tokens.length) (id::ids)
        (originalKeys n F a arity owner)) first rest
    change stepChoice (r^a) (originalKeys n F a arity owner) tokens.length ids first rest∈first::rest at hmem
    have hnew:=SemiprimeSourceWordIdControl.inMenu_cons _ ids _ (hm _ hmem) hf
    rw [select,ih _ hnew,SemiprimeSourceChoiceBits.assign,SemiprimeSourceChoiceBits.copyIDs_value,hw]
/-- Marker values carry no hidden iteration count; only the paid physical list shape is used. -/
theorem select_replicate (L:Nat) (rows:List (List Bool×List Bool)) (first:List Bool)
    (rest:List (List Bool)) (n:Nat) (left right:Bool) (ids:List (List Bool)) :
    select L rows first rest (List.replicate n left) ids=
      select L rows first rest (List.replicate n right) ids :=by
  induction n generalizing ids with
  | zero=>rfl
  | succ n ih=>simp only [List.replicate_succ,select,List.length_replicate];exact ih _
/-- The complete prepared scalar/choice specification is EXACT the original incidence-only run. -/
theorem select_run_original (n F r a:Nat) [NeZero r] (arity:Fin F→Nat)
    (owner:((e:Fin F)×Fin (arity e))→Fin n) :
    select (r^a) (originalKeys n F a arity owner) []
      (SemiprimeSourceCompactWordBank.acquire r a).ids.tail (List.replicate (n+F) true) []=
        (SemiprimeD1IncidenceSearch.run n F r a arity owner).value :=by
  rw [select_replicate (r^a) (originalKeys n F a arity owner) [] _ (n+F) true false,
    select_original n F r a arity owner [] _ _ [] (by simp) (SemiprimeSourceHistogramSearch.candidates_valid r a)]
  simp only [SemiprimeD1IncidenceSearch.run,SemiprimeSourceChoiceBits.run,
    SemiprimeSourceChoiceBits.acquireTokens_value,SemiprimeSourceHistogramSetup.bank_actual,
    SemiprimeSourceHistogramSetup.metadata_actual]
  rw [(SemiprimeSourceHistogramMetadata.sizes n F a arity).2.2.2.2]
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectMeaning
