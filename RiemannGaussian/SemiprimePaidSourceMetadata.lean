/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidFiniteEnumerationLists
import RiemannGaussian.SemiprimeMaterializedSourceWords
import RiemannGaussian.SemiprimeSourceConstraintAcquisition

/-! # Cached original source heads and factor assignments
The original search is performed once, including variables with no incidences.
The clock is scalar/list/cell control, with flat array reads, not a bit clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimePaidSourceMetadata
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation MulticolorTypes SqrtLog
open SemiprimeMaterializedSourceUniversal
variable {r Q : ℕ} [NeZero r]

/-- Materialized variable-major and factor-major coordinate arrays. -/
structure Metadata (r : ℕ) where
  /-- One cached word for each original variable, including isolated variables. -/
  heads : Array (Array (Fin r))
  /-- One cached word for each original factor. -/
  assignments : Array (Array (Fin r))

/-- Two flat array reads; absent coordinates have a total default. -/
def read (table : Array (Array (Fin r))) (i t : ℕ) : Run (Fin r) :=
  ⟨(((table[i]?).getD #[])[t]?).getD 0,4⟩

/-- Cached head coordinate. -/
def head {n : ℕ} (data : Metadata r) (t : Fin Q) (v : Fin n) : Fin r :=
  (read data.heads v.val t.val).value

/-- Cached assigned-factor coordinate. -/
def assigned {F : ℕ} (data : Metadata r) (t : Fin Q) (e : Fin F) : Fin r :=
  (read data.assignments e.val t.val).value

/-- Copy every coordinate into a literal array, charging the conversion. -/
def copy (coordinates : List (Fin Q)) (word : Word r Q) : Run (Array (Fin r)) :=
  let out := collect (fun t => (⟨word t,2⟩ : Run (Fin r))) coordinates
  ⟨out.value.toArray,out.work+out.value.length+2⟩

/-- A single chosen word is found by paid original-index and reverse-prefix scans. -/
def wordAt {A : Type*} [DecidableEq A] (first : Word r Q)
    (indices : List A) (labels : List (Word r Q)) (a : A) : Run (Word r Q) :=
  let index := SemiprimeMaterializedSourceWords.indexRun a indices
  let word := SemiprimeMaterializedWordSearch.readRun first labels index.value
  ⟨word.value,index.work+word.work+1⟩

omit [NeZero r] in
/-- The scan agrees with the source's original decoder. -/
theorem wordAt_value {A : Type*} [DecidableEq A] (first : Word r Q)
    (indices : List A) (labels : List (Word r Q)) (a : A) :
    (wordAt first indices labels a).value=decode first labels (indexCode indices a) := by
  simp only [wordAt,SemiprimeMaterializedSourceWords.indexRun_value,
    SemiprimeMaterializedWordSearch.readRun_value]

omit [NeZero r] in
/-- A real lookup has polynomial list-control cost. -/
theorem wordAt_work {A : Type*} [DecidableEq A] (first : Word r Q)
    (indices : List A) (labels : List (Word r Q)) (a : A) :
    (wordAt first indices labels a).work ≤ 2*indices.length+3*(labels.length+1)^2+3 := by
  have hi := SemiprimeMaterializedSourceWords.indexRun_work a indices
  have hw := SemiprimeMaterializedWordSearch.readRun_work first labels
    (SemiprimeMaterializedSourceWords.indexRun a indices).value
  simp only [wordAt]
  omega

/-- Build a whole side table using already acquired finite index and coordinate lists. -/
def table {A : Type*} [DecidableEq A] {s : ℕ} (positions : List (Fin s))
    (coordinates : List (Fin Q)) (inject : Fin s → A) (first : Word r Q)
    (indices : List A) (labels : List (Word r Q)) : Run (Array (Array (Fin r))) :=
  let out := collect (fun i =>
    let word := wordAt first indices labels (inject i)
    let cells := copy coordinates word.value
    (⟨cells.value,word.work+cells.work+1⟩ : Run (Array (Fin r)))) positions
  ⟨out.value.toArray,out.work+out.value.length+2⟩

/-- Materialized table lookup is the literal decoded original word coordinate. -/
theorem table_read {A : Type*} [DecidableEq A] {s : ℕ}
    (inject : Fin s → A) (first : Word r Q) (indices : List A)
    (labels : List (Word r Q)) (i : Fin s) (t : Fin Q) :
    (read (table (List.finRange s) (List.finRange Q) inject first indices labels).value
      i.val t.val).value=decode first labels (indexCode indices (inject i)) t := by
  simp [read,table,collect_value,copy,wordAt_value]

variable {I : Type} [Fintype I] [DecidableEq I] {n F : ℕ}

/-- Acquire the original chosen word list once, not an incidence-only projection. -/
def labels (owner : I → Fin n) (factor : I → Fin F)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) (Fin F) r Q) (eps : ℚ) :
    Run (List (Word r Q)) :=
  let M := en.incidences.values.length
  let D := en.types.values.length
  let x := eps*(M : ℚ)/(D : ℚ)
  let y := (n : ℚ)/(2*(r : ℚ))
  let offset := SemiprimeMaterializedSourceWords.offsetRun M n r Q x y
  let words := SemiprimeMaterializedSourceWords.computedList owner factor en.wordFirst en.wordTail
    en.terms.values en.indices.values x y offset.value
  ⟨words.value,offset.work+words.work+M+D+10⟩

omit [NeZero r] [DecidableEq I] in
/-- The acquired list decodes to precisely the existing deterministic source search. -/
theorem labels_value (owner : I → Fin n) (factor : I → Fin F)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) (Fin F) r Q) (eps : ℚ)
    (a : Fin n ⊕ Fin F) :
    decode en.wordFirst (labels owner factor en eps).value (indexCode en.indices.values a)=
      SemiprimeFiniteEnumerations.searchWords owner factor en eps a := by
  classical
  unfold labels
  dsimp only
  rw [en.incidences.length_eq_card,en.types.length_eq_card]
  have hoff := SemiprimeMaterializedSourceWords.offsetRun_value (I:=I) (V:=Fin n) (r:=r) (Q:=Q)
    (eps*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ)) ((n : ℚ)/(2*(r : ℚ)))
  simp only [Fintype.card_fin] at hoff
  rw [hoff,SemiprimeMaterializedSourceWords.computedList_value]
  simp only [SemiprimeFiniteEnumerations.searchWords,Packing.computedWords,Fintype.card_fin]

/-- Actual input-only metadata acquisition, with one shared original search. -/
def acquire (owner : I → Fin n) (factor : I → Fin F)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) (Fin F) r Q) (eps : ℚ) :
    Run (Metadata r) :=
  let words := labels owner factor en eps
  let vs := SemiprimePaidFiniteEnumerationLists.fin n
  let es := SemiprimePaidFiniteEnumerationLists.fin F
  let ts := SemiprimePaidFiniteEnumerationLists.fin Q
  let hv := table vs.value ts.value Sum.inl en.wordFirst en.indices.values words.value
  let he := table es.value ts.value Sum.inr en.wordFirst en.indices.values words.value
  ⟨⟨hv.value,he.value⟩,words.work+vs.work+es.work+ts.work+hv.work+he.work+1⟩

omit [DecidableEq I] in
/-- Exact cached heads, including every unowned variable. -/
theorem head_acquire (owner : I → Fin n) (factor : I → Fin F)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) (Fin F) r Q) (eps : ℚ)
    (t : Fin Q) (v : Fin n) :
    head (acquire owner factor en eps).value t v=
      SemiprimeSourceConstraintAcquisition.head owner factor en eps t v := by
  simp only [head,acquire,SemiprimePaidFiniteEnumerationLists.fin_value,table_read]
  exact congrFun (labels_value owner factor en eps (.inl v)) t

omit [DecidableEq I] in
/-- Exact cached factor labels, not inferred from incident vertices. -/
theorem assigned_acquire (owner : I → Fin n) (factor : I → Fin F)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) (Fin F) r Q) (eps : ℚ)
    (t : Fin Q) (e : Fin F) :
    assigned (acquire owner factor en eps).value t e=
      SemiprimeFiniteEnumerations.searchWords owner factor en eps (.inr e) t := by
  simp only [assigned,acquire,SemiprimePaidFiniteEnumerationLists.fin_value,table_read]
  exact congrFun (labels_value owner factor en eps (.inr e)) t

omit [NeZero r] in
/-- Complete finite coordinate-copy and array conversion ledger. -/
theorem copy_work (coordinates : List (Fin Q)) (word : Word r Q) :
    (copy coordinates word).work≤5*coordinates.length+3 := by
  have h := collect_work (fun t => (⟨word t,2⟩ : Run (Fin r))) coordinates 2 (by intro t _; rfl)
  simp only [copy,collect_value,List.length_map]
  omega

omit [NeZero r] in
/-- Every cached chosen word and every copied coordinate is charged. -/
theorem table_work {A : Type*} [DecidableEq A] {s : ℕ} (positions : List (Fin s))
    (coordinates : List (Fin Q)) (inject : Fin s → A) (first : Word r Q)
    (indices : List A) (labels : List (Word r Q)) :
    (table positions coordinates inject first indices labels).work≤
      positions.length*(2*indices.length+3*(labels.length+1)^2+5*coordinates.length+10)+3 := by
  have h := collect_work (fun i =>
    let word := wordAt first indices labels (inject i)
    let cells := copy coordinates word.value
    (⟨cells.value,word.work+cells.work+1⟩ : Run (Array (Fin r)))) positions
    (2*indices.length+3*(labels.length+1)^2+5*coordinates.length+7) (by
      intro i _
      have hw := wordAt_work first indices labels (inject i)
      have hc := copy_work coordinates (wordAt first indices labels (inject i)).value
      dsimp only
      omega)
  dsimp only at h
  unfold table
  dsimp only
  simp only [collect_value,List.length_map]
  nlinarith

omit [NeZero r] [DecidableEq I] [Fintype I] in
/-- The actual acquired chosen-word list retains the original index count. -/
theorem labels_length (owner : I → Fin n) (factor : I → Fin F)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) (Fin F) r Q) (eps : ℚ) :
    (labels owner factor en eps).value.length=en.indices.values.length :=
  SemiprimeMaterializedSourceWords.computedList_length owner factor en.wordFirst en.wordTail
    en.terms.values en.indices.values _ _ _

omit [NeZero r] [DecidableEq I] [Fintype I] in
/-- Original search and explicit dimension/scale acquisition retain their reports. -/
theorem labels_work (owner : I → Fin n) (factor : I → Fin F)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) (Fin F) r Q) (eps : ℚ) :
    (labels owner factor en eps).work≤
      SemiprimeMaterializedSourceWords.producerBudget en.wordTail.length en.terms.values.length
        en.indices.values.length Q+en.incidences.values.length+en.types.values.length+9 := by
  have h := SemiprimeMaterializedSourceWords.computedList_work owner factor en.wordFirst en.wordTail
    en.terms.values en.indices.values
    (eps*(en.incidences.values.length : ℚ)/(en.types.values.length : ℚ)) ((n : ℚ)/(2*(r : ℚ)))
    (SemiprimeMaterializedSourceWords.offsetRun en.incidences.values.length n r Q
      (eps*(en.incidences.values.length : ℚ)/(en.types.values.length : ℚ)) ((n : ℚ)/(2*(r : ℚ)))).value
  simp only [List.length_cons] at h
  unfold labels SemiprimeMaterializedSourceWords.producerBudget
  dsimp only
  rw [SemiprimeMaterializedSourceWords.offsetRun_work]
  omega

/-- Closed scalar/list/cell envelope for all original head and assigned labels. -/
def budget (n F M D A T N Q : ℕ) : ℕ :=
  SemiprimeMaterializedSourceWords.producerBudget A T N Q+M+D+9+
  3*(n+1)^2+3*(F+1)^2+3*(Q+1)^2+
  (n+F)*(2*N+3*(N+1)^2+5*Q+10)+7

omit [NeZero r] [DecidableEq I] [Fintype I] in
/-- No chosen-head or factor-label cost/answer premise is supplied. -/
theorem acquire_work (owner : I → Fin n) (factor : I → Fin F)
    (en : SemiprimeSourceLayout.Enumerations I (Fin n) (Fin F) r Q) (eps : ℚ) :
    (acquire owner factor en eps).work≤budget n F en.incidences.values.length en.types.values.length
      en.wordTail.length en.terms.values.length en.indices.values.length Q := by
  have hl := labels_work owner factor en eps
  have hv := SemiprimePaidFiniteEnumerationLists.fin_work n
  have he := SemiprimePaidFiniteEnumerationLists.fin_work F
  have ht := SemiprimePaidFiniteEnumerationLists.fin_work Q
  have hvt := table_work (SemiprimePaidFiniteEnumerationLists.fin n).value
    (SemiprimePaidFiniteEnumerationLists.fin Q).value Sum.inl en.wordFirst en.indices.values
    (labels owner factor en eps).value
  have het := table_work (SemiprimePaidFiniteEnumerationLists.fin F).value
    (SemiprimePaidFiniteEnumerationLists.fin Q).value Sum.inr en.wordFirst en.indices.values
    (labels owner factor en eps).value
  rw [SemiprimePaidFiniteEnumerationLists.fin_value,SemiprimePaidFiniteEnumerationLists.fin_value,
    List.length_finRange,List.length_finRange,labels_length] at hvt het
  unfold acquire budget
  dsimp only
  simp only [SemiprimePaidFiniteEnumerationLists.fin_value]
  nlinarith

end RiemannGaussian.SemiprimePaidSourceMetadata
