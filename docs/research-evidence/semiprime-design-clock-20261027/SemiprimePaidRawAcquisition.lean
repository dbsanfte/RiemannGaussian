/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCachedRawConstraints
import RiemannGaussian.SemiprimePaidSourceMetadata
import RiemannGaussian.SemiprimeEncodedRowSelection

/-! # Actual cached source metadata and rows supply the raw design
The source search, integer family, row count and measurement bound are acquired
before the raw design is exposed. Runtime callbacks read only retained data.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimePaidRawAcquisition
open OAI.Algorithms.SubexponentialSAT
open SemiprimeMaterializedSourceUniversal SemiprimeRuntimeDesignAcquisition
variable {n F r Q : ℕ} [NeZero r]

/-- Original source data retained across every node/head selector call. -/
structure Snapshot (I : Type) (r Q : ℕ) where
  /-- Cached original head and factor labels, including unowned coordinates. -/
  metadata : SemiprimePaidSourceMetadata.Metadata r
  /-- Fully acquired original integer entries. -/
  family : SemiprimePaidConstraintAcquisition.Family I r Q
  /-- Cached literal padded row count. -/
  count : ℕ
  /-- Cached source measurement bound. -/
  bound : ℕ

/-- Acquire both original searches, their output caches and the actual bound power. -/
def acquire (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (en : SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q)
    (eps : ℚ) (R B : ℕ) : Run (Snapshot ((e : Fin F) × Fin (arity e)) r Q) :=
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let metadata := SemiprimePaidSourceMetadata.acquire owner Sigma.fst en eps
  let family := SemiprimePaidOriginalConstraints.acquire owner Sigma.fst en eps R
  let power := SemiprimeMaterializedSourceWords.powNatRun (8*Q) (2*R)
  let count := family.value.indices.length
  ⟨⟨metadata.value,family.value,count,B*2*power.value⟩,
    metadata.work+family.work+power.work+count+12⟩

/-- Raw data backed entirely by the acquired original caches. -/
def raw {I : Type} (snapshot : Snapshot I r Q) (t : Fin Q) : RawDesign n F :=
  SemiprimeCachedRawConstraints.make
    (SemiprimePaidSourceMetadata.head snapshot.metadata t)
    (SemiprimePaidSourceMetadata.assigned snapshot.metadata t) snapshot.count
    (fun g j v => (SemiprimeCachedRawConstraints.read
      (SemiprimePaidSourceMetadata.head snapshot.metadata t) snapshot.family t g j.val v).value)
    snapshot.bound

/-- Actual masked cached read, with its work supplied to physical row acquisition. -/
def reader {I : Type} (snapshot : Snapshot I r Q) (t : Fin Q)
    (g : Fin r) (j : Fin snapshot.count) (v : Fin n) : SemiprimeEncodedRowSelection.IntRun :=
  let out := SemiprimeCachedRawConstraints.read
    (SemiprimePaidSourceMetadata.head snapshot.metadata t) snapshot.family t g j.val v
  ⟨out.value,out.work⟩

/-- The report-bearing reader is the actual raw design's integer callback. -/
theorem reader_value {I : Type} (snapshot : Snapshot I r Q) (t : Fin Q)
    (g : Fin r) (j : Fin snapshot.count) (v : Fin n) :
    (reader snapshot t g j v).value=(raw (n:=n) (F:=F) snapshot t).rows g j v := rfl

/-- The entire cached raw record equals the former searched record, including
all outside-head zero columns and all original padded row indices. -/
theorem acquire_raw (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ) (t : Fin Q) :
    raw (n:=n) (F:=F) (acquire arity coordinate (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B).value t=
      SemiprimeAcquiredSourceCounter.raw (r:=r) arity coordinate eps R B t := by
  let en := SemiprimeFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  unfold acquire raw
  dsimp only
  rw [SemiprimeMaterializedSourceWords.powNatRun_value]
  change SemiprimeCachedRawConstraints.data
    (SemiprimePaidSourceMetadata.head (SemiprimePaidSourceMetadata.acquire owner Sigma.fst en eps).value t)
    (SemiprimePaidSourceMetadata.assigned (SemiprimePaidSourceMetadata.acquire owner Sigma.fst en eps).value t)
    (SemiprimePaidOriginalConstraints.acquire owner Sigma.fst en eps R).value
    (SemiprimeAcquiredSourceCounter.measurementBound B Q R) t=_
  exact SemiprimeCachedRawConstraints.data_eq arity coordinate eps R B t _ _
    (SemiprimePaidSourceMetadata.head_acquire owner Sigma.fst en eps t)
    (SemiprimePaidSourceMetadata.assigned_acquire owner Sigma.fst en eps t)

omit [NeZero r] in
/-- The acquired cardinality is the original padded row-list length. -/
theorem acquire_count (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (en : SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q)
    (eps : ℚ) (R B : ℕ) :
    (acquire arity coordinate en eps R B).value.count=
      (SemiprimeSourceConstraintAcquisition.rowIndices
        (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps).values.length :=
  SemiprimeCachedRawConstraints.acquired_count arity coordinate en eps R

/-- Complete original-coordinate entry bounds transfer to the actual cached record. -/
theorem acquire_bounded (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q) (t : Fin Q) :
    ∀ g j v, |(raw (n:=n) (F:=F) (acquire arity coordinate
      (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B).value t).rows g j v|≤
      ((raw (n:=n) (F:=F) (acquire arity coordinate
        (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B).value t).W g : ℤ) := by
  rw [acquire_raw]
  exact SemiprimeAcquiredSourceCounter.raw_bounded arity coordinate eps R B howner hQ hAQ t

/-- Closed polynomial setup envelope with all separately executed searches retained. -/
def budget (n F r Q R M D A T N : ℕ) : ℕ :=
  SemiprimePaidSourceMetadata.budget n F M D A T N Q+
  SemiprimePaidOriginalConstraints.polynomial M n A D T N Q R
    (Subexp.TailInterval.intervalStart r Q R) r+4*R+1+M*D+M+12

omit [NeZero r] in
/-- Full source-metadata, integer-family, count and bound-power acquisition ledger. -/
theorem acquire_work_native (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (en : SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q)
    (hr : 2≤r) (eps : ℚ) (R B : ℕ) :
    (acquire arity coordinate en eps R B).work≤
      budget n F r Q R en.incidences.values.length en.types.values.length en.wordTail.length
        en.terms.values.length en.indices.values.length := by
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  have hm := SemiprimePaidSourceMetadata.acquire_work owner Sigma.fst en eps
  have hf := SemiprimePaidOriginalConstraints.acquire_work_native owner Sigma.fst en hr eps R
  have hc := SemiprimeCachedRawConstraints.acquired_count_le arity coordinate en eps R
  dsimp only [owner] at hm hf
  unfold acquire budget
  dsimp only
  rw [SemiprimeMaterializedSourceWords.powNatRun_work]
  omega

/-- A selector reads only stored data; no source search is repeated per entry. -/
theorem acquire_reader_work (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (en : SemiprimeSourceLayout.Enumerations ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q)
    (eps : ℚ) (R B : ℕ) (t : Fin Q) (g : Fin r)
    (j : Fin (acquire arity coordinate en eps R B).value.count) (v : Fin n) :
    (reader (acquire arity coordinate en eps R B).value t g j v).work≤
      2*(Q+r+(acquire arity coordinate en eps R B).value.count+n)+14 := by
  have hp := acquire_count arity coordinate en eps R B
  have h := SemiprimeCachedRawConstraints.read_acquire_work arity coordinate en eps R
    (SemiprimePaidSourceMetadata.head (acquire arity coordinate en eps R B).value.metadata t)
    t g (j.cast hp) v
  calc
    _ ≤ 2*(Q+r+(SemiprimeSourceConstraintAcquisition.rowIndices
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst en eps).values.length+n)+14 := h
    _ = _ := by rw [hp]

end RiemannGaussian.SemiprimePaidRawAcquisition
