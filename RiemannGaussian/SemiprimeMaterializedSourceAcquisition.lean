/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourcePullback
import RiemannGaussian.SemiprimeMaterializedPacking

/-! # Actual paid label-to-original-source array acquisition
The execution path receives the original finite incidences, owner and an actual
paid label producer. Source coefficients and packing addresses are not inputs.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedSourceAcquisition
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking SqrtLog
open SemiprimeMaterializedSourceUniversal SemiprimeJetArray
variable {I : Type} [DecidableEq I] {n r Q : ℕ}

/-- Copy the already acquired nested finite row/column lists to immutable arrays. -/
def freeze (rows : List (List (Array ℚ))) : Array (Array (Array ℚ)) :=
  (rows.map List.toArray).toArray

/-- Literal metadata cells copied by the two finite array conversions. -/
def freezeCells (rows : List (List (Array ℚ))) : ℕ :=
  rows.length+(rows.map List.length).sum+1

/-- Entire actual label/packing/universal-array/original-pullback acquisition. -/
def acquire (R : ℕ) (is : List I) (owner : I → Fin n)
    (keys : List (UniversalType r Q 1)) (producer : I → Run (UniversalType r Q 1)) :
    Run (Array (Array (Array ℚ))) :=
  let addresses := SemiprimeMaterializedPacking.acquire is keys producer
  let source := SemiprimeMaterializedSourcePullback.acquire R is owner addresses.value keys
  ⟨freeze source.value,addresses.work+source.work+freezeCells source.value⟩

/-- The immutable metadata grid has its exact acquired incidence/variable shape. -/
theorem freezeCells_acquire (R : ℕ) (is : List I) (owner : I → Fin n)
    (as : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (keys : List (UniversalType r Q 1)) :
    freezeCells (SemiprimeMaterializedSourcePullback.acquire R is owner as keys).value=
      is.length+is.length*n+1 := by
  rw [SemiprimeMaterializedSourcePullback.acquire_value]
  simp [freezeCells,List.map_map,Function.comp_def,List.sum_replicate]

/-- Cached incidence lookup reads exactly the corresponding newly acquired source row. -/
theorem read_freeze (en : FiniteEnumeration I) (f : I → Fin n → Array ℚ) (i : I) (v : Fin n) :
    SemiprimeSourceArrayAcquisition.read en
      (freeze (en.values.map (fun i => (List.finRange n).map (f i)))) i v=f i v := by
  simp [SemiprimeSourceArrayAcquisition.read,freeze,FiniteEnumeration.equivFin,
    en.complete i]

/-- All actual source coefficients agree with the existing native built source.
The only producer premise identifies its actual label output, not any source coefficient. -/
theorem acquire_coefficient [Fintype I] (P : PackingData I (UniversalType r Q 1))
    (R : ℕ) (owner : I → Fin n) (producer : I → Run (UniversalType r Q 1))
    (hp : ∀ i, (producer i).value=P.label i) (i : I) (v : Fin n) (k : ℕ) (hk : k<R+1) :
    coefficient (SemiprimeSourceArrayAcquisition.read P.vertices
      (acquire R P.vertices.values owner P.types.values producer).value i v) k=
      (LayoutPullback.row owner (LayoutBlocks.assembledRow P.completeBlocks
        (SemiprimeSourceLayout.universalLayout r Q R).row i) v).coeff k := by
  unfold acquire
  dsimp only
  rw [SemiprimeMaterializedPacking.acquire_value P producer hp]
  change coefficient (SemiprimeSourceArrayAcquisition.read P.vertices
    (freeze (SemiprimeMaterializedSourcePullback.acquire R P.vertices.values owner
      (SemiprimeMaterializedSourcePullback.packingAddresses P) P.types.values).value) i v) k=_
  rw [SemiprimeMaterializedSourcePullback.acquire_value,read_freeze]
  exact SemiprimeMaterializedSourcePullback.sourceRow_coefficient P owner R P.types.values
    P.types.complete i v k hk

/-- Packing acquisition's complete polynomial scalar/list ledger. -/
def packingBudget (M D Q B : ℕ) : ℕ :=
  M*(B+3)+1+D*(M*(7*Q+4)+3)+1+D*(M+3)+1+
    M*(D*(7*Q+4)+3*M+8)+1+M+4

/-- Whole source ledger, including actual paid labels, cache generation and all pullbacks. -/
def budget (R Q M n D A B : ℕ) : ℕ := packingBudget M D Q B+
  SemiprimeMaterializedSourcePullback.acquireBudget R Q M n D M A+M+M*n+1

theorem acquire_work (P : PackingData I (UniversalType r Q 1))
    (R : ℕ) (owner : I → Fin n) (producer : I → Run (UniversalType r Q 1))
    (hp : ∀ i, (producer i).value=P.label i) (B : ℕ) (hw : ∀ i, (producer i).work≤B) :
    (acquire R P.vertices.values owner P.types.values producer).work≤
      budget R Q P.vertices.values.length n P.types.values.length
        (SemiprimeMaterializedSourcePullback.centered r Q R) B := by
  have ha := SemiprimeMaterializedPacking.acquire_work P producer hp B hw
  have he := SemiprimeMaterializedPacking.acquire_value P producer hp
  have hs := SemiprimeMaterializedSourcePullback.acquire_work R P.vertices.values owner
    (SemiprimeMaterializedPacking.acquire P.vertices.values P.types.values producer).value P.types.values
  have hl : (SemiprimeMaterializedPacking.acquire P.vertices.values P.types.values producer).value.length=
      P.vertices.values.length := by rw [he,List.length_map]
  rw [hl] at hs
  unfold acquire
  dsimp only
  rw [freezeCells_acquire]
  unfold budget packingBudget
  omega

end RiemannGaussian.SemiprimeMaterializedSourceAcquisition
