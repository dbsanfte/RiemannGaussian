/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourceAcquisition

/-! # Retaining the acquired packing block count
This program retains the common bucket minimum alongside the actual acquired
addresses. Both outputs come from the same executed label and bucket scans.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimePaidPackingSnapshot
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking
open SemiprimeMaterializedSourceUniversal SemiprimeMaterializedPacking
variable {I : Type} [DecidableEq I] {r Q : ℕ}

/-- Finite packing metadata required to enumerate the original padded rows. -/
structure Snapshot (I : Type) (r Q : ℕ) where
  /-- The computed minimum bucket length. -/
  blocks : ℕ
  /-- Computed first-position addresses for every original incidence. -/
  addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q

/-- Acquire labels, buckets, minimum and addresses exactly once. -/
def acquire (vertices : List I) (keys : List (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) : Run (Snapshot I r Q) :=
  let ls := labels producer vertices
  let bs := mapPaid (fun u => bucket u ls.value) keys
  let blocks := minimum vertices.length bs.value
  let output := mapPaid (place keys bs.value blocks.value) ls.value
  ⟨⟨blocks.value,output.value⟩,ls.work+bs.work+blocks.work+output.work+vertices.length+5⟩

/-- The stored block count is the original complete-block count. -/
theorem acquire_blocks (P : PackingData I (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (hp : ∀ i, (producer i).value=P.label i) :
    (acquire P.vertices.values P.types.values producer).value.blocks=P.blockCount := by
  unfold acquire
  dsimp only
  simp only [mapPaid_value,labels_value,hp,bucket_value]
  exact minimum_value P P.types.values

/-- The stored addresses are the original packing addresses in their exact order. -/
theorem acquire_addresses (P : PackingData I (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (hp : ∀ i, (producer i).value=P.label i) :
    (acquire P.vertices.values P.types.values producer).value.addresses=
      SemiprimeMaterializedSourcePullback.packingAddresses P :=
  SemiprimeMaterializedPacking.acquire_value P producer hp

/-- Retaining one metadata field adds one charged cell to the existing packing run. -/
theorem acquire_work (P : PackingData I (UniversalType r Q 1))
    (producer : I → Run (UniversalType r Q 1)) (hp : ∀ i, (producer i).value=P.label i)
    (B : ℕ) (hw : ∀ i, (producer i).work≤B) :
    (acquire P.vertices.values P.types.values producer).work≤
      SemiprimeMaterializedSourceAcquisition.packingBudget
        P.vertices.values.length P.types.values.length Q B+1 := by
  have h := SemiprimeMaterializedPacking.acquire_work P producer hp B hw
  unfold acquire SemiprimeMaterializedSourceAcquisition.packingBudget
  dsimp only
  change _≤_ at h
  unfold SemiprimeMaterializedPacking.acquire at h
  dsimp only at h
  omega

end RiemannGaussian.SemiprimePaidPackingSnapshot
