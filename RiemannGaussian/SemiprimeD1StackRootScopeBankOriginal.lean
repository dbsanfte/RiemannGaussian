/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScopeBankExecution
import RiemannGaussian.SemiprimeD1RootStateResources

/-! # Original root occurrence domain of the physically acquired bank
The IDs are ascending canonical occurrence ordinals, not wire endpoint payloads.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackRootScopeBankOriginal
open SemiprimeD1StackRootScopeBankExecution
open SemiprimeBitArithmetic (bitValue)

/-- The one-push cache counts original Boolean wires. -/
theorem wire_count (bits : List Bool) :
    wireValue bits=SemiprimePublicAcquiredExecution.wireCount (bitValue bits) := by
  simp only [wireValue,records,List.length_map,SemiprimePublicAcquiredExecution.wireCount]

/-- The two-push cache is EXACTLY the canonical D1 root scope, for every prefix. -/
theorem occurrence_count (bits : List Bool) (hN : 0<bitValue bits)
    (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) :
    occurrenceCount bits=SemiprimeD1TensorNetwork.edgeCount
      (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed) := by
  rw [SemiprimeD1RootStateResources.root_edges]
  exact congrArg (2*·) (wire_count bits)

/-- Ordered bank values cover every occurrence, including unused variables. -/
theorem bank_values (bits : List Bool) :
    (SemiprimeD1OrdinalBankSpec.words (occurrenceCount bits)).map bitValue=
      List.range (occurrenceCount bits) := SemiprimeD1OrdinalBankSpec.values _

/-- Literal padded-key equality is licensed by the acquired common width. -/
theorem id_eq_iff (bits : List Bool) (i j : ℕ)
    (hi : i<occurrenceCount bits) (hj : j<occurrenceCount bits) :
    SemiprimeD1OrdinalBankSpec.idAt (occurrenceCount bits) i=
      SemiprimeD1OrdinalBankSpec.idAt (occurrenceCount bits) j ↔ i=j :=
  SemiprimeD1OrdinalBankSpec.id_eq_iff _ _ _ hi hj

/-- Actual whole-bank padding is quadratic, with no supplied scope-byte cap. -/
theorem bank_bytes (bits : List Bool) :
    (SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1OrdinalBankSpec.words
      (occurrenceCount bits))).length=2*occurrenceCount bits*occurrenceCount bits+2*occurrenceCount bits+1 :=
  SemiprimeD1OrdinalBankSpec.bank_bytes _

/-- The original public scale bounds this acquired occurrence bank's padding. -/
theorem occurrence_le_scale (bits : List Bool) (hN : 0<bitValue bits) :
    occurrenceCount bits≤SemiprimeD1PublicPackingReady.scale
      (SemiprimeMacroParameters.bitLength (bitValue bits)) := by
  rw [occurrence_count bits hN []]
  exact SemiprimeD1RootStateResources.root_edges_le_scale _ hN []

/-- Honest original-family byte bound for any physically selected sublist of
this ACTUAL bank. Acquiring a recursive filter and its port correspondence
remains a distinct caller task; no arbitrary padding bound is assumed here. -/
theorem sublist_bytes_le_scale (bits : List Bool) (hN : 0<bitValue bits)
    (xs : List (List Bool)) (hx : xs.Sublist (SemiprimeD1OrdinalBankSpec.words (occurrenceCount bits))) :
    (SemiprimeD1TensorTapeCodec.vectorBits xs).length≤
      let s:=SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength (bitValue bits))
      2*s*s+2*s+1 := by
  have h:=SemiprimeD1OrdinalBankSpec.sublist_bytes (occurrenceCount bits) xs hx
  have hs:=occurrence_le_scale bits hN
  dsimp only
  exact h.trans (by gcongr)

/-- Actual original public digit/axis/constant caches survive acquisition literally. -/
theorem retained_root (bits : List Bool) (k : SemiprimeD1BinaryPublicAcquisition.Stack) :
    result bits (SemiprimeD1StackRootScopeBank.edgeStack
      (SemiprimeD1StackEdgeCatalogue.catStack (SemiprimeD1StackVertexCatalogue.rootStack k)))=
      SemiprimeD1BinaryPublicAcquisitionComponents.result bits k := by
  rw [result_source]
  exact SemiprimeD1StackEdgeCatalogueBounds.retained_root bits k

end RiemannGaussian.SemiprimeD1StackRootScopeBankOriginal
