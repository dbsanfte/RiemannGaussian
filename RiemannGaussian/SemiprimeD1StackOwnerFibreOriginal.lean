/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreBounds
import RiemannGaussian.SemiprimeD1StackOwnerTableOriginal
/-! # Exact original factor-major scope-ID fibres from computed owner routing
These lists specify the already-routed tape consumed by the physical filter.
The original-N router must acquire that tape; no routed list is a runtime
control operand and no scope/fibre getter is used by the physical source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreOriginal
open SemiprimeD1StackOwnerFibre SemiprimeD1StackOwnerFibreExecution
open SemiprimePublicAcquiredExecution SemiprimeD1RootTensorTables
open SemiprimeBitArithmetic (bitValue)
namespace Owner
export SemiprimeD1StackOwnerLookupOriginal.Public (occurrences encode encode_value)
end Owner
/-- Original public incidence order; factors then their ascending local slots. -/
def enumeration (N:ℕ) := SemiprimeFiniteEnumerations.indexedIncidences (factorCount N) (indexedArity N)
/-- Exact original occurrence count, keeping E-wire and M-occurrence IDs distinct. -/
theorem enumeration_length (N:ℕ) : (enumeration N).values.length=Owner.occurrences N :=
  SemiprimeFiniteEnumerations.indexedIncidences_length _ _
/-- Mathematical physical scope ID of one original occurrence, using the acquired M bank. -/
def scopeWord (N:ℕ) (p:Port N) : List Bool :=
  SemiprimeD1OrdinalBankSpec.idAt (Owner.occurrences N) ((enumeration N).equivFin.symm p).val
/-- Actual common-width scope ID, with an occurrence ordinal rather than an E-wire ordinal. -/
theorem scopeWord_value (N:ℕ) (p:Port N) : bitValue (scopeWord N p)=((enumeration N).equivFin.symm p).val := by
  apply SemiprimeD1OrdinalBankSpec.id_value
  rw [←enumeration_length]
  exact ((enumeration N).equivFin.symm p).isLt
theorem scopeWord_length (N:ℕ) (p:Port N) : (scopeWord N p).length=Owner.occurrences N := by
  apply SemiprimeD1OrdinalBankSpec.id_length
  rw [←enumeration_length]
  exact ((enumeration N).equivFin.symm p).isLt
/-- The prepared routed stream uses physically computed original owner IDs and
physically zipped original occurrence IDs; it has the original port order. -/
def routed (N:ℕ) (hN:0<N) (ports:List (Port N)) : List (List Bool×List Bool) :=
  ports.map (fun p=>(Owner.encode N (indexedCoordinate N hN p.1 p.2),scopeWord N p))
/-- Numeric physical comparison selects EXACT original owner membership. -/
theorem values_original (N:ℕ) (hN:0<N) (wire:Fin (wireCount N)) (ports:List (Port N)) :
    values (Owner.encode N wire) (routed N hN ports)=
      (ports.filter (fun p=>decide (indexedCoordinate N hN p.1 p.2=wire))).map (scopeWord N) := by
  induction ports with
  | nil=>rfl
  | cons p ports ih=>
    simp only [routed,List.map_cons] at ih ⊢
    by_cases h:indexedCoordinate N hN p.1 p.2=wire
    · simp [values,Owner.encode_value N hN,h,ih]
    · simp [values,Owner.encode_value N hN,Fin.val_inj,h,ih]
/-- Complete original physical stream specification, without an advised fibre. -/
def rows (N:ℕ) (hN:0<N) : List (List Bool×List Bool) := routed N hN (enumeration N).values
/-- Original owner-node fibre order agrees with the actual physical filter output. -/
theorem original_fibre (N:ℕ) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) (wire:Fin (wireCount N)) :
    values (Owner.encode N wire) (rows N hN)=
      (ownerPorts N (acquirePositive N hN fixed).records wire).map (scopeWord N) := by
  rw [acquirePositive_records,SemiprimeD1RootTensorTablesBounds.ownerPorts_records]
  exact values_original N hN wire (enumeration N).values
/-- No supplied count/degree premise: the exact original fibre length is derived. -/
theorem original_fibre_length (N:ℕ) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool)) (wire:Fin (wireCount N)) :
    (values (Owner.encode N wire) (rows N hN)).length=
      (ownerPorts N (acquirePositive N hN fixed).records wire).length := by
  rw [original_fibre N hN fixed wire,List.length_map]
/-- Whole physical filter returns the exact original factor-major scope-ID vector. -/
theorem original_output (N:ℕ) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool))
    (wire:Fin (wireCount N)) (tail:List Bool) :
    (done (Owner.encode N wire) (rows N hN) tail).data (.inr .output)=
      SemiprimeD1TensorTapeCodec.vectorBits
        ((ownerPorts N (acquirePositive N hN fixed).records wire).map (scopeWord N)) := by
  change SemiprimeD1TensorTapeCodec.vectorBits (values _ _)=_
  rw [original_fibre N hN fixed wire]
/-- The existing real owner table consumes this exact filtered fibre and the
concrete original wire encoding, covering every original prefix and owner. -/
theorem original_owner_table (N:ℕ) (hN:0<N) (fixed:List (Fin (wireCount N)×Bool))
    (wire:Fin (wireCount N)) (tail:List Bool) :
    ∃hs:(values (Owner.encode N wire) (rows N hN)).length≤2,
      (SemiprimeD1StackOwnerTableExecution.done (Owner.encode N wire)
        (fixed.map (fun x=>(Owner.encode N x.1,x.2))) tail
        (values (Owner.encode N wire) (rows N hN)) hs).data SemiprimeD1StackOwnerTable.output=
        SemiprimeD1TensorTapeCodec.tape (ownerNode N fixed (acquirePositive N hN fixed).records wire).table :=
  SemiprimeD1StackOwnerTableOriginal.original_owner N hN fixed wire (Owner.encode N)
    (Owner.encode_value N hN) tail _ (original_fibre_length N hN fixed wire)
end RiemannGaussian.SemiprimeD1StackOwnerFibreOriginal
