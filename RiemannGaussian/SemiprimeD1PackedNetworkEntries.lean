/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedNetworkSemantics
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableOriginal
import RiemannGaussian.SemiprimeD1RootRightAssignments
/-! # Exact natural marked entry lookup across proof-only arity casts
All statements concern actual literal coefficient words and ordered gathers.
They acquire no table, coefficient, scalar or running-time advice.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedNetworkEntries
open SemiprimeD1TensorTables SemiprimeD1PackedNetworkSemantics
open SemiprimeD1LeafCounter SemiprimePublicAcquiredExecution
/-- A proof-only table-arity cast leaves every actual list lookup unchanged. -/
theorem lookup_cast {m n : ℕ} (h : m=n) (table : Table m) (bits : List Bool) :
    (lookup (cast (congrArg Table h) table) bits).words=(lookup table bits).words := by
  cases h
  rfl
/-- The marked reference table's actual list lookup has its full natural coefficient. -/
theorem reference_lookup (N : ℕ) (hN : 0<N) (v : PublicVertex N) (bits : List Bool)
    (hb : bits.length=SemiprimeMacroGraph.subdividedArity v) :
    wordNat (lookup (SemiprimeD1StackMarkedPublicInputTableOriginal.reference N hN v) bits).words=
      SemiprimeD1PackedMomentPrecision.coefficient N hN v
        (fun j => (bits.toArray[j.val]?).getD false) := by
  unfold SemiprimeD1StackMarkedPublicInputTableOriginal.reference
  rw [build_value _ _ bits hb]
  change SemiprimeBitArithmetic.bitValue
    (SemiprimeD1StackMarkedPublicInputTableOriginal.wordOf _)=_
  exact SemiprimeSourceHistogramPortKeys.encodeKey_value _
/-- Ordered complete finite bit words retain every coordinate, including empty scopes. -/
theorem bits_ofFn {n : ℕ} (bits : Fin n→Bool) :
    (fun j : Fin n => ((List.ofFn bits).toArray[j.val]?).getD false)=bits := by
  funext j
  simp only [List.getElem?_toArray,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]
/-- Literal natural entry is its actual ordered port-list lookup. -/
theorem entry_lookup {M : ℕ} (vertex : Vertex) (a : Fin M→Bool) :
    entry vertex a=wordNat (lookup vertex.table
      (vertex.ports.map (fun p => ((List.ofFn a)[p]?).getD false))).words := by
  unfold entry
  rw [SemiprimeD1RootLocalAssignments.valueAt_global_lookup]
end RiemannGaussian.SemiprimeD1PackedNetworkEntries
