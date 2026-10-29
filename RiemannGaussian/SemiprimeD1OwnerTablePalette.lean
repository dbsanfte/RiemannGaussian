/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootTensorTablesBounds
import RiemannGaussian.SemiprimeD1TensorTapeCodec
import RiemannGaussian.SemiprimeD1JetLiteralLift
/-! # All literal original owner tables of degree at most two
There are twelve fixed possibilities. Degree ZERO is retained: the unfixed
isolated owner has scalar TWO, not one or a Boolean all-equal shortcut.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1OwnerTablePalette
open SemiprimeD1TensorTables
/-- Actual old canonical precision-two sum of the two compatible Boolean values. -/
def scalar (low high : Bool) : List (List Bool) :=
  if low then (if high then [[false,true]] else [[true]]) else (if high then [[true]] else [[]])
/-- Each finite literal is the exact old physical precision-two scalar sum. -/
theorem scalar_add (low high : Bool) : scalar low high=[(SemiprimeD1JetScalarBits.add 2 [low] [high]).bits] := by
  cases low <;> cases high <;>
    simp [scalar,SemiprimeD1JetScalarBits.add,SemiprimeD1JetScalarBits.reduce,
      SemiprimeD1JetScalarBits.takeBits,SemiprimeBitArithmetic.addBits,
      SemiprimeBitArithmetic.fullAdder,SemiprimeSourceCompactBits.trim]
/-- The twelve original ordered trees, each fixed before any original input. -/
def table : (degree : Fin 3)→Bool→Bool→Table degree.val
  | ⟨0,_⟩,low,high=>.leaf (scalar low high)
  | ⟨1,_⟩,low,high=>.fork (.leaf (scalar low false)) (.leaf (scalar false high))
  | ⟨2,_⟩,low,high=>.fork
      (.fork (.leaf (scalar low false)) (.leaf (scalar false false)))
      (.fork (.leaf (scalar false false)) (.leaf (scalar false high)))
/-- Complete fixed original-codec bytes, including all tags and scalar fields. -/
def bytes (degree : Fin 3) (low high : Bool) : List Bool :=
  SemiprimeD1TensorTapeCodec.tape (table degree low high)
/-- All literal possibilities fit the fixed finite instruction-position alphabet. -/
theorem bytes_le (degree : Fin 3) (low high : Bool) : (bytes degree low high).length≤23 := by
  fin_cases degree <;> cases low <;> cases high <;> decide
/-- Exact original eager tree, with all prefix records retained in its semantics.
No old/native table-construction clock is used to bound a new program. -/
theorem table_original {n : ℕ} (degree : Fin 3) (fixed : List (Fin n×Bool)) (wire : Fin n) :
    table degree (SemiprimeD1RootOwnerTables.allowed fixed wire false)
      (SemiprimeD1RootOwnerTables.allowed fixed wire true)=
      (SemiprimeD1RootOwnerTables.acquire fixed wire degree.val).table := by
  rw [←SemiprimeD1RootOwnerTables.prefixRun_value wire false fixed,
    ←SemiprimeD1RootOwnerTables.prefixRun_value wire true fixed]
  fin_cases degree <;>
    simp [table,scalar_add,SemiprimeD1RootOwnerTables.acquire,build,
      SemiprimeD1RootOwnerTables.producer,SemiprimeD1RootOwnerTables.sameRun,
      SemiprimeD1RootOwnerTables.equalBit]
/-- Scalar TWO is physically present for the isolated unfixed original owner. -/
theorem isolated_unfixed : table 0 true true=.leaf [[false,true]] := rfl
/-- Entry scalar is the exact literal original owner entry before any product. -/
theorem entry_original {n : ℕ} (degree : Fin 3) (fixed : List (Fin n×Bool)) (wire : Fin n)
    (bits : List Bool) (hb : bits.length=degree.val) :
    (lookup (table degree (SemiprimeD1RootOwnerTables.allowed fixed wire false)
      (SemiprimeD1RootOwnerTables.allowed fixed wire true)) bits).words=
      (SemiprimeD1RootOwnerTables.producer fixed wire bits).words := by
  rw [table_original]
  exact SemiprimeD1RootOwnerTables.acquire_value fixed wire degree.val bits hb
/-- Every acquired table has the real original context/precision invariant. -/
theorem good {n : ℕ} (degree : Fin 3) (fixed : List (Fin n×Bool)) (wire : Fin n) :
    Good SemiprimeD1RootOwnerTables.rootContext
      (table degree (SemiprimeD1RootOwnerTables.allowed fixed wire false)
        (SemiprimeD1RootOwnerTables.allowed fixed wire true)) := by
  rw [table_original]
  exact SemiprimeD1RootOwnerTables.acquire_good fixed wire degree.val
/-- Each owner entry is individually lifted as an integer before any network
product, including the isolated scalar TWO; only this integral map is reduced. -/
theorem entry_reduce (degree : Fin 3) (low high : Bool) (input : Fin degree.val→Bool) (p : ℕ) :
    SemiprimeD1JetScalarMap.scalarMap (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1DyadicInteger.reduction p)
      (SemiprimeD1JetLiteralLift.literal [] (valueAt (table degree low high) input))=
      SemiprimeD1JetInterpretation.interpret ⟨[],p⟩ (valueAt (table degree low high) input) :=
  SemiprimeD1JetLiteralLift.literal_reduce [] p _
end RiemannGaussian.SemiprimeD1OwnerTablePalette
