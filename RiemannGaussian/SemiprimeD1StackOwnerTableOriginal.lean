/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerTableBounds
/-! # Exact entire original owner family from physically acquired keys/scopes
The graph caller must acquire the scope-ID fibre and binary wire/prefix keys.
The actual table source THEN acquires degree and compatibility itself. Every
original prefix, isolated owner and conflicting repeated assignment is covered.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackOwnerTableOriginal
open SemiprimeD1StackOwnerTable SemiprimeD1StackOwnerTableExecution
open SemiprimeD1OwnerPrefixBits (scan_original)
open SemiprimeD1TensorTapeCodec (tape)

/-- Exact whole original eager owner table for EVERY finite wire and prefix.
Only binary original-key identity is assumed, never allowed/count/table advice. -/
theorem output_original {n : ℕ} (wire : Fin n) (fixed : List (Fin n×Bool))
    (encode : Fin n→List Bool) (he : ∀i,SemiprimeBitArithmetic.bitValue (encode i)=i.val)
    (tail : List Bool) (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) :
    (done (encode wire) (fixed.map (fun x=>(encode x.1,x.2))) tail scopeWords hs).data output=
      tape (SemiprimeD1RootOwnerTables.acquire fixed wire scopeWords.length).table := by
  change SemiprimeD1OwnerTablePalette.bytes (actualDegree scopeWords hs)
    (SemiprimeD1OwnerPrefixBits.scan _ _ true true).1
    (SemiprimeD1OwnerPrefixBits.scan _ _ true true).2=_
  rw [scan_original wire fixed encode he]
  exact congrArg tape (SemiprimeD1OwnerTablePalette.table_original (actualDegree scopeWords hs) fixed wire)
/-- Exact actual original-N ownerNode tape once routing has supplied its actual
ordered scope-ID fibre. The degree bound is DISCHARGED by the original graph,
including zero-degree owners; no runtime count or permutation is supplied. -/
theorem original_owner (N : ℕ) (hN : 0<N) (fixed : List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool))
    (wire : Fin (SemiprimePublicAcquiredExecution.wireCount N))
    (encode : Fin (SemiprimePublicAcquiredExecution.wireCount N)→List Bool)
    (he : ∀i,SemiprimeBitArithmetic.bitValue (encode i)=i.val)
    (tail : List Bool) (scopeWords : List (List Bool))
    (hscope : scopeWords.length=(SemiprimeD1RootTensorTables.ownerPorts N
      (SemiprimeD1RootTensorTables.acquirePositive N hN fixed).records wire).length) :
    ∃hs : scopeWords.length≤2,
      (done (encode wire) (fixed.map (fun x=>(encode x.1,x.2))) tail scopeWords hs).data output=
        tape (SemiprimeD1RootTensorTables.ownerNode N fixed
          (SemiprimeD1RootTensorTables.acquirePositive N hN fixed).records wire).table := by
  have hs : scopeWords.length≤2:=hscope.trans_le (SemiprimeD1RootTensorTablesBounds.owner_degree_le N hN fixed wire)
  refine ⟨hs,?_⟩
  calc
    _ = tape (SemiprimeD1RootOwnerTables.acquire fixed wire scopeWords.length).table :=
      output_original wire fixed encode he tail scopeWords hs
    _ = _ := congrArg (fun degree=>tape (SemiprimeD1RootOwnerTables.acquire fixed wire degree).table) hscope
/-- Original binary wire key and the exact post-terminator tail remain intact. -/
theorem retained_original_key_tail (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) :
    (done key rows tail scopeWords hs).data query=key ∧ (done key rows tail scopeWords hs).data reader=tail := ⟨rfl,rfl⟩
/-- The actual scope-ID vector survives the whole count/prefix/output program. -/
theorem retained_scope (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) :
    (done key rows tail scopeWords hs).data scope=SemiprimeD1TensorTapeCodec.vectorBits scopeWords := rfl
end RiemannGaussian.SemiprimeD1StackOwnerTableOriginal
