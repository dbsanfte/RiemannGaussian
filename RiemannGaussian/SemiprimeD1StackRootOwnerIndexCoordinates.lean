/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsOriginal
import RiemannGaussian.SemiprimeD1StackRootScopeBankOriginal
/-! # Actual retained root left-count coordinates for the owner-index caller
The complete record source already retains the whole83-role incidence/count
source in its OWNER branch. The next literal program aliases that actual E tally
as the acquired bounded left-count input; it must not substitute M=2E or rebuild
the graph/count bank. These are static coordinates and proof-side projections.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootOwnerIndexCoordinates
namespace R
export SemiprimeD1StackRootNetworkRecords (Stack output originalInput ownerStack)
export SemiprimeD1StackRootNetworkRecordsExecution (done owner_preserved)
end R
namespace S
export SemiprimeD1StackRootScopeBank (Stack wireCount)
export SemiprimeD1StackRootScopeBankExecution (result)
end S
open SemiprimeBitArithmetic (bitValue)
/-- Exact whole83-role original scope source already retained inside the actual owner-record bank. -/
def scopeStack (k:S.Stack) :R.Stack :=R.ownerStack (SemiprimeD1StackOwnerRecords.source
  (SemiprimeD1StackOwnerFibreCatalogue.source (SemiprimeD1StackPortOwnerRouting.mapStack
    (SemiprimeD1StackOwnerCatalogue.source k))))
/-- Actual bounded unary LEFT count E; the occurrence tally M=2E is a separate retained word. -/
def leftCount :R.Stack :=scopeStack S.wireCount
/-- Every original source/count/bank word is retained after the actual complete record acquisition. -/
theorem retained_scope (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool))
    (tail:List Bool) (k:S.Stack) :
    (R.done bits hN fixed tail).data (scopeStack k)=S.result bits k :=by
  calc
    _=(SemiprimeD1StackOwnerRecordsExecution.done bits hN fixed tail).data
        (SemiprimeD1StackOwnerRecords.source (SemiprimeD1StackOwnerFibreCatalogue.source
          (SemiprimeD1StackPortOwnerRouting.mapStack (SemiprimeD1StackOwnerCatalogue.source k)))):=
      R.owner_preserved bits hN fixed tail _
    _=(SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data
        (SemiprimeD1StackOwnerFibreCatalogue.source
          (SemiprimeD1StackPortOwnerRouting.mapStack (SemiprimeD1StackOwnerCatalogue.source k))):=
      SemiprimeD1StackOwnerRecordsResources.retained_source bits hN fixed tail _
    _=S.result bits k:=rfl
/-- Generic cached-root construction retains its declared left count, without reducing any original N. -/
theorem fromCache_leftCount {n F:Nat} {arity:Fin F→Nat}
    (data:SemiprimeD1RootTensorTables.Acquired n F arity) :
    (SemiprimeD1RootNetwork.fromCache data).network.leftCount=n :=rfl
/-- Original root LEFT count is the original public Boolean wire count, not the incidence scope. -/
theorem root_left_count (N:Nat) (hN:0<N)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount N)×Bool)) :
    (SemiprimeD1RootStateResources.root N hN fixed).leftCount=SemiprimePublicAcquiredExecution.wireCount N :=
  fromCache_leftCount (SemiprimeD1RootTensorTables.acquirePositive N hN fixed)
/-- The literal retained physical count word is exactly the next source's original unary left-count input. -/
theorem left_word (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    (R.done bits hN fixed tail).data leftCount=
      List.replicate (SemiprimeD1RootStateResources.root (bitValue bits) hN fixed).leftCount true :=by
  unfold leftCount
  rw [retained_scope,(SemiprimeD1StackRootScopeBankExecution.result_counts bits).2,
    SemiprimeD1StackRootScopeBankOriginal.wire_count,root_left_count]
/-- The retained left-count word and complete root record tape occupy separate physical source roles. -/
theorem count_ne_output :leftCount≠R.output :=by decide
/-- The original binary-N source is distinct from its actually acquired left-count cache. -/
theorem count_ne_input :leftCount≠R.originalInput :=by decide
end RiemannGaussian.SemiprimeD1StackRootOwnerIndexCoordinates
