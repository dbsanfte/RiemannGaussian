/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingAcquisition
import RiemannGaussian.SemiprimeD1FactorScopeIncidencesOriginal
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
/-- Actual lookup roles are disjoint from both acquired sources and every fresh parser/cache role. -/
theorem lookup_injective : Function.Injective lookupStack :=
  Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective)
/-- Actual parsed-field role inclusion. -/
theorem cache_injective : Function.Injective cache :=
  Sum.inr_injective.comp (Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective))
/-- Actual private outer work-role inclusion. -/
theorem aux_injective : Function.Injective aux :=
  Sum.inr_injective.comp (Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inr_injective))
/-- Literal parsed payload projection. -/
theorem data_cache (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) (i:Fin 9) :data m s l f a (cache i)=f i:=rfl
/-- Literal actual lookup projection. -/
theorem data_lookup (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) (i:Lookup.Stack) :data m s l f a (lookupStack i)=l i:=rfl
/-- Literal private outer reader/parser projection. -/
theorem data_aux (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) (i:Aux) :data m s l f a (aux i)=a i:=rfl
/-- Exact parsed cache update retaining both source banks and real lookup work. -/
theorem update_cache (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) (i:Fin 9) (word:List Bool) :
    Function.update (data m s l f a) (cache i) word=data m s l (Function.update f i word) a := by
  funext k;rcases k with k|k
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases k with k|k
    · exact Function.update_of_ne (by intro h;cases h) _ _
    · rcases k with k|k
      · exact Function.update_of_ne (by intro h;cases h) _ _
      · rcases k with k|k
        · change Function.update (data m s l f a) (cache i) word (cache k)=(Function.update f i word) k
          simp only [Function.update_apply,data_cache,cache_injective.eq_iff]
        · exact Function.update_of_ne (by intro h;cases h) _ _
/-- Exact private-role update retaining both actual acquisition sources and parsed original words. -/
theorem update_aux (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) (i:Aux) (word:List Bool) :
    Function.update (data m s l f a) (aux i) word=data m s l f (Function.update a i word) := by
  funext k;rcases k with k|k
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases k with k|k
    · exact Function.update_of_ne (by intro h;cases h) _ _
    · rcases k with k|k
      · exact Function.update_of_ne (by intro h;cases h) _ _
      · rcases k with k|k
        · exact Function.update_of_ne (by intro h;cases h) _ _
        · change Function.update (data m s l f a) (aux i) word (aux k)=(Function.update a i word) k
          simp only [Function.update_apply,data_aux,aux_injective.eq_iff]
/-- Exact real lookup-word update retaining every actual acquired/parsed field. -/
theorem update_lookup (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (l:Lookup.Stack→List Bool)
    (f:Fin 9→List Bool) (a:Aux→List Bool) (i:Lookup.Stack) (word:List Bool) :
    Function.update (data m s l f a) (lookupStack i) word=data m s (Function.update l i word) f a := by
  funext k;rcases k with k|k
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases k with k|k
    · exact Function.update_of_ne (by intro h;cases h) _ _
    · rcases k with k|k
      · change Function.update (data m s l f a) (lookupStack i) word (lookupStack k)=(Function.update l i word) k
        simp only [Function.update_apply,data_lookup,lookup_injective.eq_iff]
      · exact Function.update_of_ne (by intro h;cases h) _ _
/-- Exact fresh reader/collector view after a row's physically paid cleanup. -/
def rowAux (reader collector:List Bool) : Aux→List Bool
  | .reader=>reader | .reversed=>collector | _=>[]
/-- Both complete acquired source states, with one actual scoped reader copy and fresh loop work. -/
def ready (bits:List Bool) : Stack→List Bool :=data
  (SemiprimeD1StackOwnerCatalogueExecution.done bits).data (SemiprimeD1StackPortScopeExecution.done bits).data
  (fun _=>[]) (fun _=>[]) (rowAux ((SemiprimeD1StackPortScopeExecution.done bits).data
    (SemiprimeD1StackPortScopeRecords.aux .output)) [])
/-- Actual nine-field acquired rows, now proved to be original typed factor-major incidences. -/
def rows (bits:List Bool) :=SemiprimeD1StackFactorScopePairExecution.rows bits
/-- The source's actual scoped tape equals its authoritative nine-field record specification. -/
theorem scoped_output (bits:List Bool) :
    (SemiprimeD1StackPortScopeExecution.done bits).data (SemiprimeD1StackPortScopeRecords.aux .output)=
      SemiprimeD1FactorScopePairEncoding.stream (rows bits) [] := by
  change SemiprimeD1StackPortScopeExecution.result bits (SemiprimeD1StackPortScopeRecords.aux .output)=_
  rw [SemiprimeD1StackPortScopeExecution.original_scope_records,rows,
    SemiprimeD1StackFactorScopePairExecution.rows,SemiprimeD1FactorScopePairEncoding.joined_stream]
  rfl
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingView
