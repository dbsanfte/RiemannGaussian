/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingParse
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingClear
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingRow
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
/-- Exact actually reached all-role lookup store after matching this port's computed compact key. -/
def lookupDone (map:List (List Bool×List Bool)) (w:Fin 9→List Bool) : Lookup.Stack→List Bool :=
  (SemiprimeD1StackOwnerLookup.done (SemiprimeD1PortOwnerRoutingSpec.query w) map []).data
/-- Exact emitted owner/scope bytes, including their physically pushed row tag. -/
def row (map:List (List Bool×List Bool)) (w:Fin 9→List Bool) : List Bool :=
  SemiprimeD1StackPortOwnerRoutingEmit.row (lookupDone map w (.inr .output)) (w 0)
/-- SAME actual parse, key framing, whole map copy, numeric lookup, emission and ALL cleanup clocks. -/
def budget (map:List (List Bool×List Bool)) (w:Fin 9→List Bool) : Nat :=
  (1+SemiprimeD1StackPortOwnerRoutingParse.time w 9)+(6*SemiprimeD1StackPortOwnerRoutingKey.mass w+31)+
  (5*(SemiprimeD1StackOwnerLookup.records map []).length+
    SemiprimeD1StackOwnerLookupBounds.runBound (SemiprimeD1PortOwnerRoutingSpec.query w) map+5)+
  (10*(lookupDone map w (.inr .output)).length+10*(w 0).length+21)+
  SemiprimeD1StackPortOwnerRoutingClear.time (SemiprimeD1StackPortOwnerRoutingClear.bank (lookupDone map w) w) 20
/-- COMPLETE physical factor-major routing iteration returns to its SAME scoped-reader loop.
All nine fields are parsed; the key is framed; the actual retained E-map is copied and scanned;
owner/scope bytes are emitted; and all eleven lookup/nine parsed words are physically drained. -/
theorem row_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool)
    (map:List (List Bool×List Bool))
    (hm:m (SemiprimeD1StackOwnerCatalogue.aux .output)=SemiprimeD1StackOwnerLookup.records map [])
    (w:Fin 9→List Bool) (tail raw:List Bool) :
    ∃time≤budget map w,Runs program time (.local .parse)
      (data m s (fun _=>[]) (fun _=>[]) (rowAux (SemiprimeD1FactorScopePairEncoding.record w tail) raw))
      (.local .parse) (data m s (fun _=>[]) (fun _=>[]) (rowAux tail ((row map w).reverse++raw))) := by
  let a:=rowAux tail raw
  let a':=Function.update a .reversed ((row map w).reverse++raw)
  have hp:=SemiprimeD1StackPortOwnerRoutingParse.parse_run m s (fun _=>[]) w tail raw
  have hk:=SemiprimeD1StackPortOwnerRoutingKey.key_run m s w a rfl
  obtain ⟨t,ht,hl⟩:=SemiprimeD1StackPortOwnerRoutingLookup.copy_lookup_run m s w a rfl map hm
  change Runs program t _ _ _ (data m s (lookupDone map w) w a) at hl
  have he:=SemiprimeD1StackPortOwnerRoutingEmit.row_run m s (lookupDone map w) w a rfl rfl
  change Runs program _ _ _ _ (data m s (lookupDone map w) w a') at he
  have hc:=SemiprimeD1StackPortOwnerRoutingClear.clear_run m s (lookupDone map w) w a'
  have ha:a'=rowAux tail ((row map w).reverse++raw):=by funext k;cases k <;> rfl
  rw [ha] at he hc
  have h:=runs_trans program _ _ _ _ _ _ _ _ hp (runs_trans program _ _ _ _ _ _ _ _ hk
    (runs_trans program _ _ _ _ _ _ _ _ hl (runs_trans program _ _ _ _ _ _ _ _ he hc)))
  refine ⟨_,?_,h⟩
  unfold budget
  omega
/-- Actual routed row equals the computed-owner/unchanged-scope pair used by the authoritative typed bridge. -/
theorem row_pair (map:List (List Bool×List Bool)) (w:Fin 9→List Bool) :
    row map w=SemiprimeD1StackPortOwnerRoutingEmit.row (SemiprimeD1PortOwnerRoutingSpec.pair map w).1
      (SemiprimeD1PortOwnerRoutingSpec.pair map w).2 := rfl
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingRow
