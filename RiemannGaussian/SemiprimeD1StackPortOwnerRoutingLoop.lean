/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingRow
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingLoop
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView
open SemiprimeD1StackProcedureTrace (Runs runs_trans)
open SemiprimeD1FactorScopePairEncoding (Record stream)
/-- Exact physically emitted pair bytes in original input-record order. -/
def bytes (map:List (List Bool×List Bool)) (rows:List Record) : List Bool :=
  rows.flatMap (SemiprimeD1StackPortOwnerRoutingRow.row map)
/-- Sum of the SAME actual all-field routing-iteration costs. -/
def budget (map:List (List Bool×List Bool)) (rows:List Record) : Nat :=
  (rows.map (SemiprimeD1StackPortOwnerRoutingRow.budget map)).sum
/-- COMPLETE original-factor-major physical reader loop, copying/scanning the retained E-map
for EVERY original scope occurrence and preserving the original row order and all multiplicities. -/
theorem loop_run (m:Map.Stack→List Bool) (s:Scope.Stack→List Bool) (map:List (List Bool×List Bool))
    (hm:m (SemiprimeD1StackOwnerCatalogue.aux .output)=SemiprimeD1StackOwnerLookup.records map [])
    (rows:List Record) (raw:List Bool) :
    ∃time≤budget map rows,Runs program time (.local .parse)
      (data m s (fun _=>[]) (fun _=>[]) (rowAux (stream rows []) raw))
      (.local .parse) (data m s (fun _=>[]) (fun _=>[]) (rowAux [] ((bytes map rows).reverse++raw))) := by
  induction rows generalizing raw with
  | nil=>refine ⟨0,by simp [budget],SemiprimeD1StackProcedureTrace.runs_refl program _ _⟩
  | cons w rows ih=>
    obtain ⟨a,ha,har⟩:=SemiprimeD1StackPortOwnerRoutingRow.row_run m s map hm w (stream rows []) raw
    obtain ⟨b,hb,hbr⟩:=ih ((SemiprimeD1StackPortOwnerRoutingRow.row map w).reverse++raw)
    have h:=runs_trans program _ _ _ _ _ _ _ _ har hbr
    refine ⟨a+b,?_,?_⟩
    · simp only [budget,List.map_cons,List.sum_cons] at *;omega
    · simpa only [stream,List.foldr_cons,bytes,List.flatMap_cons,List.reverse_append,List.append_assoc] using h
/-- The actual pair row appends its literal following scope-stream suffix. -/
theorem row_append (owner scope tail:List Bool) :
    SemiprimeD1StackPortOwnerRoutingEmit.row owner scope++tail=
      true::SemiprimeSourceHistogramKeyBits.frame owner (SemiprimeSourceHistogramKeyBits.frame scope tail) :=
  SemiprimeD1StackOwnerCatalogueOriginalMap.row_append owner scope tail
/-- The physically emitted bytes have EXACTLY the old real owner-fibre parser's pair grammar. -/
theorem bytes_records (map:List (List Bool×List Bool)) (rows:List Record) (tail:List Bool) :
    bytes map rows++false::tail=SemiprimeD1StackOwnerFibre.records
      (rows.map (SemiprimeD1PortOwnerRoutingSpec.pair map)) tail := by
  induction rows with
  | nil=>rfl
  | cons w rows ih=>
    change (SemiprimeD1StackPortOwnerRoutingRow.row map w++bytes map rows)++false::tail=_
    rw [SemiprimeD1StackPortOwnerRoutingRow.row_pair,List.append_assoc,ih,row_append]
    rfl
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingLoop
