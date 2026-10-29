/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueExecution
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueNumeric
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueRow
/-- Uniform complete-owner iteration bound in ACTUAL parsed query width and acquired routed tape bytes. -/
def rowCap (queryBytes routedBytes:Nat) :Nat:=
  100000*(queryBytes+routedBytes+100*(queryBytes+1)*(routedBytes+1)+1)
/-- Every actually reached filter word is bounded from its SAME physical source execution. -/
theorem filter_word (query:List Bool) (rows:List (List Bool×List Bool)) (k:V.Stack) :
    (filterDone query rows k).length≤query.length+(SemiprimeD1StackOwnerFibre.records rows []).length+
      SemiprimeD1StackOwnerFibreBounds.runBound query rows:=by
  let B:=SemiprimeD1StackOwnerFibre.records rows []
  have hr:=SemiprimeD1StackOwnerFibreExecution.source_run query rows []
  have hd:=SemiprimeD1StackReturnLink.run_data_bound SemiprimeD1StackOwnerFibre.program
    (SemiprimeD1StackOwnerFibreExecution.totalTime query rows) (query.length+B.length) _ _ (by
      intro i;rcases i with i|i <;> cases i <;>
        simp [SemiprimeD1StackOwnerFibre.initial,SemiprimeD1StackOwnerFibre.data,
          SemiprimeD1StackAdder.store,B]) hr k
  have ht:=SemiprimeD1StackOwnerFibreBounds.time_le query rows
  change (filterDone query rows k).length≤query.length+B.length+_ at hd
  exact hd.trans (Nat.add_le_add_left ht _)
/-- Every physically drained filter word and its actual EOF pop is counted. -/
theorem clear_time (f:V.Stack→List Bool) (cap n:Nat) (hf:∀k,(f k).length≤cap) :
    SemiprimeD1StackOwnerFibreCatalogueClear.time f n≤n*(cap+1):=by
  induction n with
  | zero=>simp only [SemiprimeD1StackOwnerFibreCatalogueClear.time,Nat.zero_mul,Nat.le_refl]
  | succ n ih=>
    have h:=hf (fibreRole ⟨n%14,Nat.mod_lt _ (by omega)⟩)
    simp only [SemiprimeD1StackOwnerFibreCatalogueClear.time]
    nlinarith
/-- COMPLETE real per-owner query/read/filter/emission/cleanup clock has a fixed polynomial byte majorant. -/
theorem row_budget (query:List Bool) (rows:List (List Bool×List Bool)) :
    SemiprimeD1StackOwnerFibreCatalogueRow.budget query rows≤rowCap query.length
      (SemiprimeD1StackOwnerFibre.records rows []).length:=by
  have hw:=filter_word query rows
  have hc:=clear_time (filterDone query rows)
    (query.length+(SemiprimeD1StackOwnerFibre.records rows []).length+
      SemiprimeD1StackOwnerFibreBounds.runBound query rows) 14 hw
  have hs:=hw (.inr .output)
  change (scopes query rows).length≤_ at hs
  unfold SemiprimeD1StackOwnerFibreCatalogueRow.budget rowCap
  unfold SemiprimeD1StackOwnerFibreBounds.runBound at *
  omega
/-- Actual-byte row majorant is monotone in both actual physical inputs. -/
theorem rowCap_mono (a A b B:Nat) (ha:a≤A) (hb:b≤B) :rowCap a b≤rowCap A B:=by
  have hp:=Nat.mul_le_mul (Nat.mul_le_mul_left 100 (show a+1≤A+1 by omega))
    (show b+1≤B+1 by omega)
  unfold rowCap;omega
/-- Physical row output bytes are paid by the SAME row source that produced them. -/
theorem row_bytes (query:List Bool) (rows:List (List Bool×List Bool)) :
    (SemiprimeD1StackOwnerFibreCatalogueRow.row query rows).length≤SemiprimeD1StackOwnerFibreCatalogueRow.budget query rows:=by
  simp only [SemiprimeD1StackOwnerFibreCatalogueRow.row,SemiprimeD1StackOwnerFibreCatalogueEmit.row,
    List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  unfold SemiprimeD1StackOwnerFibreCatalogueRow.budget;omega
/-- Final whole-catalogue reversal is bounded by actually emitted, already charged owner/fibre bytes. -/
theorem bytes_budget (queries:List (List Bool)) (rows:List (List Bool×List Bool)) :
    (SemiprimeD1StackOwnerFibreCatalogueLoop.bytes queries rows).length≤
      SemiprimeD1StackOwnerFibreCatalogueLoop.budget queries rows:=by
  induction queries with
  | nil=>exact Nat.zero_le _
  | cons q qs ih=>
    have hh:=row_bytes q rows
    change (SemiprimeD1StackOwnerFibreCatalogueRow.row q rows++SemiprimeD1StackOwnerFibreCatalogueLoop.bytes qs rows).length≤_
    rw [List.length_append]
    change _≤SemiprimeD1StackOwnerFibreCatalogueRow.budget q rows+SemiprimeD1StackOwnerFibreCatalogueLoop.budget qs rows
    omega
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueNumeric
