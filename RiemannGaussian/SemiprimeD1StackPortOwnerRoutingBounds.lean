/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOwnerRoutingNumeric
import RiemannGaussian.SemiprimeD1StackFactorScopePairBounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPortOwnerRoutingBounds
open SemiprimeD1StackPortOwnerRouting SemiprimeD1StackPortOwnerRoutingAcquisition
open SemiprimeD1StackPortOwnerRoutingView SemiprimeD1StackPortOwnerRoutingNumeric
open SemiprimeD1FactorScopePairEncoding (Record mass record stream record_length)
open SemiprimeBitArithmetic (bitValue)
/-- Actual scoped-port tape bound from its source's same-code all-prefix certificate. -/
def scopeCap (n:Nat) : Nat :=10^114*(n+1)^30
/-- Complete retained E-map bound from the actual149-role source's all-prefix certificate. -/
def mapCap (n:Nat) : Nat :=150*(n+SemiprimeD1StackOwnerCatalogueBounds.polynomial n)
/-- Actual N-copy, actual two source acquisitions and actual whole scoped-reader copy. -/
def acquisitionCap (n:Nat) : Nat :=5*n+4+(SemiprimeD1StackOwnerCatalogueBounds.polynomial n+1)+
  (10^111*(n+1)^30+1)+(5*scopeCap n+4)
/-- One fixed polynomial charges both acquisitions, EVERY original occurrence and final output bytes. -/
def polynomial (n:Nat) : Nat :=acquisitionCap n+3*scopeCap n*rowCap (scopeCap n) (mapCap n)+8
/-- Complete physically acquired scoped-stream byte bound, without a row/count/metadata premise. -/
theorem scope_bytes (bits:List Bool) (hb:bits≠[]) : (stream (rows bits) []).length≤ scopeCap bits.length :=
  SemiprimeD1StackFactorScopePairBounds.stream_length bits hb
/-- The complete actual E-map tape is bounded at the SAME executed map-source halt. -/
theorem map_bytes (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (SemiprimeD1StackOwnerLookup.records (SemiprimeD1StackPortOwnerRoutingExecution.map bits hN) []).length≤ mapCap bits.length := by
  obtain ⟨t,_,hr⟩:=SemiprimeD1StackOwnerCatalogueBounds.source_run_polynomial bits hc hN
  have hs:=SemiprimeD1StackOwnerCatalogueResources.prefix_cells bits hc hN t _ hr
  have ho:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset Map.Stack))=>
    Nat.zero_le (((SemiprimeD1StackOwnerCatalogueExecution.done bits).data k).length))
      (Finset.mem_univ (SemiprimeD1StackOwnerCatalogue.aux .output))
  have he:=congrArg List.length (SemiprimeD1StackOwnerCatalogueExecution.output_original bits hN)
  change (∑k:Map.Stack,((SemiprimeD1StackOwnerCatalogueExecution.done bits).data k).length)+0≤ mapCap bits.length at hs
  change _≤ mapCap bits.length
  change _=(SemiprimeD1StackOwnerLookup.records (SemiprimeD1StackPortOwnerRoutingExecution.map bits hN) []).length at he
  omega
/-- Actual full initial acquisition clock, including both source calls and whole tape copies. -/
theorem acquisition_bound (bits:List Bool) (hb:bits≠[]) :
    SemiprimeD1StackPortOwnerRoutingSource.budget bits≤ acquisitionCap bits.length := by
  have h:=scope_bytes bits hb
  rw [←scoped_output] at h
  unfold SemiprimeD1StackPortOwnerRoutingSource.budget acquisitionCap
  omega
/-- Whole-record physical byte count includes every field's payload mass. -/
theorem mass_record (w:Record) (tail:List Bool) : mass w≤ (record w tail).length := by
  rw [record_length];omega
/-- Original following rows remain in the same actual record tape. -/
theorem tail_record (w:Record) (tail:List Bool) : tail.length≤ (record w tail).length := by
  rw [record_length];omega
/-- Every actual record's entire payload is bounded by bytes of the actual acquired stream. -/
theorem member_mass (ws:List Record) (w:Record) (hw:w∈ws) : mass w≤ (stream ws []).length := by
  induction ws with
  | nil=>cases hw
  | cons v ws ih=>
    rcases List.mem_cons.mp hw with h|h
    · subst w;exact mass_record v _
    · exact (ih h).trans (tail_record v _)
/-- The actual EOF loop can visit no more records than the physical stream's byte inventory. -/
theorem rows_length (ws:List Record) :ws.length≤ (stream ws []).length := by
  induction ws with
  | nil=>rfl
  | cons w ws ih=>
    change ws.length+1≤ (record w (stream ws [])).length
    rw [record_length];omega
/-- Fixed polynomial row majorant is monotone in BOTH actual tape-byte inputs. -/
theorem rowCap_mono (a A b B:Nat) (ha:a≤ A) (hb:b≤ B) :rowCap a b≤ rowCap A B := by
  have hp:=Nat.mul_le_mul (Nat.mul_le_mul_left 100 (show 2*a+8≤ 2*A+8 by omega))
    (show b+1≤ B+1 by omega)
  unfold rowCap
  omega
/-- Actual finite row-loop time is the sum of its OWN proved physical iteration budgets. -/
theorem loop_budget (map:List (List Bool×List Bool)) (ws:List Record) (cap:Nat)
    (hw:∀w∈ws,SemiprimeD1StackPortOwnerRoutingRow.budget map w≤ cap) :
    SemiprimeD1StackPortOwnerRoutingLoop.budget map ws≤ ws.length*cap := by
  induction ws with
  | nil=>simp only [SemiprimeD1StackPortOwnerRoutingLoop.budget,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons w ws ih=>
    have hh:=hw w (List.mem_cons_self)
    have ht:=ih (fun v hv=>hw v (List.mem_cons_of_mem _ hv))
    change SemiprimeD1StackPortOwnerRoutingRow.budget map w+SemiprimeD1StackPortOwnerRoutingLoop.budget map ws≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
/-- All ORIGINAL factor-major occurrences have a derived uniform actual-byte routing clock. -/
theorem original_loop_budget (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    SemiprimeD1StackPortOwnerRoutingLoop.budget (SemiprimeD1StackPortOwnerRoutingExecution.map bits hN) (rows bits)≤
      scopeCap bits.length*rowCap (scopeCap bits.length) (mapCap bits.length) := by
  have hb:bits≠[]:=by intro h;subst bits;exact Nat.lt_irrefl _ hN
  have hs:=scope_bytes bits hb
  have hm:=map_bytes bits hc hN
  have h:=loop_budget (SemiprimeD1StackPortOwnerRoutingExecution.map bits hN) (rows bits)
    (rowCap (scopeCap bits.length) (mapCap bits.length)) (by
      intro w hw
      exact (row_budget _ w).trans (rowCap_mono _ _ _ _ ((member_mass _ w hw).trans hs) hm))
  exact h.trans (Nat.mul_le_mul_right _ ((rows_length _).trans hs))
/-- Every actually emitted owner/scope byte is paid by the row source that produced it. -/
theorem row_bytes (map:List (List Bool×List Bool)) (w:Record) :
    (SemiprimeD1StackPortOwnerRoutingRow.row map w).length≤ SemiprimeD1StackPortOwnerRoutingRow.budget map w := by
  simp only [SemiprimeD1StackPortOwnerRoutingRow.row,SemiprimeD1StackPortOwnerRoutingEmit.row,
    List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  unfold SemiprimeD1StackPortOwnerRoutingRow.budget
  omega
/-- The final whole-output physical reversal is charged by actual emitted bytes. -/
theorem bytes_budget (map:List (List Bool×List Bool)) (ws:List Record) :
    (SemiprimeD1StackPortOwnerRoutingLoop.bytes map ws).length≤ SemiprimeD1StackPortOwnerRoutingLoop.budget map ws := by
  induction ws with
  | nil=>exact Nat.zero_le _
  | cons w ws ih=>
    have hh:=row_bytes map w
    change (SemiprimeD1StackPortOwnerRoutingRow.row map w++SemiprimeD1StackPortOwnerRoutingLoop.bytes map ws).length≤ _
    rw [List.length_append]
    change _≤ SemiprimeD1StackPortOwnerRoutingRow.budget map w+SemiprimeD1StackPortOwnerRoutingLoop.budget map ws
    omega
/-- COMPLETE original-N routing source has ONE fixed polynomial bit-transition budget. -/
theorem budget_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    SemiprimeD1StackPortOwnerRoutingExecution.budget bits hN≤ polynomial bits.length := by
  have hb:bits≠[]:=by intro h;subst bits;exact Nat.lt_irrefl _ hN
  have ha:=acquisition_bound bits hb
  have hl:=original_loop_budget bits hc hN
  have hr:=bytes_budget (SemiprimeD1StackPortOwnerRoutingExecution.map bits hN) (rows bits)
  unfold SemiprimeD1StackPortOwnerRoutingExecution.budget polynomial
  simp only [Nat.mul_assoc]
  omega
/-- The majorant's C,d are fixed before EVERY original binary N. -/
theorem polynomial_monomial :∃C d:Nat,∀n,polynomial n≤ C*(n+1)^d := by
  change SemiprimeReportPolynomialGrowth.Bound polynomial
  unfold polynomial acquisitionCap scopeCap mapCap rowCap
    SemiprimeD1StackOwnerCatalogueBounds.polynomial SemiprimeD1StackOwnerCatalogueBounds.acquisitionCap
    SemiprimeD1StackOwnerCatalogueBounds.bankCap SemiprimeD1StackOwnerCatalogueNumeric.rowCap
    SemiprimeD1StackOwnerCatalogueNumeric.recipeCap SemiprimeD1StackOwnerCatalogueOriginalBounds.operandCap
    SemiprimeD1StackRootScopeBankBounds.polynomial SemiprimeD1StackRootScopeBankBounds.tapeCap
  boundArithmetic
/-- Same actual physical routing source, now with its original-binary-width uniform polynomial clock. -/
theorem source_run_polynomial (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤ polynomial bits.length,C.run program time (initial bits)=some (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPortOwnerRoutingExecution.source_run bits hc hN
  exact ⟨t,ht.trans (budget_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackPortOwnerRoutingBounds
