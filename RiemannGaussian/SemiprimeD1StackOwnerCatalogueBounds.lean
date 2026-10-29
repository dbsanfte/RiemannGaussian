/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueExecution
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueOriginalBounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueBounds
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogueOriginalRow SemiprimeD1StackOwnerCatalogueOriginalIds
open SemiprimeD1StackOwnerCatalogueOriginalBounds SemiprimeD1StackOwnerCatalogueNumeric
open SemiprimeBitArithmetic (bitValue)
open SemiprimeMacroParameters
/-- Exact whole-bank byte majorant from its actual acquired M bound. -/
def bankCap (n:Nat) : Nat :=2*(2*Old.tapeCap n)^2+4*Old.tapeCap n+1
/-- Source acquisition and BOTH actual immutable tape copies. -/
def acquisitionCap (n:Nat) : Nat :=Old.polynomial n+5*Old.tapeCap n+5*bankCap n+9
/-- One fixed polynomial charging acquisition, all E real rows, every cleanup and final reversal. -/
def polynomial (n:Nat) : Nat :=acquisitionCap n+3*Old.tapeCap n*rowCap (operandCap n)+8
/-- The actual copied edge tape has the original executed edge-source bound. -/
theorem edge_bytes (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (edges bits).length≤Old.tapeCap bits.length := by
  have he:=SemiprimeD1StackOwnerCatalogueOriginalMetadata.edge_reader_original bits hc hN
  change edges bits=SemiprimeD1StackEdgeCount.tape (SemiprimeD1StackRootScopeBankExecution.records bits) [] at he
  rw [he]
  exact SemiprimeD1StackRootScopeBankBounds.tape_bytes bits hc hN
/-- Whole physical ID-bank bytes, including every unused M-E owner word, are charged. -/
theorem id_bytes (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (ids bits).length≤bankCap bits.length := by
  have hi:ids bits=SemiprimeD1TensorTapeCodec.vectorBits
      (SemiprimeD1OrdinalBankSpec.words (SemiprimeD1StackRootScopeBankExecution.occurrenceCount bits)):=
    SemiprimeD1StackRootScopeBankExecution.result_ids bits
  rw [hi,SemiprimeD1OrdinalBankSpec.bank_bytes]
  have hm:=SemiprimeD1StackRootScopeBankBounds.count_le bits hc hN
  have hs:=Nat.mul_le_mul hm hm
  unfold bankCap
  simp only [pow_two,Nat.mul_assoc] at hs ⊢
  omega
/-- Same actual prefix clock, including both whole-reader physical copies. -/
theorem acquisition_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    SemiprimeD1StackOwnerCatalogueSource.budget bits≤acquisitionCap bits.length := by
  have he:=edge_bytes bits hc hN
  have hi:=id_bytes bits hc hN
  have hb:=SemiprimeD1StackRootScopeBankBounds.budget_le bits hc hN
  unfold SemiprimeD1StackOwnerCatalogueSource.budget acquisitionCap
  omega
/-- Generic finite sum of actual row budgets, bounded uniformly on its actual list members. -/
theorem loop_budget {r t digits:Nat} (ps:List (SemiprimeD1StackOwnerCatalogueLoop.Pair r t digits)) (cap:Nat)
    (hp:∀p∈ps,SemiprimeD1StackOwnerCatalogueRow.budget (fields p.1 p.2)
      (SemiprimeD1StackPortOwnerRecipeSpec.original p.1)
      (SemiprimeD1StackPortOwnerRecipeClassify.originalTag p.1)≤cap) :
    SemiprimeD1StackOwnerCatalogueLoop.budget ps≤ps.length*cap := by
  induction ps with
  | nil=>simp only [SemiprimeD1StackOwnerCatalogueLoop.budget,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons p ps ih=>
    have hh:=hp p (List.mem_cons_self)
    have ht:=ih (fun q hq=>hp q (List.mem_cons_of_mem _ hq))
    change SemiprimeD1StackOwnerCatalogueRow.budget (fields p.1 p.2)
      (SemiprimeD1StackPortOwnerRecipeSpec.original p.1)
      (SemiprimeD1StackPortOwnerRecipeClassify.originalTag p.1)+SemiprimeD1StackOwnerCatalogueLoop.budget ps≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
/-- Every actual original row budget follows from original fields, acquired metadata and actual ID width. -/
theorem original_loop_budget (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    SemiprimeD1StackOwnerCatalogueLoop.budget (pairs (bitValue bits))≤
      Old.tapeCap bits.length*rowCap (operandCap bits.length) := by
  have h:=loop_budget (pairs (bitValue bits)) (rowCap (operandCap bits.length)) (by
    intro p hp
    apply row_budget_bound _ _ _ (SemiprimeD1StackPortOwnerRecipeClassify.original_tag p.1)
      (digitCount_bounds (bitLength_pos hN)).1 _ (original_payloads bits hc hN p hp) (original_volume bits hc hN p.1))
  have hn:(pairs (bitValue bits)).length=SemiprimePublicAcquiredExecution.wireCount (bitValue bits):=by
    simp only [pairs,List.length_ofFn]
  rw [hn] at h
  exact h.trans (Nat.mul_le_mul_right _ (wire_count_le bits hc hN))
/-- Every emitted bit is paid for by the physical row source that produced it. -/
theorem emitted_length (p:Fin 7→List Bool) (c:SemiprimeD1StackOwnerCatalogueRow.P.Counters)
    (tag:SemiprimeD1StackOwnerCatalogueRow.P.Tag) :
    (SemiprimeD1StackOwnerCatalogueRow.emitted p c tag).length≤SemiprimeD1StackOwnerCatalogueRow.budget p c tag := by
  simp only [SemiprimeD1StackOwnerCatalogueRow.emitted,SemiprimeD1StackOwnerCatalogueEmit.rowBytes,
    List.length_append,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  unfold SemiprimeD1StackOwnerCatalogueRow.budget
  omega
/-- Final whole-map reversal is charged using actual emitted byte inventory. -/
theorem bytes_budget {r t digits:Nat} (ps:List (SemiprimeD1StackOwnerCatalogueLoop.Pair r t digits)) :
    (SemiprimeD1StackOwnerCatalogueLoop.bytes ps).length≤SemiprimeD1StackOwnerCatalogueLoop.budget ps := by
  induction ps with
  | nil=>exact Nat.zero_le _
  | cons p ps ih=>
    have hh:=emitted_length (fields p.1 p.2) (SemiprimeD1StackPortOwnerRecipeSpec.original p.1)
      (SemiprimeD1StackPortOwnerRecipeClassify.originalTag p.1)
    change ((SemiprimeD1StackOwnerCatalogueRow.emitted (fields p.1 p.2)
      (SemiprimeD1StackPortOwnerRecipeSpec.original p.1)
      (SemiprimeD1StackPortOwnerRecipeClassify.originalTag p.1))++SemiprimeD1StackOwnerCatalogueLoop.bytes ps).length≤_
    rw [List.length_append]
    change _≤SemiprimeD1StackOwnerCatalogueRow.budget (fields p.1 p.2)
      (SemiprimeD1StackPortOwnerRecipeSpec.original p.1)
      (SemiprimeD1StackPortOwnerRecipeClassify.originalTag p.1)+SemiprimeD1StackOwnerCatalogueLoop.budget ps
    omega
/-- COMPLETE original-N actual-source clock is bounded by ONE fixed input-width polynomial. -/
theorem budget_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    SemiprimeD1StackOwnerCatalogueExecution.budget bits≤polynomial bits.length := by
  have ha:=acquisition_bound bits hc hN
  have hl:=original_loop_budget bits hc hN
  have hb:=bytes_budget (pairs (bitValue bits))
  unfold SemiprimeD1StackOwnerCatalogueExecution.budget polynomial
  simp only [Nat.mul_assoc]
  omega
/-- The polynomial is fixed before all original N, not a source-clock assumption. -/
theorem polynomial_monomial : ∃C d:Nat,∀n,polynomial n≤C*(n+1)^d := by
  change SemiprimeReportPolynomialGrowth.Bound polynomial
  unfold polynomial acquisitionCap bankCap rowCap recipeCap operandCap Old.polynomial Old.tapeCap
  boundArithmetic
/-- Actual original-N finite-source execution, including all acquisition and every address-key recipe. -/
theorem source_run_polynomial (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤polynomial bits.length,C.run program time (initial bits)=some (SemiprimeD1StackOwnerCatalogueExecution.done bits) := by
  obtain ⟨time,ht,hr⟩:=SemiprimeD1StackOwnerCatalogueExecution.source_run bits hc hN
  exact ⟨time,ht.trans (budget_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueBounds
