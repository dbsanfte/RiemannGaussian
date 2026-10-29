/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueNumeric
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueBounds
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueSource
open SemiprimeD1StackOwnerFibreCatalogueView SemiprimeD1StackOwnerFibreCatalogueOriginal
open SemiprimeD1StackOwnerFibreCatalogueNumeric
open SemiprimeBitArithmetic (bitValue)
/-- Honest complete retained-state cap from the SAME actual original routing source. -/
def baseCap (n:Nat) :Nat:=283*(n+SemiprimeD1StackPortOwnerRoutingBounds.polynomial n)
/-- Actual N-only routing plus whole preserving E-tally and M-bank copies. -/
def acquisitionCap (n:Nat) :Nat:=SemiprimeD1StackPortOwnerRoutingBounds.polynomial n+10*baseCap n+9
/-- One fixed polynomial counts source, ALL E filters/drains and final whole-output materialization. -/
def polynomial (n:Nat) :Nat:=acquisitionCap n+3*baseCap n*rowCap (2*baseCap n) (baseCap n)+8
/-- Every actual retained upstream word is bounded at the SAME routing source's real halt. -/
theorem source_word (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) (k:R.Stack) :
    ((SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data k).length≤ baseCap bits.length:=by
  obtain ⟨t,_,hr⟩:=SemiprimeD1StackPortOwnerRoutingBounds.source_run_polynomial bits hc hN
  have hs:=SemiprimeD1StackPortOwnerRoutingResources.prefix_cells bits hc hN t _ hr
  have ho:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset R.Stack))=>
    Nat.zero_le (((SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data k).length)) (Finset.mem_univ k)
  change (∑k:R.Stack,((SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data k).length)+0≤ baseCap bits.length at hs
  omega
/-- Actual original E count follows from retained physically acquired unary tally, not a count premise. -/
theorem count_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    SemiprimePublicAcquiredExecution.wireCount (bitValue bits)≤ baseCap bits.length:=by
  have h:=source_word bits hc hN (SemiprimeD1StackPortOwnerRouting.mapStack
    (SemiprimeD1StackOwnerCatalogue.source SemiprimeD1StackRootScopeBank.wireCount))
  rw [original_count,List.length_replicate] at h
  exact h
/-- The actual complete original factor-major routed tape is charged at source halt. -/
theorem routed_bytes (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (SemiprimeD1StackOwnerFibre.records (pairs bits hN) []).length≤ baseCap bits.length:=by
  have h:=source_word bits hc hN (SemiprimeD1StackPortOwnerRouting.aux .output)
  rw [source_pairs bits hc hN] at h
  exact h
/-- Actual full acquisition clock, with BOTH physically copied metadata/ID streams. -/
theorem acquisition_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    SemiprimeD1StackOwnerFibreCatalogueSource.budget bits hN≤ acquisitionCap bits.length:=by
  have he:=source_word bits hc hN (SemiprimeD1StackPortOwnerRouting.mapStack
    (SemiprimeD1StackOwnerCatalogue.source SemiprimeD1StackRootScopeBank.wireCount))
  have hi:=source_word bits hc hN (SemiprimeD1StackPortOwnerRouting.mapStack
    (SemiprimeD1StackOwnerCatalogue.source SemiprimeD1StackRootScopeBank.ids))
  change (countBytes bits hN).length≤ baseCap bits.length at he
  change (idBytes bits hN).length≤ baseCap bits.length at hi
  unfold SemiprimeD1StackOwnerFibreCatalogueSource.budget acquisitionCap;omega
/-- Every ACTUALLY selected owner query retains the acquired common M width; M is distinct from E. -/
theorem query_width (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (q:List Bool) (hq:q∈queries (bitValue bits)) :q.length≤ 2*baseCap bits.length:=by
  have hm:q∈SemiprimeD1OrdinalBankSpec.words (2*SemiprimePublicAcquiredExecution.wireCount (bitValue bits)):=
    (List.take_sublist _ _).subset hq
  have hw:=SemiprimeD1OrdinalBankSpec.word_length _ q hm
  have he:=count_bound bits hc hN
  omega
/-- Generic sum of the SAME physically executed owner-loop iteration clocks. -/
theorem loop_budget (qs:List (List Bool)) (rs:List (List Bool×List Bool)) (cap:Nat)
    (hq:∀q∈qs,SemiprimeD1StackOwnerFibreCatalogueRow.budget q rs≤ cap) :
    SemiprimeD1StackOwnerFibreCatalogueLoop.budget qs rs≤ qs.length*cap:=by
  induction qs with
  | nil=>simp only [SemiprimeD1StackOwnerFibreCatalogueLoop.budget,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons q qs ih=>
    have hh:=hq q (List.mem_cons_self)
    have ht:=ih (fun v hv=>hq v (List.mem_cons_of_mem _ hv))
    change SemiprimeD1StackOwnerFibreCatalogueRow.budget q rs+SemiprimeD1StackOwnerFibreCatalogueLoop.budget qs rs≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul];omega
/-- ALL original owners have actual metadata-derived uniform physical fibre acquisition clocks. -/
theorem original_loop_budget (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    SemiprimeD1StackOwnerFibreCatalogueLoop.budget (queries (bitValue bits)) (pairs bits hN)≤
      baseCap bits.length*rowCap (2*baseCap bits.length) (baseCap bits.length):=by
  have hb:=routed_bytes bits hc hN
  have h:=loop_budget (queries (bitValue bits)) (pairs bits hN)
    (rowCap (2*baseCap bits.length) (baseCap bits.length)) (by
      intro q hq
      exact (row_budget q _).trans (rowCap_mono _ _ _ _ (query_width bits hc hN q hq) hb))
  rw [queries_length] at h
  exact h.trans (Nat.mul_le_mul_right _ (count_bound bits hc hN))
/-- COMPLETE actual original-N source is bounded by ONE fixed input-width polynomial. -/
theorem budget_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    SemiprimeD1StackOwnerFibreCatalogueExecution.budget bits hN≤ polynomial bits.length:=by
  have ha:=acquisition_bound bits hc hN
  have hl:=original_loop_budget bits hc hN
  have hb:=bytes_budget (queries (bitValue bits)) (pairs bits hN)
  unfold SemiprimeD1StackOwnerFibreCatalogueExecution.budget polynomial
  simp only [Nat.mul_assoc];omega
/-- Its C,d are fixed before ALL original binary N, rather than supplied by a clock oracle. -/
theorem polynomial_monomial :∃C d:Nat,∀n,polynomial n≤ C*(n+1)^d:=by
  change SemiprimeReportPolynomialGrowth.Bound polynomial
  unfold polynomial acquisitionCap baseCap rowCap
    SemiprimeD1StackPortOwnerRoutingBounds.polynomial SemiprimeD1StackPortOwnerRoutingBounds.acquisitionCap
    SemiprimeD1StackPortOwnerRoutingBounds.scopeCap SemiprimeD1StackPortOwnerRoutingBounds.mapCap
    SemiprimeD1StackPortOwnerRoutingNumeric.rowCap SemiprimeD1StackOwnerCatalogueBounds.polynomial
    SemiprimeD1StackOwnerCatalogueBounds.acquisitionCap SemiprimeD1StackOwnerCatalogueBounds.bankCap
    SemiprimeD1StackOwnerCatalogueNumeric.rowCap SemiprimeD1StackOwnerCatalogueNumeric.recipeCap
    SemiprimeD1StackOwnerCatalogueOriginalBounds.operandCap SemiprimeD1StackRootScopeBankBounds.polynomial
    SemiprimeD1StackRootScopeBankBounds.tapeCap
  boundArithmetic
/-- Same physical305-role N-only all-owner source, with its derived fixed-polynomial whole clock. -/
theorem source_run_polynomial (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤ polynomial bits.length,C.run program time (initial bits)=some (SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN):=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackOwnerFibreCatalogueExecution.source_run bits hc hN
  exact ⟨t,ht.trans (budget_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueBounds
