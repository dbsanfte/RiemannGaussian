/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsExecution
import RiemannGaussian.SemiprimeD1StackOwnerRecordsNumeric
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsBounds
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsView
open SemiprimeD1StackOwnerRecordsLoop SemiprimeD1StackOwnerRecordsAcquisition
open SemiprimeD1StackOwnerRecordsOriginal SemiprimeD1StackOwnerRecordsNumeric
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (wireCount)
open SemiprimeD1OwnerPrefixBits (records)
open SemiprimeReportPolynomialGrowth (Bound constant_bound identity_bound add_bound mul_bound)
namespace P
export SemiprimeD1StackOwnerLookupOriginal.Public (occurrences occurrences_eq encode)
end P
namespace F
export SemiprimeD1StackOwnerFibreOriginal (scopeWord scopeWord_length scopeWord_value enumeration enumeration_length original_fibre rows routed)
end F
/-- BOTH actual whole305-state retention and real E tally are bounded, without E=M. -/
def baseCap (n:Nat) :Nat:=SemiprimeD1StackOwnerFibreCatalogueBounds.baseCap n+
  306*(n+SemiprimeD1StackOwnerFibreCatalogueBounds.polynomial n)
/-- Whole actual source bound in original input length and physically present caller prefix bytes. -/
def runCap (n P:Nat) :Nat:=SemiprimeD1StackOwnerFibreCatalogueBounds.polynomial n+5*baseCap n+
  3*baseCap n*rowCap (2*baseCap n) P+100
/-- Fixed EMPTY-prefix original-N polynomial, accounting for real prefix initialization. -/
def polynomial (n:Nat) :Nat:=runCap n 1
/-- Actual retained catalogue byte bound comes from its OWN source's full physical inventory. -/
theorem catalogue_length (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (catalogueBytes bits hN).length≤baseCap bits.length:=by
  obtain ⟨t,_,hr⟩:=SemiprimeD1StackOwnerFibreCatalogueBounds.source_run_polynomial bits hc hN
  have hs:=SemiprimeD1StackOwnerFibreCatalogueResources.prefix_cells bits hc hN t _ hr
  have ho:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset S.Stack))=>
    Nat.zero_le (((SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data k).length))
    (Finset.mem_univ (SemiprimeD1StackOwnerFibreCatalogue.aux .output))
  change (∑k:S.Stack,((SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data k).length)+0≤_ at hs
  unfold catalogueBytes baseCap;omega
theorem owners_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    wireCount (bitValue bits)≤baseCap bits.length:=by
  have h:=SemiprimeD1StackOwnerFibreCatalogueBounds.count_bound bits hc hN
  unfold baseCap;omega
theorem occurrences_bound (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    P.occurrences (bitValue bits)≤2*baseCap bits.length:=by
  rw [P.occurrences_eq _ hN]
  exact Nat.mul_le_mul_left 2 (owners_bound bits hc hN)
/-- Generic selection keeps only ACTUAL payloads; it never changes a selected scope word. -/
theorem values_all (query:List Bool) (rows:List (List Bool×List Bool)) (PropWord:List Bool→Prop)
    (h:∀pair∈rows,PropWord pair.2) :∀w∈SemiprimeD1StackOwnerFibre.values query rows,PropWord w:=by
  induction rows with
  | nil=>simp only [SemiprimeD1StackOwnerFibre.values,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons pair rows ih=>
    have ht:=ih (fun p hp=>h p (List.mem_cons_of_mem pair hp))
    have hh:=h pair List.mem_cons_self
    rcases pair with ⟨owner,scope⟩
    simp only [SemiprimeD1StackOwnerFibre.values]
    split
    · intro w hw
      rcases List.mem_cons.mp hw with he|he
      · simpa only [he] using hh
      · exact ht w he
    · exact ht
/-- Generic opaque-enumeration rank bound, proved BEFORE original-N specialization. -/
theorem enumeration_rank_bound {A:Type} [DecidableEq A]
    (en:OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.FiniteEnumeration A) (p:A) :
    (en.equivFin.symm p).val≤en.values.length:=
  (en.equivFin.symm p).isLt.le
/-- Physical original scope value is bounded through the SAME generic rank theorem. -/
theorem scope_value_bound (N:Nat) (p:SemiprimeD1RootTensorTables.Port N) :
    bitValue (F.scopeWord N p)≤P.occurrences N:=by
  have h:=enumeration_rank_bound (F.enumeration N) p
  have he:=F.scopeWord_value N p
  rw [←he,F.enumeration_length N] at h
  exact h
/-- Physical ALL-original-owner query widths remain M bits, while values remain in E. -/
theorem original_key_width (N:Nat) (hN:0<N) (r:Row) (hr:r∈originalRows N hN) :
    (keyOf r).length≤P.occurrences N:=by
  have hall:∀r∈originalRows N hN,(keyOf r).length≤P.occurrences N:=by
    unfold originalRows
    rw [List.forall_mem_ofFn_iff]
    intro e
    change (SemiprimeD1OrdinalBankSpec.idAt (P.occurrences N) e.val).length≤P.occurrences N
    have he:e.val<P.occurrences N:=by
      rw [P.occurrences_eq N hN]
      have hh:=e.isLt
      omega
    exact (SemiprimeD1OrdinalBankSpec.id_length (P.occurrences N) e.val he).le
  exact hall r hr
/-- Actual scope words are unchanged selections from the original M-occurrence stream. -/
theorem original_scope_width (N:Nat) (hN:0<N) (r:Row) (hr:r∈originalRows N hN)
    (w:List Bool) (hw:w∈wordsOf r) :w.length≤P.occurrences N:=by
  have hall:∀r∈originalRows N hN,∀w∈wordsOf r,w.length≤P.occurrences N:=by
    unfold originalRows
    rw [List.forall_mem_ofFn_iff]
    intro e
    change ∀w∈SemiprimeD1StackOwnerFibre.values (P.encode N e) (F.rows N hN),w.length≤P.occurrences N
    apply values_all
    intro pair hp
    change pair∈(F.enumeration N).values.map _ at hp
    obtain ⟨p,_,rfl⟩:=List.mem_map.mp hp
    exact (F.scopeWord_length N p).le
  exact hall r hr w hw
/-- Scope VALUE bounds are in the M-occurrence domain, independent of owner E ordering. -/
theorem original_scope_value (N:Nat) (hN:0<N) (r:Row) (hr:r∈originalRows N hN)
    (w:List Bool) (hw:w∈wordsOf r) :bitValue w≤P.occurrences N:=by
  have hall:∀r∈originalRows N hN,∀w∈wordsOf r,bitValue w≤P.occurrences N:=by
    unfold originalRows
    rw [List.forall_mem_ofFn_iff]
    intro e
    change ∀w∈SemiprimeD1StackOwnerFibre.values (P.encode N e) (F.rows N hN),bitValue w≤P.occurrences N
    apply values_all
    intro pair hp
    change pair∈(F.enumeration N).values.map _ at hp
    obtain ⟨p,_,rfl⟩:=List.mem_map.mp hp
    exact scope_value_bound N p
  exact hall r hr w hw
/-- The number of iterations is exactly original E, derived from actual acquired owner rows. -/
theorem original_loop_budget (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    loopBudget (originalRows (bitValue bits) hN) (prefixRows (bitValue bits) fixed) tail≤
      baseCap bits.length*rowCap (2*baseCap bits.length) (records (prefixRows (bitValue bits) fixed) tail).length:=by
  have hm:=occurrences_bound bits hc hN
  have h:=loop_budget_le (originalRows (bitValue bits) hN) (prefixRows (bitValue bits) fixed) tail
    (2*baseCap bits.length)
    (fun r hr=>(original_key_width _ hN r hr).trans hm)
    (fun r hr w hw=>(original_scope_width _ hN r hr w hw).trans hm)
    (fun r hr w hw=>(original_scope_value _ hN r hr w hw).trans hm)
  simp only [originalRows,List.length_ofFn] at h
  exact h.trans (Nat.mul_le_mul_right _ (owners_bound bits hc hN))
/-- EVERY prefix/copy/parser/cleanup cell of the SAME whole original source is paid. -/
theorem budget_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    SemiprimeD1StackOwnerRecordsExecution.budget bits hN fixed tail+1≤
      runCap bits.length (records (prefixRows (bitValue bits) fixed) tail).length:=by
  have hcata:=catalogue_length bits hc hN
  have hl:=original_loop_budget bits hc hN fixed tail
  have hb:=bytes_budget (originalRows (bitValue bits) hN) (prefixRows (bitValue bits) fixed) tail
  unfold SemiprimeD1StackOwnerRecordsExecution.budget acquisitionBudget runCap
  simp only [Nat.mul_assoc];omega
/-- Fixed C,d before every N; no externally supplied source/cost answer. -/
theorem polynomial_monomial :∃C d:Nat,∀n,polynomial n≤C*(n+1)^d:=by
  have hs :Bound (fun n=>SemiprimeD1StackOwnerFibreCatalogueBounds.polynomial n):=
    SemiprimeD1StackOwnerFibreCatalogueBounds.polynomial_monomial
  have hr :Bound (fun n=>SemiprimeD1StackPortOwnerRoutingBounds.polynomial n):=
    SemiprimeD1StackPortOwnerRoutingBounds.polynomial_monomial
  have h0 :Bound (fun n=>SemiprimeD1StackOwnerFibreCatalogueBounds.baseCap n):=
    mul_bound (constant_bound 283) (add_bound identity_bound hr)
  have hb :Bound baseCap:=
    add_bound h0 (mul_bound (constant_bound 306) (add_bound identity_bound hs))
  have hc :Bound (fun n=>rowCap (2*baseCap n) 1):=
    mul_bound (mul_bound (constant_bound 10000)
      (add_bound (mul_bound (constant_bound 2) hb) (constant_bound 1))) (constant_bound 2)
  exact add_bound (add_bound (add_bound hs (mul_bound (constant_bound 5) hb))
    (mul_bound (mul_bound (constant_bound 3) hb) hc)) (constant_bound 100)
/-- Complete real N-only all-owner source with its OWN uniform fixed polynomial. -/
theorem source_run_polynomial (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃time≤polynomial bits.length,C.run program time (initial bits)=
      some (SemiprimeD1StackOwnerRecordsExecution.done bits hN [] []):=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackOwnerRecordsExecution.source_run bits hc hN
  refine ⟨t,ht.trans ?_,hr⟩
  exact budget_le bits hc hN [] []
end RiemannGaussian.SemiprimeD1StackOwnerRecordsBounds
