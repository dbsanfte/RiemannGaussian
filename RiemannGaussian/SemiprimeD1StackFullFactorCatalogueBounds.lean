/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueCapacities
/-! # Whole actual all-factor source clock with an original scope exponent
Every row is charged at its real current history size. The history invariant
is additive in original factor count, giving a fixed polynomial times 2^(19 B).
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueBounds
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueRows
open SemiprimeD1StackFullFactorCatalogueLoop SemiprimeD1StackFullFactorCatalogueExecution
open SemiprimeD1StackFullFactorCatalogueCapacities SemiprimeD1StackFullFactorCatalogueHistoryBounds
open SemiprimeD1BooleanFactorCatalogueIndices (vertex scopeWords key indices)
open SemiprimeD1BooleanFactorCatalogueIndicesBounds (cons_values)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount)
/-- Actual whole-history allowance, summing zero-history row byte bounds once per factor. -/
def historyAllowance (bits:List Bool) :Nat:=factorAllowance bits.length*rowAllowance bits
/-- A fixed width polynomial for an entire row, including the next retained-source query. -/
def rowPolynomial (n:Nat) :Nat:=
  10^130*(polynomial n+factorAllowance n*polynomial n+2)^18+2*polynomial n
/-- Fixed width polynomial for setup, all rows, full reversal and halt. -/
def runPolynomial (n:Nat) :Nat:=
  polynomial n+factorAllowance n*rowPolynomial n+2*factorAllowance n*polynomial n+4
/-- Whole original N-only clock; all18 table families use the genuine common scope bound. -/
def runBound (bits:List Bool) :Nat:=runPolynomial bits.length*2^(19*R.arityCapacity bits)
/-- The accumulated-history exponent joins the eighteenth-power input cap once. -/
theorem exponent_join (B:Nat) :((2:Nat)^B)^18*2^B=2^(19*B):=by
  rw [←pow_mul,←pow_add]
  congr 1
  omega
/-- The original table exponent is below the final caller-history exponent. -/
theorem exponent_le (B:Nat) :(2:Nat)^B ≤ 2^(19*B):=
  Nat.pow_le_pow_right (by decide) (by omega)
/-- Every real dispatcher input, including actual accumulated history and output sentinel, is charged. -/
theorem capacity_le (bits:List Bool) (hist:List Bool) (hh:hist.length ≤ historyAllowance bits) :
    R.capacity bits hist [false]+1 ≤
      (polynomial bits.length+factorAllowance bits.length*polynomial bits.length+2)*2^(R.arityCapacity bits):=by
  have hb:=base_le bits.length
  have he:1 ≤ (2:Nat)^(R.arityCapacity bits):=Nat.pow_pos (by decide)
  have h0:=Nat.mul_le_mul_left (polynomial bits.length) he
  have h2:=Nat.mul_le_mul_left 2 he
  unfold historyAllowance rowAllowance at hh
  unfold R.capacity R.baseCapacity
  simp only [List.length_singleton]
  nlinarith only [hb,hh,h0,h2]
/-- Same actual full row timeBound at the current history size; no repeated-growth clock recurrence. -/
theorem dispatcher_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) (hist:List Bool) (hh:hist.length ≤ historyAllowance bits) :
    DS.timeBound (DR.originalCode (vertex (bitValue bits) f)) (DR.rawFields bits (vertex (bitValue bits) f))
      (scopeWords bits f.val) hist [false] ≤
        (10^130*(polynomial bits.length+factorAllowance bits.length*polynomial bits.length+2)^18)*
          2^(19*R.arityCapacity bits):=by
  have h:=R.timeBound_original bits hc hN f hist [false]
  have hp:=Nat.pow_le_pow_left (capacity_le bits hist hh) 18
  rw [mul_pow] at hp
  have hm:=Nat.mul_le_mul_left (10^130) (Nat.mul_le_mul_right (2^(R.arityCapacity bits)) hp)
  rw [Nat.mul_assoc,exponent_join] at hm
  exact h.trans (by simpa only [Nat.mul_assoc] using hm)
/-- Parsing, real full component, physical cleanup and EOF fit the same per-row width polynomial. -/
theorem row_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (f:Fin (factorCount (bitValue bits))) (hist:List Bool) (hh:hist.length ≤ historyAllowance bits) :
    rowBudget bits f.val f hist [false]+1+polynomial bits.length ≤
      rowPolynomial bits.length*2^(19*R.arityCapacity bits):=by
  have ht:=dispatcher_le bits hc hN f hist hh
  have hcl:=cleanup_le bits hc hN f
  have he:1 ≤ (2:Nat)^(19*R.arityCapacity bits):=Nat.pow_pos (by decide)
  have hp:=Nat.mul_le_mul_left (2*polynomial bits.length) he
  unfold rowBudget rowPolynomial
  nlinarith only [ht,hcl,hp]
/-- Every current history and every not-yet-emitted row fits one invariant total byte allowance. -/
theorem loop_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (n:Nat) (fs:List (Fin (factorCount (bitValue bits))))
    (hseq:fs.map Fin.val=List.range' n fs.length) (hist:List Bool)
    (hh:hist.length+fs.length*rowAllowance bits ≤ historyAllowance bits) :
    loopBudget bits n fs hist [false] ≤ fs.length*(rowPolynomial bits.length*2^(19*R.arityCapacity bits)):=by
  induction fs generalizing n hist with
  | nil=>simp only [loopBudget,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons f fs ih=>
    have horder:=cons_values (bitValue bits) n f fs hseq
    have hhist:hist.length ≤ historyAllowance bits:=by omega
    have hr:=row_le bits hc hN f hist hhist
    rw [horder.1] at hr
    have hhnext:(afterRow bits n f hist [false]).length+fs.length*rowAllowance bits ≤ historyAllowance bits:=by
      have hi:=history_increment bits hc hN f hist [false]
      have hc0:=row_cap_le bits hc hN f
      rw [horder.1] at hi
      simp only [List.length_cons] at hh
      nlinarith only [hi,hc0,hh]
    cases fs with
    | nil=>
      simp only [loopBudget,List.length_cons,List.length_nil,ite_true,Nat.add_zero,Nat.zero_add,Nat.one_mul]
      omega
    | cons g gs=>
      have hg:=cons_values (bitValue bits) (n+1) g gs horder.2
      have hq:=query_le bits hc hN g
      rw [hg.1] at hq
      have hi:=ih (n+1) horder.2 (afterRow bits n f hist [false]) hhnext
      change rowBudget bits n f hist [false]+1+
        (SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key (n+1))+2+
          loopBudget bits (n+1) (g::gs) (afterRow bits n f hist [false]) [false]) ≤
        ((g::gs).length+1)*(rowPolynomial bits.length*2^(19*R.arityCapacity bits))
      nlinarith only [hr,hq,hi]
/-- Actual complete output history uses at most one paid row allowance per original factor. -/
theorem history_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    (afterRows bits 0 (indices (bitValue bits)) [] [false]).length ≤ historyAllowance bits:=by
  have h:=history_length_le bits hc hN 0 (indices (bitValue bits)) (indices_sequence (bitValue bits)) [] [false]
  have hs:((indices (bitValue bits)).map (rowCap bits)).sum ≤
      (indices (bitValue bits)).length*rowAllowance bits:=by
    induction indices (bitValue bits) with
    | nil=>simp
    | cons f fs ih=>
      have hr:=row_cap_le bits hc hN f
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [hr,ih]
  have hf:=factor_count_le bits hc hN
  rw [indices_length] at hs
  have hm:=Nat.mul_le_mul_right (rowAllowance bits) hf
  unfold historyAllowance
  simp only [List.length_nil,Nat.add_zero] at h
  omega
/-- Whole SAME N-only acquisition, including setup, every acquired row/query, reversal and halt. -/
theorem timeBound_le (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    timeBound bits ≤ runBound bits:=by
  have hf:=factor_count_le bits hc hN
  have hi:([]:List Bool).length+(indices (bitValue bits)).length*rowAllowance bits ≤ historyAllowance bits:=by
    rw [indices_length]
    simpa only [List.length_nil,Nat.zero_add,historyAllowance] using Nat.mul_le_mul_right (rowAllowance bits) hf
  have hl:=loop_le bits hc hN 0 (indices (bitValue bits)) (indices_sequence (bitValue bits)) [] hi
  rw [indices_length] at hl
  have hloop:=Nat.mul_le_mul_right (rowPolynomial bits.length*2^(19*R.arityCapacity bits)) hf
  have hh:=history_le bits hc hN
  have hs:=setup_le bits
  have hex:=exponent_le (R.arityCapacity bits)
  have hhist:=Nat.mul_le_mul_left (factorAllowance bits.length*polynomial bits.length) hex
  have he:1 ≤ (2:Nat)^(19*R.arityCapacity bits):=Nat.pow_pos (by decide)
  have hsetup:=Nat.mul_le_mul_left (polynomial bits.length+4) he
  unfold historyAllowance rowAllowance at hh
  unfold timeBound runBound runPolynomial
  nlinarith only [hl,hloop,hh,hs,hhist,hsetup]
/-- The complete actual fixed1454-role source now has one original-width fixed-rate bound. -/
theorem source_run_bounded (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    ∃t ≤ runBound bits,C.run program t (initial bits)=some (done bits):=by
  obtain ⟨t,ht,hr⟩:=source_run bits hc hN
  exact ⟨t,ht.trans (timeBound_le bits hc hN),hr⟩
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueBounds
