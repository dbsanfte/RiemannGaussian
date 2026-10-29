/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesExecution
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesCapacities
/-! # Own complete two-tape recovery-entry source polynomial
Every actual indexed read, metadata scan, copied byte, framed entry, cleanup,
real return and the final physical history reverse belongs to the SAME clock.
Child byte estimates here and in the original cap never use subtree runtimes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesBounds
open SemiprimeD1StackRecoveryEntries SemiprimeD1StackRecoveryEntriesExecution
open SemiprimeD1StackRecoveryEntriesLoop SemiprimeD1StackRecoveryEntriesOrder
open SemiprimeD1StackRecoveryEntriesEncoding (childTape selectedChild)
open SemiprimeD1StackRecoveryDenominatorEncoding (Row tape)
open SemiprimeD1StackRecoveryDenominatorCapacities (fieldMass field_mass_le payload_le_tape rows_length)
namespace B
export SemiprimeD1StackRecoveryEntriesCapacities (row_time chunk_bound)
end B
/-- Actual sum of row-step clocks, each independent of prior history length. -/
def rowSum (children:List (List (List Bool))) (rows:List Row):Nat:=(rows.map (SemiprimeD1StackRecoveryEntriesLoop.rowTime children)).sum
/-- Exact actual loop clock decomposes into row work plus ONE final history-byte reverse. -/
theorem budget_eq (children:List (List (List Bool))) (rows:List Row) (history:List Bool):
    budget children rows history=rowSum children rows+2*(chunks children rows).length+2*history.length+4:=by
  induction rows generalizing history with
  | nil=>
    simp only [budget,rowSum,List.map_nil,List.sum_nil,chunks,List.length_nil,Nat.mul_zero,Nat.zero_add]
    omega
  | cons r rows ih=>
    rw [budget,ih]
    simp only [rowSum,List.map_cons,List.sum_cons,chunks,List.length_append,List.length_reverse]
    omega
/-- Every actual row source clock is paid by its actual source/child bytes, not any child execution budget. -/
theorem row_sum_bound (children:List (List (List Bool))) (rows:List Row) (L:Nat)
    (hr:∀r∈rows,fieldMass r ≤L):
    rowSum children rows ≤10000000*rows.length*((childTape children).length+L+1)^2:=by
  induction rows with
  | nil=>simp only [rowSum,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.le_refl]
  | cons r rows ih=>
    have hr0:=hr r (List.mem_cons_self)
    have h0:SemiprimeD1StackRecoveryEntriesLoop.rowTime children r ≤10000000*((childTape children).length+L+1)^2:=
      (B.row_time children r).trans (Nat.mul_le_mul_left 10000000 (Nat.pow_le_pow_left (by omega:(childTape children).length+fieldMass r+1 ≤(childTape children).length+L+1) 2))
    have h1:=ih (fun s hs=>hr s (List.mem_cons_of_mem r hs))
    dsimp only [rowSum] at h1 ⊢
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_mul]
    omega
/-- Actual logged bytes grow only by the actually framed new entries. -/
theorem chunks_bound (children:List (List (List Bool))) (rows:List Row) (L:Nat)
    (hr:∀r∈rows,fieldMass r ≤L):
    (chunks children rows).length ≤5*rows.length*((childTape children).length+L+1):=by
  induction rows with
  | nil=>simp only [chunks,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.le_refl]
  | cons r rows ih=>
    have hr0:=hr r (List.mem_cons_self)
    have h0:(SemiprimeD1StackRecoveryEntriesLogger.chunk r (selectedChild children (r 0) (r 1))).length ≤5*((childTape children).length+L+1):=by
      have h:=B.chunk_bound children r
      have hm:=Nat.mul_le_mul_left 5 (by omega:(childTape children).length+fieldMass r+1 ≤(childTape children).length+L+1)
      exact h.trans hm
    have h1:=ih (fun s hs=>hr s (List.mem_cons_of_mem r hs))
    simp only [chunks,List.length_append,List.length_cons]
    nlinarith only [h0,h1]
/-- Only the actual two physical input byte lengths form the whole-source resource. -/
def resource (rows:List Row) (children:List (List (List Bool))):Nat:=(tape rows).length+(childTape children).length
/-- Fixed coefficient/degree precede every actual row tape, child cache and binary address family. -/
def runBound (rows:List Row) (children:List (List (List Bool))):Nat:=1000000000000*(resource rows children+1)^4
/-- SAME actual two-tape source has one fixed quartic bound, with all final history work included once. -/
theorem timeBound_le (rows:List Row) (children:List (List (List Bool))):timeBound rows children ≤runBound rows children:=by
  let rowBytes:=(tape rows).length
  let S:=resource rows children+1
  have hr:∀r∈rows,fieldMass r ≤rowBytes:=fun r he=>(field_mass_le rows r he).trans (payload_le_tape rows)
  have ht:=row_sum_bound children rows rowBytes hr
  have hc:=chunks_bound children rows rowBytes hr
  have hn:=rows_length rows
  have hnS:rows.length ≤S:=by dsimp [S,resource,rowBytes];omega
  have hS:(childTape children).length+rowBytes+1=S:=by dsimp [S,resource,rowBytes];omega
  rw [hS] at ht hc
  have ht':rowSum children rows ≤10000000*S^3:=by
    calc
      _ ≤10000000*rows.length*S^2:=ht
      _ ≤10000000*S*S^2:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10000000 hnS)
      _=10000000*S^3:=by ring
  have hc':(chunks children rows).length ≤5*S^2:=by
    calc
      _ ≤5*rows.length*S:=hc
      _ ≤5*S*S:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 5 hnS)
      _=5*S^2:=by ring
  have hpos:1 ≤S:=by dsimp [S];omega
  have h2:S^2 ≤S^4:=Nat.pow_le_pow_right hpos (by decide)
  have h3:S^3 ≤S^4:=Nat.pow_le_pow_right hpos (by decide)
  have h1:S ≤S^4:=by simpa only [pow_one] using Nat.pow_le_pow_right hpos (by decide:1 ≤4)
  have hrt:rowSum children rows ≤10000000*S^4:=ht'.trans (Nat.mul_le_mul_left 10000000 h3)
  have hrc:(chunks children rows).length ≤5*S^4:=hc'.trans (Nat.mul_le_mul_left 5 h2)
  have hrb:rowBytes+1 ≤S:=by dsimp [S,resource,rowBytes];omega
  unfold timeBound bodyTime
  change 5*rowBytes+5+budget children rows []+1 ≤1000000000000*S^4
  rw [budget_eq]
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero]
  omega
/-- Actual source trace bounded by its own fixed whole-program input-byte polynomial. -/
theorem source_run_bounded (rows:List Row) (children:List (List (List Bool))):
    ∃q ≤runBound rows children,SemiprimeD1StackCalls.run program q (initial (tape rows) (childTape children))=some (done rows children):=
  ⟨timeBound rows children,timeBound_le rows children,source_run rows children⟩
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesBounds
