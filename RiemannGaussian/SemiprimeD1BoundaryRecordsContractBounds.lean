/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecordsGroupBounds
import RiemannGaussian.SemiprimeD1BoundaryRecordsSortBounds

/-! # Full-record sequential contraction report -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsContractBounds
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsCanonical
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1BoundaryRecordsGroupBounds
open SemiprimeD1JetAxes (Context)

/-- Paid identifier comparison metadata, independent of assignment count. -/
def portMass (ps : List Nat) : Nat := (ps.map (fun p => Nat.size p+1)).sum

/-- Search pays actual binary identifier widths and sequential traversal. -/
theorem findPort_clock (p : Nat) (ps : List Nat) :
    (findPort p ps).clock ≤ 3*(Nat.size p+1)*(portMass ps+1) := by
  induction ps with
  | nil => simp [findPort,portMass]; omega
  | cons q qs ih =>
    simp only [findPort]
    split <;> simp only [portMass,List.map_cons,List.sum_cons] at ih ⊢ <;> nlinarith

/-- Sequential bit access pays at most the entire input address. -/
theorem readBit_clock (bits : List Bool) (i : Nat) :
    (readBit bits i).clock ≤ 3*(bits.length+1) := by
  induction bits generalizing i with
  | nil => simp [readBit]
  | cons b bs ih =>
    cases i with
    | zero => simp only [readBit,List.length_cons]; omega
    | succ i =>
      have ht:=ih i
      simp only [readBit,List.length_cons]
      omega

/-- Port projection has polynomial metadata work and no table scan. -/
def projectBudget (source target : List Nat) (K : Nat) : Nat :=
  3*(portMass target+1)*(portMass source+1)+3*(target.length+1)*(K+2)

theorem project_clock (bits : List Bool) (source target : List Nat) (K : Nat)
    (hk : bits.length≤K) : (project bits source target).clock ≤ projectBudget source target K := by
  induction target with
  | nil => simp [project,projectBudget,portMass]; omega
  | cons p ps ih =>
    have hf:=findPort_clock p source
    have hb:=readBit_clock bits (findPort p source).value
    simp only [project]
    unfold projectBudget at ih ⊢
    simp only [portMass,List.map_cons,List.sum_cons,List.length_cons] at ih hf ⊢
    nlinarith

/-- Full rekey work retains all payload bytes and address projection. -/
def rekeyBudget (ctx : Context) (source target : List Nat) (K : Nat) : Nat :=
  projectBudget source target K+3*recordBudget ctx K+6

theorem rekey_clock (ctx : Context) (source target : List Nat) (K : Nat)
    (es : List Entry) (hg : GoodEntries ctx es) (hk : Keys K es) :
    (rekey source target es).clock ≤ rekeyBudget ctx source target K*(es.length+1) := by
  induction es with
  | nil => simp only [rekey,List.length_nil,Nat.zero_add,Nat.mul_one]; unfold rekeyBudget; omega
  | cons e es ih =>
    have ht:=ih (fun x hx => hg x (List.mem_cons_of_mem _ hx))
      (fun x hx => hk x (List.mem_cons_of_mem _ hx))
    have hp:=project_clock e.key source target K (hk e List.mem_cons_self)
    have hs:=size_le ctx K e (hg e List.mem_cons_self) (hk e List.mem_cons_self)
    simp only [rekey,List.length_cons]
    unfold rekeyBudget at ht ⊢
    nlinarith

theorem rekey_keys (source target : List Nat) (es : List Entry) :
    Keys target.length (rekey source target es).value := by
  induction es with
  | nil => simp [rekey,Keys]
  | cons e es ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (project_length e.key source target).le
    · exact ih x hx

/-- Actual sort and full-jet grouping cost one exponential catalogue, with a
polynomial independent factor. Precision zero still retains rank delimiters. -/
def contractBudget (ctx : Context) (source target : List Nat) (K W : Nat) : Nat :=
  rekeyBudget ctx source target K+
  200*(recordBudget ctx target.length+1)*(W+3)+sumBudget ctx target.length+5

theorem contract_clock_pow (ctx : Context) (source target : List Nat) (K W : Nat)
    (es : List Entry) (hg : GoodEntries ctx es) (hk : Keys K es) (hn : es.length≤2^W) :
    (contract ctx source target es).clock ≤ contractBudget ctx source target K W*(2^W+1) := by
  have hr:=rekey_clock ctx source target K es hg hk
  have hgood:=rekey_good ctx source target es hg
  have hkeys:=rekey_keys source target es
  have hs:=SemiprimeD1BoundaryRecordsSortBounds.sort_clock_pow
    (rekey source target es).value (recordBudget ctx target.length) W
    (fun e he => size_le ctx target.length e (hgood e he) (hkeys e he))
    (by rw [rekey_length]; exact hn)
  have hg':=sort_good ctx _ hgood
  have hk' : Keys target.length (sort (rekey source target es).value).value := by
    intro e he
    exact hkeys e ((SemiprimeD1BoundaryRecordsSort.sort_perm _).mem_iff.mp he)
  have ht:=group_clock ctx target.length _ hg' hk'
  rw [SemiprimeD1BoundaryRecordsSort.sort_length,rekey_length] at ht
  have hr':=hr.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1))
  have ht':=ht.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1))
  simp only [contract]
  unfold contractBudget
  nlinarith only [hr',hs,ht',Nat.zero_le (2^W)]

end RiemannGaussian.SemiprimeD1BoundaryRecordsContractBounds
