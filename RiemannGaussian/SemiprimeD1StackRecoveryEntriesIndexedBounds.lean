/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedExecution
/-! # Own physical-byte binary-query scan clock, independent of address value
The acquired ordinal grows only with actual scanned fields. All comparisons,
full binary increments, materialized payloads, unread suffix drains and real
returns are bounded by actual cache/query bytes, never by numeric query value.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedBounds
open SemiprimeD1StackRecoveryEntriesIndexed SemiprimeD1StackRecoveryEntriesIndexedSpec
open SemiprimeD1StackRecoveryEntriesIndexedOperators SemiprimeD1StackRecoveryEntriesIndexedLoop
open SemiprimeD1StackRecoveryEntriesIndexedExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Actual full numeric comparison plus two real operand copies and physical decision pop is linear in binary bytes. -/
theorem compare_time (query counter:List Bool):compareTime query counter ≤10*(query.length+counter.length+2):=by
  have h:=SemiprimeD1StackWordEqualExecution.executionTime_le query counter
  unfold compareTime
  omega
/-- Actual full increment adder clock is linear in the acquired binary ordinal's physical width. -/
theorem add_time (counter:List Bool):addTime counter ≤10*(counter.length+2):=by
  have h:=increment_length counter
  have hm:max counter.length 1 ≤counter.length+1:=max_le (by omega) (by omega)
  unfold addTime
  omega
/-- All actual counter copies, drains, one-bit seed, full adder and restored output are paid. -/
theorem increment_time (counter:List Bool):incrementTime counter ≤100*(counter.length+1):=by
  have h:=increment_length counter
  have ha:=add_time counter
  unfold incrementTime
  omega
/-- Exact physical vector-byte recurrence, including true marker and frame delimiter. -/
theorem vector_cons_length (word:List Bool) (words:List (List Bool)):
    (vectorBits (word::words)).length=2*word.length+(vectorBits words).length+2:=by
  simp only [vectorBits,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length]
/-- Every actual future field and every ordinal increment is paid by remaining source fields, not query magnitude. -/
theorem budget_cap (words:List (List Bool)) (query counter:List Bool) (cap L:Nat)
    (hc:counter.length+2*words.length ≤cap) (hl:(vectorBits words).length ≤L):
    budget query counter words ≤1000*(words.length+1)*(query.length+cap+L+1):=by
  induction words generalizing counter with
  | nil=>
    simp only [budget,List.length_nil,Nat.mul_zero,Nat.add_zero] at hc ⊢
    omega
  | cons word words ih=>
    have hv:=vector_cons_length word words
    have hn:(increment counter).length+2*words.length ≤cap:=by
      have hi:=increment_length counter
      simp only [List.length_cons] at hc
      omega
    have ht:=ih (increment counter) hn (by omega)
    have he:=compare_time query counter
    have hi:=increment_time counter
    have hcounter:counter.length ≤cap:=by omega
    have hw:word.length ≤L:=by omega
    have hrest:(vectorBits words).length ≤L:=by omega
    unfold budget
    split
    · have hstep:(1+compareTime query counter)+(8*word.length+8)+((vectorBits words).length+1)+(counter.length+1) ≤
        1000*(query.length+cap+L+1):=by omega
      have hm:1000*(query.length+cap+L+1) ≤1000*((word::words).length+1)*(query.length+cap+L+1):=by
        have hpos:1 ≤(word::words).length+1:=by omega
        have h:=Nat.mul_le_mul_right (query.length+cap+L+1) (Nat.mul_le_mul_left 1000 hpos)
        simpa only [Nat.mul_one] using h
      simpa only [Nat.add_assoc] using hstep.trans hm
    · have hstep:(1+compareTime query counter)+(9*word.length+9)+incrementTime counter ≤
        1000*(query.length+cap+L+1):=by omega
      simp only [List.length_cons]
      nlinarith only [hstep,ht]
/-- SAME actual complete binary-index source has a fixed quadratic bound in its two physical input lengths. -/
def runBound (words:List (List Bool)) (query:List Bool):Nat:=1000000*((vectorBits words).length+query.length+1)^2
/-- All actual source copies/branches/returns and genuine halt fit the same physical-byte quadratic. -/
theorem timeBound_le (words:List (List Bool)) (query:List Bool):timeBound words query ≤runBound words query:=by
  let C:=(vectorBits words).length
  let S:=C+query.length+1
  have hv:=SemiprimeD1TensorTapeCodec.vectorBits_length words
  have hc:2*words.length ≤C:=by dsimp [C];omega
  have hb:=budget_cap words query [] (2*words.length) C (by simp) (by rfl)
  have hn:words.length+1 ≤S:=by dsimp [S];omega
  have hinner:query.length+2*words.length+C+1 ≤2*S:=by dsimp [S];omega
  have hh:(words.length+1)*(query.length+2*words.length+C+1) ≤2*S^2:=by
    calc
      _ ≤S*(2*S):=Nat.mul_le_mul hn hinner
      _=2*S^2:=by ring
  have hb':budget query [] words ≤2000*S^2:=by
    calc
      _ ≤1000*((words.length+1)*(query.length+2*words.length+C+1)):=by simpa only [Nat.mul_assoc] using hb
      _ ≤1000*(2*S^2):=Nat.mul_le_mul_left 1000 hh
      _=2000*S^2:=by ring
  have hpos:1 ≤S:=by dsimp [S];omega
  have hs:S ≤S^2:=by simpa only [pow_one] using Nat.pow_le_pow_right hpos (by decide:1 ≤2)
  have hC:C+1 ≤S:=by dsimp [S];omega
  have hlinear:5*C+5 ≤10*S^2:=by omega
  change 5*C+4+budget query [] words+1 ≤1000000*S^2
  omega
/-- Every actual physical vector field is bounded by its acquired source bytes. -/
theorem member_length (words:List (List Bool)) (word:List Bool) (h:word∈words):
    word.length ≤(vectorBits words).length:=by
  induction words with
  | nil=>cases h
  | cons head words ih=>
    have hv:=vector_cons_length head words
    simp only [List.mem_cons] at h
    rcases h with rfl|h
    · omega
    · have ht:=ih h
      omega
/-- Actual selected field or EOF default never exceeds the actual physical cache length. -/
theorem result_length (words:List (List Bool)) (query:List Bool):
    ((words[SemiprimeBitArithmetic.bitValue query]?).getD []).length ≤(vectorBits words).length:=by
  cases h:words[SemiprimeBitArithmetic.bitValue query]? with
  | none=>simp
  | some word=>
    have hm:word∈words:=List.mem_of_getElem? h
    exact member_length words word hm
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedBounds
