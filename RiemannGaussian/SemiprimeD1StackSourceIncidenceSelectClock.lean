/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectExecution
import RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectScanBound
/-! # Own whole fixed polynomial clock of the literal incidence selector
All variables and candidates are paid by actual acquired unary markers and
catalogue bytes. Every query cap comes from the same closed47-role source and
all prefix/result/rollback byte widths are charged; no old native clock enters.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectClock
open SemiprimeD1StackSourceIncidenceSelect SemiprimeD1StackSourceIncidenceSelectExecution
open SemiprimeD1StackSourceIncidenceSelectLoop SemiprimeD1StackSourceIncidenceSelectVariable
open SemiprimeD1StackSourceIncidenceSelectScanBound
/-- Exact seven-input physical-byte allowance, including both unary marker words and unit slack. -/
def inputSize (i:Inputs) :Nat :=
  (occurrenceTape i).length+(catalogue i).length+i.square.length+i.cube.length+i.fourth.length+i.n+i.F+1
/-- Fixed whole source clock, chosen before every original graph and alphabet. -/
def polynomial (i:Inputs) :Nat :=1000000000000000000000000000000*(inputSize i+1)^16
/-- Elementary physical input projections; no numeric field is supplied to the literal controller. -/
theorem basic_bounds (i:Inputs) :
    0 < inputSize i ∧ (catalogue i).length ≤ inputSize i ∧
      (occurrenceTape i).length+i.square.length+i.cube.length+i.fourth.length ≤ inputSize i ∧
      i.n+i.F ≤ inputSize i :=by
  unfold inputSize
  omega
/-- Every complete actual variable step preserves the prefix byte invariant used to pay its next closed query. -/
theorem loopClock_uniform (rows:List (List Bool×List Bool)) (square cube fourth:List Bool)
    (first:List Bool×List Bool) (entries:List (List Bool×List Bool)) (n:Nat) (ids:List (List Bool)) (S:Nat)
    (hlen:ids.length+n ≤ S) (hw:∀word∈ids,word.length ≤ S)
    (hcat:(SemiprimeD1StackOwnerLookup.records (first::entries) []).length ≤ S)
    (he:∀entry∈first::entries,entry.1.length+entry.2.length ≤ S)
    (hd:(SemiprimeD1StackOwnerLookup.records rows []).length+square.length+cube.length+fourth.length ≤ S) :
    loopClock rows square cube fourth first entries n ids ≤ n*(100000000000000000000000*(S+1)^13)+1 :=by
  induction n generalizing ids with
  | zero=>simp only [loopClock,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | succ n ih=>
    have hv:=variableBound_uniform ids rows square cube fourth first entries S (by omega) hw hcat he hd
    have hnxt:∀word∈(winnerPair ids rows square cube fourth first entries).1::ids,word.length ≤ S:=by
      intro word hword
      rcases List.mem_cons.mp hword with rfl|hword
      · exact hv.2.1
      · exact hw word hword
    have ht:=ih ((winnerPair ids rows square cube fourth first entries).1::ids)
      (by simp only [List.length_cons];omega) hnxt
    simp only [loopClock,Nat.add_mul,Nat.one_mul]
    omega
/-- The whole actual source cap has one fixed degree and constant in its physical acquired input bytes. -/
theorem timeBound_le (i:Inputs) :timeBound i ≤ polynomial i :=by
  let S:=inputSize i
  have hS:0 < S:=(basic_bounds i).1
  have hcat:(SemiprimeD1StackOwnerLookup.records (i.first::i.entries) []).length ≤ S:=(basic_bounds i).2.1
  have hdata:(SemiprimeD1StackOwnerLookup.records i.rows []).length+i.square.length+i.cube.length+i.fourth.length ≤ S:=
    (basic_bounds i).2.2.1
  have hN:i.n+i.F ≤ S:=(basic_bounds i).2.2.2
  have he:∀entry∈i.first::i.entries,entry.1.length+entry.2.length ≤ S:=by
    intro entry hentry
    exact (SemiprimeD1StackSourceIncidenceBytes.record_width_le entry _ hentry).trans hcat
  have ht:=loopClock_uniform i.rows i.square i.cube i.fourth i.first i.entries (i.n+i.F) [] S
    (by simpa only [List.length_nil,Nat.zero_add] using hN) (by simp) hcat he hdata
  have hclock:loopClock i.rows i.square i.cube i.fourth i.first i.entries (i.n+i.F) [] ≤
      100000000000000000000000*(S+1)^14+1:=by
    calc
      _ ≤ (i.n+i.F)*(100000000000000000000000*(S+1)^13)+1:=ht
      _ ≤ (S+1)*(100000000000000000000000*(S+1)^13)+1:=Nat.add_le_add_right
        (Nat.mul_le_mul_right _ (by omega : i.n+i.F ≤ S+1)) _
      _=100000000000000000000000*(S+1)^14+1:=by ring
  have h1416:(S+1)^14 ≤ (S+1)^16:=SemiprimeD1StackSourceIncidenceBounds.pow_mono (S+1) (by omega) 14 16 (by decide)
  have h116:S+1 ≤ (S+1)^16:=by simpa only [pow_one] using
    SemiprimeD1StackSourceIncidenceBounds.pow_mono (S+1) (by omega) 1 16 (by decide)
  have hm:=Nat.mul_le_mul_left 100000000000000000000000 h1416
  change 5*(i.n+i.F)+12+loopClock i.rows i.square i.cube i.fourth i.first i.entries (i.n+i.F) []+1 ≤
    1000000000000000000000000000000*(S+1)^16
  omega
/-- SAME whole literal prepared selector uses its own fixed physical-input polynomial clock. -/
theorem source_run_bounded (i:Inputs) :
    ∃t ≤ polynomial i,SemiprimeD1StackCalls.run program t (source i)=some (done i) :=by
  obtain ⟨t,ht,hr⟩:=source_run i
  exact ⟨t,ht.trans (timeBound_le i),hr⟩
/-- Genuine same compiled finite machine has this whole-source bound; acquisition of the seven actual inputs is caller work. -/
noncomputable def machineSelector (i:Inputs) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source i))
      (some (SemiprimeD1StackCalls.configuration (done i))) (polynomial i) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (queryStack (Q.aux .source)) selected (.local .start) program
  let h:=source_run_bounded i
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceIncidenceSelectClock
