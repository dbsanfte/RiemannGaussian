/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerTableExecution
/-! # Whole actual owner-table clock and all eighteen roles/real frames
Scope records and prefix keys are physically consumed/scanned, every constant
output byte is pushed. Their original acquisition remains caller work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackOwnerTableBounds
open SemiprimeD1StackOwnerTable SemiprimeD1StackOwnerTableExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1OwnerPrefixBits (records)

/-- Complete own bound: actual scope scan, full prefix/equality work, all output
and local degree/flag/call/halt work. Fixed before all scope/key/prefix streams. -/
def runBound (key : List Bool) (rows : List (List Bool×Bool)) (scopeWords : List (List Bool)) : ℕ :=
  11*(vectorBits scopeWords).length+SemiprimeD1StackOwnerPrefixBounds.runBound key rows+100
/-- The SAME actual trace satisfies the closed byte/word-width bound. -/
theorem traceTime_le (key : List Bool) (rows : List (List Bool×Bool))
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) : traceTime key rows scopeWords hs≤runBound key rows scopeWords := by
  have hc:=SemiprimeD1StackDigitCountExecution.totalTime_le scopeWords
  have hp:=SemiprimeD1StackOwnerPrefixBounds.time_le key rows
  have ht:=SemiprimeD1OwnerTablePalette.bytes_le (actualDegree scopeWords hs)
    (SemiprimeD1OwnerPrefixBits.scan key rows true true).1 (SemiprimeD1OwnerPrefixBits.scan key rows true true).2
  dsimp only [traceTime,runBound]
  omega
/-- Whole source with all caller data/flags/returns accounted for. -/
def sourceTable (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) :
    StateTransition.EvalsToInTime (C.step program) (initial key (records rows tail) (vectorBits scopeWords))
      (some (done key rows tail scopeWords hs)) (runBound key rows scopeWords) :=
  ⟨⟨_,source_run key rows tail scopeWords hs⟩,traceTime_le key rows scopeWords hs⟩
/-- ONE genuine finite machine; initial data contains no degree/allowed/table
answer, coefficient evaluator, input-dependent instruction or clock. -/
def machineTable (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial key (records rows tail) (vectorBits scopeWords)))
      (some (SemiprimeD1StackCalls.configuration (done key rows tail scopeWords hs))) (runBound key rows scopeWords) :=
  SemiprimeD1StackCalls.evalsCorrect reader output Label.start program _ _ _ (sourceTable key rows tail scopeWords hs)
/-- Every source prefix stops before the SAME literal source's completed halt. -/
theorem prefix_fuel_le (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial key (records rows tail) (vectorBits scopeWords))=some out) :
    fuel≤traceTime key rows scopeWords hs := by
  by_contra hn
  have he:fuel=traceTime key rows scopeWords hs+(1+(fuel-(traceTime key rows scopeWords hs+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run key rows tail scopeWords hs,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz:C.run program 1 (done key rows tail scopeWords hs)=none := rfl
  rw [hz,Option.bind_none] at hr
  cases hr
/-- Every actual prefix counts ALL18 Boolean roles and actual finite-label
return cells, including key/scope retention, query copies and parser work. -/
theorem prefix_cells (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial key (records rows tail) (vectorBits scopeWords))=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤
      19*(key.length+(records rows tail).length+(vectorBits scopeWords).length+runBound key rows scopeWords) := by
  let I:=key.length+(records rows tail).length+(vectorBits scopeWords).length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out (by
    intro k
    rcases k with k|k
    · rcases k with k|k <;> cases k <;>
        simp [initial,data,P.data,SemiprimeD1StackAdder.store,I] <;> omega
    · rcases k with k|k
      · cases k <;> simp [initial,data,D.data,I]
      · cases k;simp [initial,data,I]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hi:(∑k : Stack,(out.data k).length)≤18*(I+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(I+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=(prefix_fuel_le key rows tail scopeWords hs fuel out hr).trans (traceTime_le key rows scopeWords hs)
  change _≤19*(I+runBound key rows scopeWords)
  omega
/-- The SAME all-role/real-return inventory for every compiled-machine prefix. -/
theorem machine_prefix_cells (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial key (records rows tail) (vectorBits scopeWords))))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      19*(key.length+(records rows tail).length+(vectorBits scopeWords).length+runBound key rows scopeWords) := by
  have he:=SemiprimeD1StackCalls.run_correct reader output Label.start program fuel
    (initial key (records rows tail) (vectorBits scopeWords))
  change (C.run program fuel (initial key (records rows tail) (vectorBits scopeWords))).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial key (records rows tail) (vectorBits scopeWords)))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial key (records rows tail) (vectorBits scopeWords)) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells key rows tail scopeWords hs fuel out hc
end RiemannGaussian.SemiprimeD1StackOwnerTableBounds
