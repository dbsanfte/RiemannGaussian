/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerLookupExecution
/-! # Actual scan cost and every physical stack/return cell at every prefix -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackOwnerLookupBounds
open SemiprimeD1StackOwnerLookup SemiprimeD1StackOwnerLookupExecution
open SemiprimeSourceHistogramKeyBits (frame_length)
/-- Exact actual catalogue inventory; both key and owner-ID bytes are paid. -/
theorem records_length (rows:List (List Bool×List Bool)) (tail:List Bool) :
    (records rows tail).length=2*(rows.map (fun x=>x.1.length+x.2.length)).sum+3*rows.length+tail.length+1 := by
  induction rows with
  | nil=>simp [records]
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    simp only [records,List.length_cons,frame_length,ih,List.map_cons,List.sum_cons]
    omega
/-- The trace counts both parsers, every comparison and every failed payload erase. -/
theorem loopTime_le (query:List Bool) (rows:List (List Bool×List Bool)) :
    loopTime query rows≤10*(rows.map (fun x=>x.1.length+x.2.length)).sum+(7*query.length+32)*rows.length+1 := by
  induction rows with
  | nil=>simp [loopTime]
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    have he:=SemiprimeD1StackWordEqualExecution.executionTime_le key query
    simp only [loopTime,List.map_cons,List.sum_cons,List.length_cons]
    split_ifs <;> nlinarith
/-- Fixed polynomial in actual acquired bytes and actual query width. -/
def runBound (query:List Bool) (rows:List (List Bool×List Bool)) : ℕ :=
  100*(query.length+1)*((records rows []).length+1)
theorem time_le (query:List Bool) (rows:List (List Bool×List Bool)) :
    loopTime query rows+1≤runBound query rows := by
  have h:=loopTime_le query rows
  unfold runBound
  rw [records_length]
  simp only [List.length_nil,Nat.add_zero]
  let K:=100*(query.length+1)
  let s:=(rows.map (fun x=>x.1.length+x.2.length)).sum
  have hs:10*s≤K*(2*s) := by
    calc
      _≤(K*2)*s:=Nat.mul_le_mul_right s (by dsimp [K];omega)
      _=_:=by ring
  have hr:(7*query.length+32)*rows.length≤K*(3*rows.length) := by
    calc
      _≤(K*3)*rows.length:=Nat.mul_le_mul_right rows.length (by dsimp [K];omega)
      _=_:=by ring
  have hc:2≤K*2:=by dsimp [K];omega
  calc
    _≤10*s+(7*query.length+32)*rows.length+2:=by omega
    _≤K*(2*s)+K*(3*rows.length)+K*2:=Nat.add_le_add (Nat.add_le_add hs hr) hc
    _=_:=by dsimp [K,s];ring
/-- The physically prepared map/query source has a SAME-code time certificate. -/
def sourceLookup (query:List Bool) (rows:List (List Bool×List Bool)) (tail:List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial query (records rows tail))
      (some (done query rows tail)) (runBound query rows) :=
  ⟨⟨_,source_run query rows tail⟩,time_le query rows⟩
/-- One fixed finite machine, with the same actual lookup trace. -/
def machineLookup (query:List Bool) (rows:List (List Bool×List Bool)) (tail:List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial query (records rows tail)))
      (some (SemiprimeD1StackCalls.configuration (done query rows tail))) (runBound query rows) :=
  SemiprimeD1StackCalls.evalsCorrect (.inr .reader:Stack) (.inr .output:Stack) Label.loop program _ _ _
    (sourceLookup query rows tail)
theorem prefix_fuel_le (query:List Bool) (rows:List (List Bool×List Bool)) (tail:List Bool)
    (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial query (records rows tail))=some out) : fuel≤loopTime query rows+1 := by
  by_contra hn
  have he:fuel=(loopTime query rows+1)+(1+(fuel-(loopTime query rows+2))):=by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz:C.run program 1 (done query rows tail)=none:=rfl
  rw [hz,Option.bind_none] at hr
  cases hr
/-- Every prefix counts all eleven actual Bool roles and actual return frames. -/
theorem prefix_cells (query:List Bool) (rows:List (List Bool×List Bool)) (tail:List Bool)
    (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial query (records rows tail))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤
      12*(query.length+(records rows tail).length+runBound query rows) := by
  let I:=query.length+(records rows tail).length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out (by
    intro k;rcases k with k|k <;> cases k <;> simp [initial,data,SemiprimeD1StackAdder.store,I]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤11*(I+fuel):=by
    calc
      _≤∑_k:Stack,(I+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=(prefix_fuel_le query rows tail fuel out hr).trans (time_le query rows)
  change _≤12*(I+runBound query rows)
  omega
/-- Same complete inventory for every genuine compiled-machine prefix. -/
theorem machine_prefix_cells (query:List Bool) (rows:List (List Bool×List Bool)) (tail:List Bool)
    (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial query (records rows tail))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      12*(query.length+(records rows tail).length+runBound query rows) := by
  have he:=SemiprimeD1StackCalls.run_correct (.inr .reader) (.inr .output) Label.loop program fuel
    (initial query (records rows tail))
  change (C.run program fuel (initial query (records rows tail))).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial query (records rows tail)))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial query (records rows tail)) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells query rows tail fuel out hc
end RiemannGaussian.SemiprimeD1StackOwnerLookupBounds
