/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerPrefixExecution
/-! # Closed physical owner-prefix costs and all ten roles/real return cells
The scan consumes original records; it never asks for an allowed-value answer.
Its cost is linear in prefix bytes times actual binary query-key width.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackOwnerPrefixBounds
open SemiprimeD1StackOwnerPrefix SemiprimeD1StackOwnerPrefixExecution
open SemiprimeD1OwnerPrefixBits (records records_length scan_original)

/-- All actual field/copy/equality/read branches summed over original records. -/
theorem loopTime_le (query : List Bool) (rows : List (List Bool×Bool)) :
    loopTime query rows≤10*(rows.map (fun x=>x.1.length)).sum+(7*query.length+24)*rows.length+3 := by
  induction rows with
  | nil=>simp only [loopTime,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    have he:=SemiprimeD1StackWordEqualExecution.executionTime_le key query
    simp only [loopTime,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith
/-- Fixed SAME-program bound before every binary key and physical prefix. -/
def runBound (query : List Bool) (rows : List (List Bool×Bool)) : ℕ :=
  100*(query.length+1)*((records rows []).length+1)
/-- The exact source trace, including every call and halt, obeys this bound. -/
theorem time_le (query : List Bool) (rows : List (List Bool×Bool)) : loopTime query rows+1≤runBound query rows := by
  have h:=loopTime_le query rows
  unfold runBound
  rw [records_length]
  simp only [List.length_nil,Nat.add_zero]
  let K:=100*(query.length+1)
  let s:=(rows.map (fun x=>x.1.length)).sum
  have hs:10*s≤K*(2*s) := by
    calc
      _ ≤ (K*2)*s := Nat.mul_le_mul_right s (by dsimp [K];omega)
      _ = _ := by ring
  have hr:(7*query.length+24)*rows.length≤K*(3*rows.length) := by
    calc
      _ ≤ (K*3)*rows.length := Nat.mul_le_mul_right rows.length (by dsimp [K];omega)
      _ = _ := by ring
  have hc:4≤K*2 := by dsimp [K];omega
  calc
    _ ≤ 10*s+(7*query.length+24)*rows.length+4 := by omega
    _ ≤ K*(2*s)+K*(3*rows.length)+K*2 := Nat.add_le_add (Nat.add_le_add hs hr) hc
    _ = _ := by dsimp [K,s];ring
/-- Actual complete source execution, retaining every unread suffix byte. -/
def sourceScan (query : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial query (records rows tail))
      (some (done query rows tail)) (runBound query rows) :=
  ⟨⟨_,source_run query rows tail⟩,time_le query rows⟩
/-- Genuine SAME finite machine with no source-length/count/equality premise. -/
def machineScan (query : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial query (records rows tail)))
      (some (SemiprimeD1StackCalls.configuration (done query rows tail))) (runBound query rows) :=
  SemiprimeD1StackCalls.evalsCorrect (Sum.inr Aux.reader : Stack) (Sum.inr Aux.output : Stack)
    (Label.loop true true) program _ _ _
    (sourceScan query rows tail)
/-- Every original finite-wire prefix, including duplicate/conflicting records,
produces the exact original pair of compatible owner values. -/
theorem output_original {n : ℕ} (wire : Fin n) (fixed : List (Fin n×Bool))
    (encode : Fin n→List Bool) (he : ∀i,SemiprimeBitArithmetic.bitValue (encode i)=i.val)
    (tail : List Bool) :
    (done (encode wire) (fixed.map (fun x=>(encode x.1,x.2))) tail).data (.inr .output)=
      [SemiprimeD1RootOwnerTables.allowed fixed wire false,SemiprimeD1RootOwnerTables.allowed fixed wire true] := by
  change [(SemiprimeD1OwnerPrefixBits.scan _ _ true true).1,(SemiprimeD1OwnerPrefixBits.scan _ _ true true).2]=_
  rw [scan_original wire fixed encode he]
/-- No successful physical prefix extends beyond the actual literal halt. -/
theorem prefix_fuel_le (query : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial query (records rows tail))=some out) : fuel≤loopTime query rows+1 := by
  by_contra hn
  have he:fuel=(loopTime query rows+1)+(1+(fuel-(loopTime query rows+2))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz:C.run program 1 (done query rows tail)=none := rfl
  rw [hz,Option.bind_none] at hr
  cases hr
/-- EVERY prefix counts all ten actual Boolean roles, all unread suffix/cache
bytes and all real finite-label return cells; no pointer/stack is omitted. -/
theorem prefix_cells (query : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial query (records rows tail))=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤
      11*(query.length+(records rows tail).length+runBound query rows) := by
  let I:=query.length+(records rows tail).length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out (by
    intro k;rcases k with k|k <;> cases k <;> simp [initial,data,SemiprimeD1StackAdder.store,I]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k : Stack,(out.data k).length)≤10*(I+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(I+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=(prefix_fuel_le query rows tail fuel out hr).trans (time_le query rows)
  change _≤11*(I+runBound query rows)
  omega
/-- The same all-role/return inventory for the genuine compiled machine. -/
theorem machine_prefix_cells (query : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial query (records rows tail))))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      11*(query.length+(records rows tail).length+runBound query rows) := by
  have he:=SemiprimeD1StackCalls.run_correct (.inr .reader) (.inr .output) (.loop true true) program fuel
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
end RiemannGaussian.SemiprimeD1StackOwnerPrefixBounds
