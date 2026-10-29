/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryExecution
/-! # Actual whole trace, genuine compiled execution and all115/return prefixes
The clock is the same actual source composition. Its fixed polynomial closure
is a later estimate, not an extra runtime operand or assumed trace supplier.
The front door here has thirteen physical words, not a binary-N initList.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTraceBounds
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackProcedureTrace
namespace E
export SemiprimeD1StackChildGroupFactoryExecution (done timeBound source_run)
end E
namespace P
export SemiprimeD1StackChildGroupFactoryEndpointParse (Fields)
end P
/-- Byte interpretations/domain facts of actual producer tapes; none are runtime operands. -/
structure Valid (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields):Prop where
  id_members:∀id∈ids,id∈(SemiprimeSourceCompactWordBank.acquire 64 a).ids
  environment:i.environment=SemiprimeD1StackSourceEnvironmentEncoding.dictionary ids
  catalogue:i.catalogue=SemiprimeD1StackPacketRowsOriginal.catalogue a
  colour:i.colourIndex=List.replicate coordinate true
  count:ids.length=i.owners.length+i.factors.length
  pairs:i.occurrences=SemiprimeD1StackChildGroupFactoryEndpointKeys.pairs fields
  placements:i.placements=SemiprimeD1StackChildGroupFactoryEndpointKeys.placements fields
  domain:∀f∈fields,SemiprimeBitArithmetic.bitValue f.owner < ids.length ∧
    SemiprimeBitArithmetic.bitValue f.factor < ids.length
  packet_tape:i.packets=SemiprimeD1TensorTapeCodec.vectorBits packets
/-- The whole actual run follows from byte facts, without a supplied run or output answer. -/
theorem source_run (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:Valid i a coordinate ids packets fields):
    ∃t≤E.timeBound i a coordinate ids packets fields,
      C.run program t (initial i)=some (E.done i a coordinate ids packets fields):=
  E.source_run i a coordinate ids packets fields hv.id_members hv.environment hv.catalogue hv.colour hv.count
    hv.pairs hv.placements hv.domain hv.packet_tape
/-- Genuine compiled prepared-configuration execution of the SAME finite program. -/
noncomputable def sourceInTime (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:Valid i a coordinate ids packets fields):
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial i))
      (some (SemiprimeD1StackCalls.configuration (E.done i a coordinate ids packets fields)))
      (E.timeBound i a coordinate ids packets fields):=by
  let h:=source_run i a coordinate ids packets fields hv
  let t:=Classical.choose h
  have ht:=Classical.choose_spec h
  apply SemiprimeD1StackCalls.evalsCorrect (aux .environment) (aux .output) entry program
  exact ⟨⟨t,ht.2⟩,ht.1⟩
/-- An actual halt makes every successfully executed prefix no longer than that same trace. -/
theorem prefix_le {K L:Type} [DecidableEq K] (code:L→C.Instruction K L)
    (start finish out:C.State K L) (time fuel:Nat)
    (ht:C.run code time start=some finish) (hp:finish.pc=none)
    (hr:C.run code fuel start=some out):fuel≤time:=by
  by_contra hn
  have he:fuel=time+(1+(fuel-(time+1))):=by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,ht,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz:C.run code 1 finish=none:=by simp [C.run,C.step,hp]
  rw [hz,Option.bind_none] at hr
  cases hr
/-- Actual successful prefixes are bounded by this whole controller's own source clock. -/
theorem prefix_time (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:Valid i a coordinate ids packets fields) (fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initial i)=some out):fuel≤E.timeBound i a coordinate ids packets fields:=by
  obtain ⟨t,ht,he⟩:=source_run i a coordinate ids packets fields hv
  exact (prefix_le program _ _ _ t fuel he rfl hr).trans ht
/-- Only the thirteen actual front-door word lengths contribute here. -/
def inputBytes (i:Inputs):Nat:=i.environment.length+i.catalogue.length+i.owners.length+i.factors.length+
  i.occurrences.length+i.placements.length+i.packets.length+i.colourIndex.length+i.group.length+
  i.oldAxes.length+i.oldPrecision.length+i.jetAxis.length+i.newPrecision.length+1
/-- Every actual allocated initial word, including all empty callee/shadow words, is covered. -/
theorem input_word_le (i:Inputs) (k:Stack):(input i k).length≤ inputBytes i:=by
  rcases k with k|k|k|k|k|k
  all_goals first
    | exact Nat.zero_le _
    | cases k <;> simp only [input,List.length_nil,inputBytes] <;> omega
/-- Full physical Boolean payload plus actual saved returns; no tape is omitted. -/
def cells (s:C.State Stack Label):Nat:=(∑k:Stack,(s.data k).length)+s.frames.length
private theorem finite_sum_bound {K:Type} [Fintype K] (f:K→Nat) (cap:Nat) (h:∀k,f k≤cap):
    (∑k,f k)≤Fintype.card K*cap:=by
  calc
    _≤∑_k:K,cap:=Finset.sum_le_sum (fun k _=>h k)
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- ALL115 data tapes and actual returns are bounded at EVERY successful source prefix. -/
theorem prefix_cells (i:Inputs) (a coordinate:Nat) (ids packets:List (List Bool)) (fields:List P.Fields)
    (hv:Valid i a coordinate ids packets fields) (fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initial i)=some out):
    cells out≤116*(inputBytes i+E.timeBound i a coordinate ids packets fields+1):=by
  have ht:=prefix_time i a coordinate ids packets fields hv fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputBytes i) (initial i) out
    (input_word_le i) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (initial i) out hr
  have hs:=finite_sum_bound (fun k:Stack=>(out.data k).length) (inputBytes i+fuel) hd
  rw [stack_card] at hs
  change out.frames.length≤0+fuel at hf
  dsimp only [cells]
  nlinarith
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTraceBounds
