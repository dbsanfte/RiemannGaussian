/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldBounds
/-! # Genuine full/acquired-cache fold machine and all111-role prefixes
The full input is original headers plus actual physical child-result vectors.
The ready input is the exact actual acquired context cache. Every private bank,
unused alias shadow, saved Boolean head and real return symbol is counted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldResources
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackJetFoldWords
open SemiprimeD1StackJetFoldSpec SemiprimeD1StackJetFoldContext SemiprimeD1StackJetFoldExecution
open SemiprimeD1StackJetFoldBounds
open SemiprimeD1StackCalls (configuration)
local notation "entry" => Label.local Control.start
/-- Actual physical original input inventory; no rank or decoded-precision word is supplied here. -/
def inputCells (axes:List Nat) (precision:List Bool) (modes:Modes):Nat:=
  (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)).length+
    precision.length+(modeTape modes).length
/-- Actual ready inventory additionally counts both physically acquired unary context caches. -/
def readyCells (axes:List Nat) (precision:List Bool) (modes:Modes):Nat:=inputCells axes precision modes+
  (acquiredHeader axes precision (modeTape modes)).rank.length+
  (acquiredHeader axes precision (modeTape modes)).width.length
/-- Every real word in the complete111-role boundary fits the maximum actual live-word length. -/
theorem data_length_le (v:Values) (B:Nat) (hv:∀s,(v s).length ≤B) (k:Stack):(data v k).length ≤B:=by
  by_cases hex:∃s,k=address s
  · obtain ⟨s,rfl⟩:=hex
    rw [data_get]
    exact hv s
  · have hk:∀s,k≠address s:=by simpa only [not_exists] using hex
    rw [data_other _ _ hk,List.length_nil]
    exact Nat.zero_le _
/-- Each initialized full-source word is paid by its actual three physical input tape lengths. -/
theorem initial_length (axes:List Nat) (precision:List Bool) (modes:Modes) (k:Stack):
    ((initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes)).data k).length ≤
      inputCells axes precision modes:=by
  rw [initial_data]
  apply data_length_le
  intro s
  cases s <;> simp only [values,List.length_nil] <;> unfold inputCells <;> omega
/-- Each initialized ready word includes the actual retained rank/precision values and all original child-result bytes. -/
theorem ready_length (axes:List Nat) (precision:List Bool) (modes:Modes) (k:Stack):
    ((ready axes precision (modeTape modes)).data k).length ≤readyCells axes precision modes:=by
  apply data_length_le
  intro s
  cases s <;> dsimp only [bank,values,readyCells,inputCells,acquiredHeader,List.length_nil] <;> omega
/-- Every successful prefix precedes the same deterministic source's actual final halt. -/
theorem prefix_time {start finish:C.State Stack Label} (B:Nat)
    (he:∃time ≤B,C.run program time start=some finish) (hh:C.run program 1 finish=none)
    (fuel:Nat) (out:C.State Stack Label) (hr:C.run program fuel start=some out):fuel ≤B:=by
  obtain ⟨time,ht,he⟩:=he
  have hf:fuel ≤time:=by
    by_contra hn
    have h:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- No actual full-source prefix exceeds its own fixed-polynomial-per-actual-node source allowance. -/
theorem prefix_fuel (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes))=some out):
    fuel ≤runBound axes precision modes:=prefix_time _ (source_run_bounded axes hp precision modes) rfl fuel out hr
/-- The exact same program's acquired-cache path also has a real bounded halt. -/
theorem ready_prefix_fuel (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (ready axes precision (modeTape modes))=some out):fuel ≤runBound axes precision modes:=
  prefix_time _ (ready_run_bounded axes hp precision modes) rfl fuel out hr
/-- Abstract finite-role summation avoids expanding any concrete operator/source role enumeration. -/
theorem word_sum_le {K:Type} [Fintype K] (d:K→List Bool) (B:Nat) (h:∀k,(d k).length ≤B):
    (∑k:K,(d k).length) ≤Fintype.card K*B:=by
  calc
    _ ≤∑_k:K,B:=Finset.sum_le_sum (fun k _=>h k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- Every actual full-source prefix counts all111allocated data roles and all real nested/recursive returns. -/
theorem prefix_cells (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤112*(inputCells axes precision modes+runBound axes precision modes):=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputCells axes precision modes)
    _ _ (initial_length axes precision modes) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤0+fuel at hf
  have hs:=word_sum_le out.data (inputCells axes precision modes+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel axes hp precision modes fuel out hr
  omega
/-- Ready prefixes count the same entire111-role bank, both actual acquired counters, and every actual return. -/
theorem ready_prefix_cells (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes)
    (fuel:Nat) (out:C.State Stack Label) (hr:C.run program fuel (ready axes precision (modeTape modes))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤112*(readyCells axes precision modes+runBound axes precision modes):=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (readyCells axes precision modes)
    _ _ (ready_length axes precision modes) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤0+fuel at hf
  have hs:=word_sum_le out.data (readyCells axes precision modes+fuel) hd
  rw [stack_card] at hs
  have ht:=ready_prefix_fuel axes hp precision modes fuel out hr
  omega
/-- Genuine complete fixed-machine certificate for exactly the three original physical input words. -/
noncomputable def foldInTime (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes):
    StateTransition.EvalsToInTime machine.step
      (configuration (initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes)))
      (some (configuration (done axes precision modes))) (runBound axes precision modes):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .children) output entry program
  have h:=source_run_bounded axes hp precision modes
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine SAME-machine certificate on its ACTUALLY acquired-cache entry. -/
noncomputable def readyFoldInTime (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes):
    StateTransition.EvalsToInTime machine.step (configuration (ready axes precision (modeTape modes)))
      (some (configuration (done axes precision modes))) (runBound axes precision modes):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .children) output entry program
  have h:=ready_run_bounded axes hp precision modes
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every compiled full-source prefix includes all data words and all real fixed-alphabet return symbols. -/
theorem machine_prefix_cells (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (configuration
      (initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes))))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤112*(inputCells axes precision modes+runBound axes precision modes):=by
  let start:=initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes)
  have he:=SemiprimeD1StackCalls.run_correct (aux .children) output entry program fuel start
  have hh:=he.trans hr
  cases hout:C.run program fuel start with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells axes hp precision modes fuel out hout
/-- Compiled acquired-cache prefixes have the same complete-bank and actual-return accounting. -/
theorem machine_ready_prefix_cells (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (configuration (ready axes precision (modeTape modes))))=some cfg):
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤112*(readyCells axes precision modes+runBound axes precision modes):=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .children) output entry program fuel (ready axes precision (modeTape modes))
  have hh:=he.trans hr
  cases hout:C.run program fuel (ready axes precision (modeTape modes)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact ready_prefix_cells axes hp precision modes fuel out hout
/-- Every actual source transition expands to at most four fixed-machine primitive commands. -/
theorem compile_depth (pc:Label):SemiprimeD1StackBytecode.statementDepth (machine.m pc) ≤4:=
  SemiprimeD1StackCalls.compile_depth entry (program pc)
end RiemannGaussian.SemiprimeD1StackJetFoldResources
