/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksBounds
/-! # Every actual31-role data bank and real return word, including ready caches -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksStorage
open SemiprimeD1StackJetBlocks SemiprimeD1StackJetBlocksView SemiprimeD1StackJetBlocksReady
open SemiprimeD1StackJetBlocksExecution SemiprimeD1StackJetBlocksBounds
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- All actual four-input source words are charged without an initial-height supplier. -/
theorem initial_role_bound (axes:List Nat) (precision:List Bool) (q:Nat) (words:List (List Bool)) (k:Stack) :
    ((source axes precision q words).data k).length≤resource axes precision q words :=by
  have hq:q≤q*(axes.prod+1):=Nat.le_mul_of_pos_right q (Nat.succ_pos _)
  rcases k with k|k
  · have h:=SemiprimeD1StackJetContextBounds.initial_length axes precision k
    exact h.trans (by unfold resource;omega)
  · cases k <;> simp [source,initial,input,privateInput] <;> unfold resource <;> omega
/-- Every successful prefix precedes this SAMEactual source's proved genuine halt. -/
theorem prefix_fuel (axes:List Nat) (hp:∀r∈axes,0<r) (precision:List Bool) (q:Nat)
    (words:List (List Bool)) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source axes precision q words)=some out) :
    fuel≤10000*(resource axes precision q words+1)^2 :=by
  obtain ⟨t,ht,he⟩:=source_run_bounded axes hp precision q words
  have hf:fuel≤t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done (contextResult axes precision) axes.prod q words)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All31 actual data roles and every real return cell are included at every reached prefix. -/
theorem prefix_cells (axes:List Nat) (hp:∀r∈axes,0<r) (precision:List Bool) (q:Nat)
    (words:List (List Bool)) (fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (source axes precision q words)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤1000000*(resource axes precision q words+1)^2 :=by
  let S:=resource axes precision q words
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel S _ _ (initial_role_bound axes precision q words) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤31*(S+fuel):=by
    calc
      _≤∑_k:Stack,(S+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel axes hp precision q words fuel out hr
  change fuel≤10000*(S+1)^2 at ht
  have hp0:S≤(S+1)^2:=by nlinarith
  change _≤1000000*(S+1)^2
  omega
/-- Every genuine compiled source prefix counts all31roles plus its actual physical return word. -/
theorem machine_prefix_cells (axes:List Nat) (hp:∀r∈axes,0<r) (precision:List Bool) (q:Nat)
    (words:List (List Bool)) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (source axes precision q words)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤1000000*(resource axes precision q words+1)^2 :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .coefficients) (aux .output) (ctl .start) program fuel (source axes precision q words)
  have hh:=he.trans hr
  cases hout:SemiprimeD1StackCalls.run program fuel (source axes precision q words) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hc:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells axes hp precision q words fuel out hout
/-- Every already acquired context word is retained and charged, even if the block loop never reads it. -/
def readySize (context:X.Stack→List Bool) (rank q:Nat) (words:List (List Bool)) :Nat :=
  (∑k:X.Stack,(context k).length)+(vectorBits words).length+q*(rank+1)+1
/-- The ready bank accounts for all15 actual context words and all16 new words. -/
theorem ready_role_bound (context:X.Stack→List Bool) (rank q:Nat) (words:List (List Bool)) (k:Stack) :
    ((ready context q words).data k).length≤readySize context rank q words :=by
  have hq:q≤q*(rank+1):=Nat.le_mul_of_pos_right q (Nat.succ_pos _)
  rcases k with k|k
  · have h:(context k).length≤∑j:X.Stack,(context j).length:=
      Finset.single_le_sum (fun j _=>Nat.zero_le (context j).length) (Finset.mem_univ k)
    exact h.trans (by unfold readySize;omega)
  · cases k <;> simp [ready,data] <;> unfold readySize <;> omega
/-- All31 ready-entry data roles and real return cells are bounded without re-running the context supplier. -/
theorem ready_prefix_cells (context:X.Stack→List Bool) (rank q:Nat)
    (hcontext:context X.rankCache=List.replicate rank true) (words:List (List Bool)) (fuel:Nat)
    (out:C.State Stack Label) (hr:SemiprimeD1StackCalls.run program fuel (ready context q words)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤100000*readySize context rank q words :=by
  obtain ⟨t,ht,he⟩:=ready_run_linear context rank q hcontext words
  have ht0:fuel≤t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done context rank q words)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  let S:=readySize context rank q words
  have hb:(vectorBits words).length+q*(rank+1)+1≤S:=by dsimp only [S,readySize];omega
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel S _ _ (ready_role_bound context rank q words) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤31*(S+fuel):=by
    calc
      _≤∑_k:Stack,(S+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  change _≤100000*S
  omega
end RiemannGaussian.SemiprimeD1StackJetBlocksStorage
