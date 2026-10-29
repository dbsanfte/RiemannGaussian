/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeBounds
/-! # Genuine compiled prepared-input enumeration and all-prefix resources
This front door explicitly receives catalogue and WIDTH bytes. It is not
claimed to initialize from binary N alone or to acquire packet metadata.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeResources
open SemiprimeD1StackWeightedMode SemiprimeD1StackWeightedModeView
open SemiprimeD1StackWeightedModeExecution SemiprimeD1StackWeightedModeBounds
open SemiprimeD1StackWeightedModeCapacities
open SemiprimeD1StackCalls (configuration)
local notation "main" => (Sum.inl Control.start : Label)
/-- Every original mode coordinate pays its true tag and actual framed weight bytes. -/
theorem vector_length (ws:List Nat) :(vector ws).length=2*ws.sum+2*ws.length+1:=by
  induction ws with
  | nil=>rfl
  | cons w ws ih=>rw [vector_length_cons,ih,List.sum_cons,List.length_cons];omega
/-- Actual byte size, before any enumeration has taken place. -/
def inputSize (ws:List Nat) (width:Nat) :Nat:=(vector ws).length+width+2
/-- The saved-path allowance is polynomial in the acquired physical input size. -/
theorem capacity_bytes (ws:List Nat) (width:Nat) :
    capacity ws (width-1) 1 ≤3*(inputSize ws width)^2:=by
  let I:=inputSize ws width
  have hI:1 ≤ I:=by dsimp [I,inputSize];omega
  have hB:(vector ws).length ≤ I:=by dsimp [I,inputSize];omega
  have hW:width+1 ≤ I:=by dsimp [I,inputSize];omega
  have hd:ws.length ≤ (vector ws).length:=by rw [vector_length];omega
  have hm:ws.length*(width-1+1) ≤ I*I:=Nat.mul_le_mul (hd.trans hB) (by omega)
  have hs:I ≤ I*I:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left I hI
  unfold capacity
  change _ ≤ 3*I^2
  have hb:(vector ws).length+1+(width-1)+1 ≤ I:=by dsimp [I,inputSize];omega
  nlinarith only [hm,hs,hb]
/-- A fixed cubic byte polynomial pays each actual feasible visit. -/
theorem coefficient_bytes (ws:List Nat) (width:Nat) :
    visitCoefficient ws width ≤10000*(inputSize ws width)^3:=by
  let I:=inputSize ws width
  have hI:1 ≤ I:=by dsimp [I,inputSize];omega
  have hd:ws.length+1 ≤ I:=by dsimp [I,inputSize];rw [vector_length];omega
  have hc:=capacity_bytes ws width
  have hm:=Nat.mul_le_mul hc hd
  change capacity ws (width-1) 1*(ws.length+1) ≤3*I^2*I at hm
  have hs:I ≤ I^3:=by simpa only [pow_one] using Nat.pow_le_pow_right hI (by omega:1 ≤ 3)
  unfold visitCoefficient
  have he:(vector ws).length+width+2=I:=rfl
  nlinarith only [hm,hs,he]
/-- Whole actual clock, including reversal, is cubic in input bytes per feasible visit. -/
theorem runBound_bytes (ws:List Nat) (width:Nat) :
    runBound ws width ≤10000*(inputSize ws width)^3*SemiprimeD1WeightedTuples.visits ws (width-1):=
  Nat.mul_le_mul_right _ (coefficient_bytes ws width)
/-- Concrete final halt bounds all successful prefixes of the same deterministic source. -/
theorem prefix_fuel (ws:List Nat) (hw:∀w∈ws,0 < w) (width fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initial (vector ws) (unary width))=some out) :fuel ≤ runBound ws width:=by
  obtain ⟨t,ht,he⟩:=source_run_bounded ws hw width
  have hh:C.run program 1 (done ws width)=none:=rfl
  have hf:fuel ≤ t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Both real prepared inputs are charged at every actual prefix. -/
theorem initial_length (ws:List Nat) (width:Nat) (k:Stack) :
    ((initial (vector ws) (unary width)).data k).length ≤(vector ws).length+width:=by
  cases k <;> simp only [initial,input,unary_length,List.length_nil] <;> omega
/-- Finite role summation is independent of the concrete enum representation. -/
theorem word_sum_le {K:Type} [Fintype K] (d:K→List Bool) (n:Nat) (h:∀k,(d k).length ≤ n) :
    (∑k:K,(d k).length) ≤Fintype.card K*n:=by
  calc
    _ ≤ ∑_k:K,n:=Finset.sum_le_sum (fun k _=>h k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- All seventeen real data roles, activation bytes and actual return symbols are counted. -/
theorem prefix_cells (ws:List Nat) (hw:∀w∈ws,0 < w) (width fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initial (vector ws) (unary width))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤
      18*((vector ws).length+width+runBound ws width):=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel ((vector ws).length+width)
    _ _ (initial_length ws width) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length ≤0+fuel at hf
  have hs:=word_sum_le out.data ((vector ws).length+width+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_fuel ws hw width fuel out hr
  omega
/-- A genuine finite-machine certificate for the explicitly prepared physical entry. -/
noncomputable def modesInTime (ws:List Nat) (hw:∀w∈ws,0 < w) (width:Nat) :
    StateTransition.EvalsToInTime machine.step
      (configuration (initial (vector ws) (unary width)))
      (some (configuration (done ws width))) (runBound ws width):=by
  apply SemiprimeD1StackCalls.evalsCorrect Stack.width Stack.output main program
  have h:=source_run_bounded ws hw width
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- All compiled-machine prefixes count the same actual input, data and return bytes. -/
theorem machine_prefix_cells (ws:List Nat) (hw:∀w∈ws,0 < w) (width fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel]
      (some (configuration (initial (vector ws) (unary width))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      18*((vector ws).length+width+runBound ws width):=by
  have he:=SemiprimeD1StackCalls.run_correct Stack.width Stack.output main program fuel
    (initial (vector ws) (unary width))
  have hh:=he.trans hr
  cases hout:C.run program fuel (initial (vector ws) (unary width)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells ws hw width fuel out hout
end RiemannGaussian.SemiprimeD1StackWeightedModeResources
