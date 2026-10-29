/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentExecution
/-! # Own quadratic whole-prefix clock, all25words and genuine return cells
Every count/key is acquired from the actual encoded prefix. The cache lookup
and extension entries charge their actual retained physical word lengths.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentBounds
open SemiprimeD1StackSourceEnvironment SemiprimeD1StackSourceEnvironmentExecution
open SemiprimeD1StackSourceEnvironmentEncoding SemiprimeD1StackSourceEnvironmentView
open SemiprimeD1StackSourceEnvironmentReverse SemiprimeD1StackSourceEnvironmentPrefix
open SemiprimeD1StackCalls (run configuration)
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Whole actual prefix-vector byte count, including tags, padding and terminal false. -/
def inputSize (ids:List (List Bool)) :Nat :=(vectorBits ids).length+1
/-- Fixed before every prefix/selected candidate sequence. -/
def runBound (ids:List (List Bool)) :Nat :=2000*(inputSize ids)^2
/-- Reversing field order preserves the entire actual input byte inventory. -/
theorem vector_reverse_length (ids:List (List Bool)) :(vectorBits ids.reverse).length=(vectorBits ids).length :=by
  simp only [SemiprimeD1TensorTapeCodec.vectorBits_length,List.map_reverse,List.sum_reverse,List.length_reverse]
/-- Own actual primitive/call sum is quadratic in physical prefix bytes. -/
theorem timeBound_le (ids:List (List Bool)) :timeBound ids≤runBound ids :=by
  have hr:=reverseClock_le ids
  have ho:=oldClock_le ids.reverse
  rw [vector_reverse_length] at ho
  unfold timeBound runBound inputSize
  rw [vector_reverse_length]
  nlinarith only [hr,ho,Nat.zero_le ((vectorBits ids).length^2)]
/-- Same actual whole-prefix source executes within its own quadratic bit-stack allowance. -/
theorem source_run_bounded (ids:List (List Bool)) :
    ∃q≤runBound ids,run program q (source ids)=some (done ids) :=by
  obtain ⟨q,hq,hr⟩:=source_run ids
  exact ⟨q,hq.trans (timeBound_le ids),hr⟩
/-- Literal initialization contains exactly the retained physical prefix word and no acquired answer. -/
theorem initial_length (pfx:List Bool) (k:Stack) :((initial pfx).data k).length≤pfx.length :=by
  change (input pfx k).length≤pfx.length
  unfold input
  by_cases h:k=aux .prefix
  · subst k;simp
  · rw [Function.update_of_ne h]
    exact Nat.zero_le _
/-- A successful prefix cannot continue past the same actual source's true final halt. -/
theorem prefix_time {start finish:C.State Stack Label} (B:Nat)
    (he:∃q≤B,run program q start=some finish) (hh:run program 1 finish=none)
    (fuel:Nat) (out:C.State Stack Label) (hr:run program fuel start=some out) :fuel≤B :=by
  obtain ⟨q,hq,he⟩:=he
  have hf:fuel≤q:=by
    by_contra hn
    have h:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hh,Option.bind_none] at hr
    cases hr
  exact hf.trans hq
/-- Finite physical-bank sum, independent of all actual prefix values. -/
theorem word_sum_le {K:Type} [Fintype K] (words:K→List Bool) (B:Nat)
    (h:∀k,(words k).length≤B) :(∑k:K,(words k).length)≤Fintype.card K*B :=by
  calc
    _≤∑_k:K,B:=Finset.sum_le_sum (fun k _=>h k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]
/-- Every actual whole-source prefix pays all25data tapes and every real return frame. -/
theorem prefix_cells (ids:List (List Bool)) (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (source ids)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤100000*(inputSize ids)^2 :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (vectorBits ids).length _ out (initial_length _) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel (source ids) out hr
  change out.frames.length≤0+fuel at hf
  have hs:=word_sum_le out.data ((vectorBits ids).length+fuel) hd
  rw [stack_card] at hs
  have ht:=prefix_time _ (source_run_bounded ids) rfl fuel out hr
  have hL:(vectorBits ids).length≤(inputSize ids)^2:=by
    unfold inputSize
    nlinarith only [Nat.zero_le ((vectorBits ids).length^2)]
  unfold runBound at ht
  omega
/-- The actual compiled whole source starts with its one physical prefix vector at genuine initList. -/
theorem initial_eq (pfx:List Bool) :Turing.initList machine pfx=configuration (initial pfx) :=by
  have he:initial pfx=SemiprimeD1StackCalls.initial (aux .prefix) (ctl .acquire) pfx:=by
    unfold initial input SemiprimeD1StackCalls.initial
    congr 1
    funext k
    by_cases h:k=aux .prefix <;> simp [Function.update,h]
  rw [he]
  exact (SemiprimeD1StackCalls.initial_correct (aux .prefix) (aux .dictionary) (ctl .acquire) program pfx).symm
/-- Genuine compiled whole-prefix source certificate, with no input count/key/dictionary. -/
noncomputable def environmentInTime (ids:List (List Bool)) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine (vectorBits ids))
      (some (configuration (done ids))) (runBound ids) :=by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect (aux .prefix) (aux .dictionary) (ctl .acquire) program
  let h:=source_run_bounded ids
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every reached genuine machine prefix counts every actual role and return symbol. -/
theorem machine_prefix_cells (ids:List (List Bool)) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine (vectorBits ids)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤100000*(inputSize ids)^2 :=by
  rw [initial_eq] at hr
  have he:=SemiprimeD1StackCalls.run_correct (aux .prefix) (aux .dictionary) (ctl .acquire) program fuel (source ids)
  have hh:=he.trans hr
  cases hout:run program fuel (source ids) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells ids fuel out hout
/-- Actual retained cache/input byte inventory for one prepared lookup or chosen-ID extension. -/
def cacheSize (ids:List (List Bool)) (chosen q pfx:List Bool) :Nat :=
  (dictionary ids).length+(variableKey ids.length).length+chosen.length+q.length+pfx.length+1
/-- Same physical cache bank initializes every work/output/found field empty. -/
theorem cache_initial_bound (ids:List (List Bool)) (chosen q pfx:List Bool) (k:Stack) :
    (view (dictionary ids) (variableKey ids.length) chosen q pfx [] [] [] [] [] k).length≤cacheSize ids chosen q pfx :=by
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp only [view,Sum.elim_inl,L.data,SemiprimeD1StackAdder.store,List.length_nil] <;> unfold cacheSize <;> omega
    · cases k <;> simp only [view,Sum.elim_inl,L.data,List.length_nil] <;> unfold cacheSize <;> omega
  · cases k <;> simp only [view,Sum.elim_inr,List.length_nil] <;> unfold cacheSize <;> omega
/-- Paid query/copy/scan/marker/drain/halt work is quadratic in the actual retained cache operands. -/
theorem lookup_run_bounded (ids:List (List Bool)) (chosen q pfx:List Bool) :
    ∃t≤201*(cacheSize ids chosen q pfx)^2,
      run program t (lookupReady ids chosen q pfx)=some (lookupDone ids chosen q pfx) :=by
  obtain ⟨t,ht,hr⟩:=lookup_run ids chosen q pfx
  have hq:q.length+1≤cacheSize ids chosen q pfx:=by unfold cacheSize;omega
  have hd:(dictionary ids).length+1≤cacheSize ids chosen q pfx:=by unfold cacheSize;omega
  have hm:=Nat.mul_le_mul hq hd
  refine ⟨t,ht.trans ?_,hr⟩
  nlinarith only [hm]
/-- Paid chosen-ID extension uses the SAMEactual compact counter and a fixed quadratic physical-cache cap. -/
theorem extend_run_bounded (ids:List (List Bool)) (chosen q pfx:List Bool) :
    ∃t≤201*(cacheSize ids chosen q pfx)^2,
      run program t (extendReady ids chosen q pfx)=some (extendDone ids chosen q pfx) :=by
  obtain ⟨t,ht,hr⟩:=extend_run ids chosen q pfx
  have hs:chosen.length+(variableKey ids.length).length+1≤cacheSize ids chosen q pfx:=by unfold cacheSize;omega
  have hp:cacheSize ids chosen q pfx≤(cacheSize ids chosen q pfx)^2:=Nat.le_pow (by decide:0<(2:Nat))
  refine ⟨t,?_,hr⟩
  omega
/-- Complete25word/real-return inventory for either actual cache operation, from its SAMEsuccessful trace. -/
theorem cache_prefix_cells (ids:List (List Bool)) (chosen q pfx:List Bool) (isLookup:Bool)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (if isLookup then lookupReady ids chosen q pfx else extendReady ids chosen q pfx)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤10000*(cacheSize ids chosen q pfx)^2 :=by
  have he:∃t≤201*(cacheSize ids chosen q pfx)^2,run program t
      (if isLookup then lookupReady ids chosen q pfx else extendReady ids chosen q pfx)=
        some (if isLookup then lookupDone ids chosen q pfx else extendDone ids chosen q pfx):=by
    cases isLookup
    · exact extend_run_bounded ids chosen q pfx
    · exact lookup_run_bounded ids chosen q pfx
  have ht:=prefix_time _ he (by cases isLookup <;> rfl) fuel out hr
  have hb:∀k,(((if isLookup then lookupReady ids chosen q pfx else extendReady ids chosen q pfx):C.State Stack Label).data k).length≤cacheSize ids chosen q pfx:=by
    cases isLookup <;> exact cache_initial_bound ids chosen q pfx
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (cacheSize ids chosen q pfx) _ out hb hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  have hframes:((if isLookup then lookupReady ids chosen q pfx else extendReady ids chosen q pfx):C.State Stack Label).frames=[]:=by
    cases isLookup <;> rfl
  rw [hframes,List.length_nil] at hf
  have hsum:=word_sum_le out.data (cacheSize ids chosen q pfx+fuel) hd
  rw [stack_card] at hsum
  have hp:cacheSize ids chosen q pfx≤(cacheSize ids chosen q pfx)^2:=Nat.le_pow (by decide:0<(2:Nat))
  omega
/-- Every literal transition has fixed fundamental command depth before the selected prefix. -/
theorem compile_depth (pc:Label) :SemiprimeD1StackBytecode.statementDepth (machine.m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth (ctl .acquire) (program pc)
/-- Genuine compiled fixed-program cache lookup certificate uses only its actual retained physical operands. -/
noncomputable def lookupInTime (ids:List (List Bool)) (chosen q pfx:List Bool) :
    StateTransition.EvalsToInTime machine.step (configuration (lookupReady ids chosen q pfx))
      (some (configuration (lookupDone ids chosen q pfx))) (201*(cacheSize ids chosen q pfx)^2) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .prefix) (aux .dictionary) (ctl .acquire) program
  let h:=lookup_run_bounded ids chosen q pfx
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine compiled fixed-program extension certificate pays the actual key/candidate normalization and return. -/
noncomputable def extendInTime (ids:List (List Bool)) (chosen q pfx:List Bool) :
    StateTransition.EvalsToInTime machine.step (configuration (extendReady ids chosen q pfx))
      (some (configuration (extendDone ids chosen q pfx))) (201*(cacheSize ids chosen q pfx)^2) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .prefix) (aux .dictionary) (ctl .acquire) program
  let h:=extend_run_bounded ids chosen q pfx
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Both prepared compiled operation entries count all25physical data roles and real returns. -/
theorem cache_machine_prefix_cells (ids:List (List Bool)) (chosen q pfx:List Bool) (isLookup:Bool)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun x=>x.bind machine.step)^[fuel]
      (some (configuration (if isLookup then lookupReady ids chosen q pfx else extendReady ids chosen q pfx)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤10000*(cacheSize ids chosen q pfx)^2 :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .prefix) (aux .dictionary) (ctl .acquire) program fuel
    (if isLookup then lookupReady ids chosen q pfx else extendReady ids chosen q pfx)
  have hh:=he.trans hr
  cases hout:run program fuel (if isLookup then lookupReady ids chosen q pfx else extendReady ids chosen q pfx) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact cache_prefix_cells ids chosen q pfx isLookup fuel out hout
/-- Actual empty-cache initialization has no hidden dictionary/key advice; retained physical operands pay every word. -/
theorem initialize_initial_bound (chosen q pfx:List Bool) (k:Stack) :
    ((initializeReady chosen q pfx).data k).length≤cacheSize [] chosen q pfx :=by
  by_cases h:k=aux .dictionary
  · subst k;exact Nat.zero_le _
  · have he:(initializeReady chosen q pfx).data k=(lookupReady [] chosen q pfx).data k:=by
      rcases k with k|k
      · rfl
      · cases k <;> first | rfl | exact (h rfl).elim
    rw [he]
    exact cache_initial_bound [] chosen q pfx k
/-- All25initialization words and real returns are paid even when caller ID/query/prefix words are retained. -/
theorem initialize_prefix_cells (chosen q pfx:List Bool) (fuel:Nat) (out:C.State Stack Label)
    (hr:run program fuel (initializeReady chosen q pfx)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤100*(cacheSize [] chosen q pfx) :=by
  have ht:=prefix_time 2 ⟨2,by omega,initialize_run chosen q pfx⟩ rfl fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (cacheSize [] chosen q pfx) _ out
    (initialize_initial_bound chosen q pfx) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:=word_sum_le out.data (cacheSize [] chosen q pfx+fuel) hd
  rw [stack_card] at hs
  have hp:1≤cacheSize [] chosen q pfx:=by unfold cacheSize;omega
  omega
/-- Actual initialization is a genuine same-program two-transition source certificate. -/
def initializeInTime (chosen q pfx:List Bool) :
    StateTransition.EvalsToInTime machine.step (configuration (initializeReady chosen q pfx))
      (some (configuration (initializeDone chosen q pfx))) 2 :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .prefix) (aux .dictionary) (ctl .acquire) program
  exact ⟨⟨2,initialize_run chosen q pfx⟩,Nat.le_refl 2⟩
/-- Every compiled initialization prefix includes all25data words and actual return cells. -/
theorem initialize_machine_prefix_cells (chosen q pfx:List Bool) (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun x=>x.bind machine.step)^[fuel] (some (configuration (initializeReady chosen q pfx)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤100*(cacheSize [] chosen q pfx) :=by
  have he:=SemiprimeD1StackCalls.run_correct (aux .prefix) (aux .dictionary) (ctl .acquire) program fuel
    (initializeReady chosen q pfx)
  have hh:=he.trans hr
  cases hout:run program fuel (initializeReady chosen q pfx) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact initialize_prefix_cells chosen q pfx fuel out hout
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentBounds
