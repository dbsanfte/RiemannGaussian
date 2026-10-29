/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Bounds
/-! # Genuine physical unary-width entry and all30 tapes plus actual return cells -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Storage
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Execution SemiprimeD1StackSourceAlphabet64Bounds
attribute [local irreducible] runBound result
/-- Actual initial store has ONE physical unary-width source word and no other operand/advice. -/
theorem input_eq (markers:List Bool) (k:Stack) :
    input markers k=(if k=aux .source then markers else []) :=by
  rcases k with k|k
  · rfl
  · simp [input,aux]
/-- Actual prepared unary-width input is exactly the genuine finite-machine one-word input tape. -/
theorem initial_eq (markers:List Bool) :
    Turing.initList machine markers=SemiprimeD1StackCalls.configuration (initial markers) :=by
  have hs:SemiprimeD1StackCalls.initial (aux .source) .start markers=initial markers:=by
    apply congrArg (fun d=>(⟨some .start,none,none,d,[]⟩:C.State Stack Label))
    funext k
    exact (input_eq markers k).symm
  exact (SemiprimeD1StackCalls.initial_correct (aux .source) (aux .output) .start program markers).symm.trans
    (congrArg SemiprimeD1StackCalls.configuration hs)
/-- Own complete genuine machine certificate; this is unary-width acquisition, not N-only selection. -/
noncomputable def sourceInTime (a:Nat) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine (List.replicate a true))
      (some (SemiprimeD1StackCalls.configuration (done a))) (10000*(a+1)*(64^a+1)) :=by
  have hcert:StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (List.replicate a true)))
      (some (SemiprimeD1StackCalls.configuration (done a))) (10000*(a+1)*(64^a+1)):=by
    apply SemiprimeD1StackCalls.evalsCorrect (aux .source) (aux .output) .start program
    let h:=source_run_bounded a
    exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
  exact Eq.mpr (congrArg (fun cfg:machine.Cfg=>StateTransition.EvalsToInTime machine.step cfg
    (some (SemiprimeD1StackCalls.configuration (done a))) (10000*(a+1)*(64^a+1)))
      (initial_eq (List.replicate a true))) hcert
/-- Every initialized physical word is paid by actual source-marker count. -/
theorem initial_role_bound (a:Nat) (k:Stack) :((initial (List.replicate a true)).data k).length ≤ a :=by
  change (input (List.replicate a true) k).length ≤ _
  rw [input_eq]
  split <;> simp
/-- A successful actual prefix cannot cross the SAME literal program's genuine whole halt. -/
theorem prefix_fuel (a fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (List.replicate a true))=some out) :fuel ≤ runBound a :=by
  obtain ⟨q,hq,hfinal⟩:=source_run a
  have ht:fuel ≤ q:=by
    by_contra hn
    have he:fuel=q+(1+(fuel-(q+1))):=by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hfinal,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh:SemiprimeD1StackCalls.run program 1 (done a)=none:=rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact ht.trans hq
/-- All30 actual words include both unused reducer inputs, the retained raw vector,
every growing catalogue byte and every real fixed-alphabet return cell. -/
theorem prefix_cells (a fuel:Nat) (out:C.State Stack Label)
    (hr:SemiprimeD1StackCalls.run program fuel (initial (List.replicate a true))=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ 31*(a+runBound a+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel a _ _ (initial_role_bound a) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length) ≤ 30*(a+fuel):=by
    calc
      _ ≤ ∑_k:Stack,(a+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel a fuel out hr
  omega
/-- Actual total storage is polynomial in width and alphabet cardinality; no powers are unary values. -/
theorem polynomial_space (a:Nat) :31*(a+runBound a+1) ≤ 1000000*(a+1)*(64^a+1) :=by
  have ht:=runBound_le a
  have h:(a+1) ≤ (a+1)*(64^a+1):=Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hpos:1 ≤ (a+1)*(64^a+1):=Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  rw [Nat.mul_assoc] at ht ⊢
  omega
/-- Same all30/real-return bound for EVERY actual compiled finite-machine prefix. -/
theorem machine_prefix_cells (a fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun c=>c.bind machine.step)^[fuel]
      (some (Turing.initList machine (List.replicate a true)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 31*(a+runBound a+1) :=by
  have hinit:=congrArg (fun c:machine.Cfg=>(fun q=>q.bind machine.step)^[fuel] (some c))
    (initial_eq (List.replicate a true))
  have hr':(fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (List.replicate a true))))=some cfg:=hinit.symm.trans hr
  have he:=SemiprimeD1StackCalls.run_correct (aux .source) (aux .output) .start program fuel
    (initial (List.replicate a true))
  have hh:=he.trans hr'
  cases hout:SemiprimeD1StackCalls.run program fuel (initial (List.replicate a true)) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells a fuel out hout
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Storage
