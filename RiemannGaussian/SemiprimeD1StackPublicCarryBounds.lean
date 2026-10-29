/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryOriginal
/-! # Actual physical carry-body component costs
All costs below are derived from literal completed traces and actual cache
lengths; none is a supplied component clock or canonicality/answer premise.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicCarryBounds
open SemiprimeD1StackPublicCarry SemiprimeD1StackPublicCarryState
open SemiprimeD1StackPublicCarryGuards SemiprimeD1StackPublicCarryEquation
open SemiprimeD1StackPublicCarryExecution
/-- Actual fitted input words all have the acquired physical modulus width. -/
theorem word_length (context : T.Stack→List Bool) (raw : List Bool) (k : Fin 3) :
    (word context raw k).length=(width context).length := by
  fin_cases k <;> exact SemiprimeD1StackWordBlockExecution.result_length _ _
/-- Literal copied-modulus bound construction increases no width by more than one. -/
theorem bound_length (context : T.Stack→List Bool) :
    (boundWord context).length≤(width context).length+1 := by
  simp only [boundWord,List.length_cons,List.length_tail];omega
/-- Each ACTUAL physical guard has a derived linear component allowance. -/
theorem guard_le (context : T.Stack→List Bool) (raw : List Bool) (k : Fin 3) :
    guardBudget context raw k≤22*(width context).length+33 := by
  have h:=SemiprimeD1StackWordLessExecution.totalTime_le (word context raw k) (guardBound context k)
  have hb : (guardBound context k).length≤(width context).length+1 := by
    fin_cases k <;> first | exact bound_length context | simp [guardBound]
  rw [word_length] at h
  unfold guardBudget
  rw [word_length]
  omega
/-- Full retained body cost is linear in actual raw/cache/target/radix lengths;
this pays both tails as an allowance, while the trace executes only its branch. -/
theorem body_le (context : T.Stack→List Bool) (raw : List Bool) :
    bodyBudget context raw≤10000*(raw.length+(width context).length+(target context).length+(radix context).length+1) := by
  have h0:=guard_le context raw 0
  have h1:=guard_le context raw 1
  have h2:=guard_le context raw 2
  have hc : (coefficient context raw).length=(width context).length := SemiprimeD1StackWordBlockExecution.result_length _ _
  have hp : (previous context raw).length=(width context).length := SemiprimeD1StackWordBlockExecution.result_length _ _
  have hn : (next context raw).length=(width context).length := SemiprimeD1StackWordBlockExecution.result_length _ _
  have he:=SemiprimeD1StackCarryEquationBounds.totalTime_le (radix context) (coefficient context raw)
    (previous context raw) (target context) (next context raw)
  unfold SemiprimeD1StackCarryEquationBounds.timeBound SemiprimeD1StackCarryEquationBounds.operandSize at he
  rw [hc,hp,hn] at he
  unfold bodyBudget guardsBudget parseBudget clearBudget framesBudget equationBudget
  simp only [SemiprimeD1StackWordVectorExecution.timeBound,three,List.length_cons,List.length_nil,hc,hp,hn]
  omega
/-- Every original acquired target block has intrinsic width at most its
actual radix template, including the missing-cell empty default. -/
theorem target_length (bits index : List Bool) :
    (target (actualContext bits index)).length≤(radix (actualContext bits index)).length := by
  have hb : ∀n raw,∀w∈SemiprimeD1StackDigitBankSpec.blocks
      (SemiprimeD1BinaryDigitAcquisitionComponents.radix bits) n raw,
      w.length≤(SemiprimeD1BinaryDigitAcquisitionComponents.radix bits).length := by
    intro n
    induction n with
    | zero=>simp [SemiprimeD1StackDigitBankSpec.blocks]
    | succ n ih=>
      intro raw w hw
      cases raw with
      | nil=>simp [SemiprimeD1StackDigitBankSpec.blocks] at hw
      | cons b bs=>
        simp only [SemiprimeD1StackDigitBankSpec.blocks,List.mem_cons] at hw
        rcases hw with rfl|hw
        · exact SemiprimeD1StackDigitBankSpec.block_length _ _
        · exact ih _ _ hw
  change (((SemiprimeD1StackPublicTargetExecution.digits bits)[index.length]?).getD []).length≤_
  cases he : (SemiprimeD1StackPublicTargetExecution.digits bits)[index.length]? with
  | none=>simp only [Option.getD_none,List.length_nil];exact Nat.zero_le _
  | some w=>exact hb bits.length bits w (List.mem_of_getElem? he)
/-- Fixed polynomial actual whole-program transition allowance. -/
def runBound (bits raw index : List Bool) : ℕ := 1000000000000*(bits.length+raw.length+index.length+2)^2
/-- Original binary preprocessing and physical carry-body costs are BOTH paid. -/
theorem timeBound_le (bits raw index : List Bool) :
    SemiprimeD1StackPublicCarryExecution.timeBound bits raw index≤runBound bits raw index := by
  have h:=body_le (actualContext bits index) raw
  have ht:=target_length bits index
  have hr:=SemiprimeD1StackPublicCarryOriginal.acquired_radix_length bits index
  have hw:=SemiprimeD1StackPublicCarryOriginal.acquired_width_length bits index
  have hR: SemiprimeMacroParameters.transformLength bits.length≤64*bits.length+1 :=
    (SemiprimeD1StackTransformArithmetic.prefix_powers bits.length _ le_rfl).1
  have hb:=SemiprimeD1StackTransformArithmetic.radix_bound bits.length
  rw [hr] at ht
  rw [hw,hr] at h
  have hS : bits.length+raw.length+index.length+2≤(bits.length+raw.length+index.length+2)^2 := by
    have hh:=Nat.pow_le_pow_right (by omega : 1≤bits.length+raw.length+index.length+2) (by decide : 1≤2)
    simpa only [pow_one] using hh
  have hp : (bits.length+index.length+2)^2≤(bits.length+raw.length+index.length+2)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  unfold SemiprimeD1StackPublicCarryExecution.timeBound SemiprimeD1StackPublicTargetBounds.timeBound runBound
  omega
/-- The closed source trace has a fixed polynomial bound on actual inputs. -/
theorem source_run_bounded (bits raw index : List Bool) (hb : bits≠[]) :
    ∃t≤runBound bits raw index,C.run program t (initial bits raw index)=some (done bits raw index) := by
  obtain ⟨t,ht,hr⟩:=source_run bits raw index hb
  exact ⟨t,ht.trans (timeBound_le bits raw index),hr⟩
/-- Proof-only certificate of the ACTUALLY executed bounded source trace. -/
noncomputable def sourceCheck (bits raw index : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime (C.step program) (initial bits raw index)
      (some (done bits raw index)) (runBound bits raw index) := by
  let h:=source_run_bounded bits raw index hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine finite-control finite-alphabet execution, with actual input/cache bytes. -/
noncomputable def machineCheck (bits raw index : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial bits raw index))
      (some (SemiprimeD1StackCalls.configuration (done bits raw index))) (runBound bits raw index) :=
  SemiprimeD1StackCalls.evalsCorrect inputRole output Label.start program _ _ _ (sourceCheck bits raw index hb)
/-- No successful prefix can occur after the proved closed halt. -/
theorem prefix_fuel_le (bits raw index : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw index)=some out) : fuel≤runBound bits raw index := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded bits raw index hb
  have hf : fuel≤t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done bits raw index)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Every actual source prefix counts ALL51 Boolean data stacks plus real return
labels. Prepared target/metadata widths are not supplied as storage advice. -/
theorem prefix_cells (bits raw index : List Bool) (hb : bits≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw index)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤
      1000000000000000*(bits.length+raw.length+index.length+2)^2 := by
  let inv:=bits.length+index.length+raw.length
  have hdata : ∀k,((initial bits raw index).data k).length≤ inv := by
    intro k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;> simp only [initial,store,T.input,SemiprimeD1StackPublicTarget.store,SemiprimeD1BinaryPublicAcquisition.input,
              SemiprimeD1BinaryPublicAcquisition.store,SemiprimeD1BinaryPublicAcquisition.Digits.input,
              SemiprimeD1BinaryDigitAcquisition.store,SemiprimeD1StackTransform.input,Sum.elim_inl,List.length_nil]
              <;> dsimp [inv] <;> omega
          · rcases k with k|k <;> exact Nat.zero_le _
        · rcases k with k|k <;> exact Nat.zero_le _
      · cases k <;> simp only [initial,store,T.input,SemiprimeD1StackPublicTarget.store,SemiprimeD1StackJetRead.store,Sum.elim_inl,Sum.elim_inr,List.length_nil]
          <;> dsimp [inv] <;> omega
    · cases k <;> simp only [initial,store,aux,Sum.elim_inr,List.length_nil] <;> dsimp [inv] <;> omega
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel inv _ out hdata hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length)≤51*(inv+fuel) := by
    calc
      _≤∑_k : Stack,(inv+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits raw index hb fuel out hr
  have hraw : bits.length+index.length+raw.length≤(bits.length+raw.length+index.length+2)^2 := by
    have hh:=Nat.pow_le_pow_right (by omega : 1≤bits.length+raw.length+index.length+2) (by decide : 1≤2)
    simp only [pow_one] at hh;omega
  unfold runBound at ht
  dsimp [inv] at hs
  omega
/-- The same inventory holds at EVERY genuine FinTM2 prefix, including real
return-stack symbols rather than an erased native call stack. -/
theorem machine_prefix_cells (bits raw index : List Bool) (hb : bits≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits raw index)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      1000000000000000*(bits.length+raw.length+index.length+2)^2 := by
  have he:=SemiprimeD1StackCalls.run_correct inputRole output Label.start program fuel (initial bits raw index)
  have hh:=he.trans hr
  cases hc : C.run program fuel (initial bits raw index) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits raw index hb fuel out hc
end RiemannGaussian.SemiprimeD1StackPublicCarryBounds
