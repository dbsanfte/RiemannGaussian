/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformSelectorsExecution
/-! # Same-source selector clock and all seven physical/return-prefix cells -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackTransformSelectorsBounds
open SemiprimeD1StackTransformSelectors SemiprimeD1StackTransformSelectorsExecution
/-- Actual original-field and stale-selector byte inventory. -/
def inputSize (tag tr oldStage oldInverse : List Bool) : Nat :=
  tag.length+tr.length+oldStage.length+oldInverse.length
/-- Every actual initial data role is charged. -/
theorem initial_data_bound (tag tr oldStage oldInverse : List Bool) (k : Stack) :
    ((initial tag tr oldStage oldInverse).data k).length≤ inputSize tag tr oldStage oldInverse :=by
  cases k <;> simp [initial,data,inputSize] <;> omega
/-- Every successful prefix precedes the proved actual complete source halt. -/
theorem prefix_fuel_le (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (hcode : tagDispatch tagCode=.copyTransform second) (oldStage oldInverse : List Bool)
    (fuel : Nat) (finish : C.State Stack Label)
    (hr : C.run program fuel
      (initial (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse)=some finish) :
    fuel≤timeBound (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse :=by
  have he:=source_run tagCode trCode second hcode oldStage oldInverse
  by_contra hn
  let t:=timeBound (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse
  have ht:fuel=t+(1+(fuel-(t+1))):=by dsimp [t];omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
  have hz:C.run program 1 (done (List.replicate tagCode.val true) (List.replicate trCode.val true) second (trCode.val==2))=none:=rfl
  rw [hz,Option.bind_none] at hr
  cases hr
/-- All seven real Boolean words, private scratch, bounded-field readers and
every actual nested return cell at every reached source prefix. -/
theorem prefix_cells (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (hcode : tagDispatch tagCode=.copyTransform second) (oldStage oldInverse : List Bool)
    (fuel : Nat) (finish : C.State Stack Label)
    (hr : C.run program fuel
      (initial (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse)=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      8*(inputSize (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse+
        timeBound (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse+1) :=by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (inputSize (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse) _ finish
    (initial_data_bound _ _ _ _) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ finish hr
  change finish.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(finish.data k).length)≤
      7*(inputSize (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse+fuel):=by
    calc
      _≤∑_k:Stack,(inputSize (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse+fuel):=
        Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le tagCode trCode second hcode oldStage oldInverse fuel finish hr
  omega
/-- The same inventory on the actual compiled finite-control machine. -/
theorem machine_prefix_cells (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (hcode : tagDispatch tagCode=.copyTransform second) (oldStage oldInverse : List Bool)
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration
      (initial (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      8*(inputSize (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse+
        timeBound (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse+1) :=by
  have he:=SemiprimeD1StackCalls.run_correct .tag .stage .start program fuel
    (initial (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse)
  have hh:(C.run program fuel
      (initial (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse)).map
      SemiprimeD1StackCalls.configuration=some cfg:=he.trans hr
  cases hrun:C.run program fuel
      (initial (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse) with
  | none=>rw [hrun] at hh;cases hh
  | some finish=>
    rw [hrun] at hh
    have heq:SemiprimeD1StackCalls.configuration finish=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells tagCode trCode second hcode oldStage oldInverse fuel finish hrun
/-- Actual Boolean and remembered-return flags are finite before original N. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite .tag .stage .start program
/-- Every Boolean data and actual return-label alphabet is finite. -/
theorem all_alphabets_finite (k : machine.K) : Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite .tag .stage .start program k
/-- Every actual primitive transition has at most four fundamental commands. -/
theorem compile_depth (pc : Label) : SemiprimeD1StackBytecode.statementDepth (machine.m pc)≤4 :=
  SemiprimeD1StackCalls.compile_depth (.start : Label) (program pc)
end RiemannGaussian.SemiprimeD1StackTransformSelectorsBounds
