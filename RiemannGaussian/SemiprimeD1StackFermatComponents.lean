/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFermatConstants

/-! # Actual metadata and counter-copy calls for public constants
The original metadata nested calls are included literally. No source counter,
constant value, inverse or desired word is passed to the original-input program.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackFermatComponents
open SemiprimeD1StackFermatConstants
open SemiprimeD1StackProcedureFragments (At Runs included_call one_base)

/-- Exact actual metadata payload, overlaid only at its empty work and two new outputs. -/
def data (base:Meta.Stack→List Bool) (rw ew tmp modulus normalizer:List Bool) : Stack→List Bool
  | .inl .squareWork => rw
  | .inl .thresholdWork => ew
  | .inl .temporary => tmp
  | .inl k => base k
  | .inr false => modulus
  | .inr true => normalizer

/-- Actual Copy input projection requires only its actual empty scratch. -/
theorem copy_input (mode:Bool) (store:Stack→List Bool) (ht:store (.inl .temporary)=[]) :
    LinkB.DataRel (copyStack mode) store
      (SemiprimeD1StackCopy.payload (store (copyInput mode)) (store (copyOutput mode)) []) store := by
  constructor
  · intro k
    fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.payload,ht]
  · intro k _
    rfl

/-- The copied R/E words are acquired from their actual retained source stacks. -/
theorem copy_output (mode:Bool) (store:Stack→List Bool) (ht:store (.inl .temporary)=[]) :
    LinkB.DataRel (copyStack mode) store
      (SemiprimeD1StackCopy.payload (store (copyInput mode))
        (store (copyInput mode)++store (copyOutput mode)) [])
      (Function.update store (copyOutput mode) (store (copyInput mode)++store (copyOutput mode))) := by
  constructor
  · intro k
    cases mode <;> fin_cases k <;>
      simp [copyStack,copyInput,copyOutput,SemiprimeD1StackCopy.payload,Function.update,ht]
  · intro k hk
    have hne:k≠copyOutput mode:=by
      intro he
      apply hk 1
      simpa only [copyStack,show ¬((1:Fin 3)=0) by decide,ite_false,ite_true] using he.symm
    exact Function.update_of_ne hne _ _

/-- Real included Copy call with its actual continuation push and return pop. -/
theorem copy_call (mode:Bool) (store:Stack→List Bool) (ht:store (.inl .temporary)=[])
    (pc next:Label) (hcall:program pc=.call (copyLabel mode 0) next) :
    Runs program (5*(store (copyInput mode)).length+4) pc store next
      (Function.update store (copyOutput mode) (store (copyInput mode)++store (copyOutput mode))) := by
  apply included_call program (copyStack mode) (copyLabel mode) (copyStack_injective mode)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hcall
    (5*(store (copyInput mode)).length+3)
    (SemiprimeD1StackCopy.state 0 none (store (copyInput mode)) (store (copyOutput mode)) [])
    (SemiprimeD1StackCopy.done (store (copyInput mode)) (store (copyInput mode)++store (copyOutput mode)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · exact copy_input mode store ht
  · exact copy_output mode store ht

/-- Original-input projection has no prepared metadata or constant output. -/
theorem meta_input (bits:List Bool) :
    LinkB.DataRel Sum.inl (input bits) (Meta.initial bits).data (input bits) := by
  constructor
  · intro k;rfl
  · intro k _;rfl

/-- The actual completed metadata source determines all acquired operands. -/
theorem meta_output (bits:List Bool) :
    LinkB.DataRel Sum.inl (input bits) (SemiprimeD1StackTransformExecution.done bits).data
      (data (SemiprimeD1StackTransformExecution.result bits) [] [] [] [] []) := by
  constructor
  · intro k
    cases k <;> rfl
  · intro k hk
    cases k with
    | inl k => exact False.elim (hk k rfl)
    | inr bit => cases bit <;> rfl

/-- Actual nested metadata execution from N alone; every source call and return is retained. -/
theorem metadata_call (bits:List Bool) :
    Runs program (SemiprimeD1StackTransformArithmetic.totalTime bits.length+1) (.inl .start) (input bits)
      (.inl .modStart) (data (SemiprimeD1StackTransformExecution.result bits) [] [] [] [] []) := by
  intro frames target h
  rcases h with ⟨hpc,hdata,hframes⟩
  let entry:Meta.Label:=.inl .start
  let mid:=C.execute (.call (metaLabel entry) (.inl .modStart)) target
  have hm:C.run program 1 target=some mid:=by
    change C.step program target=some mid
    simp [C.step,SemiprimeD1StackCalls.step,hpc,program,mid,entry]
  have hrel:LinkC.Rel Sum.inl metaLabel (input bits) (.inl .modStart) frames (Meta.initial bits) mid:=by
    constructor
    · change LinkB.DataRel Sum.inl (input bits) (Meta.initial bits).data target.data
      rw [hdata]
      exact meta_input bits
    · simp [SemiprimeD1StackValidationLink.PcRel,Meta.initial,mid,C.execute,hframes,entry]
  obtain ⟨finish,hfinish,hrel⟩:=LinkC.run_rel Sum.inl metaLabel Sum.inl_injective program Meta.program
    (fun _=>rfl) (input bits) (.inl .modStart) frames
    (SemiprimeD1StackTransformArithmetic.totalTime bits.length) (Meta.initial bits)
    (SemiprimeD1StackTransformExecution.done bits) mid hrel
    (SemiprimeD1StackTransformExecution.acquire_run bits) rfl
  have hd:finish.data=data (SemiprimeD1StackTransformExecution.result bits) [] [] [] [] []:=
    LinkB.data_unique Sum.inl (input bits) _ _ _ hrel.1 (meta_output bits)
  have hp:finish.pc=some (.inl .modStart) ∧ finish.frames=frames:=by
    simpa only [SemiprimeD1StackValidationLink.PcRel,SemiprimeD1StackTransformExecution.done] using hrel.2
  refine ⟨finish,?_,hp.1,hd,hp.2⟩
  rw [show SemiprimeD1StackTransformArithmetic.totalTime bits.length+1=
    1+SemiprimeD1StackTransformArithmetic.totalTime bits.length by omega,
    SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,hfinish]
end RiemannGaussian.SemiprimeD1StackFermatComponents
