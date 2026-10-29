/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformSelectorsDecode
/-! # Complete real copy/decode/push selector trace with its own exact clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackTransformSelectorsExecution
open SemiprimeD1StackTransformSelectors SemiprimeD1StackTransformSelectorsPrimitives
open SemiprimeD1StackTransformSelectorsDecode SemiprimeD1StackProcedureTrace
/-- Exact whole physical source time, including stale-selector drains, both
preserving copies, all bounded pops, two singleton pushes and the real halt. -/
def timeBound (tag tr oldStage oldInverse : List Bool) : Nat :=
  oldStage.length+oldInverse.length+6*(tag.length+tr.length)+15
/-- The same actual trace up to the final caller-visible done location;
all outer frames and original tag/coord0 bytes are retained. -/
theorem source_trace (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (hcode : tagDispatch tagCode=.copyTransform second) (oldStage oldInverse : List Bool) :
    Runs program (timeBound (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse-1)
      .start (initial (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse).data
      .done (done (List.replicate tagCode.val true) (List.replicate trCode.val true) second (trCode.val==2)).data :=by
  let tag:=List.replicate tagCode.val true
  let tr:=List.replicate trCode.val true
  have h0:=clear_stage tag tr oldStage oldInverse
  have h1:=clear_inverse tag tr oldInverse
  have h2:=copy_tag tag tr
  have h3:=tag_decode tagCode.val 0 (by omega) tag tr
  have he:(⟨0+tagCode.val,by omega⟩:Fin 18)=tagCode:=by apply Fin.ext;change 0+tagCode.val=tagCode.val;omega
  rw [he,hcode] at h3
  have h4:=copy_transform tag tr second
  have h5:=transform_decode trCode.val 0 (by omega) tag tr second
  have he:(⟨0+trCode.val,by omega⟩:Fin 3)=trCode:=by apply Fin.ext;change 0+trCode.val=trCode.val;omega
  rw [he] at h5
  have h6:=emit tag tr second (trCode.val==2)
  have h:=compose h0 (compose h1 (compose h2 (compose h3 (compose h4 (compose h5 h6)))))
  change Runs program _ .start _ .done _ at h
  convert h using 1 <;> first | rfl | (dsimp only [timeBound,tag,tr];simp only [List.length_replicate];omega)
/-- Entire actual successful source from only acquired original words and
charged stale selectors; the two output Booleans are physically constructed. -/
theorem source_run (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (hcode : tagDispatch tagCode=.copyTransform second) (oldStage oldInverse : List Bool) :
    C.run program (timeBound (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse)
      (initial (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse)=
      some (done (List.replicate tagCode.val true) (List.replicate trCode.val true) second (trCode.val==2)) :=by
  have h:=source_trace tagCode trCode second hcode oldStage oldInverse
  obtain ⟨finish,hr,ho⟩:=h [] (initial (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse)
    ⟨rfl,rfl,rfl⟩
  have ht:timeBound (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse=
      (timeBound (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse-1)+1:=by
    unfold timeBound;omega
  rw [ht,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  rcases ho with ⟨hp,hd,hf⟩
  change C.step program finish=some (done _ _ second (trCode.val==2))
  simp [SemiprimeD1StackCalls.step,hp,program,SemiprimeD1StackCalls.execute,hd,hf,done]
/-- The actual fixed finite machine and its complete exact source clock. -/
def selectorsInTime (tagCode : Fin 18) (trCode : Fin 3) (second : Bool)
    (hcode : tagDispatch tagCode=.copyTransform second) (oldStage oldInverse : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse))
      (some (SemiprimeD1StackCalls.configuration
        (done (List.replicate tagCode.val true) (List.replicate trCode.val true) second (trCode.val==2))))
      (timeBound (List.replicate tagCode.val true) (List.replicate trCode.val true) oldStage oldInverse) :=by
  apply SemiprimeD1StackCalls.evalsCorrect .tag .stage .start program
  exact ⟨⟨_,source_run tagCode trCode second hcode oldStage oldInverse⟩,le_refl _⟩
end RiemannGaussian.SemiprimeD1StackTransformSelectorsExecution
