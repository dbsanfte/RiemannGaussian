/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackTransformSelectorsDecode
/-! # Unknown and malformed copied codes take actual abort instructions
No singleton stage/inverse word is pushed on any of these rejection fragments.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackTransformSelectorsReject
open SemiprimeD1StackTransformSelectors SemiprimeD1StackTransformSelectorsPrimitives
open SemiprimeD1StackTransformSelectorsDecode SemiprimeD1StackProcedureTrace
/-- Exact actual halted rejection store; unconsumed copied suffixes are explicit. -/
def aborted (tag tr tagReader transformReader : List Bool) : C.State Stack Label :=
  ⟨none,none,none,data tag tr tagReader transformReader [] [],[]⟩
/-- Every unknown bounded constructor code really reaches abort, with both
old selector words erased and no newly pushed selector or record. -/
theorem tag_abort_trace (code : Fin 18) (hcode : tagDispatch code=.abort)
    (tr oldStage oldInverse : List Bool) :
    Runs program (oldStage.length+oldInverse.length+6*code.val+7) .start
      (initial (List.replicate code.val true) tr oldStage oldInverse).data .abort
      (data (List.replicate code.val true) tr [] [] [] []) :=by
  let tag:=List.replicate code.val true
  have h0:=clear_stage tag tr oldStage oldInverse
  have h1:=clear_inverse tag tr oldInverse
  have h2:=copy_tag tag tr
  have h3:=tag_decode code.val 0 (by omega) tag tr
  have he:(⟨0+code.val,by omega⟩:Fin 18)=code:=by apply Fin.ext;change 0+code.val=code.val;omega
  rw [he,hcode] at h3
  have h:=compose h0 (compose h1 (compose h2 h3))
  convert h using 1 <;> first | rfl | (dsimp only [tag];simp only [List.length_replicate];omega)
/-- The actual unknown-constructor source halt, retaining original input bytes. -/
theorem tag_abort_run (code : Fin 18) (hcode : tagDispatch code=.abort)
    (tr oldStage oldInverse : List Bool) :
    C.run program (oldStage.length+oldInverse.length+6*code.val+8)
      (initial (List.replicate code.val true) tr oldStage oldInverse)=
      some (aborted (List.replicate code.val true) tr [] []) :=by
  have h:=tag_abort_trace code hcode tr oldStage oldInverse
  obtain ⟨finish,hr,ho⟩:=h [] (initial (List.replicate code.val true) tr oldStage oldInverse) ⟨rfl,rfl,rfl⟩
  rw [show oldStage.length+oldInverse.length+6*code.val+8=
    (oldStage.length+oldInverse.length+6*code.val+7)+1 by omega,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  rcases ho with ⟨hp,hd,hf⟩
  change C.step program finish=some (aborted _ _ [] [])
  simp [SemiprimeD1StackCalls.step,hp,program,SemiprimeD1StackCalls.execute,hd,hf,aborted]
/-- An eighteenth constructor marker takes the fixed overflow abort branch. -/
theorem tag_overflow (tag tr tail : List Bool) :
    Runs program 1 (.tag 17) (data tag tr (true::tail) [] [] []) .abort (data tag tr tail [] [] []) :=by
  apply one_base program _ _ (.pop .tagReader (tagDispatch 17) .abort .abort) _ _ rfl
  · rfl
  · exact update_tagReader _ _ _ _ _ _ _
/-- A false copied constructor marker takes the fixed malformed-code abort. -/
theorem tag_false (tag tr tail : List Bool) (count : Fin 18) :
    Runs program 1 (.tag count) (data tag tr (false::tail) [] [] []) .abort (data tag tr tail [] [] []) :=by
  apply one_base program _ _ (.pop .tagReader (tagDispatch count) .abort (nextTag count)) _ _ rfl
  · rfl
  · exact update_tagReader _ _ _ _ _ _ _
/-- A third coord0 transform marker takes the fixed overflow abort branch. -/
theorem transform_overflow (tag tr tail : List Bool) (second : Bool) :
    Runs program 1 (.transform second 2) (data tag tr [] (true::tail) [] []) .abort (data tag tr [] tail [] []) :=by
  apply one_base program _ _ (.pop .transformReader (transformDispatch second 2) .abort .abort) _ _
    rfl
  · rfl
  · exact update_transformReader _ _ _ _ _ _ _
/-- A false copied transform marker takes the fixed malformed-code abort. -/
theorem transform_false (tag tr tail : List Bool) (second : Bool) (count : Fin 3) :
    Runs program 1 (.transform second count) (data tag tr [] (false::tail) [] []) .abort (data tag tr [] tail [] []) :=by
  apply one_base program _ _ (.pop .transformReader (transformDispatch second count) .abort (nextTransform second count)) _ _ rfl
  · rfl
  · exact update_transformReader _ _ _ _ _ _ _
end RiemannGaussian.SemiprimeD1StackTransformSelectorsReject
