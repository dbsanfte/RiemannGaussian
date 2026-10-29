/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketOrientationPrimitives
/-! # Real paid strict comparison of the two acquired colour words
Only actual preserving copies feed the real five-role WordLess source. Its
computed Boolean is physically popped; the whole other bank, including both
actual colour words and every caller return, survives this fragment.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketOrientationCompare
open SemiprimeD1StackPacketOrientation SemiprimeD1StackPacketOrientationPrimitives
open SemiprimeD1StackProcedureTrace
local notation "ctl" => Label.local
/-- Complete nineteen-role comparison bank; all other sixteen words retain their actual prior values. -/
def view (retained:Stack→List Bool) (left right result:List Bool) :Stack→List Bool :=
  fun k=>if k=operand false then left else if k=operand true then right
    else if k=answer then result else retained k
/-- One actual left comparison update preserves every other physical stack. -/
theorem update_left (retained:Stack→List Bool) (left right result word:List Bool) :
    Function.update (view retained left right result) (operand false) word=view retained word right result :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual right comparison update preserves every other physical stack. -/
theorem update_right (retained:Stack→List Bool) (left right result word:List Bool) :
    Function.update (view retained left right result) (operand true) word=view retained left word result :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- One actual result comparison update preserves every other physical stack. -/
theorem update_result (retained:Stack→List Bool) (left right result word:List Bool) :
    Function.update (view retained left right result) answer word=view retained left right word :=by
  funext k
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- The chosen colour directions are compared by real copied operand words, with no supplied order Boolean. -/
theorem compare_run (backward:Bool) (retained:Stack→List Bool) (first second:List Bool)
    (hn:retained (copyStack (.operand backward false) 0)=first)
    (ho:retained (copyStack (.operand backward true) 0)=second)
    (hc:retained (aux .copyScratch)=[]) (hs:retained scratch=[])
    (hd:retained buffer=[]) :
    Runs program (5*first.length+5*second.length+
        SemiprimeD1StackWordLessExecution.totalTime first second+10)
      (ctl (.copyOperand backward false)) (view retained [] [] [])
      (ctl (if SemiprimeD1StackWordLessExecution.answer first second then
        (if backward then .slot false true else .slot true false) else
        (if backward then .padding else .copyOperand true false)))
      (view retained [] [] []) :=by
  have h0:=copy_call (.operand backward false) (.copyOperand backward false) (.copyOperand backward true) rfl
    (view retained [] [] []) first [] (by cases backward <;> exact hn) rfl hc
  change Runs program _ _ _ _
    (Function.update (view retained [] [] []) (operand false) (first++[])) at h0
  rw [List.append_nil,update_left] at h0
  have h1:=copy_call (.operand backward true) (.copyOperand backward true) (.compare backward) rfl
    (view retained first [] []) second [] (by cases backward <;> exact ho) rfl hc
  change Runs program _ _ _ _
    (Function.update (view retained first [] []) (operand true) (second++[])) at h1
  rw [List.append_nil,update_right] at h1
  have h2:=less_call backward (view retained first second []) first second rfl rfl hs hd rfl
  rw [update_left,update_right,update_result] at h2
  let low:Control:=if backward then .padding else .copyOperand true false
  let high:Control:=if backward then .slot false true else .slot true false
  have hcode:program (ctl (.compared backward))=.base (.pop answer (ctl .reject) (ctl low) (ctl high)):=by cases backward <;> rfl
  have h3:=pop_run (.compared backward) (ctl .reject) (ctl low) (ctl high) answer
    (view retained [] [] [SemiprimeD1StackWordLessExecution.answer first second])
    [SemiprimeD1StackWordLessExecution.answer first second] hcode rfl
  change Runs program 1 _ _ _ (Function.update
    (view retained [] [] [SemiprimeD1StackWordLessExecution.answer first second]) answer []) at h3
  rw [update_result] at h3
  have hp:SemiprimeD1StackBytecode.choose (ctl .reject) (ctl low) (ctl high)
      [SemiprimeD1StackWordLessExecution.answer first second].head?=
      ctl (if SemiprimeD1StackWordLessExecution.answer first second then high else low):=by
    cases SemiprimeD1StackWordLessExecution.answer first second <;> rfl
  rw [hp] at h3
  have h:=join (join (join h0 h1) h2) h3
  have ht:(5*first.length+4)+(5*second.length+4)+
      (SemiprimeD1StackWordLessExecution.totalTime first second+1)+1=
      5*first.length+5*second.length+SemiprimeD1StackWordLessExecution.totalTime first second+10:=by omega
  simpa only [ht,low,high] using h
/-- Empty comparison overrides are exactly the original caller bank once its three real words are clear. -/
theorem view_empty (retained:Stack→List Bool) (hl:retained (operand false)=[])
    (hr:retained (operand true)=[]) (ho:retained answer=[]) :view retained [] [] []=retained :=by
  funext k
  by_cases h0:k=operand false
  · subst k;simp only [view,ite_true];exact hl.symm
  · by_cases h1:k=operand true
    · subst k;simp only [view,h0,ite_false,ite_true];exact hr.symm
    · by_cases h2:k=answer
      · subst k;simp only [view,h0,h1,ite_false,ite_true];exact ho.symm
      · simp only [view,h0,h1,h2,ite_false]
end RiemannGaussian.SemiprimeD1StackPacketOrientationCompare
