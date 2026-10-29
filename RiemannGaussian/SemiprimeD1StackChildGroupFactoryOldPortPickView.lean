/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortPick
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketHeader
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryChildParse
/-! # Exact old-port filter boundary before its actual nested first-index query -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortPickView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryOldPortPick
open SemiprimeBitArithmetic (bitValue)
namespace Cleanup
export SemiprimeD1StackChildGroupFactoryOldPortCleanup (role result_role result_other)
end Cleanup
namespace Header
export SemiprimeD1StackChildGroupFactoryBucketHeader (cleanRoles)
end Header
namespace Child
export SemiprimeD1StackChildGroupFactoryChildParse (cleanRoles)
end Child
/-- Actual original-port reader suffix, after parsing and both real cleanup paths. -/
theorem result_oldReader (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool):
    result before p tail target (aux .oldReader)=tail:=by
  by_cases h:bitValue p.vertex=bitValue target <;> simp [result,h,built,parsed,Parse.result,Cleanup.result,aux]
/-- All three actual original raw fields are physically empty. -/
theorem result_role (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool) (j:Fin 3):
    result before p tail target (Cleanup.role j)=[]:=by rw [result];exact Cleanup.result_role _ _
/-- Every other actual caller/cache word outside the target tag and old reader is retained literally. -/
theorem result_other (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (ho:k≠aux .oldReader) (ht:k≠aux .tagWord):
    result before p tail target k=before k:=by
  rw [result,Cleanup.result_other _ _ hf]
  have h0:=Ne.symm (hf 0)
  have h1:=Ne.symm (hf 1)
  have h2:=Ne.symm (hf 2)
  simp only [Cleanup.role] at h0 h1 h2
  by_cases h:bitValue p.vertex=bitValue target <;>
    simp only [h,ite_true,ite_false,built,parsed,Parse.result,Function.update_of_ne ht,
      Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0,Function.update_of_ne ho]
/-- The matching old record really built its literal edge/side tag. -/
theorem result_tag (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool)
    (h:bitValue p.vertex=bitValue target):
    result before p tail target (aux .tagWord)=Build.rawTag p.edge p.side:=by
  simp [result,h,built,Cleanup.result,aux]
/-- A skipped other-vertex old port leaves its actually empty target-tag word unchanged. -/
theorem result_skipped_tag (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool)
    (h:bitValue p.vertex≠bitValue target):result before p tail target (aux .tagWord)=before (aux .tagWord):=by
  simp [result,h,parsed,Parse.result,Cleanup.result,aux]
/-- All old-port parser/private words are restored by the actual filter source. -/
theorem result_clean (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):∀k∈Parse.cleanRoles,result before p tail target k=[]:=by
  intro k hk
  simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact result_role _ _ _ _ 0
  · exact result_role _ _ _ _ 1
  · exact result_role _ _ _ _ 2
  all_goals
    exact (result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans
      (hz _ (by simp [Parse.cleanRoles]))
/-- Every destination/parser role of the actual next bucket-header source is still physically empty. -/
theorem result_headerClean (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool)
    (hh:∀k∈Header.cleanRoles,before k=[]):∀k∈Header.cleanRoles,result before p tail target k=[]:=by
  intro k hk
  have hd:∀j,Cleanup.role j≠k:=by
    intro j
    simp only [Header.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> fin_cases j <;> decide
  have ho:k≠aux .oldReader:=by
    simp only [Header.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  have ht:k≠aux .tagWord:=by
    simp only [Header.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact (result_other _ _ _ _ k hd ho ht).trans (hh k hk)
/-- Every destination/parser role of the actual next child source is physically empty. -/
theorem result_childClean (before:Stack→List Bool) (p:Parse.Point) (tail target:List Bool)
    (hz:∀k∈Child.cleanRoles,before k=[]):∀k∈Child.cleanRoles,result before p tail target k=[]:=by
  intro k hk
  simp only [Child.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact result_role _ _ _ _ 0
  · exact (result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans
      (hz _ (by simp [Child.cleanRoles]))
  · exact (result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans
      (hz _ (by simp [Child.cleanRoles]))
  · exact result_role _ _ _ _ 1
  · exact result_role _ _ _ _ 2
  all_goals
    exact (result_other _ _ _ _ _ (by intro j;fin_cases j <;> decide) (by decide) (by decide)).trans
      (hz _ (by simp [Child.cleanRoles]))
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortPickView
