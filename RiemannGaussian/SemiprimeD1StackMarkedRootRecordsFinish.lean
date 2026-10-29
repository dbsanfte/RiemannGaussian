/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRowView
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsPrimitives
/-! # Actual owner-first byte rejoin with all borrowed original work restored -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsFinish
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackMarkedRootRecordsView
open SemiprimeD1StackMarkedRootRecordsRowView SemiprimeD1StackMarkedRootRecordsPrimitives
open SemiprimeD1StackProcedureTrace
/-- Two actual borrowed original work words; no source/cache role is overwritten. -/
def borrowed (r : R.Stack → List Bool) (left rev : List Bool) : R.Stack → List Bool :=
  Function.update (Function.update r (R.aux .left) left) (R.aux .reverse) rev
/-- Literal owner-copy workspace boundary, with all144 and local parse work empty. -/
def joining (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits left rev out : List Bool) : Stack → List Bool :=
  view (borrowed r left rev) v bits {} {output := out}
/-- A real owner-copy write updates only its actually borrowed source-bank role. -/
theorem joining_left (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits left rev out word : List Bool) :
    Function.update (joining r v bits left rev out) ownerCopy word=joining r v bits word rev out := by
  unfold joining view ownerCopy
  rw [update_root]
  unfold borrowed
  rw [Function.update_comm (by decide : R.aux .left≠R.aux .reverse),Function.update_idem,
    Function.update_comm (by decide : R.aux .reverse≠R.aux .left)]
/-- A real reversal write changes only the second borrowed physical word. -/
theorem joining_reverse (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits left rev out word : List Bool) :
    Function.update (joining r v bits left rev out) ownerReverse word=joining r v bits left word out := by
  unfold joining view ownerReverse
  rw [update_root]
  unfold borrowed
  rw [Function.update_idem]
/-- A real final append writes only the actual new output. -/
theorem joining_output (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits left rev out word : List Bool) :
    Function.update (joining r v bits left rev out) (aux .output) word=joining r v bits left rev word :=
  set_output _ _ _ _ _ _
/-- Restoring BOTH actual borrowed words recovers the entire original1804 bank verbatim. -/
theorem borrowed_clean (r : R.Stack → List Bool) (hl : r (R.aux .left)=[]) (hr : r (R.aux .reverse)=[]) :
    borrowed r [] []=r := by
  have h0 : Function.update r (R.aux .left) []=r := by rw [←hl,Function.update_eq_self]
  unfold borrowed
  rw [h0,←hr,Function.update_eq_self]
/-- Paid owner copy/reversal/terminator removal/reversal plus actual success push.
No prepared owner answer or native append is used by the machine. -/
theorem join_run (r : R.Stack → List Bool) (v : V.Stack → List Bool) (bits ownerBytes factors : List Bool)
    (ho : r (R.ownerStack SemiprimeD1StackOwnerRecords.output)=ownerBytes++[false])
    (hl : r (R.aux .left)=[]) (hr : r (R.aux .reverse)=[]) (hs : r (R.aux .scratch)=[]) :
    Runs program (9*ownerBytes.length+19) (ctl .copyOwners) (view r v bits {} {output := factors})
      (ctl .done) (view r v bits {} {status := [true],output := ownerBytes++factors}) := by
  have h0 := copy_call .owners .copyOwners .reverseOwners rfl (joining r v bits [] [] factors)
    (ownerBytes++[false]) [] ho rfl hs
  change Runs program _ _ _ _ (Function.update (joining r v bits [] [] factors) ownerCopy ((ownerBytes++[false])++[])) at h0
  rw [List.append_nil,joining_left] at h0
  have h1 := reverse_call false .reverseOwners .stripOwnerEnd rfl
    (joining r v bits (ownerBytes++[false]) [] factors) (ownerBytes++[false]) [] rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (joining r v bits (ownerBytes++[false]) [] factors) ownerCopy []) ownerReverse ((ownerBytes++[false]).reverse++[])) at h1
  rw [joining_left,joining_reverse,List.append_nil,List.reverse_append,List.reverse_singleton,List.singleton_append] at h1
  have h2 : Runs program 1 (ctl .stripOwnerEnd) (joining r v bits [] (false::ownerBytes.reverse) factors)
      (ctl .join) (joining r v bits [] ownerBytes.reverse factors) := by
    apply one_base program _ _ (.pop ownerReverse (ctl .abort) (ctl .join) (ctl .abort)) _ _ rfl
    · rfl
    · exact joining_reverse _ _ _ _ _ _ _
  have h3 := reverse_call true .join .accept rfl (joining r v bits [] ownerBytes.reverse factors)
    ownerBytes.reverse factors rfl rfl
  change Runs program _ _ _ _ (Function.update (Function.update
    (joining r v bits [] ownerBytes.reverse factors) ownerReverse []) (aux .output) (ownerBytes.reverse.reverse++factors)) at h3
  rw [joining_reverse,joining_output,List.reverse_reverse] at h3
  have h4 : Runs program 1 (ctl .accept) (joining r v bits [] [] (ownerBytes++factors)) (ctl .done)
      (view (borrowed r [] []) v bits {} {status := [true],output := ownerBytes++factors}) := by
    apply one_base program _ _ (.push (aux .status) true (ctl .done)) _ _ rfl
    · rfl
    · exact set_status _ _ _ _ _ _
  have h := join (join (join (join h0 h1) h2) h3) h4
  unfold joining at h
  rw [borrowed_clean r hl hr] at h
  convert h using 1
  simp only [List.length_append,List.length_cons,List.length_nil,List.length_reverse]
  omega
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsFinish
