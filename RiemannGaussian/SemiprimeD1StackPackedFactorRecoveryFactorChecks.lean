/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCopies
/-! # Actual nontrivial-factor checks with real comparison output pops -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryFactorChecks
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecoveryPrimitives SemiprimeD1StackProcedureTrace
/-- Exact physical comparison-left update. -/
theorem compare_left (a b scratch difference answer xs : List Bool) :
    Function.update (W.store a b scratch difference answer) (.inl .left) xs=W.store xs b scratch difference answer := by
  funext k;rcases k with k|k
  · cases k <;> rfl
  · cases k;rfl
/-- Exact physical comparison-right update. -/
theorem compare_right (a b scratch difference answer xs : List Bool) :
    Function.update (W.store a b scratch difference answer) (.inl .right) xs=W.store a xs scratch difference answer := by
  funext k;rcases k with k|k
  · cases k <;> rfl
  · cases k;rfl
/-- Exact physical computed-answer update. -/
theorem compare_output (a b scratch difference answer xs : List Bool) :
    Function.update (W.store a b scratch difference answer) W.output xs=W.store a b scratch difference xs := by
  funext k;rcases k with k|k
  · cases k <;> rfl
  · cases k;rfl
/-- Real copy to a comparison's left operand, preserving all physical source/caches. -/
theorem copy_left (site : Copy) (pc finish : Label) (r m a x v u) (left right scratch difference answer value : List Bool)
    (hc : program pc=.call (copyLabel site 0) finish) (hd : copyStack site 1=SemiprimeD1StackPackedFactorRecovery.compare (.inl .left))
    (hv : (view r m a x (W.store left right scratch difference answer) v u) (copyStack site 0)=value)
    (hs : u .scratch=[]) :
    Runs program (5*value.length+4) pc (view r m a x (W.store left right scratch difference answer) v u)
      finish (view r m a x (W.store (value++left) right scratch difference answer) v u) := by
  have ht : (view r m a x (W.store left right scratch difference answer) v u) (copyStack site 1)=left := by rw [hd];rfl
  have h:=copy_call site pc finish hc _ value left hv ht hs
  rw [hd,view_compare,compare_left] at h
  exact h
/-- Real copy to a comparison's right operand, preserving all physical source/caches. -/
theorem copy_right (site : Copy) (pc finish : Label) (r m a x v u) (left right scratch difference answer value : List Bool)
    (hc : program pc=.call (copyLabel site 0) finish) (hd : copyStack site 1=SemiprimeD1StackPackedFactorRecovery.compare (.inl .right))
    (hv : (view r m a x (W.store left right scratch difference answer) v u) (copyStack site 0)=value)
    (hs : u .scratch=[]) :
    Runs program (5*value.length+4) pc (view r m a x (W.store left right scratch difference answer) v u)
      finish (view r m a x (W.store left (value++right) scratch difference answer) v u) := by
  have ht : (view r m a x (W.store left right scratch difference answer) v u) (copyStack site 1)=right := by rw [hd];rfl
  have h:=copy_call site pc finish hc _ value right hv ht hs
  rw [hd,view_compare,compare_right] at h
  exact h
/-- Complete clean validation boundary, retaining every acquired readout and SQ cache. -/
def work (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (v : SemiprimeD1StackBinarySquareRoot.Aux→List Bool) (small large : List Bool)
    (x : X.Stack→List Bool) (w : W.Stack→List Bool) : Stack→List Bool :=
  view r m (A.store [] [] [] []) x w v (words small large [] [])
/-- Literal selected factor and copy site, both controlled by a finite Bool only. -/
def site (large : Bool) : Copy := if large then .checkLarge else .checkSmall
/-- Exact physical nontrivial-factor-check cost. -/
def time (factor : List Bool) : ℕ := (5*factor.length+4)+1+1+compareTime factor [false,true]+1
/-- Real factor copy, real binary2 seed, whole numeric Less and actual FALSE result pop. -/
theorem factor_run (large : Bool) (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (v : SemiprimeD1StackBinarySquareRoot.Aux→List Bool) (small big : List Bool) (x : X.Stack→List Bool)
    (hf : SemiprimeD1StackWordLessExecution.answer (if large then big else small) [false,true]=false) :
    Runs program (time (if large then big else small)) (ctl (.copy (site large)))
      (work r m v small big x (W.store [] [] [] [] []))
      (if large then ctl (.copy .productLeft) else ctl (.copy .checkLarge))
      (work r m v small big x (W.store [] [] [] [] [])) := by
  let f:=if large then big else small
  let a:=A.store [] [] [] []
  let u:=words small big [] []
  have h0:=copy_left (site large) (ctl (.copy (site large))) (ctl (.seed2a large))
    r m a x v u [] [] [] [] [] f (by cases large <;> rfl) (by cases large <;> rfl)
      (by cases large <;> rfl) rfl
  simp only [List.append_nil] at h0
  have h1:=push_bit (ctl (.seed2a large)) (ctl (.seed2b large)) (SemiprimeD1StackPackedFactorRecovery.compare (.inl .right)) true
    (work r m v small big x (W.store f [] [] [] [])) rfl
  rw [work,view_compare,compare_right] at h1
  have h2:=push_bit (ctl (.seed2b large)) (ctl (.lessFactor large)) (SemiprimeD1StackPackedFactorRecovery.compare (.inl .right)) false
    (work r m v small big x (W.store f [true] [] [] [])) rfl
  rw [work,view_compare,compare_right] at h2
  have h3:=compare_call r m a x v u f [false,true] (ctl (.lessFactor large)) (ctl (.factorFlag large)) rfl
  rw [hf] at h3
  have h4:=pop_false (ctl (.factorFlag large))
    (if large then ctl (.copy .productLeft) else ctl (.copy .checkLarge)) (ctl (.abort 0)) (ctl (.abort 0))
    (compare W.output) (work r m v small big x (W.store [] [] [] [] [false])) [] rfl rfl
  rw [work,view_compare,compare_output] at h4
  exact join (join (join (join h0 h1) h2) h3) h4
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryFactorChecks
