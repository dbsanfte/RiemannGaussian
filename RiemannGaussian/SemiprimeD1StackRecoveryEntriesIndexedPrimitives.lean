/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedState
/-! # Real preserving copies and every physical single-bit/drain transition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedPrimitives
open SemiprimeD1StackRecoveryEntriesIndexed SemiprimeD1StackProcedureTrace
/-- Exact chronological composition retains every actual external return cell. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack → List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after):
    Runs program (m+n) pc before next after:=runs_trans program m n pc mid next before between after h g
/-- Each actual input/ordinal copy pays both traversals and its real call/return. -/
theorem copy_call (site:Copy) (pc next:Label) (before:Stack → List Bool) (xs ys:List Bool)
    (hp:program pc=.call (.copy site 0) next) (hx:before (copySource site)=xs)
    (hy:before (copyTarget site)=ys) (hs:before (aux .copy)=[]):
    Runs program (5*xs.length+4) pc before next (Function.update before (copyTarget site) (xs++ys)):=by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi:SemiprimeD1StackMultiplierLink.DataRel (copyStack site) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=SemiprimeD1StackMultiplierLink.data_update (copyStack site) (copy_injective site) before start.store before hi (1:Fin 3) (xs++ys)
  have he:Function.update start.store 1 (xs++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack site) (Label.copy site) (copy_injective site) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) pc next hp (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- One actual push writes exactly one Boolean cell. -/
theorem push_run (pc next:Label) (k:Stack) (bit:Bool) (before:Stack → List Bool)
    (hp:program pc=.base (.push k bit next)):
    Runs program 1 pc before next (Function.update before k (bit::before k)):=
  one_base program pc next (.push k bit next) before _ hp rfl rfl
/-- One actual pop branches on the actual bit or EOF, never a semantic address test. -/
theorem pop_run (pc empty low high:Label) (k:Stack) (before:Stack → List Bool) (word:List Bool)
    (hp:program pc=.base (.pop k empty low high)) (hw:before k=word):
    Runs program 1 pc before (SemiprimeD1StackBytecode.choose empty low high word.head?) (Function.update before k word.tail):=by
  apply one_base program _ _ _ _ _ hp
  · simp only [SemiprimeD1StackBytecode.execute,hw]
  · simp only [SemiprimeD1StackBytecode.execute,hw]
/-- All actual drain bits and the final physical EOF test are counted. -/
theorem drain_run (pc next:Label) (k:Stack) (before:Stack → List Bool) (word:List Bool)
    (hp:program pc=.base (.pop k next pc pc)) (hw:before k=word):
    Runs program (word.length+1) pc before next (Function.update before k []):=by
  induction word generalizing before with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose]
      using pop_run pc next pc pc k before [] hp hw
  | cons bit word ih=>
    have h0:=pop_run pc next pc pc k before (bit::word) hp hw
    have h1:=ih (Function.update before k word) (Function.update_self _ _ _)
    have h:=join (by cases bit <;> exact h0) h1
    simpa only [Function.update_idem,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedPrimitives
