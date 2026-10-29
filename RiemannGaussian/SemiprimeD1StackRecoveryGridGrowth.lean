/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridCalls
/-! # Paid physical grid-size doubling and index-template growth -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridGrowth
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackProcedureTrace
/-- Only four actual mutable growth buffers; every other original/cache word is retained. -/
def buffers (w:Words) (scan todo work index:List Bool) :Words:=
  {w with auxiliary:=fun k=>match k with
    | .scan=>scan | .todo=>todo | .doubleWork=>work | .indexTemplate=>index | _=>w.auxiliary k}
/-- A real write of scan changes exactly its actual growth buffer. -/
theorem update_scan (w:Words) (scan todo work index xs:List Bool) :
    Function.update (bank (buffers w scan todo work index)) (aux .scan) xs=
      bank (buffers w xs todo work index):=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · rcases p with p|p
      · rfl
      · rcases p with p|p
        · rfl
        · rcases p with p|p
          · rfl
          · cases p <;> simp [bank,buffers,aux]
/-- A real write of todo changes exactly its actual growth buffer. -/
theorem update_todo (w:Words) (scan todo work index xs:List Bool) :
    Function.update (bank (buffers w scan todo work index)) (aux .todo) xs=
      bank (buffers w scan xs work index):=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · rcases p with p|p
      · rfl
      · rcases p with p|p
        · rfl
        · rcases p with p|p
          · rfl
          · cases p <;> simp [bank,buffers,aux]
/-- A real write of doubleWork changes exactly its actual growth buffer. -/
theorem update_doubleWork (w:Words) (scan todo work index xs:List Bool) :
    Function.update (bank (buffers w scan todo work index)) (aux .doubleWork) xs=
      bank (buffers w scan todo xs index):=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · rcases p with p|p
      · rfl
      · rcases p with p|p
        · rfl
        · rcases p with p|p
          · rfl
          · cases p <;> simp [bank,buffers,aux]
/-- A real write of indexTemplate changes exactly its actual growth buffer. -/
theorem update_indexTemplate (w:Words) (scan todo work index xs:List Bool) :
    Function.update (bank (buffers w scan todo work index)) (aux .indexTemplate) xs=
      bank (buffers w scan todo work xs):=by
  funext p
  rcases p with p|p
  · rfl
  · rcases p with p|p
    · rfl
    · rcases p with p|p
      · rfl
      · rcases p with p|p
        · rfl
        · rcases p with p|p
          · rfl
          · cases p <;> simp [bank,buffers,aux]
/-- Actual TRUE cells are consumed individually and two actual TRUE cells are pushed for each. -/
theorem double_drain (w:Words) (scan index:List Bool) (n m:Nat) :
    Runs program (3*n+1) (.local .doubleDrain)
      (bank (buffers w scan (List.replicate n true) (List.replicate m true) index))
      (.local .doubleRestore)
      (bank (buffers w scan [] (List.replicate (m+2*n) true) index)):=by
  induction n generalizing m with
  | zero=>
    have h:=PTrace.pop_run (.local .doubleDrain) (.local .doubleRestore) (.local .abort)
      (.local .doubleFirst) (aux .todo) (bank (buffers w scan [] (List.replicate m true) index)) [] rfl rfl
    rw [update_todo] at h
    exact h
  | succ n ih=>
    have h0:=PTrace.pop_run (.local .doubleDrain) (.local .doubleRestore) (.local .abort)
      (.local .doubleFirst) (aux .todo)
      (bank (buffers w scan (List.replicate (n+1) true) (List.replicate m true) index))
      (true::List.replicate n true) rfl (by simp [bank,buffers,aux,List.replicate_succ])
    rw [update_todo] at h0
    change Runs program 1 _ _ (.local .doubleFirst) _ at h0
    have h1:=PTrace.push_run (.local .doubleFirst) (.local .doubleSecond) (aux .doubleWork) true
      (bank (buffers w scan (List.replicate n true) (List.replicate m true) index)) rfl
    change Runs program 1 _ _ _ (Function.update _ (aux .doubleWork) (true::List.replicate m true)) at h1
    rw [update_doubleWork] at h1
    rw [←List.replicate_succ] at h1
    have h2:=PTrace.push_run (.local .doubleSecond) (.local .doubleDrain) (aux .doubleWork) true
      (bank (buffers w scan (List.replicate n true) (List.replicate (m+1) true) index)) rfl
    change Runs program 1 _ _ _ (Function.update _ (aux .doubleWork) (true::List.replicate (m+1) true)) at h2
    rw [update_doubleWork,←List.replicate_succ] at h2
    have h3:=ih (m+1+1)
    have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
    simpa only [show 1+1+1+(3*n+1)=3*(n+1)+1 by omega,
      show m+1+1+2*n=m+2*(n+1) by omega] using h
/-- The real reverse-style restore consumes each work marker and pushes it onto todo. -/
theorem double_restore (w:Words) (scan index:List Bool) (n m:Nat) :
    Runs program (2*n+1) (.local .doubleRestore)
      (bank (buffers w scan (List.replicate m true) (List.replicate n true) index))
      (.local .grow)
      (bank (buffers w scan (List.replicate (m+n) true) [] index)):=by
  induction n generalizing m with
  | zero=>
    have h:=PTrace.pop_run (.local .doubleRestore) (.local .grow) (.local .abort)
      (.local .doubleSave) (aux .doubleWork) (bank (buffers w scan (List.replicate m true) [] index)) [] rfl rfl
    rw [update_doubleWork] at h
    exact h
  | succ n ih=>
    have h0:=PTrace.pop_run (.local .doubleRestore) (.local .grow) (.local .abort)
      (.local .doubleSave) (aux .doubleWork)
      (bank (buffers w scan (List.replicate m true) (List.replicate (n+1) true) index))
      (true::List.replicate n true) rfl (by simp [bank,buffers,aux,List.replicate_succ])
    rw [update_doubleWork] at h0
    change Runs program 1 _ _ (.local .doubleSave) _ at h0
    have h1:=PTrace.push_run (.local .doubleSave) (.local .doubleRestore) (aux .todo) true
      (bank (buffers w scan (List.replicate m true) (List.replicate n true) index)) rfl
    change Runs program 1 _ _ _ (Function.update _ (aux .todo) (true::List.replicate m true)) at h1
    rw [update_todo,←List.replicate_succ] at h1
    have h2:=ih (m+1)
    have h:=PTrace.join (PTrace.join h0 h1) h2
    simpa only [show 1+1+(2*n+1)=2*(n+1)+1 by omega,
      show m+1+n=m+(n+1) by omega] using h
/-- One actual doubling pays both complete marker passes and preserves every source/cache word. -/
theorem double_run (w:Words) (scan index:List Bool) (n:Nat) :
    Runs program (7*n+2) (.local .doubleDrain)
      (bank (buffers w scan (List.replicate n true) [] index))
      (.local .grow) (bank (buffers w scan (List.replicate (2*n) true) [] index)):=by
  have h0:=double_drain w scan index n 0
  have h1:=double_restore w scan index (2*n) 0
  simp only [Nat.zero_add,List.replicate_zero] at h0 h1
  have h:=PTrace.join h0 h1
  simpa only [show 3*n+1+(2*(2*n)+1)=7*n+2 by omega] using h
/-- Own exact instruction budget of the physically nested marker-doubling loop. -/
def growTime :Nat→Nat→Nat
  | 0,_=>1
  | steps+1,n=>7*n+4+growTime steps (2*n)
/-- Actual original a markers drive the entire doubling loop; no numerical grid size is supplied. -/
theorem grow_run (w:Words) (steps n width:Nat) :
    Runs program (growTime steps n) (.local .grow)
      (bank (buffers w (List.replicate steps true) (List.replicate n true) [] (List.replicate width false)))
      (.local .heightCheck)
      (bank (buffers w [] (List.replicate (n*2^steps) true) [] (List.replicate (width+steps) false))):=by
  induction steps generalizing n width with
  | zero=>
    have h:=PTrace.pop_run (.local .grow) (.local .heightCheck) (.local .abort) (.local .indexBit)
      (aux .scan) (bank (buffers w [] (List.replicate n true) [] (List.replicate width false))) [] rfl rfl
    rw [update_scan] at h
    change Runs program 1 _ _ (.local .heightCheck) (bank (buffers w [] (List.replicate n true) [] (List.replicate width false))) at h
    simpa only [growTime,pow_zero,Nat.mul_one,Nat.add_zero,List.replicate_zero] using h
  | succ steps ih=>
    have h0:=PTrace.pop_run (.local .grow) (.local .heightCheck) (.local .abort) (.local .indexBit)
      (aux .scan)
      (bank (buffers w (List.replicate (steps+1) true) (List.replicate n true) [] (List.replicate width false)))
      (true::List.replicate steps true) rfl (by simp [bank,buffers,aux,List.replicate_succ])
    rw [update_scan] at h0
    change Runs program 1 _ _ (.local .indexBit) _ at h0
    have h1:=PTrace.push_run (.local .indexBit) (.local .doubleDrain) (aux .indexTemplate) false
      (bank (buffers w (List.replicate steps true) (List.replicate n true) [] (List.replicate width false))) rfl
    change Runs program 1 _ _ _ (Function.update _ (aux .indexTemplate) (false::List.replicate width false)) at h1
    rw [update_indexTemplate,←List.replicate_succ] at h1
    have h2:=double_run w (List.replicate steps true) (List.replicate (width+1) false) n
    have h3:=ih (2*n) (width+1)
    have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
    have hn:(2*n)*2^steps=n*2^(steps+1):=by rw [pow_succ];ring
    simpa only [growTime,hn,show width+1+steps=width+(steps+1) by omega,
      show 1+1+(7*n+2)=7*n+4 by omega] using h
/-- All emitted markers and all actual growing passes have a uniform VALUE bound. -/
theorem growTime_le (steps n:Nat) :growTime steps n≤20*(steps+1)*(n*2^steps+1):=by
  induction steps generalizing n with
  | zero=>simp only [growTime,pow_zero,Nat.mul_one];omega
  | succ steps ih=>
    have hi:=ih (2*n)
    have hp:1≤2^steps:=Nat.one_le_pow steps 2 (by decide)
    have hn:n≤n*2^steps:=by nlinarith
    rw [growTime,pow_succ]
    nlinarith
end RiemannGaussian.SemiprimeD1StackRecoveryGridGrowth
