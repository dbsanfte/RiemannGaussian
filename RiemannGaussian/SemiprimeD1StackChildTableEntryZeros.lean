/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryRows
/-! # Physically acquired remaining-rank markers allocate all zero-axis coefficients
Every zero word follows the same actual scalar reduction and logging source.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryZeros
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryView SemiprimeD1StackChildTableEntryPrimitives
open SemiprimeD1StackChildTableEntryScalar SemiprimeD1StackChildTableEntryFields SemiprimeD1StackChildTableEntryRows
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)
local notation "ctl"=>Label.local
/-- Actual zero-counter pops, scalar calls and final EOF pop, no numeric power or host vector allocation. -/
def budget (p:List Bool):Nat→Nat
  | 0=>1
  | n+1=>1+scalarTime [] p+budget p n
/-- Remaining ACTUAL acquired rank markers drive every appended zero coefficient, even at zero precision. -/
theorem zeros_run (old child:J.Stack→List Bool) (assignment path table order entry hist p:List Bool)
    (count:Nat) (hp:child J.precisionBits=p):
    Runs program (budget p count) (ctl .zeros)
      (state old child assignment path table order entry [] [] (unary count) hist)
      (ctl .clearPath) (state old child assignment path table order entry [] [] []
        ((history (List.replicate count (SR.result [] p))).reverse++hist)):=by
  induction count generalizing hist with
  | zero=>
    let w:=loopWords table order entry [] [] hist
    have h0:=pop_run .zeros (ctl .clearPath) (ctl .abort) (ctl (.precision true)) (aux .remaining)
      (view old child assignment path [] w) [] rfl rfl
    change Runs program 1 _ _ _ (Function.update (view old child assignment path [] w) (aux .remaining) []) at h0
    dsimp only [view] at h0
    rw [update_aux,words_update] at h0
    exact h0
  | succ n ih=>
    let w0:=loopWords table order entry [] (unary (n+1)) hist
    have h0:=pop_run .zeros (ctl .clearPath) (ctl .abort) (ctl (.precision true)) (aux .remaining)
      (view old child assignment path [] w0) (true::unary n) rfl rfl
    change Runs program 1 _ _ _ (Function.update (view old child assignment path [] w0) (aux .remaining) (unary n)) at h0
    dsimp only [view] at h0
    rw [update_aux,words_update] at h0
    have h1:=scalar_run true [] p old child (G.contents [] assignment [] [] [] path) (T.contents [] [] [] [] [])
      (loopWords table order entry [] (unary n) hist) hp
    have h2:=ih ((row (SR.result [] p)).reverse++hist)
    have h:=join (join h0 h1) h2
    simpa only [budget,List.replicate_succ,history,List.flatMap_cons,List.reverse_append,List.append_assoc,state,view,loopWords,w0] using h
/-- Exact scalar-source multiplication count, proved from the real loop recurrence. -/
theorem budget_eq (p:List Bool) (n:Nat):budget p n=n*(1+scalarTime [] p)+1:=by
  induction n with
  | zero=>simp only [budget,Nat.zero_mul,Nat.zero_add]
  | succ n ih=>rw [budget,ih,Nat.succ_mul];omega
end RiemannGaussian.SemiprimeD1StackChildTableEntryZeros
