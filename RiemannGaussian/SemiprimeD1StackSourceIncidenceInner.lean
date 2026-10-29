/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceParse
import RiemannGaussian.SemiprimeD1StackSourceIncidenceAddition
/-! # Actual complete inner occurrence scan, every repeated term and final false tag -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceInner
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidencePrimitives SemiprimeD1StackSourceIncidenceLoopView
open SemiprimeD1StackSourceIncidenceParse SemiprimeD1StackSourceIncidenceAddition
open SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (addBits)
namespace Spec
export SemiprimeD1StackSourceIncidenceSpec (inner term)
end Spec
/-- Proof-side complete actual inner clock; its accumulator follows real binary additions. -/
def innerClock (i:Inputs) (lo lf:List Bool) :List (List Bool×List Bool)→List Bool→Nat
  | [],_=>1
  | (ro,rf)::rows,acc=>8*(ro.length+rf.length)+17+pairClock i lo lf ro rf acc+
      innerClock i lo lf rows (addBits acc (Spec.term i.ids i.square i.cube i.fourth (lo,lf) (ro,rf)) false).bits
/-- Complete actual byte scan processes every ordered inner incidence, including diagonals and duplicates. -/
theorem inner_run (i:Inputs) (outer lo lf:List Bool) (rows:List (List Bool×List Bool)) (acc:List Bool) :
    ∃ q ≤ innerClock i lo lf rows acc,
      Runs program q .innerHeader (bank i outer (Records.records rows []) lo lf [] [] [] [] [] [] acc)
        .innerEOF (bank i outer [] lo lf [] [] [] [] [] [] (Spec.inner i.ids i.square i.cube i.fourth (lo,lf) rows acc)) :=by
  induction rows generalizing acc with
  | nil=>
    have h:=pop_run .innerHeader .abort .innerEOF (.parse true .owner) (aux .innerReader)
      (bank i outer (Records.records [] []) lo lf [] [] [] [] [] [] acc) [false] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer (Records.records [] []) lo lf [] [] [] [] [] [] acc)
      (aux .innerReader) []) at h
    rw [update_inner] at h
    exact ⟨1,le_rfl,h⟩
  | cons row rows ih=>
    rcases row with ⟨ro,rf⟩
    have h0:=read_inner i outer lo lf ro rf acc rows
    obtain ⟨q,hq,h1⟩:=pair_run i outer (Records.records rows []) lo lf ro rf acc
    obtain ⟨u,hu,h2⟩:=ih (addBits acc (Spec.term i.ids i.square i.cube i.fourth (lo,lf) (ro,rf)) false).bits
    refine ⟨_,?_,join (join h0 h1) h2⟩
    dsimp only [innerClock]
    omega
/-- The final false tag has been consumed; the real EOF peek checks its unread physical tail before cleanup. -/
theorem inner_finish (i:Inputs) (outer lo lf acc:List Bool) :
    Runs program 1 .innerEOF (bank i outer [] lo lf [] [] [] [] [] [] acc)
      (.clearKey false .owner) (bank i outer [] lo lf [] [] [] [] [] [] acc) :=by
  exact peek_run .innerEOF (.clearKey false .owner) .abort .abort (aux .innerReader)
    (bank i outer [] lo lf [] [] [] [] [] [] acc) [] rfl rfl
end RiemannGaussian.SemiprimeD1StackSourceIncidenceInner
