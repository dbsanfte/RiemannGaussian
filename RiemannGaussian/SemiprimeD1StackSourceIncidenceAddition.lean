/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceTerm
/-! # Actual total-copy/drain/ripple-add and descriptor cleanup for each ordered pair -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceAddition
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidencePrimitives SemiprimeD1StackSourceIncidenceLoopView
open SemiprimeD1StackSourceIncidenceTerm SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (addBits)
/-- Exact actual elapsed length of the paid total-copy, old-total drain and complete ripple-adder call. -/
def sumTime (acc word:List Bool) :Nat :=
  (5*acc.length+4)+(acc.length+1)+(3*(max acc.length word.length+1)+2*(addBits acc word false).bits.length+3)
/-- The source accumulator is physically copied/drained and the SAME real binary adder writes the new total. -/
theorem sum_run (i:Inputs) (outer inner lo lf ro rf word acc:List Bool) :
    Runs program (sumTime acc word) .copySum (bank i outer inner lo lf ro rf [] [] [] word acc)
      (.clearKey true .owner) (bank i outer inner lo lf ro rf [] [] [] [] (addBits acc word false).bits) :=by
  have h0:=copy_call .sum .copySum .clearTotal rfl (bank i outer inner lo lf ro rf [] [] [] word acc) rfl rfl
  change Runs program (5*acc.length+4) _ _ _
    (Function.update (bank i outer inner lo lf ro rf [] [] [] word acc) (aux .sumLeft) acc) at h0
  rw [update_sumLeft] at h0
  have h1:=drain_loop .clearTotal .add (aux .total) rfl (bank i outer inner lo lf ro rf [] [] acc word acc) acc rfl
  rw [update_total] at h1
  have h2:=add_call (bank i outer inner lo lf ro rf [] [] acc word []) rfl rfl
  change Runs program _ _ _ _
    (Function.update (Function.update (Function.update (bank i outer inner lo lf ro rf [] [] acc word [])
      (aux .sumLeft) []) (aux .term) []) (aux .total) (addBits acc word false).bits) at h2
  rw [update_sumLeft,update_term,update_total] at h2
  exact join (join h0 h1) h2
/-- Both actual inner endpoint fields are completely erased before the next inner record. -/
theorem clear_inner (i:Inputs) (outer inner lo lf ro rf total:List Bool) :
    Runs program ((ro.length+1)+(rf.length+1)) (.clearKey true .owner)
      (bank i outer inner lo lf ro rf [] [] [] [] total) .innerHeader
      (bank i outer inner lo lf [] [] [] [] [] [] total) :=by
  have h0:=drain_loop (.clearKey true .owner) (.clearKey true .factor) (aux .ownerRight) rfl
    (bank i outer inner lo lf ro rf [] [] [] [] total) ro rfl
  rw [update_ro] at h0
  have h1:=drain_loop (.clearKey true .factor) .innerHeader (aux .factorRight) rfl
    (bank i outer inner lo lf [] rf [] [] [] [] total) rf rfl
  rw [update_rf] at h1
  exact join h0 h1
/-- Both actual outer endpoint fields are erased exactly once after the complete inner scan. -/
theorem clear_outer (i:Inputs) (outer total lo lf:List Bool) :
    Runs program ((lo.length+1)+(lf.length+1)) (.clearKey false .owner)
      (bank i outer [] lo lf [] [] [] [] [] [] total) .outerHeader
      (bank i outer [] [] [] [] [] [] [] [] [] total) :=by
  have h0:=drain_loop (.clearKey false .owner) (.clearKey false .factor) (aux .ownerLeft) rfl
    (bank i outer [] lo lf [] [] [] [] [] [] total) lo rfl
  rw [update_lo] at h0
  have h1:=drain_loop (.clearKey false .factor) .outerHeader (aux .factorLeft) rfl
    (bank i outer [] [] lf [] [] [] [] [] [] total) lf rfl
  rw [update_lf] at h1
  exact join h0 h1
/-- Complete real one-pair source budget; parsing is paid separately by the actual field reader. -/
def pairClock (i:Inputs) (lo lf ro rf acc:List Bool) :Nat :=
  termClock i lo lf ro rf+sumTime acc
    (SemiprimeD1StackSourceIncidenceSpec.term i.ids i.square i.cube i.fourth (lo,lf) (ro,rf))+ro.length+1+(rf.length+1)
/-- Complete actual pair classification/addition/cleanup preserves every unrelated tape and exact chronology. -/
theorem pair_run (i:Inputs) (outer inner lo lf ro rf acc:List Bool) :
    ∃q≤pairClock i lo lf ro rf acc,
      Runs program q .ownerCall (bank i outer inner lo lf ro rf [] [] [] [] acc) .innerHeader
        (bank i outer inner lo lf [] [] [] [] [] []
          (addBits acc (SemiprimeD1StackSourceIncidenceSpec.term i.ids i.square i.cube i.fourth (lo,lf) (ro,rf)) false).bits) :=by
  obtain ⟨q,hq,h0⟩:=term_run i outer inner lo lf ro rf acc
  have h1:=sum_run i outer inner lo lf ro rf
    (SemiprimeD1StackSourceIncidenceSpec.term i.ids i.square i.cube i.fourth (lo,lf) (ro,rf)) acc
  have h2:=clear_inner i outer inner lo lf ro rf
    (addBits acc (SemiprimeD1StackSourceIncidenceSpec.term i.ids i.square i.cube i.fourth (lo,lf) (ro,rf)) false).bits
  refine ⟨_,?_,join (join h0 h1) h2⟩
  unfold pairClock
  omega
/-- Actual sum cost is linear in the physical old total and selected term; no decoded sum-width advice. -/
theorem sumTime_le (acc word:List Bool) :sumTime acc word ≤ 11*acc.length+5*word.length+13 :=by
  have h:=SemiprimeD1StackSourceIncidenceSpec.add_length acc word
  have hm:max acc.length word.length ≤ acc.length+word.length:=max_le (by omega) (by omega)
  unfold sumTime
  omega
end RiemannGaussian.SemiprimeD1StackSourceIncidenceAddition
