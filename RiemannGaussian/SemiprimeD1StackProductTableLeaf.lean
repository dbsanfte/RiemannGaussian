/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableLeafCode
/-! # Whole literal product-table leaf, with full physical reuse cleanup
Every leaf executes the real original-input checker and physically drains ALL76
checker roles. Its complete own clock includes copies, reversal, scalar writes,
all cleanup reads/EOFs, and the actual recursive return-label pop.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableLeaf
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableState SemiprimeD1StackProductTableSpec
open SemiprimeD1StackProductTableLeafCalls SemiprimeD1StackProductTableLeafCode
open SemiprimeD1StackProcedureTrace SemiprimeD1StackProcedureReturns
open SemiprimeD1BooleanTreeStream (leafBytes)
/-- Full literal-bank clearing retains exactly the private reached DFS store. -/
theorem clean_withChecker (bits : List Bool) (depth : ℕ) (front hist : List Bool)
    (checker : P.Stack→List Bool) :
    SemiprimeD1StackProductTableCleanup.clean (withChecker (data bits depth front hist) checker)=
      data bits depth front hist := by funext k;cases k <;> rfl
/-- Own uniform leaf clock, fixed before ALL original N and prefix words. -/
def leafBound (bits front : List Bool) : ℕ :=1000000000000000000*(bits.length+front.length+2)^3
/-- Exact chronological composition of actual fragments of this SAME program. -/
theorem chain {m n : ℕ} {pc mid next : Label} {input middle output : Stack→List Bool}
    (h : Runs program m pc input mid middle) (g : Runs program n mid middle next output) :
    Runs program (m+n) pc input next output := runs_trans program _ _ _ _ _ _ _ _ h g
/-- COMPLETE actual leaf: reverse the real prefix, copy N, execute original
product checker, pop its real result, write its literal scalar, drain ALL76
roles and actually return. No entry producer/evaluator/cache/clock is input. -/
theorem leaf_returns (bits front hist : List Bool) (hb : bits≠[]) :
    ∃t≤leafBound bits front,Returns program t .leaf (data bits 0 front hist)
      (data bits 0 front ((leafBytes (answer bits front.reverse)).reverse++hist)) := by
  let b:=answer bits front.reverse
  let nextHist:=(leafBytes b).reverse++hist
  let cleanupData:=withChecker (data bits 0 front nextHist) (poppedChecker bits front)
  have h0:=copy_prefix bits front hist
  have h1:=reverse_prefix bits front hist
  have h2:=copy_source bits front hist
  obtain ⟨t,ht,h3⟩:=checker_call bits front hist hb
  have h4:=verdict_pop bits front hist
  have h5:=emit_run b (poppedChecker bits front) bits front hist
  obtain ⟨m,hm,hclear⟩:=SemiprimeD1StackProductTableCleanup.clear_returns cleanupData
  have h6:=SemiprimeD1StackProcedureReturns.call program m .leafCleanup (.clear 0) .leafReturn
    cleanupData (SemiprimeD1StackProductTableCleanup.clean cleanupData) rfl hclear
  have he:SemiprimeD1StackProductTableCleanup.clean cleanupData=data bits 0 front nextHist:=
    clean_withChecker bits 0 front nextHist (poppedChecker bits front)
  rw [he] at h6
  have h:=chain h0 (chain h1 (chain h2 (chain h3 (chain h4 (chain h5 h6)))))
  refine ⟨_,?_,of_runs program _ .leaf .leafReturn _ _ h rfl⟩
  let I:=bits.length+front.length+2
  have hi:bits.length+front.length+2≤I^3 := by
    have hp:=Nat.pow_le_pow_right (by dsimp [I];omega : 1≤I) (by decide : 1≤3)
    simpa only [pow_one,I] using hp
  have ht':t≤1000000000000*I^3 := by
    simpa only [SemiprimeD1StackPublicProductBounds.runBound,List.length_reverse,I] using ht
  have hc:=popped_inventory_le bits front nextHist hb
  change SemiprimeD1StackProductTableCleanup.inventory cleanupData≤100000000000000*I^3 at hc
  have hl:(leafBytes b).length≤6 := by cases b <;> decide
  change _≤1000000000000000000*I^3
  omega
/-- Literal false/true vector is the EXACT old root scalar payload for this
actually acquired raw assignment, before any tensor product or reduction. -/
theorem leaf_bytes (bits front : List Bool) :
    leafBytes (answer bits front.reverse)=SemiprimeD1TensorTapeCodec.tape (tree bits front.reverse 0) :=
  SemiprimeD1BooleanTreeStream.leafBytes_original _
end RiemannGaussian.SemiprimeD1StackProductTableLeaf
