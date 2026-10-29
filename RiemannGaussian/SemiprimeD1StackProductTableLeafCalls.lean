/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableState
import RiemannGaussian.SemiprimeD1BooleanTreeStream
/-! # Actual original-N copies, raw-prefix reversal and whole product checker
The actual checker is embedded as fixed code. No table, entry predicate,
assignment answer, cache, guard or clock is an input to the executing program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableLeafCalls
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableState
open SemiprimeD1StackProcedureTrace
namespace X
export SemiprimeD1StackProductTablePrimitives (copy_call reverse_call)
end X

/-- Actual preserving copy of the physical reverse-prefix stack. -/
theorem copy_prefix (bits front hist : List Bool) :
    Runs program (5*front.length+4) .leaf (data bits 0 front hist)
      .reversePrefix (prefixCopied bits front hist) := by
  exact X.copy_call .prefix .leaf .reversePrefix rfl (data bits 0 front hist) rfl rfl
/-- The actual copied prefix is physically reversed into the raw assignment. -/
theorem reverse_prefix (bits front hist : List Bool) :
    Runs program (2*front.length+3) .reversePrefix (prefixCopied bits front hist)
      .check (rawReady bits front hist) := by
  have h:=X.reverse_call .prefix .reversePrefix .check rfl (prefixCopied bits front hist)
  have hd : Function.update (Function.update (prefixCopied bits front hist) (.inr .work) [])
      (.inl P.assignment) front.reverse=rawReady bits front hist := by
    funext k
    cases k with
    | inl k=>simp [prefixCopied,rawReady,data,Function.update_apply]
    | inr k=>cases k <;> rfl
  change Runs program (2*front.length+3) .reversePrefix (prefixCopied bits front hist) .check
    (Function.update (Function.update (prefixCopied bits front hist) (.inr .work) [])
      (.inl P.assignment) (front.reverse++[])) at h
  rw [List.append_nil,hd] at h
  exact h
/-- The retained original binary N is actually copied for THIS checker call. -/
theorem copy_source (bits front hist : List Bool) :
    Runs program (5*bits.length+4) .check (rawReady bits front hist)
      .verdict (checkerReady bits front hist) := by
  exact X.copy_call .source .check .verdict rfl (rawReady bits front hist) rfl rfl
/-- ONE whole actual public checker call, including original-N acquisition,
raw grouping, computed guards, residue multiplication and final equality. -/
theorem checker_call (bits front hist : List Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1StackPublicProductBounds.runBound bits front.reverse,
      Runs program (t+1) .verdict (checkerReady bits front hist) .leafClear (checked bits front hist) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPublicProductBounds.source_run_bounded bits front.reverse hb
  refine ⟨t,ht,?_⟩
  rw [checkerReady_input]
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.checker Sum.inl_injective
    P.program .start (fun _=>rfl) .verdict .leafClear rfl t
    (SemiprimeD1StackPublicProduct.initial bits front.reverse)
    (SemiprimeD1StackPublicProductExecution.done bits front.reverse)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k hk;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>cases k <;> rfl
/-- Actual computed verdict has been consumed, with every other checker role
still physically present until the subsequent literal full-bank cleanup. -/
def poppedChecker (bits front : List Bool) : P.Stack→List Bool :=
  Function.update (SemiprimeD1StackPublicProductExecution.done bits front.reverse).data P.output []
/-- Actual bit-dependent leaf-code branch, a fixed Boolean control choice. -/
def emitStart (b : Bool) : Label := if b then .one 0 else .zero 0
/-- The actual singleton result bit is popped and determines the emitted leaf.
The native expression in the theorem is only its proved value specification. -/
theorem verdict_pop (bits front hist : List Bool) :
    Runs program 1 .leafClear (checked bits front hist)
      (emitStart (SemiprimeD1StackProductTableSpec.answer bits front.reverse))
      (withChecker (data bits 0 front hist) (poppedChecker bits front)) := by
  apply one_base program .leafClear _ (.pop (.inl P.output) .bad (.zero 0) (.one 0)) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose Label.bad (.zero 0) (.one 0)
      (some (SemiprimeD1StackProductTableSpec.answer bits front.reverse)))=_
    cases SemiprimeD1StackProductTableSpec.answer bits front.reverse <;> rfl
  · funext k
    cases k with
    | inl k=>
      by_cases he:k=P.output
      · subst k;rfl
      · change (Function.update (checked bits front hist) (.inl P.output)
          (((checked bits front hist) (.inl P.output)).tail)) (.inl k)=poppedChecker bits front k
        rw [Function.update_of_ne (by intro h;exact he (Sum.inl.inj h)),poppedChecker,Function.update_of_ne he]
        rfl
    | inr k=>cases k <;> rfl
/-- Every ACTUAL reached checker data cell is paid by its own finite-machine
trace, including deliberately retained metadata, raw and private work fields. -/
theorem popped_inventory_le (bits front hist : List Bool) (hb : bits≠[]) :
    SemiprimeD1StackProductTableCleanup.inventory
      (withChecker (data bits 0 front hist) (poppedChecker bits front))≤
      100000000000000*(bits.length+front.length+2)^3 := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPublicProductBounds.source_run_bounded bits front.reverse hb
  have hs:=SemiprimeD1StackPublicProductBounds.prefix_cells bits front.reverse hb t
    (SemiprimeD1StackPublicProductExecution.done bits front.reverse) hr
  simp only [SemiprimeD1StackPublicProductExecution.done,List.length_nil,Nat.add_zero,List.length_reverse] at hs
  apply le_trans (b:=∑k : P.Stack,((SemiprimeD1StackPublicProductExecution.done bits front.reverse).data k).length) ?_ hs
  apply Finset.sum_le_sum
  intro k hk
  change (poppedChecker bits front k).length≤_
  by_cases he:k=P.output
  · simp only [poppedChecker,he,Function.update_same,List.length_nil,Nat.zero_le]
  · simp only [poppedChecker,Function.update_of_ne he,le_refl]
end RiemannGaussian.SemiprimeD1StackProductTableLeafCalls
