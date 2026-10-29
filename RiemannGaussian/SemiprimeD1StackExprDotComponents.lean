/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprDotSpec

/-! # Actual copy and exponent-acquisition calls inside dot construction
The products below are consequences of included literal machine traces. No
intermediate product, timing, selected value or resolved syntax is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprDotComponents
open SemiprimeD1StackExprDot SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)
local notation "ctl" => SemiprimeD1StackExprDot.Label.control

/-- A real included Copy works on the reached bank and restores its own scratch. -/
theorem copy_call (kind : CopyKind) (data : Stack→List Bool) (hs : data .copyScratch=[])
    (pc next : Label) (hcall : program pc=.call (.copy kind 0) next) :
    Runs program (5*(data (copyInput kind)).length+4) pc data next
      (Function.update data (copyOutput kind) (data (copyInput kind)++data (copyOutput kind))) := by
  apply included_call program (copyStack kind) (Label.copy kind) (copyStack_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hcall
    (5*(data (copyInput kind)).length+3)
    (SemiprimeD1StackCopy.state 0 none (data (copyInput kind)) (data (copyOutput kind)) [])
    (SemiprimeD1StackCopy.done (data (copyInput kind)) (data (copyInput kind)++data (copyOutput kind)))
    data (Function.update data (copyOutput kind) (data (copyInput kind)++data (copyOutput kind)))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · constructor
    · intro k;fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,hs]
    · intro k _;rfl
  · constructor
    · intro k
      cases kind <;> fin_cases k <;>
        simp [copyStack,copyInput,copyOutput,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,Function.update,hs]
    · intro k hk
      have hn : k≠copyOutput kind := by
        intro he
        apply hk 1
        simpa only [copyStack,show ¬((1:Fin 3)=0) by decide,ite_false,ite_true] using he.symm
      exact Function.update_of_ne hn _ _

/-- The loop-index multiplier is acquired by an actual preserving copy. -/
theorem copy_product (c : Cache) (remaining out : List Bool) :
    Runs program (5*remaining.length+4) (ctl .copyProduct) (bank c {remaining:=remaining,output:=out})
      (ctl .productFirst) (bank c {remaining:=remaining,multiplier:=remaining,output:=out}) := by
  have h:=copy_call .product (bank c {remaining:=remaining,output:=out}) rfl
    (ctl .copyProduct) (ctl .productFirst) rfl
  have he : Function.update (bank c {remaining:=remaining,output:=out}) .multiplier remaining=
      bank c {remaining:=remaining,multiplier:=remaining,output:=out} := by
    funext k;cases k <;> simp [Function.update,bank]
  simpa only [copyInput,copyOutput,bank,List.append_nil,he] using h

/-- Actual first unary product acquires j*frequency and preserves the frequency
cache. Its only numeric premises identify the physically present original tapes. -/
theorem product_first (c : Cache) (j frequency : ℕ) (hf : c.frequency=unary frequency)
    (out : List Bool) :
    ∃t ≤ 5*(j*(2*frequency+3)+1),Runs program (t+1) (ctl .productFirst)
      (bank c {remaining:=unary j,multiplier:=unary j,output:=out}) (ctl .productSecond)
      (bank c {remaining:=unary j,intermediate:=unary (j*frequency),output:=out}) := by
  obtain ⟨t,ht,hr⟩:=U.product_run j frequency
  refine ⟨t,ht,?_⟩
  apply included_call program (productStack false) (Label.product false) (productStack_injective false)
    U.code U.entry (fun _=>rfl) (ctl .productFirst) (ctl .productSecond) rfl t
    (⟨some U.entry,none,U.contents (unary j) (unary frequency) [] []⟩:
      SemiprimeD1StackBytecode.State U.Stack U.Label)
    (⟨none,none,U.contents [] (unary frequency) [] (unary (j*frequency))⟩:
      SemiprimeD1StackBytecode.State U.Stack U.Label)
    (bank c {remaining:=unary j,multiplier:=unary j,output:=out})
    (bank c {remaining:=unary j,intermediate:=unary (j*frequency),output:=out})
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> simp [productStack,bank,U.contents,hf]
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> simp [productStack,bank,U.contents,hf]
    · intro k hk
      cases k <;> first | rfl | exact False.elim (hk .multiplier rfl) | exact False.elim (hk .product rfl)

/-- The actual second product consumes the actual first product directly and
acquires the complete original exponent stride*(j*frequency). -/
theorem product_second (c : Cache) (j stride frequency : ℕ) (hs : c.stride=unary stride)
    (out : List Bool) :
    ∃t ≤ 5*((j*frequency)*(2*stride+3)+1),Runs program (t+1) (ctl .productSecond)
      (bank c {remaining:=unary j,intermediate:=unary (j*frequency),output:=out}) (ctl .powerCall)
      (bank c {remaining:=unary j,exponent:=unary (stride*(j*frequency)),output:=out}) := by
  obtain ⟨t,ht,hr⟩:=U.product_run (j*frequency) stride
  refine ⟨t,ht,?_⟩
  apply included_call program (productStack true) (Label.product true) (productStack_injective true)
    U.code U.entry (fun _=>rfl) (ctl .productSecond) (ctl .powerCall) rfl t
    (⟨some U.entry,none,U.contents (unary (j*frequency)) (unary stride) [] []⟩:
      SemiprimeD1StackBytecode.State U.Stack U.Label)
    (⟨none,none,U.contents [] (unary stride) [] (unary (stride*(j*frequency)))⟩:
      SemiprimeD1StackBytecode.State U.Stack U.Label)
    (bank c {remaining:=unary j,intermediate:=unary (j*frequency),output:=out})
    (bank c {remaining:=unary j,exponent:=unary (stride*(j*frequency)),output:=out})
  · rfl
  · rfl
  · simpa only [Nat.mul_comm (j*frequency) stride] using hr
  · constructor
    · intro k;cases k <;> simp [productStack,bank,U.contents,hs]
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> simp [productStack,bank,U.contents,hs]
    · intro k hk
      cases k <;> first | rfl | exact False.elim (hk .multiplier rfl) | exact False.elim (hk .product rfl)

/-- The actual full power-syntax builder executes with the product tape acquired
above. All syntax/base/counter scratch and both caches follow its literal trace. -/
theorem power_call (c : Cache) (j e : ℕ) (out : List Bool) :
    Runs program (SemiprimeD1StackExprPowerExecution.totalTime c.base (unary e)+1)
      (ctl .powerCall) (bank c {remaining:=unary j,exponent:=unary e,output:=out})
      (ctl .clearExponent) (bank c {remaining:=unary j,exponent:=unary e,output:=SemiprimeD1StackExprPowerSpec.result e c.base out}) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program powerStack Label.power powerStack_injective
    Power.program .start (fun _=>rfl) (ctl .powerCall) (ctl .clearExponent) rfl
    (SemiprimeD1StackExprPowerExecution.totalTime c.base (unary e)) (Power.initial c.base (unary e) out)
    (SemiprimeD1StackExprPowerExecution.done c.base (unary e) out)
    (bank c {remaining:=unary j,exponent:=unary e,output:=out})
    (bank c {remaining:=unary j,exponent:=unary e,output:=SemiprimeD1StackExprPowerSpec.result e c.base out})
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackExprPowerExecution.source_run c.base (unary e) out
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      fin_cases k <;> simp [powerStack,bank,SemiprimeD1StackExprPowerExecution.done,
        SemiprimeD1StackExprPower.store,unary]
    · intro k hk
      cases k <;> first | rfl | exact False.elim (hk 4 rfl)

/-- Every preserved exponent marker is physically cleared before the next term. -/
theorem clear_exponent (c : Cache) (remaining exponent out : List Bool) :
    Runs program (exponent.length+1) (ctl .clearExponent)
      (bank c {remaining:=remaining,exponent:=exponent,output:=out}) (ctl .copyIndex)
      (bank c {remaining:=remaining,output:=out}) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (ctl .clearExponent) (ctl .copyIndex)
    Stack.exponent rfl (bank c {remaining:=remaining,output:=out}) exponent
  have hi : Function.update (bank c {remaining:=remaining,output:=out}) Stack.exponent exponent=
      bank c {remaining:=remaining,exponent:=exponent,output:=out} := by
    funext k;cases k <;> simp [Function.update,bank]
  have ho : Function.update (bank c {remaining:=remaining,output:=out}) Stack.exponent []=
      bank c {remaining:=remaining,output:=out} := Function.update_eq_self _ _
  rw [hi,ho] at h
  exact h

/-- The selected-word index comes from another real preserving loop-counter Copy. -/
theorem copy_index (c : Cache) (remaining out : List Bool) :
    Runs program (5*remaining.length+4) (ctl .copyIndex) (bank c {remaining:=remaining,output:=out})
      (ctl .readCall) (bank c {remaining:=remaining,index:=remaining,output:=out}) := by
  have h:=copy_call .index (bank c {remaining:=remaining,output:=out}) rfl (ctl .copyIndex) (ctl .readCall) rfl
  have he : Function.update (bank c {remaining:=remaining,output:=out}) .index remaining=
      bank c {remaining:=remaining,index:=remaining,output:=out} := by
    funext k;cases k <;> simp [Function.update,bank]
  simpa only [copyInput,copyOutput,bank,List.append_nil,he] using h

end RiemannGaussian.SemiprimeD1StackExprDotComponents
