/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleTable
import RiemannGaussian.SemiprimeD1StackStaticTableSpec
import RiemannGaussian.SemiprimeD1StackPublicInputTableTrace
/-! # Concrete complete trace contract from the frozen actual scale checker
There is no unknown checker/acquisition supplier in this instance. The entire
literal160-role source executes for every leaf, with its own proved bit clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicScaleTableTrace
open SemiprimeD1StackPublicScaleTable SemiprimeD1StackStaticTableSpec
/-- Actual arithmetic postcondition only; it is never supplied to finite code. -/
def answer (bits stride frequency : List Bool) (inverse : Bool) (raw : List Bool) : Bool :=
  SemiprimeD1StackPublicScaleMeaning.answer (SemiprimeD1StackPublicScaleState.cached bits)
    (SemiprimeD1StackPublicScaleInputs.expression bits inverse) stride.length frequency.length
    (SemiprimeD1StackPublicScaleDot.inputWord bits raw) (SemiprimeD1StackPublicScaleDot.outputWord bits raw)
/-- The frozen actual scale checker's own full original-input polynomial. -/
def budget (bits stride frequency : List Bool) (width : Nat) : Nat :=
  10^70*(bits.length+width+stride.length+frequency.length+2)^16
/-- Real copied physical template plus actual reversed prefix is the frozen input. -/
theorem initial_eq (bits raw stride frequency : List Bool) (inverse : Bool) :
    checkerInitial static (inputTemplate bits stride frequency inverse) raw=
      P.initial bits raw stride frequency inverse := by
  apply congrArg (fun d=>(⟨some .start,none,none,d,[]⟩:SemiprimeD1StackCalls.State P.Stack P.Label))
    (template_raw_update bits raw stride frequency inverse)
/-- Concrete trace premise discharged by the SAME frozen complete real checker.
The unary-marker hypotheses describe only actual physical descriptor fields. -/
theorem actual_trace (bits stride frequency : List Bool) (inverse : Bool)
    (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) :
    CheckerTrace static (inputTemplate bits stride frequency inverse)
      (answer bits stride frequency inverse) (budget bits stride frequency) := by
  intro raw
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPublicScaleBounds.source_run_bounded bits raw stride frequency inverse
    stride.length frequency.length hj hk hc hN
  refine ⟨t,ht,SemiprimeD1StackPublicScaleExecution.done bits raw stride frequency inverse
    stride.length frequency.length,rfl,rfl,?_,?_⟩
  · rw [initial_eq];exact hr
  · exact SemiprimeD1StackPublicScaleOriginal.verdict_value bits raw stride frequency inverse _ _
/-- Only N, physical j/k markers and the singleton selector populate the template.
All arithmetic sources, moduli, vectors, guards and results are initially empty. -/
theorem template_only (bits stride frequency : List Bool) (inverse : Bool) (k : P.Stack) :
    inputTemplate bits stride frequency inverse k=
      if k=P.inputRole then bits else if k=P.stride then stride else
      if k=P.frequency then frequency else if k=P.selector then [inverse] else [] := by
  have hk:=roles_complete k
  change k∈roles at hk
  simp only [roles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst k;rfl
/-- Each physical input field is paid by its actual original bytes. -/
theorem template_cell_le (bits stride frequency : List Bool) (inverse : Bool) (k : P.Stack) :
    (inputTemplate bits stride frequency inverse k).length≤
      bits.length+stride.length+frequency.length+1 := by
  rw [template_only]
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split <;> simp only [List.length_cons,List.length_nil] <;> omega
end RiemannGaussian.SemiprimeD1StackPublicScaleTableTrace
