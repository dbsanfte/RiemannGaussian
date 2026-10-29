/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformTable
import RiemannGaussian.SemiprimeD1StackStaticTableSpec
/-! # Concrete complete trace contract from the frozen actual transform checker
There is no unknown checker/acquisition supplier in this instance. The entire
literal204-role source executes for every leaf, with its own proved bit clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformTableTrace
open SemiprimeD1StackPublicTransformTable SemiprimeD1StackStaticTableSpec
/-- Actual complete transform postcondition, used only in specifications. -/
def answer (bits : List Bool) (second inverse : Bool) (raw : List Bool) : Bool :=
  SemiprimeD1StackPublicTransformOriginal.verdict bits raw second inverse
/-- The frozen complete original-input arithmetic source allowance. -/
def budget (bits : List Bool) (width : Nat) : Nat :=10^90*(bits.length+width+1)^18
/-- Real template copy and reversed physical prefix reproduce the frozen input. -/
theorem initial_eq (bits raw : List Bool) (second inverse : Bool) :
    checkerInitial static (inputTemplate bits second inverse) raw=P.initial bits raw second inverse := by
  apply congrArg (fun d=>(⟨some .start,none,none,d,[]⟩:SemiprimeD1StackCalls.State P.Stack P.Label))
    (template_raw_update bits raw second inverse)
/-- Concrete contract discharged by the frozen ENTIRE original transform source,
including actual roots/axes/modulus/normalization/vectors/guards/every query. -/
theorem actual_trace (bits : List Bool) (second inverse : Bool)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) :
    CheckerTrace static (inputTemplate bits second inverse) (answer bits second inverse) (budget bits) := by
  intro raw
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPublicTransformResources.source_run_bounded bits raw second inverse hc hN
  refine ⟨t,ht,SemiprimeD1StackPublicTransformMachine.done bits raw second inverse,rfl,rfl,?_,?_⟩
  · rw [initial_eq];exact hr
  · exact SemiprimeD1StackPublicTransformOriginal.final_output bits raw second inverse
/-- ONLY N and two physical singleton descriptor flags populate the template.
No arithmetic source, width/count, normalizer, vector, guard or verdict is present. -/
theorem template_only (bits : List Bool) (second inverse : Bool) (k : P.Stack) :
    inputTemplate bits second inverse k=
      if k=P.inputRole then bits else if k=P.second then [second] else if k=P.inverse then [inverse] else [] := by
  have hk:=roles_complete k
  change k∈roles at hk
  simp only [roles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst k;rfl
/-- Each initialized physical field is paid by actual N bytes and a flag cell. -/
theorem template_cell_le (bits : List Bool) (second inverse : Bool) (k : P.Stack) :
    (inputTemplate bits second inverse k).length≤bits.length+1 := by
  rw [template_only]
  split
  · omega
  · split
    · simp only [List.length_cons,List.length_nil];omega
    · split <;> simp only [List.length_cons,List.length_nil] <;> omega
end RiemannGaussian.SemiprimeD1StackPublicTransformTableTrace
