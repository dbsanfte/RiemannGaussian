/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearNormalize
/-! # Own real primitive and signed-subtraction physical-byte bounds -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearArithmeticBounds
open SemiprimeD1StackKernelLinearView SemiprimeD1StackKernelLinearPrimitives
open SemiprimeBitArithmetic SemiprimeBitDivision
namespace Spec
export SemiprimeD1StackKernelLinearSpec (magnitude odd decompose power_length)
end Spec
namespace Signed
export SemiprimeD1StackKernelLinearSigned (timeBound firstTime reverseTime)
end Signed
namespace Tail
export SemiprimeD1StackKernelLinearTail (divideTime quotient remainder)
end Tail
/-- The real add/subtract output widths are bounded before any actual operand values. -/
theorem add_length (xs ys:List Bool):
    (addBits xs ys false).bits.length ≤ max xs.length ys.length+1:=(addBits_counts xs ys false).2.2.2.2
/-- A ripple difference retains exactly the maximum actual physical input width. -/
theorem sub_length (xs ys:List Bool):
    (subBits xs ys false).result.bits.length=max xs.length ys.length:=(subBits_counts xs ys false).2.2.2.2
/-- Signed reversal preserves all original padding, including a zero magnitude. -/
theorem magnitude_length (xs ys:List Bool):
    (Spec.magnitude xs ys).length=max xs.length ys.length:=by
  unfold Spec.magnitude
  split
  · rw [sub_length,Nat.max_comm]
  · exact sub_length xs ys
/-- The actual retained suffix never exceeds the physical input word. -/
theorem odd_length (xs:List Bool):(Spec.odd xs).length ≤ xs.length:=by
  have h:=congrArg List.length (Spec.decompose xs)
  simp only [List.length_append,List.length_replicate] at h
  omega
/-- Actual copy/ripple/reversal/return addition cost. -/
theorem addTime_le (xs ys:List Bool):addTime xs ys ≤ 10*(xs.length+ys.length+1):=by
  have h:=add_length xs ys
  have hm:max xs.length ys.length ≤ xs.length+ys.length:=max_le (by omega) (by omega)
  unfold addTime
  omega
/-- Actual subtraction includes the true borrow-prefix output and real caller return. -/
theorem subTime_le (xs ys:List Bool):subTime xs ys ≤ 10*(xs.length+ys.length+1):=by
  have h:=sub_length xs ys
  have hm:max xs.length ys.length ≤ xs.length+ys.length:=max_le (by omega) (by omega)
  unfold subTime
  omega
/-- Actual fitting clock charges padding and the entire discarded source suffix. -/
theorem fitTime_le (xs template:List Bool):
    SemiprimeD1StackKernelLinearCalls.fitTime xs template ≤ 10*template.length+xs.length+9:=by
  have h: (xs.drop template.length).length ≤ xs.length:=by simp only [List.length_drop];omega
  unfold SemiprimeD1StackKernelLinearCalls.fitTime SemiprimeD1StackWordFitExecution.totalTime
  omega
/-- Both physically executed signed branches have a common linear source-width bound. -/
theorem signedTime_le (w:Words) (r:Nat) (hj:w.j.length ≤ r) (hd:w.displacement.length ≤ r):
    Signed.timeBound w ≤ 100*(r+1):=by
  have h0:=subTime_le w.j w.displacement
  have h1:=subTime_le w.displacement w.j
  have hw:=sub_length w.j w.displacement
  have hm:max w.j.length w.displacement.length ≤ r:=max_le hj hd
  unfold Signed.timeBound
  split
  · dsimp only [Signed.firstTime,Signed.reverseTime]
    omega
  · dsimp only [Signed.firstTime]
    omega
/-- Whole actual restoring-divider loop, paid copies and retained quotient cache. -/
theorem divideTime_le (w:Words) (r:Nat) (ha:w.alpha.length ≤ r) (hc:w.content.length ≤ r+1):
    Tail.divideTime w ≤ 20000*(r+2)^2:=by
  have h0:=SemiprimeD1StackDividerExecution.source_time w.alpha w.content
  have h1:=SemiprimeD1StackDividerExecution.timeBound_le_square w.alpha.length w.content.length
  have hw: (Tail.quotient w).length=w.alpha.length:=(divideLoop_widths w.alpha w.content).2.1
  have hm:w.alpha.length+w.content.length+2 ≤ 2*r+3:=by omega
  have hp:(w.alpha.length+w.content.length+2)^2 ≤ (2*r+3)^2:=Nat.pow_le_pow_left hm 2
  unfold Tail.divideTime
  nlinarith only [h0,h1,hw,ha,hc,hp]
end RiemannGaussian.SemiprimeD1StackKernelLinearArithmeticBounds
