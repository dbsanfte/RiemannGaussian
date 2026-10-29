/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackKernelLinearArithmeticBounds
/-! # Own fixed polynomial for the whole real normalization continuation -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearNormalizeBounds
open SemiprimeD1StackKernelLinearView SemiprimeD1StackKernelLinearArithmeticBounds
open SemiprimeBitDivision
namespace Norm
export SemiprimeD1StackKernelLinearNormalize (timeBound mag scanned signed zeroed prepared divided)
end Norm
namespace Scan
export SemiprimeD1StackKernelLinearScan (timeBound timeBound_le leading_le result)
end Scan
namespace Tail
export SemiprimeD1StackKernelLinearTail (prepareTime divideTime quotient remainder)
end Tail
namespace Finish
export SemiprimeD1StackKernelLinearFinish (timeBound)
end Finish
/-- The acquired-cache normalization time depends only on actual physical word lengths.
No old native clock, factor width advice or arithmetic callback is a premise. -/
theorem timeBound_le (w:Words) (r:Nat) (hj:w.j.length ≤ r) (hd:w.displacement.length ≤ r)
    (ha:w.alpha.length ≤ r) (hb:w.buffer.length ≤ r):Norm.timeBound w ≤ 1000000*(r+2)^2:=by
  have hm:(Norm.mag w).length ≤ r:=by
    rw [Norm.mag,magnitude_length]
    exact max_le hj hd
  have ho:(SemiprimeD1StackKernelLinearSpec.odd (Norm.mag w)).length ≤ r:=
    (odd_length (Norm.mag w)).trans hm
  have hl:=Scan.leading_le (Norm.mag w)
  have hc:(SemiprimeD1StackKernelLinearSpec.power
      (SemiprimeD1StackKernelLinearSpec.leading (Norm.mag w))).length ≤ r+1:=by
    rw [SemiprimeD1StackKernelLinearSpec.power_length]
    omega
  have h0:=signedTime_le w r hj hd
  have h1:Scan.timeBound (Norm.mag w) ≤ 10*(r+1):=(Scan.timeBound_le (Norm.mag w)).trans (by omega)
  have h2:((Norm.scanned w).content.length+3)+(5*(Norm.scanned w).alpha.length+4)+1 ≤ 6*r+9:=by
    change (SemiprimeD1StackKernelLinearSpec.power
      (SemiprimeD1StackKernelLinearSpec.leading (Norm.mag w))).length+3+(5*w.alpha.length+4)+1 ≤ _
    omega
  have h3:Finish.timeBound (Norm.zeroed w) (Norm.mag w) [] [] ≤ 2*r+13:=by
    change (Norm.mag w).length+w.buffer.length+0+0+13 ≤ _
    omega
  have h4:Tail.prepareTime (Norm.scanned w) (Norm.mag w) ≤ 10*(r+1):=by
    change (5*(SemiprimeD1StackKernelLinearSpec.odd (Norm.mag w)).length+4)+
      ((SemiprimeD1StackKernelLinearSpec.odd (Norm.mag w)).length+3)+((Norm.mag w).length+3) ≤ _
    omega
  have h5:=divideTime_le (Norm.prepared w) r ha hc
  have hq:(Tail.quotient (Norm.prepared w)).length ≤ r:=by
    rw [Tail.quotient,(divideLoop_widths _ _).2.1]
    exact ha
  have hr:(Tail.remainder (Norm.prepared w)).length ≤ r+1:=by
    rw [Tail.remainder,(divideLoop_widths _ _).1]
    exact hc
  have h6:Finish.timeBound (Norm.divided w) [] (Tail.remainder (Norm.prepared w))
      (Tail.quotient (Norm.prepared w)) ≤ 3*r+14:=by
    change 0+w.buffer.length+(Tail.quotient (Norm.prepared w)).length+(Tail.remainder (Norm.prepared w)).length+13 ≤ _
    omega
  have hp:r+1 ≤ (r+2)^2:=by nlinarith
  unfold Norm.timeBound
  split
  · nlinarith only [h0,h1,h2,h3,hp]
  · nlinarith only [h0,h1,h4,h5,h6,hp]
end RiemannGaussian.SemiprimeD1StackKernelLinearNormalizeBounds
