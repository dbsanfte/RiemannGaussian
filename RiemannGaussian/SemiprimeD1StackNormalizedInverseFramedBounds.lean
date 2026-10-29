/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseStateBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInverseNegate
/-! # Actual coefficient-row allocation and cache materialization widths -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseFramedBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseBankBounds SemiprimeD1StackNormalizedInverseWidths
open SemiprimeD1StackNormalizedInverseCoefficientFrame SemiprimeD1StackNormalizedInverseNegate
open SemiprimeD1StackNormalizedInverseOperationCall
/-- Prefix framing allocates every actual sign/denominator bit, tag and delimiter; no coefficient value is expanded. -/
theorem framed_bound (w : Words) (r c u : ℕ) (h : BoundedBank w r c u)
    (word : SemiprimeRationalBits.RationalWord) :
    BoundedBank (framed w word) r c (u+2*bytes word+3) := by
  refine ⟨h.1,h.2.1,?_⟩
  intro k
  by_cases hk:k=.prefixReverse
  · subst k
    change (Function.update w.auxiliary .prefixReverse (row word (w.auxiliary .prefixReverse)) .prefixReverse).length ≤ _
    rw [Function.update_self,row_bytes]
    have hh:=h.2.2 .prefixReverse
    omega
  · change (Function.update w.auxiliary .prefixReverse (row word (w.auxiliary .prefixReverse)) k).length ≤ _
    rw [Function.update_of_ne hk]
    exact (h.2.2 k).trans (by omega)
/-- Wider auxiliary caps retain every original/checker/shadow word bound. -/
theorem widen_aux (w : Words) (r c u v : ℕ) (h : BoundedBank w r c u) (hu : u ≤ v) : BoundedBank w r c v :=
  ⟨h.1,h.2.1,fun k=>(h.2.2 k).trans hu⟩
/-- The complete actual negated/framed row remains quadratic in original marker/template cell count. -/
theorem beforeClear_bound (w : Words) (width : List Bool) (s : ℕ) (hs : 1 ≤ s) (hw : width.length ≤ s)
    (h : BoundedBank w s (5*s) (14*s^2)) :
    BoundedBank (beforeClear w width) s (5*s) (30*s^2) := by
  have hseed:=put_bound w s (5*s) (14*s^2) h .right SemiprimeRationalBits.zeroWord (by rw [zero_bytes];omega)
  have hneg:=after_bound .negate _ width _ _ _ hseed (by omega)
  have hh:=framed_bound _ s (5*s) (14*s^2) hneg (output w width)
  have hout : bytes (output w width)=2*width.length+1 := execute_bytes .neg _ _ width
  apply widen_aux _ _ _ _ _ hh
  rw [hout]
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  nlinarith only [hs2,hw,hs]
/-- ALL58 existing words are counted after actual row materialization, before all8 coefficient drains. -/
theorem beforeClear_mass (w : Words) (width : List Bool) (s : ℕ) (hs : 1 ≤ s) (hw : width.length ≤ s)
    (h : BoundedBank w s (5*s) (14*s^2)) :
    SemiprimeD1StackNormalizedInverseCleanup.mass (store (beforeClear w width)) ≤ 500*s^2 := by
  have hh:=mass_le _ s (5*s) (30*s^2) (beforeClear_bound w width s hs hw h)
  have hs2:s ≤ s^2:=Nat.le_pow (by decide:0<2)
  nlinarith only [hh,hs2]
end RiemannGaussian.SemiprimeD1StackNormalizedInverseFramedBounds
