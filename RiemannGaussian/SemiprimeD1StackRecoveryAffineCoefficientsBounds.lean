/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientBounds
/-! # Same whole physical coefficient-array loop has a quadratic acquired-q clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientsBounds
open SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffineWordCaps
open SemiprimeD1StackRecoveryAffineByteCaps (Small)
/-- Uniform whole-array coefficient budget, with constants before all inputs and physical dimensions. -/
def cap (B L:Nat):Nat:=10^42*(112*L+B^6+1)
/-- Actual remaining markers are paid by the actual framed row budget, never by an advised coefficient count. -/
theorem count_budget (width next:List Bool) (n L:Nat) (h:next.length+n*(4*width.length+9)≤ L):n≤ L:=by
  have hn:n≤ n*(4*width.length+9):=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left n (by omega:1≤ 4*width.length+9)
  omega
/-- All real count pops, original ordered dot source calls, coefficient frames and cache drains have a quadratic q cap. -/
theorem source_le (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (c:SemiprimeRationalBits.RationalWord)
    (width:List Bool) (n:Nat) (next:List Bool) (B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Registers w B) (hd:Data w L)
    (hxs:∀x∈xs,Small width x) (hc:Small width c)
    (ha:(vector xs).length≤ L) (hbudget:next.length+n*(4*width.length+9)≤ L):
    SemiprimeD1StackRecoveryAffineCoefficients.runBound w xs c width n next≤ (n+1)^2*cap B L:=by
  have hone:1≤ cap B L:=by unfold cap;omega
  have hcap:SemiprimeD1StackRecoveryAffineCoefficientBounds.cap B L≤ cap B L:=by
    unfold SemiprimeD1StackRecoveryAffineCoefficientBounds.cap cap
    omega
  induction n generalizing next with
  | zero=>
    change 1≤ (0+1)^2*cap B L
    simpa only [Nat.zero_add,one_pow,Nat.one_mul] using hone
  | succ n ih=>
    have hn:n≤ L:=by have h:=count_budget width next (n+1) L hbudget;omega
    have ht:next.length≤ L:=by omega
    have h0:=SemiprimeD1StackRecoveryAffineCoefficientBounds.source_le w xs c width n next B L hW hBL hr hd hxs hc ha hn ht
    have hcoef:=h0.trans (Nat.mul_le_mul_left (n+1) hcap)
    let emitted:=SemiprimeD1StackRecoveryGridView.slopeRow (SemiprimeD1StackRecoveryAffineCoefficient.answer xs c width n) next
    have hlen:emitted.length≤ next.length+(4*width.length+9):=
      SemiprimeD1StackRecoveryAffineLoopCaps.coefficient_row_length xs c width next n
    have hb:emitted.length+n*(4*width.length+9)≤ L:=by
      rw [Nat.add_mul,Nat.one_mul] at hbudget
      omega
    have hrest:=ih emitted hb
    change 1+SemiprimeD1StackRecoveryAffineCoefficient.runBound w xs c width n next+
      SemiprimeD1StackRecoveryAffineCoefficients.runBound w xs c width n emitted≤ (n+1+1)^2*cap B L
    calc
      _≤1+(n+1)*cap B L+(n+1)^2*cap B L:=Nat.add_le_add (Nat.add_le_add_left hcoef 1) hrest
      _≤cap B L+(n+1)*cap B L+(n+1)^2*cap B L:=by omega
      _=(1+(n+1)+(n+1)^2)*cap B L:=by ring
      _≤(n+1+1)^2*cap B L:=Nat.mul_le_mul_right _ (by nlinarith)
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientsBounds
