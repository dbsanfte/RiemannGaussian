/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePairBounds
/-! # Same whole descending-k source clock, with semantic fitted operands at every iteration -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerBounds
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineWordCaps
open SemiprimeD1StackRecoveryAffineByteCaps (Small)
open SemiprimeD1StackRecoveryAffinePairMeaning (step)
/-- Every completed actual pair leaves a twice-fitted suffix; no intermediate fit answer is supplied. -/
theorem step_small (width:List Bool) (x y suffix:SemiprimeRationalBits.RationalWord):Small width (step width x y suffix):=by
  have h:=SemiprimeD1StackRecoveryGridByteBounds.operation_lengths .add
    (SemiprimeRationalBits.executeOperation .mul x y width).word suffix width
  exact ⟨h.1.le.trans (by omega),h.2.le.trans (by omega)⟩
/-- One complete actual iteration plus its physical marker pop has this uniform cap. -/
def cap (B L:Nat):Nat:=10^39*(112*L+B^6+1)
/-- The own complete source clock is linear in the materialized index, without expanding binary coefficient values. -/
theorem loop_le (part:Part) (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (c suffix:SemiprimeRationalBits.RationalWord) (width:List Bool) (B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Registers w B) (hd:Data w L)
    (hxs:∀x∈xs,Small width x) (hc:Small width c) (hs:Small width suffix)
    (ha:(vector xs).length≤ L) (hn:n≤ L):
    SemiprimeD1StackRecoveryAffineInnerLoop.runBound part w xs c width n suffix≤ (n+1)*cap B L:=by
  have hcap:10^38*(112*L+B^6+1)+1≤ cap B L:=by unfold cap;omega
  induction n generalizing part suffix with
  | zero=>
    have hdata:=counter_data w 0 L hd (by omega)
    have hi:=SemiprimeD1StackRecoveryAffinePairBounds.inner_le part
      (SemiprimeD1StackRecoveryAffineCache.counter w 0) xs 0 c suffix width B L hW hBL hr hdata hxs hc hs ha (by omega)
    change _+1+0≤ (0+1)*cap B L
    simpa only [Nat.zero_add,Nat.add_zero,Nat.one_mul] using (Nat.add_le_add_right hi 1).trans hcap
  | succ n ih=>
    let next:=step width (SemiprimeD1StackRecoveryAffineReadLoop.wordAt xs (n+1))
      (SemiprimeD1StackRecoveryAffineFactor.value part c) suffix
    have hdata:=counter_data w (n+1) L hd hn
    have hi:=SemiprimeD1StackRecoveryAffinePairBounds.inner_le part
      (SemiprimeD1StackRecoveryAffineCache.counter w (n+1)) xs (n+1) c suffix width B L hW hBL hr hdata hxs hc hs ha hn
    have hs':Small width next:=step_small width _ _ suffix
    have hh:=ih (nextPart part) next hs' (by omega)
    change _+1+SemiprimeD1StackRecoveryAffineInnerLoop.runBound (nextPart part) w xs c width n next≤ (n+1+1)*cap B L
    calc
      _≤ cap B L+(n+1)*cap B L:=Nat.add_le_add ((Nat.add_le_add_right hi 1).trans hcap) hh
      _=_:=by ring
end RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerBounds
