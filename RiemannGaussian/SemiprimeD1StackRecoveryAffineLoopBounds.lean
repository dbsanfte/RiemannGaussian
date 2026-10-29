/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeBounds
/-! # Whole actual affine slope traversal has a fixed polynomial physical-source clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopBounds
open SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffineWordCaps
open SemiprimeD1StackRecoveryAffineByteCaps (Small)
open SemiprimeRationalBits (RationalWord)
/-- Fixed whole-row allowance includes every actual parse/source/cleanup step. -/
def cap (B L:Nat):Nat:=10^45*(112*L+B^6+1)
/-- Actual current arrays retain only the literal seed or at most q fitted coefficient rows. -/
theorem array_bytes (width:List Bool) (q L:Nat) (xs:List RationalWord)
    (hx:∀x∈xs,Small width x) (hn:xs.length≤ q+1) (hb:(q+1)*(4*width.length+9)+1≤ L):
    (vector xs).length≤ L:=by
  have h:=SemiprimeD1StackRecoveryAffineByteCaps.vector_length width xs hx
  exact h.trans ((Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1).trans hb)
/-- Whole SAME reverse-row traversal pays every ordered q-by-q convolution and physical row/array byte. -/
theorem source_le (w:Words) (width:List Bool) (q:Nat) (slopes xs:List RationalWord) (B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Registers w B) (hd:Data w L)
    (hx:∀x∈xs,Small width x) (hn:xs.length≤ q+1)
    (hs:∀c∈slopes,Small width c) (ht:(vector slopes).length≤ L)
    (hq:q≤ L) (hb:(q+1)*(4*width.length+9)+1≤ L):
    SemiprimeD1StackRecoveryAffineLoop.runBound w width q slopes xs≤
      (slopes.length+1)*(q+1)^2*cap B L:=by
  have hcap:SemiprimeD1StackRecoveryAffineSlopeBounds.rowCap B L≤ cap B L:=by
    unfold SemiprimeD1StackRecoveryAffineSlopeBounds.rowCap cap
    omega
  induction slopes generalizing xs with
  | nil=>
    have hq2:1≤ (q+1)^2:=by nlinarith
    have hbase:2≤ cap B L:=by unfold cap;omega
    change 2≤ (0+1)*(q+1)^2*cap B L
    calc
      _≤ cap B L:=hbase
      _≤ (q+1)^2*cap B L:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (cap B L) hq2
      _=_:=by ring
  | cons c cs ih=>
    have hc:Small width c:=hs c List.mem_cons_self
    have hcs:∀x∈cs,Small width x:=fun x hx=>hs x (List.mem_cons_of_mem c hx)
    have htail:(vector cs).length≤ L:=by
      have hlen:=SemiprimeD1StackRecoveryAffineReadBounds.row_length c cs
      omega
    have harray:=array_bytes width q L xs hx hn hb
    have hr0:=SemiprimeD1StackRecoveryAffineLoopCaps.state_registers w xs cs B hr
    have hd0:=SemiprimeD1StackRecoveryAffineLoopCaps.state_data w xs cs L hd harray htail
    have hr1:=SemiprimeD1StackRecoveryAffineLoopCaps.small_put_registers _ .slope c width B hr0 hc hW
    have hd1:=SemiprimeD1StackRecoveryAffineLoopCaps.small_put_data _ .slope c width B L hd0 hc hW hBL
    have hbudget:q*(4*width.length+9)+1≤ L:=by
      rw [Nat.add_mul,Nat.one_mul] at hb
      omega
    have hrow:=SemiprimeD1StackRecoveryAffineSlopeBounds.row_le
      (putReg (SemiprimeD1StackRecoveryAffineLoopView.state w xs cs) .slope c) xs c width q B L
      hW hBL hr1 hd1 hx hc harray hq hbudget
    have hrow':(1+(8*(signed c).length+8+(8*c.denominator.length+8)))+
        SemiprimeD1StackRecoveryAffineSlopeStage.runBound
          (putReg (SemiprimeD1StackRecoveryAffineLoopView.state w xs cs) .slope c) xs c width q≤ (q+1)^2*cap B L:=
      hrow.trans (Nat.mul_le_mul_left _ hcap)
    have hsmall:=SemiprimeD1StackRecoveryAffineByteCaps.multiply_small width xs c q
    have hlen:(SemiprimeD1StackRecoveryAffineLoopView.multiply width xs c q).length≤ q+1:=by
      rw [SemiprimeD1StackRecoveryAffineByteCaps.multiply_length]
      omega
    have hrest:=ih (SemiprimeD1StackRecoveryAffineLoopView.multiply width xs c q) hsmall hlen hcs htail
    change (1+(8*(signed c).length+8+(8*c.denominator.length+8)))+
        SemiprimeD1StackRecoveryAffineSlopeStage.runBound
          (putReg (SemiprimeD1StackRecoveryAffineLoopView.state w xs cs) .slope c) xs c width q+
        SemiprimeD1StackRecoveryAffineLoop.runBound w width q cs (SemiprimeD1StackRecoveryAffineLoopView.multiply width xs c q)≤ _
    calc
      _≤(q+1)^2*cap B L+(cs.length+1)*(q+1)^2*cap B L:=Nat.add_le_add hrow' hrest
      _=(cs.length+1+1)*(q+1)^2*cap B L:=by ring
end RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopBounds
