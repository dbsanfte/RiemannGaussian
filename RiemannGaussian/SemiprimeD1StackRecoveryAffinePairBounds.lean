/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineStateCaps
import RiemannGaussian.SemiprimeD1StackRecoveryAffineOperationBounds
import RiemannGaussian.SemiprimeD1StackRecoveryAffineInnerStep
import RiemannGaussian.SemiprimeD1StackRecoveryAffineByteCaps
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadBounds
/-! # Same actual read/factor/two-scalar/six-drain budget from fitted operand bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffinePairBounds
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineWordCaps
open SemiprimeD1StackRecoveryAffineByteCaps (Small)
open SemiprimeD1StackRecoveryGrid (Reg)
/-- Every actual source byte and all112 retained physical words enter this fixed same-site cap. -/
def siteCap (B L:Nat):Nat:=10^36*(112*L+B^6+1)
/-- Included R36 source depends only on its five source words; actual foreign bytes enter cleanup additively. -/
theorem site_le (site:Site) (w:Words) (width:List Bool) (B L:Nat)
    (hW:width.length+2≤ B) (hr:Registers w B) (hd:Data w L):
    SemiprimeD1StackRecoveryAffineSite.runBound site w width≤ siteCap B L:=by
  have h:=SemiprimeD1StackRecoveryAffineOperationBounds.site_le site w width B (by omega) (by omega) hr
  have hm:=mass_le w L hd
  exact h.trans (Nat.mul_le_mul_left _ (by omega))
/-- Both actual arithmetic sites and all six physical drains share the same semantic word/data envelope. -/
theorem pair_le (w:Words) (width:List Bool) (B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Registers w B) (hd:Data w L):
    SemiprimeD1StackRecoveryAffinePair.runBound w width≤ 10^37*(112*L+B^6+1):=by
  have h0:=site_le .product w width B L hW hr hd
  have hr0:=SemiprimeD1StackRecoveryAffineStateCaps.site_registers .product w width B hr (by omega)
  have hd0:=SemiprimeD1StackRecoveryAffineStateCaps.site_data .product w width L hd (by omega)
  have h1:=site_le .sum (SemiprimeD1StackRecoveryAffineSite.result .product w width) width B L hW hr0 hd0
  have hd1:=SemiprimeD1StackRecoveryAffineStateCaps.site_data .sum
    (SemiprimeD1StackRecoveryAffineSite.result .product w width) width L hd0 (by omega)
  have hm:=mass_le _ L hd1
  unfold SemiprimeD1StackRecoveryAffinePair.runBound siteCap at *
  omega
/-- A physically fitted/literal word has a bounded actual signed register and denominator. -/
theorem small_put_registers (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord) (width:List Bool) (B:Nat)
    (hw:Registers w B) (hx:Small width x) (hW:width.length+2≤ B):Registers (putReg w r x) B:=
  put_registers w r x B hw (by have h:=hx.1;omega) (by have h:=hx.2;omega)
/-- All foreign112 tapes stay bounded while actual small operands are physically acquired. -/
theorem small_put_data (w:Words) (r:Reg) (x:SemiprimeRationalBits.RationalWord) (width:List Bool) (B L:Nat)
    (hw:Data w L) (hx:Small width x) (hW:width.length+2≤ B) (hBL:B≤ L):Data (putReg w r x) L:=
  put_data w r x L hw (by have h:=hx.1;omega) (by have h:=hx.2;omega)
/-- All three actual loader caches retain semantic byte bounds independently of numeric coefficient values. -/
theorem acquired_registers (w:Words) (x y suffix:SemiprimeRationalBits.RationalWord) (width:List Bool) (B:Nat)
    (hw:Registers w B) (hx:Small width x) (hy:Small width y) (hs:Small width suffix) (hW:width.length+2≤ B):
    Registers (SemiprimeD1StackRecoveryAffineInnerStep.acquired w x y suffix) B:=
  small_put_registers _ .denBase y width B
    (small_put_registers _ .numBase x width B (small_put_registers w .denPower suffix width B hw hs hW) hx hW) hy hW
/-- Paid actual loader writes preserve the complete physical-word envelope. -/
theorem acquired_data (w:Words) (x y suffix:SemiprimeRationalBits.RationalWord) (width:List Bool) (B L:Nat)
    (hw:Data w L) (hx:Small width x) (hy:Small width y) (hs:Small width suffix) (hW:width.length+2≤ B) (hBL:B≤ L):
    Data (SemiprimeD1StackRecoveryAffineInnerStep.acquired w x y suffix) L:=
  small_put_data _ .denBase y width B L
    (small_put_data _ .numBase x width B L (small_put_data w .denPower suffix width B L hw hs hW hBL) hx hW hBL) hy hW hBL
/-- The literal finite factor cases pay only actual retained slope bytes or fixed literal seed pushes. -/
theorem factor_le (part:Part) (c:SemiprimeRationalBits.RationalWord) (width:List Bool) (B:Nat)
    (hc:Small width c) (hW:width.length+2≤ B):SemiprimeD1StackRecoveryAffineFactor.runBound part c≤ 20*(B+1):=by
  have hn:(signed c).length≤ B:=by change c.numerator.magnitude.length+1≤ B;have h:=hc.1;omega
  have hd:=hc.2
  cases part <;> dsimp only [SemiprimeD1StackRecoveryAffineFactor.runBound] <;> omega
/-- Complete actual coefficient read/factor/two-site/six-drain iteration has one fixed physical-resource cap. -/
theorem inner_le (part:Part) (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (n:Nat)
    (c suffix:SemiprimeRationalBits.RationalWord) (width:List Bool) (B L:Nat)
    (hW:width.length+2≤ B) (hBL:B≤ L) (hr:Registers w B) (hd:Data w L)
    (hxs:∀x∈xs,Small width x) (hc:Small width c) (hs:Small width suffix)
    (ha:(vector xs).length≤ L) (hn:n≤ L):
    SemiprimeD1StackRecoveryAffineInnerStep.runBound part w xs n c suffix width≤ 10^38*(112*L+B^6+1):=by
  have hx:=SemiprimeD1StackRecoveryAffineByteCaps.read_small width xs n hxs
  have hy:=SemiprimeD1StackRecoveryAffineByteCaps.factor_small width part c hc
  have hr0:=acquired_registers w _ _ suffix width B hr hx hy hs hW
  have hd0:=acquired_data w _ _ suffix width B L hd hx hy hs hW hBL
  have hp:=pair_le _ width B L hW hBL hr0 hd0
  have hf:=factor_le part c width B hc hW
  have ha0:=SemiprimeD1StackRecoveryAffineReadBounds.source_le xs n
  have hpow:B≤ B^6:=Nat.le_pow (by decide:0<6)
  unfold SemiprimeD1StackRecoveryAffineInnerStep.runBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffinePairBounds
