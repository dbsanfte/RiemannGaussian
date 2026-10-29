/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridFrontBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridEnvelope
/-! # Fixed whole frontend polynomial, charging actual grid-size VALUE acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridFrontClock
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace F
export SemiprimeD1StackRecoveryGridFront (result clean centered decremented runBound)
end F
namespace R
export SemiprimeD1StackRecoveryGridResource (resource cacheWidth dataWidth resource_pos a_le cache_le width_cache cache_data counts_data)
end R
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (mass_le power_width put_registers put_data)
end Caps
/-- The same honest five-word source pays all metadata acquisition, physical drains, both full powers and real returns. -/
theorem front_le (a M u:Nat) (t width:List Bool) :
    F.runBound a M u t width≤10^54*(R.resource a M u t width)^8:=by
  let r:=R.resource a M u t width
  let B:=R.cacheWidth a width
  let L:=R.dataWidth a M u t width
  have hR:1≤r:=R.resource_pos a M u t width
  have ha:a≤r:=R.a_le a M u t width
  have hBL:B≤L:=R.cache_data a M u t width
  have hWB:width.length+2≤B:=R.width_cache a width
  have hB:B≤2*r:=R.cache_le a M u t width
  have hL:L=10^9*r^3:=rfl
  have hcount:=R.counts_data a M u t width
  have hc:a+1≤L:=by omega
  have hn:SemiprimeD1RecoveryGridBits.twoWord.numerator.magnitude.length≤B:=by change 2≤B;dsimp [B,R.cacheWidth];omega
  have hd:SemiprimeD1RecoveryGridBits.twoWord.denominator.length≤B:=by change 1≤B;dsimp [B,R.cacheWidth];omega
  obtain ⟨hr0,hd0⟩:=SemiprimeD1StackRecoveryGridFrontBounds.clean_caps a M u t width
  have hp0:=SemiprimeD1StackRecoveryGridPowerBounds.source_le .center (F.clean a M u t width) width
    SemiprimeD1RecoveryGridBits.twoWord a B L hWB hBL hn hd hc hr0 hd0
  have hx:=Caps.power_width width SemiprimeD1RecoveryGridBits.twoWord a B hWB
  have hr1:=Caps.put_registers (F.clean a M u t width) .center _ B hr0 hx.1 hx.2
  have hd1:=Caps.put_data (F.clean a M u t width) .center _ L hd0 (hx.1.trans hBL) (hx.2.trans hBL)
  have hp1:=SemiprimeD1StackRecoveryGridPowerBounds.source_le .alpha (F.centered a M u t width) width
    SemiprimeD1RecoveryGridBits.twoWord a B L hWB hBL hn hd hc hr1 hd1
  have he:=SemiprimeD1StackRecoveryGridEnvelope.power_le r B L a hR hB (by rw [hL]) (by omega)
  change _≤SemiprimeD1StackRecoveryGridStageBounds.powerCap a B L at hp0 hp1
  have hp0':_≤10^53*r^7:=hp0.trans he
  have hp1':_≤10^53*r^7:=hp1.trans he
  have hmass:=Caps.mass_le (F.decremented a M u t width) L (SemiprimeD1StackRecoveryGridFrontBounds.decremented_data a M u t width)
  have hacq:=SemiprimeD1StackRecoveryGridFrontBounds.acquisition_le a M u t width
  have hdec:=SemiprimeD1StackRecoveryGridFrontBounds.decrement_le a M u t width
  change _≤10000*r^2 at hacq
  change _≤300*r at hdec
  have h28:r^2≤r^8:=Nat.pow_le_pow_right hR (by decide:2≤8)
  have h38:r^3≤r^8:=Nat.pow_le_pow_right hR (by decide:3≤8)
  have h78:r^7≤r^8:=Nat.pow_le_pow_right hR (by decide:7≤8)
  have h18:r≤r^8:=Nat.le_pow (by decide:0<8)
  have h08:1≤r^8:=Nat.one_le_pow 8 _ hR
  rw [hL] at hmass
  unfold F.runBound
  change _≤10^54*r^8
  norm_num1 at hp0' hp1' ⊢
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridFrontClock
