/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopBounds
import RiemannGaussian.SemiprimeD1StackRecoveryAffineResource
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopesBounds
/-! # Fixed paid-VALUE polynomial for the SAME entire original affine-array traversal -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopClock
open SemiprimeD1StackRecoveryAffineView
namespace R
export SemiprimeD1StackRecoveryGridResource (resource resource_pos cacheWidth dataWidth cache_le cache_data width_cache)
end R
namespace E
export SemiprimeD1StackRecoveryAffineEncoding (retained)
end E
namespace A
export SemiprimeD1StackRecoveryAffineOriginalInput (slopes)
end A
open SemiprimeD1StackRecoveryAffineSource (counted)
/-- Original true geometry, complete original slopes and all physical fitted operands pay every actual nested-loop instruction. -/
theorem whole_le (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    SemiprimeD1StackRecoveryAffineLoop.runBound (counted a M u selected t width) width (E.retained a M u selected)
      (A.slopes a M u selected width).reverse [SemiprimeJetBits.oneWord]≤ 10^60*(R.resource a M u t width)^10:=by
  let r:=R.resource a M u t width
  let B:=R.cacheWidth a width
  let L:=R.dataWidth a M u t width
  let q:=E.retained a M u selected
  have hr:1≤ r:=R.resource_pos a M u t width
  have hB:B≤ 2*r:=R.cache_le a M u t width
  have hBL:B≤ L:=R.cache_data a M u t width
  have hW:width.length+2≤ B:=R.width_cache a width
  obtain ⟨hregs,hdata⟩:=SemiprimeD1StackRecoveryAffineResource.counted_caps a M u selected t width ht
  have hq:q≤ 3*r:=SemiprimeD1StackRecoveryAffineResource.q_le a M u selected t width
  have hqL:q≤ L:=by
    have h:=SemiprimeD1StackRecoveryGridResource.counts_data a M u t width
    omega
  have hbudget:(q+1)*(4*width.length+9)+1≤ L:=SemiprimeD1StackRecoveryAffineResource.array_budget a M u selected t width
  have hs:∀x∈(A.slopes a M u selected width).reverse,SemiprimeD1StackRecoveryAffineByteCaps.Small width x:=by
    intro x hx
    exact SemiprimeD1StackRecoveryAffineByteCaps.slopes_small a M u selected width x (List.mem_reverse.mp hx)
  have hbytes:(vector (A.slopes a M u selected width).reverse).length≤ L:=by
    rw [SemiprimeD1StackRecoveryAffineSlopesBounds.vector_reverse_length]
    exact SemiprimeD1StackRecoveryAffineResource.slopes_bytes a M u selected t width
  have h:=SemiprimeD1StackRecoveryAffineLoopBounds.source_le (counted a M u selected t width) width q
    (A.slopes a M u selected width).reverse [SemiprimeJetBits.oneWord] B L hW hBL hregs hdata
    (by intro x hx;rcases List.mem_singleton.mp hx with rfl;exact SemiprimeD1StackRecoveryAffineByteCaps.one_small width)
    (by simp only [List.length_singleton];omega) hs hbytes hqL hbudget
  have hlen:(A.slopes a M u selected width).length≤ 3*r^2:=SemiprimeD1StackRecoveryAffineResource.slopes_le a M u selected t width
  have hsl:(A.slopes a M u selected width).reverse.length+1≤ 4*r^2:=by
    rw [List.length_reverse]
    have h1:1≤ r^2:=Nat.one_le_pow _ _ hr
    omega
  have hq':q+1≤ 4*r:=by omega
  have hq2:(q+1)^2≤ 16*r^2:=by
    have hh:=Nat.pow_le_pow_left hq' 2
    nlinarith
  have hB6:B^6≤ 64*r^6:=by
    have hh:=Nat.pow_le_pow_left hB 6
    rw [mul_pow] at hh
    norm_num1 at hh
    exact hh
  have h36:r^3≤ r^6:=Nat.pow_le_pow_right hr (by decide:3≤6)
  have h06:1≤ r^6:=Nat.one_le_pow _ _ hr
  have hres:112*L+B^6+1≤ 10^12*r^6:=by
    change 112*(10^9*r^3)+B^6+1≤ 10^12*r^6
    omega
  have hcap:SemiprimeD1StackRecoveryAffineLoopBounds.cap B L≤ 10^57*r^6:=by
    unfold SemiprimeD1StackRecoveryAffineLoopBounds.cap
    calc
      _≤ 10^45*(10^12*r^6):=Nat.mul_le_mul_left _ hres
      _=_:=by ring
  calc
    _≤ (4*r^2)*(16*r^2)*(10^57*r^6):=h.trans (Nat.mul_le_mul (Nat.mul_le_mul hsl hq2) hcap)
    _≤ 10^60*r^10:=by rw [show (4*r^2)*(16*r^2)*(10^57*r^6)=64*10^57*r^10 by ring];omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopClock
