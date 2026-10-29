/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineRetainedData
/-! # Own actual true-q acquisition has a fixed cubic paid-metadata/byte clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineRetainedBounds
open SemiprimeD1StackRecoveryAffineView
namespace R
export SemiprimeD1StackRecoveryGridResource (resource dataWidth resource_pos t_le u_le index_le height_le height_product_le)
end R
namespace G
export SemiprimeD1StackPhaseGeometryArithmetic (magnitude valuation_le magnitude_length)
end G
/-- Actual byte-scanned order markers do not exceed actual metadata and binaryt bytes. -/
theorem order_le (a M u:Nat) (t width:List Bool):
    SemiprimeD1StackRecoveryAffineRetained.order a t≤ R.resource a M u t width:=by
  have h:=G.valuation_le (G.magnitude a t)
  rw [G.magnitude_length] at h
  have ht:=R.t_le a M u t width
  have ha:=R.index_le a M u t width
  exact h.trans (max_le ht (by omega))
/-- Every original true-q source call/copy/scan/product/geometry drain is paid from actual acquired words and true metadata. -/
theorem source_le (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    SemiprimeD1StackRecoveryAffineRetained.runBound
      (SemiprimeD1StackRecoveryAffineEncoding.original a M u selected t width)
      a (SemiprimeD1TaperedLoss.height M u) u t≤ 10^16*(R.resource a M u t width)^3:=by
  let r:=R.resource a M u t width
  let L:=R.dataWidth a M u t width
  have hr:1≤ r:=R.resource_pos a M u t width
  have htl:t.length≤ r:=R.t_le a M u t width
  have ha:a+t.length+1≤ r:=by unfold r R.resource;omega
  have hheight:SemiprimeD1TaperedLoss.height M u≤ 3*r:=R.height_le a M u t width
  have hu:u≤ r:=R.u_le a M u t width
  have ho:SemiprimeD1StackRecoveryAffineRetained.order a t≤ r:=order_le a M u t width
  have hmag:(G.magnitude a t).length≤ r:=by
    rw [G.magnitude_length]
    have hi:=R.index_le a M u t width
    exact max_le htl (by omega)
  have hq:SemiprimeD1TaperedLoss.height M u*(u-SemiprimeD1StackRecoveryAffineRetained.order a t)≤ 3*r:=
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (R.height_product_le a M u t width)
  have hg:20000*(a+t.length+1)≤ L:=by
    apply SemiprimeD1StackRecoveryGridResource.small_le_cubic r _ hr
    omega
  have htL:t.length≤ L:=by
    have h:=SemiprimeD1StackRecoveryGridResource.counts_data a M u t width
    omega
  have hdata:SemiprimeD1StackRecoveryGridWordCaps.Data
      (SemiprimeD1StackRecoveryAffineEncoding.original a M u selected t width).toWords L:=
    (SemiprimeD1StackRecoveryAffineInitialCaps.original_caps a M u selected t width ht).2
  have hm:=SemiprimeD1StackRecoveryAffineRetainedData.product_cleared_mass _ a
    (SemiprimeD1TaperedLoss.height M u) u t L hdata htL hg
  have hmeta:=SemiprimeD1StackRecoveryAffineMultiplicity.runBound_le (SemiprimeD1TaperedLoss.height M u) u
    (SemiprimeD1StackRecoveryAffineRetained.order a t)
  have hsum:SemiprimeD1TaperedLoss.height M u+u+SemiprimeD1StackRecoveryAffineRetained.order a t+1≤ 6*r:=by omega
  have hmeta':SemiprimeD1StackRecoveryAffineMultiplicity.runBound (SemiprimeD1TaperedLoss.height M u) u
      (SemiprimeD1StackRecoveryAffineRetained.order a t)≤ 3600*r^2:=by
    calc
      _≤100*(6*r)^2:=hmeta.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 2))
      _=_:=by ring
  have h13:r≤ r^3:=Nat.le_pow (by decide:0<3)
  have h23:r^2≤ r^3:=Nat.pow_le_pow_right hr (by decide:2≤3)
  have h03:1≤ r^3:=Nat.one_le_pow _ _ hr
  unfold SemiprimeD1StackRecoveryAffineRetained.runBound SemiprimeD1StackPhaseGeometryComponents.runBound
  simp only [List.length_replicate]
  change _≤10^16*r^3
  change _≤104*(10^9*r^3) at hm
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineRetainedBounds
