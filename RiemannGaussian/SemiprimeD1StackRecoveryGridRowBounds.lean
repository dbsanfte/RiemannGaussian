/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridModelBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridWorkBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridEnvelope
import RiemannGaussian.SemiprimeD1StackRecoveryGridRow
/-! # Whole actual row clock at the physical original-grid loop invariant -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRowBounds
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView
namespace Row
export SemiprimeD1StackRecoveryGridRow (geometry indexed order runBound)
end Row
namespace Model
export SemiprimeD1StackRecoveryGridModel (view Payload)
end Model
namespace R
export SemiprimeD1StackRecoveryGridResource (resource gridSize cacheWidth dataWidth resource_pos a_le M_le u_le t_le width_le grid_le index_le cache_le width_cache cache_data counts_data small_le_cubic height_le height_product_le)
end R
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data put_registers put_data auxiliary_data)
end Caps
namespace Payload
export SemiprimeD1StackRecoveryGridPayloadBounds (Bounded)
end Payload
/-- The actual acquired order markers never exceed the actual scanned geometry magnitude width. -/
theorem order_le (a:Nat) (q:List Bool) (hq:q.length≤a+2) :Row.order a q≤a+2:=by
  have h:=SemiprimeD1StackPhaseGeometryArithmetic.valuation_le (SemiprimeD1StackPhaseGeometryArithmetic.magnitude a q)
  rw [SemiprimeD1StackPhaseGeometryArithmetic.magnitude_length] at h
  exact h.trans (by omega)
/-- Actual row entry, true geometry and paid current-index copy retain semantic register/data caps. -/
theorem input_caps (a M u n v:Nat) (t q width:List Bool) (p:Model.Payload)
    (hp:Payload.Bounded width p v (SemiprimeD1TaperedLoss.height M u*u))
    (hv:v+(n+1)≤R.gridSize a) (hq:q.length≤a+2) :
    Caps.Registers (Row.geometry (Model.view a M u (n+1) t q width p) a n q) (R.cacheWidth a width) ∧
    Caps.Data (Row.geometry (Model.view a M u (n+1) t q width p) a n q) (R.dataWidth a M u t width) ∧
    Caps.Registers (Row.indexed (Model.view a M u (n+1) t q width p) a n q) (R.cacheWidth a width) ∧
    Caps.Data (Row.indexed (Model.view a M u (n+1) t q width p) a n q) (R.dataWidth a M u t width):=by
  have hr:=SemiprimeD1StackRecoveryGridModelBounds.registers_le a M u (n+1) v t q width p hp
  have hd:=SemiprimeD1StackRecoveryGridModelBounds.data_le a M u (n+1) v t q width p hp hv hq
  have hR:=R.resource_pos a M u t width
  have ha:=R.a_le a M u t width
  have hqR:q.length≤R.resource a M u t width:=hq.trans (R.index_le a M u t width)
  have hN:=R.grid_le a M u t width
  have hL:=R.counts_data a M u t width
  have hn:n≤R.dataWidth a M u t width:=by omega
  have hd0:=Caps.auxiliary_data (Model.view a M u (n+1) t q width p) .todo (List.replicate n true) _ hd (by rwa [List.length_replicate])
  have hg:20000*((List.replicate a true).length+q.length+1)≤R.dataWidth a M u t width:=by
    rw [List.length_replicate]
    apply R.small_le_cubic _ _ hR
    omega
  have hd1:=SemiprimeD1StackRecoveryGridStateCaps.geometry_data _ (List.replicate a true) q _ hd0 hg
  have hr1:Caps.Registers (Row.geometry (Model.view a M u (n+1) t q width p) a n q) (R.cacheWidth a width):=hr
  have hnB:q.length+1≤R.cacheWidth a width:=by unfold R.cacheWidth;omega
  have hb:=R.cache_data a M u t width
  refine ⟨hr1,hd1,?_,?_⟩
  · apply Caps.put_registers _ .index _ _ hr1 hnB
    change 1≤R.cacheWidth a width
    unfold R.cacheWidth;omega
  · apply Caps.put_data _ .index _ _ hd1 (hnB.trans hb)
    change 1≤R.dataWidth a M u t width
    omega
/-- Whole actual row budget, including both skip paths and the complete unskipped body, is uniformly eighth degree in paid source bytes/VALUEs. -/
theorem row_le (a M u n v:Nat) (t q width:List Bool) (p:Model.Payload)
    (hp:Payload.Bounded width p v (SemiprimeD1TaperedLoss.height M u*u))
    (hv:v+(n+1)≤R.gridSize a) (hq:q.length≤a+2) :
    Row.runBound (Model.view a M u (n+1) t q width p) width a (SemiprimeD1TaperedLoss.height M u) u n q t≤
      10^55*(R.resource a M u t width)^8:=by
  let r:=R.resource a M u t width
  let B:=R.cacheWidth a width
  let L:=R.dataWidth a M u t width
  have hR:1≤r:=R.resource_pos a M u t width
  have ha:a≤r:=R.a_le a M u t width
  have hu:u≤r:=R.u_le a M u t width
  have ht:t.length≤r:=R.t_le a M u t width
  have hW:width.length≤r:=R.width_le a M u t width
  have hqR:q.length≤r:=hq.trans (R.index_le a M u t width)
  have hh:SemiprimeD1TaperedLoss.height M u≤3*r:=R.height_le a M u t width
  have hmul:SemiprimeD1TaperedLoss.height M u*(u-Row.order a q)≤3*r:=
    (Nat.mul_le_mul_left _ (Nat.sub_le u (Row.order a q))).trans (R.height_product_le a M u t width)
  have ho:Row.order a q≤r:=(order_le a q hq).trans (R.index_le a M u t width)
  have hB:B≤2*r:=R.cache_le a M u t width
  have hL:L=10^9*r^3:=rfl
  have hBL:B≤L:=R.cache_data a M u t width
  have hWB:width.length+2≤B:=R.width_cache a width
  have hcount:=R.counts_data a M u t width
  obtain ⟨hr0,hd0,hr1,hd1⟩:=input_caps a M u n v t q width p hp hv hq
  have hbytes:SemiprimeD1TaperedLoss.height M u*(u-Row.order a q)*(4*width.length+5)≤L:=
    SemiprimeD1StackRecoveryGridEnvelope.frame_bytes_le r width.length _ hR hW hmul
  have hw:=SemiprimeD1StackRecoveryGridWorkBounds.work_le
    (Row.indexed (Model.view a M u (n+1) t q width p) a n q) width
    (SemiprimeD1TaperedLoss.height M u) u (Row.order a q) B L hWB hBL hr1 hd1 (by omega) hbytes
  have he:=SemiprimeD1StackRecoveryGridEnvelope.work_le r (SemiprimeD1TaperedLoss.height M u) u (Row.order a q)
    width.length _ B L hR hh hu ho hW hmul hB hL
  have hwork:=hw.trans he
  have hcleanup:=SemiprimeD1StackRecoveryGridStageBounds.cleanup_le
    (Row.geometry (Model.view a M u (n+1) t q width p) a n q) L hd0
  have hcompare:=SemiprimeD1StackRecoveryGridCompare.runBound_le q t
  have hmag:(SemiprimeD1StackPhaseGeometryArithmetic.magnitude a q).length≤r:=by
    rw [SemiprimeD1StackPhaseGeometryArithmetic.magnitude_length]
    have hi:=R.index_le a M u t width
    omega
  have hstart:SemiprimeD1StackRecoveryGridRowStart.runBound a q≤4000*r:=by
    unfold SemiprimeD1StackRecoveryGridRowStart.runBound SemiprimeD1StackPhaseGeometryComponents.runBound
    rw [List.length_replicate]
    omega
  have h38:r^3≤r^8:=Nat.pow_le_pow_right hR (by decide:3≤8)
  have h18:r≤r^8:=Nat.le_pow (by decide:0<8)
  have h08:1≤r^8:=Nat.one_le_pow 8 _ hR
  unfold Row.runBound
  change _≤10^55*r^8
  rw [hL] at hcleanup
  norm_num1 at hwork hcleanup ⊢
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridRowBounds
