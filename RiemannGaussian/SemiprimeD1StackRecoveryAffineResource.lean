/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineInitialCaps
import RiemannGaussian.SemiprimeD1StackRecoveryAffineByteCaps
/-! # Actual acquired grid/multiplicity/vector dimensions fit one paid-VALUE envelope -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineResource
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineWordCaps
namespace R
export SemiprimeD1StackRecoveryGridResource (resource cacheWidth dataWidth resource_pos grid_le width_le cache_le cache_data counts_data)
end R
namespace E
export SemiprimeD1StackRecoveryAffineEncoding (original retained)
end E
open SemiprimeD1StackRecoveryAffineSource (counted)
/-- The actual retained q is bounded by the acquired unary M/u metadata values. -/
theorem q_le (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    E.retained a M u selected≤ 3*R.resource a M u t width:=by
  have h:=SemiprimeD1StackRecoveryAffineByteCaps.retained_le a M u selected
  unfold R.resource
  omega
/-- Every original repeated slope is paid by the actual grid size and bounded multiplicity VALUES. -/
theorem slopes_le (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    (SemiprimeD1StackRecoveryAffineOriginalInput.slopes a M u selected width).length≤ 3*(R.resource a M u t width)^2:=by
  have hn:=R.grid_le a M u t width
  have hmu:3*M+u≤ 3*R.resource a M u t width:=by unfold R.resource;omega
  calc
    _≤ 2^(a+1)*(3*M+u):=SemiprimeD1StackRecoveryAffineByteCaps.slopes_count a M u selected width
    _≤ R.resource a M u t width*(3*R.resource a M u t width):=Nat.mul_le_mul hn hmu
    _=_:=by ring
/-- Sign/tag/delimiter overhead and every raw fitted source slope bit fit the same cubic physical-word envelope. -/
theorem slopes_bytes (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    (vector (SemiprimeD1StackRecoveryAffineOriginalInput.slopes a M u selected width)).length≤ R.dataWidth a M u t width:=by
  let r:=R.resource a M u t width
  have hr:1≤ r:=R.resource_pos a M u t width
  have hw:width.length≤ r:=R.width_le a M u t width
  have hlen:=slopes_le a M u selected t width
  have hb:=SemiprimeD1StackRecoveryAffineByteCaps.vector_length width _
    (SemiprimeD1StackRecoveryAffineByteCaps.slopes_small a M u selected width)
  have hrow:4*width.length+9≤ 13*r:=by omega
  have hlen':(SemiprimeD1StackRecoveryAffineOriginalInput.slopes a M u selected width).length≤ 3*r^2:=hlen
  have h: (vector (SemiprimeD1StackRecoveryAffineOriginalInput.slopes a M u selected width)).length≤ 39*r^3+1:=by
    calc
      _≤ (3*r^2)*(13*r)+1:=hb.trans (Nat.add_le_add_right (Nat.mul_le_mul hlen' hrow) 1)
      _=_:=by ring
  have hone:1≤ r^3:=Nat.one_le_pow _ _ hr
  change _≤ 10^9*r^3
  omega
/-- Every initial literal or q-word fitted coefficient array and all in-progress frames fit the actual data envelope. -/
theorem array_budget (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    (E.retained a M u selected+1)*(4*width.length+9)+1≤ R.dataWidth a M u t width:=by
  let r:=R.resource a M u t width
  have hr:1≤ r:=R.resource_pos a M u t width
  have hw:width.length≤ r:=R.width_le a M u t width
  have hq:=q_le a M u selected t width
  have hq':E.retained a M u selected+1≤ 4*r:=by omega
  have hrow:4*width.length+9≤ 13*r:=by omega
  have h:(E.retained a M u selected+1)*(4*width.length+9)+1≤ 52*r^2+1:=by
    calc
      _≤ (4*r)*(13*r)+1:=Nat.add_le_add_right (Nat.mul_le_mul hq' hrow) 1
      _=_:=by ring
  have hp:r^2≤ r^3:=Nat.pow_le_pow_right hr (by decide:2≤3)
  have hone:1≤ r^3:=Nat.one_le_pow _ _ hr
  change _≤ 10^9*r^3
  omega
/-- Every actual112-word counted source boundary has semantic register caps and a true cubic physical byte cap. -/
theorem counted_caps (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:SemiprimeBitArithmetic.bitValue t=selected.val):
    Registers (counted a M u selected t width) (R.cacheWidth a width) ∧
      Data (counted a M u selected t width) (R.dataWidth a M u t width):=by
  obtain ⟨hr,hd⟩:=SemiprimeD1StackRecoveryAffineInitialCaps.original_caps a M u selected t width ht
  have hbase:Data (E.original a M u selected t width) (R.dataWidth a M u t width):=by
    intro slot
    rcases slot with slot|slot
    · exact hd slot
    · exact Nat.zero_le _
  have hq:=q_le a M u selected t width
  have hc:=R.counts_data a M u t width
  refine ⟨hr,?_⟩
  apply added_data (E.original a M u selected t width) .retainedQ _ _ hbase
  simp only [List.length_replicate]
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryAffineResource
