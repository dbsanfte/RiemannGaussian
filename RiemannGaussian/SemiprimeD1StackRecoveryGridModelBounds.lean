/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridPayloadBounds
import RiemannGaussian.SemiprimeD1StackRecoveryGridResource
/-! # Semantic104-word loop-boundary caps from physical metadata and fitted fields -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridModelBounds
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridOperationInput
namespace Model
export SemiprimeD1StackRecoveryGridModel (Payload view cache registers auxiliary center alpha node)
end Model
namespace P
export SemiprimeD1StackRecoveryGridPayloadBounds (Bounded)
end P
namespace R
export SemiprimeD1StackRecoveryGridResource (resource gridSize cacheWidth dataWidth resource_pos a_le M_le u_le t_le width_le grid_le index_le cache_le width_cache height_le height_product_le small_le_cubic cache_data counts_data)
end R
namespace Caps
export SemiprimeD1StackRecoveryGridWordCaps (Registers Data)
end Caps
/-- Actual paid index fitting gives exactly a+2 magnitude bytes and the literal one denominator. -/
theorem node_lengths (a:Nat) (t:List Bool) :(Model.node a t).numerator.magnitude.length=a+2 ∧(Model.node a t).denominator.length=1:=by
  constructor
  · change (SemiprimeD1StackWordFitExecution.result t (List.replicate (a+2) false)).length=_
    rw [SemiprimeD1StackWordFitExecution.result_length,List.length_replicate]
  · rfl
/-- The actual center power has only fitted W bytes or the literal one seed. -/
theorem center_lengths (a:Nat) (width:List Bool) :
    (Model.center a width).numerator.magnitude.length≤width.length+1 ∧(Model.center a width).denominator.length≤width.length+1:=
  SemiprimeD1StackRecoveryGridByteBounds.power_lengths width SemiprimeD1RecoveryGridBits.twoWord a
/-- The actual alpha power has the same fitted/literal physical-byte bound. -/
theorem alpha_lengths (a:Nat) (width:List Bool) :
    (Model.alpha a width).numerator.magnitude.length≤width.length+1 ∧(Model.alpha a width).denominator.length≤width.length+1:=
  SemiprimeD1StackRecoveryGridByteBounds.power_lengths width SemiprimeD1RecoveryGridBits.twoWord (a+1)
attribute [local irreducible] Model.center Model.alpha Model.node
/-- All actual operand and destination register bytes use the semantic cache cap, independently of elapsed execution. -/
theorem registers_le (a M u n v:Nat) (t q width:List Bool) (p:Model.Payload)
    (hp:P.Bounded width p v (SemiprimeD1TaperedLoss.height M u*u)) :
    Caps.Registers (Model.view a M u n t q width p) (R.cacheWidth a width):=by
  have hc:=center_lengths a width
  have ha:=alpha_lengths a width
  obtain ⟨hnm,hnd⟩:=node_lengths a t
  obtain ⟨hcm,hcd⟩:=hc
  obtain ⟨ham,had⟩:=ha
  have hnm0:=hp.num_mag
  have hnd0:=hp.num_den
  have hdm0:=hp.den_mag
  have hdd0:=hp.den_den
  intro r b
  cases r <;> cases b
  all_goals
    dsimp only [Model.view,Model.registers,Model.cache,signed,SemiprimeD1RecoveryGridBits.twoWord]
    try rw [ite_eq_left (Eq.refl true)]
    try rw [ite_eq_right (by decide:¬false=true)]
    repeat first | rw [List.length_cons] | rw [List.length_nil]
    unfold R.cacheWidth
    omega
/-- All chronological slope bytes are paid by actual visited rows and actual h*u, without scanning accumulated tails. -/
theorem slopes_le (a M u n v:Nat) (t _q width:List Bool) (p:Model.Payload)
    (hp:P.Bounded width p v (SemiprimeD1TaperedLoss.height M u*u)) (hv:v+n≤ R.gridSize a) :
    (slopeTape p.slopes).length≤ R.dataWidth a M u t width:=by
  have hR:=R.resource_pos a M u t width
  have hW:=R.width_le a M u t width
  have hN:=R.grid_le a M u t width
  have hH:=R.height_product_le a M u t width
  have hvR:v≤ R.resource a M u t width:=by omega
  have hcount:=hp.count
  have hc:p.slopes.length≤3*(R.resource a M u t width)^2:=by
    have hm:=Nat.mul_le_mul hvR hH
    nlinarith
  have hx:∀x∈p.slopes,x.numerator.magnitude.length+x.denominator.length≤2*width.length:=by
    intro x hx
    have h:=hp.slopes x hx
    omega
  have hs:=SemiprimeD1StackRecoveryGridByteBounds.slopeTape_length p.slopes (2*width.length) hx
  have hm:=Nat.mul_le_mul hc (show 2*(2*width.length)+5≤4*R.resource a M u t width+5 by omega)
  have hp2:(R.resource a M u t width)^2≤(R.resource a M u t width)^3:=Nat.pow_le_pow_right hR (by decide:2≤3)
  have hp0:1≤(R.resource a M u t width)^3:=Nat.one_le_pow 3 _ hR
  unfold R.dataWidth
  norm_num1
  nlinarith
/-- Every actual original, retained, counter and output word fits the same cubic physical envelope. -/
theorem data_le (a M u n v:Nat) (t q width:List Bool) (p:Model.Payload)
    (hp:P.Bounded width p v (SemiprimeD1TaperedLoss.height M u*u)) (hvn:v+n≤ R.gridSize a) (hq:q.length≤ a+2) :
    Caps.Data (Model.view a M u n t q width p) (R.dataWidth a M u t width):=by
  have hR:=R.resource_pos a M u t width
  have ha:=R.a_le a M u t width
  have hM:=R.M_le a M u t width
  have hu:=R.u_le a M u t width
  have ht:=R.t_le a M u t width
  have hW:=R.width_le a M u t width
  have hN:=R.grid_le a M u t width
  have hi:=R.index_le a M u t width
  have hh:=R.height_le a M u t width
  have hreg:=registers_le a M u n v t q width p hp
  have hB:=R.cache_data a M u t width
  have hD:=R.counts_data a M u t width
  have hD0:3*R.resource a M u t width≤R.dataWidth a M u t width:=by omega
  have hSlopes:=slopes_le a M u n v t q width p hp hvn
  intro k
  rcases k with k|k
  · change (emptyRational width k).length≤_
    rw [SemiprimeD1StackRecoveryGridOperation.emptyRational_explicit]
    dsimp only
    split
    · exact (R.width_le a M u t width).trans (by omega)
    · exact Nat.zero_le _
  · rcases k with k|k
    · exact Nat.zero_le _
    · rcases k with k|k
      · cases k <;> first
          | exact Nat.zero_le _
          | change (List.replicate (SemiprimeD1TaperedLoss.height M u) true).length≤_;rw [List.length_replicate];exact hh.trans hD0
      · rcases k with k|k
        · exact Nat.zero_le _
        · rcases k with k|k
          · exact (hreg k.1 k.2).trans hB
          · cases k <;> first
              | exact Nat.zero_le _
              | exact hSlopes
              | change (List.replicate _ _).length≤_;rw [List.length_replicate];omega
              | exact ht.trans (by omega)
              | exact hq.trans (by omega)
end RiemannGaussian.SemiprimeD1StackRecoveryGridModelBounds
