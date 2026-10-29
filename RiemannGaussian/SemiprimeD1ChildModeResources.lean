/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildOriginalFields
import RiemannGaussian.SemiprimeD1CatalogSize

/-! # Actual original catalogue dimension and eager packet exponential
The catalogue is acquired from literal packets and computed precision. The
naive physical coefficient recursion plus all table assignments fits the fixed
original degree envelope; no catalogue or coefficient-count answer is given.
-/
set_option autoImplicit false
set_option maxHeartbeats 140000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildModeResources
open SemiprimeD1JetAxes SemiprimeD1TensorNetwork SemiprimeD1TensorNetworkRecursion

/-- Actual complete descriptor dimension for this original acquired node. -/
def catalogueLength (net : Network) (a u : ℕ) (i : Fin a) (p : ℕ) : ℕ :=
  let source := SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64
    a u i.val p (arity net.rows) (owner net.rows)
  (SemiprimeD1ModeCatalog.catalog (source.packets.state.packets.length*2^(i.val+1))
    (source.precision-1)).length

/-- The actual catalogue has a derived fixed quadratic original-scope bound. -/
theorem catalogue_quadratic (net : Network) (hw : WellFormed net) (D a u : ℕ) (i : Fin a) (p : ℕ)
    (hd : DegreeBound net D) (hsmall : 2*(64^(2*a))^2*D ≤ edgeCount net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount net) (hu : 0 < u) (huM : u ≤ edgeCount net)
    (hp : p*u ≤ edgeCount net*2^(a-i.val)) (ha : (a+1)*u ≤ 2^(a-i.val)) :
    catalogueLength net a u i p ≤ 246*(edgeCount net)^2 := by
  have hdegree := original_degree_contract net hw D a hd
  have hM : (SemiprimeD1CollisionOriginal.ports net.leftCount net.rows.length a (arity net.rows)).length =
      edgeCount net := by rw [SemiprimeD1TensorNetworkLayout.original_ports];rfl
  have hpack := SemiprimeD1PacketReplayCapacity.threeM_capacity net.leftCount net.rows.length 64 a
    (arity net.rows) (owner net.rows) D hdegree.1 hdegree.2 (by rw [hM];exact hsmall)
    (by rw [hM];exact hsize)
  rw [hM] at hpack
  have h := SemiprimeD1CatalogSize.catalog_quadratic
    (SemiprimeD1PacketReplayOriginal.acquire net.leftCount net.rows.length 64 a
      (arity net.rows) (owner net.rows)).state.packets.length
    (edgeCount net) u a i.val p i.isLt.le hpack hu huM hp ha
  change (SemiprimeD1ModeCatalog.catalog _
    ((SemiprimeD1OriginalModeAcquisition.acquire net.leftCount net.rows.length 64 a u i.val p
      (arity net.rows) (owner net.rows)).precision-1)).length ≤ _
  rw [SemiprimeD1OriginalModeAcquisition.precision_original,SemiprimeD1TensorNetworkLayout.original_ports]
  exact h

/-- Actual original packet scopes fit the same fixed global stored-degree cap. -/
theorem slots_bound (lam a : ℕ) (hlam : 1000 ≤ lam) (ha : a ≤ 4*(lam/131072)) :
    2*2^a ≤ 2^((9*lam+9)/10) := by
  have h := (SemiprimeD1PackingReady.exponent_margin lam hlam).2
  rw [←pow_succ']
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Literal truth-table materialization and naive affine coefficient recursion
are both absorbed by the original global degree envelope. -/
theorem coefficient_envelope (net : Network) (hw : WellFormed net) (lam a u : ℕ)
    (i : Fin a) (p : ℕ) (hlam : 1000 ≤ lam) (haSmall : a ≤ 4*(lam/131072))
    (hM : edgeCount net ≤ 2^lam)
    (hd : DegreeBound net (2^((9*lam+9)/10)))
    (hsmall : 2*(64^(2*a))^2*(2^((9*lam+9)/10)) ≤ edgeCount net)
    (hsize : 64^(2*a)*2^a ≤ edgeCount net) (hu : 0 < u) (huM : u ≤ edgeCount net)
    (hp : p*u ≤ edgeCount net*2^(a-i.val)) (ha : (a+1)*u ≤ 2^(a-i.val)) :
    2^(2*2^a)*(catalogueLength net a u i p+1)^(2*2^a) ≤ 2^(2^((9*lam+9)/10)) := by
  have hK := catalogue_quadratic net hw _ a u i p hd hsmall hsize hu huM hp ha
  have hbin := SemiprimeD1CatalogSize.quadratic_binary (edgeCount net) lam (catalogueLength net a u i p) hM hK
  exact SemiprimeD1CatalogSize.packet_coefficient_envelope lam a _ (2*2^a) hlam haSmall hbin le_rfl

end RiemannGaussian.SemiprimeD1ChildModeResources
