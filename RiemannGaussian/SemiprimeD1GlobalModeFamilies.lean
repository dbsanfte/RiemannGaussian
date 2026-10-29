/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1GlobalModeFibres

/-! # Total actual mode-owner families, with no fictitious owner outside the cache
An optional owner handles empty packet inventories and high zero indices
uniformly. Every real index has the explicit acquired owner; absent indices
have none. The actual mask sets are exactly the corresponding owner fibres.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1GlobalModeFamilies
open SemiprimeD1GlobalModeOwners SemiprimeD1GlobalModeFibres
open SemiprimeD1PacketModeProjection

/-- Total target owner determined by actual catalogue membership and route reads. -/
def targetFamily (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a) (j : ℕ) :
    Option (Fin (original n F r a arity owner).state.packets.length × Fin r) :=
  if hj : j < (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length then
    some (packet n F r a _ arity owner i ⟨j,hj⟩, target n F r a _ arity owner i ⟨j,hj⟩)
  else none

/-- Total source owner uses the same literal global catalogue and actual source bytes. -/
def sourceFamily (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a) (j : ℕ) :
    Option (Fin (original n F r a arity owner).state.packets.length × Fin r) :=
  if hj : j < (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length then
    some (packet n F r a _ arity owner i ⟨j,hj⟩, source n F r a _ arity owner i ⟨j,hj⟩)
  else none

/-- Every actual local descriptor cache has the complete GLOBAL catalogue dimension. -/
theorem cache_length (n F r a u p : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (f : Fin (original n F r a arity owner).state.packets.length) (g : Fin r) :
    (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g).items.length =
      (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length := by
  have h := congrArg List.length (SemiprimeD1PacketModeMask.fromModes_catalogue
    (node n F r a u p arity owner i) f i g)
  simp only [List.length_map] at h
  exact h

/-- The actual target mask, on ALL natural indices, equals its actual owner fibre. -/
theorem target_set (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (f : Fin (original n F r a arity owner).state.packets.length) (g : Fin r) :
    targetSet (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g) =
      {j | targetFamily n F r a u p arity owner i j = some (f,g)} := by
  ext j
  by_cases hj : j < (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length
  · have h := target_mask n F r a u p arity owner i f g ⟨j,hj⟩
    simpa only [targetFamily,hj,dite_true,Set.mem_ofPred_eq,Option.some.injEq,Prod.mk.injEq] using h
  · have hn : j ∉ targetSet (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g) := by
      intro hm
      have h := targetSet_lt _ j hm
      rw [cache_length] at h
      exact hj h
    simp [targetFamily,hj,hn]

/-- Original-beta source factors likewise use the exact actual source-owner fibre. -/
theorem source_set (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (f : Fin (original n F r a arity owner).state.packets.length) (g : Fin r) :
    sourceSet (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g) =
      {j | sourceFamily n F r a u p arity owner i j = some (f,g)} := by
  ext j
  by_cases hj : j < (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length
  · have h := source_mask n F r a u p arity owner i f g ⟨j,hj⟩
    simpa only [sourceFamily,hj,dite_true,Set.mem_ofPred_eq,Option.some.injEq,Prod.mk.injEq] using h
  · have hn : j ∉ sourceSet (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g) := by
      intro hm
      have h := sourceSet_lt _ j hm
      rw [cache_length] at h
      exact hj h
    simp [sourceFamily,hj,hn]

end RiemannGaussian.SemiprimeD1GlobalModeFamilies
