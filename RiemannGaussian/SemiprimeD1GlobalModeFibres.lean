/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1GlobalModeOwners

/-! # Actual packet masks are the fibres of the computed GLOBAL mode owners
This closes the finite owner-projection seam in mode separation: every actual
catalogue coordinate has exactly one packet/target owner and exactly one
packet/source owner. The witnesses are explicit slot/route reads, never chosen
from an assumed projection or a successful factorization example.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1GlobalModeFibres
open SemiprimeD1GlobalModeOwners SemiprimeD1PacketModeProjection

/-- The actual original mode node, with phase fixed to the current grid valuation. -/
abbrev node (n F r a u p : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a) :=
  SemiprimeD1OriginalModeAcquisition.acquire n F r a u i.val p arity owner

/-- Actual strict cutoff supplied by the acquired node precision. -/
def cutoff (n F r a u p : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a) : ℕ :=
  (node n F r a u p arity owner i).precision-1

/-- Original route target agrees with a specified packet once its actual quotient agrees. -/
theorem route_target_at (n F r a P : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a P arity owner i).length)
    (f : Fin (original n F r a arity owner).state.packets.length)
    (hf : packet n F r a P arity owner i j = f) :
    (route n F r a P arity owner i j).target =
      (SemiprimeD1ModeRoutingBits.acquire (original n F r a arity owner).state.packets[f.val]
        a i (tile n F r a P arity owner i j)).target := by
  unfold route
  rw [hf]
  exact (SemiprimeD1ModeRoutingBits.fromReplay_data _ _ _ _).2

/-- The same literal quotient alignment holds for the original source route. -/
theorem route_source_at (n F r a P : ℕ) (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a P arity owner i).length)
    (f : Fin (original n F r a arity owner).state.packets.length)
    (hf : packet n F r a P arity owner i j = f) :
    (route n F r a P arity owner i j).source =
      (SemiprimeD1ModeRoutingBits.acquire (original n F r a arity owner).state.packets[f.val]
        a i (tile n F r a P arity owner i j)).source := by
  unfold route
  rw [hf]
  exact (SemiprimeD1ModeRoutingBits.fromReplay_data _ _ _ _).1

/-- The ACTUAL computed target mask is precisely its packet/target-owner fibre. -/
theorem target_mask (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (f : Fin (original n F r a arity owner).state.packets.length) (g : Fin r)
    (j : Fin (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length) :
    j.val ∈ targetSet (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g) ↔
      packet n F r a (cutoff n F r a u p arity owner i) arity owner i j = f ∧
      target n F r a (cutoff n F r a u p arity owner i) arity owner i j = g := by
  have hh := SemiprimeD1PacketModeProjection.original_target (node n F r a u p arity owner i) f i g j
  refine hh.trans ?_
  change (mode n F r a _ arity owner i j).slot/2^(i.val+1) = f.val ∧
    (SemiprimeD1ModeRoutingBits.acquire (original n F r a arity owner).state.packets[f.val]
      a i (tile n F r a _ arity owner i j)).target =
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits ↔ _
  constructor
  · rintro ⟨hf, hb⟩
    have hf' : packet n F r a _ arity owner i j = f := Fin.ext hf
    refine ⟨hf', (target_bytes n F r a _ arity owner i j g).mpr ?_⟩
    exact (route_target_at n F r a _ arity owner i j f hf').trans hb
  · rintro ⟨hf, hg⟩
    refine ⟨congrArg Fin.val hf, ?_⟩
    exact (route_target_at n F r a _ arity owner i j f hf).symm.trans
      ((target_bytes n F r a _ arity owner i j g).mp hg)

/-- The ACTUAL original-beta source mask is precisely its packet/source-owner fibre. -/
theorem source_mask (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (f : Fin (original n F r a arity owner).state.packets.length) (g : Fin r)
    (j : Fin (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length) :
    j.val ∈ sourceSet (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) f i g) ↔
      packet n F r a (cutoff n F r a u p arity owner i) arity owner i j = f ∧
      source n F r a (cutoff n F r a u p arity owner i) arity owner i j = g := by
  have hh := SemiprimeD1PacketModeProjection.original_source (node n F r a u p arity owner i) f i g j
  refine hh.trans ?_
  change (mode n F r a _ arity owner i j).slot/2^(i.val+1) = f.val ∧
    (SemiprimeD1ModeRoutingBits.acquire (original n F r a arity owner).state.packets[f.val]
      a i (tile n F r a _ arity owner i j)).source =
        (SemiprimeSourceHistogramPortKeys.encodeKey g.val).bits ↔ _
  constructor
  · rintro ⟨hf, hb⟩
    have hf' : packet n F r a _ arity owner i j = f := Fin.ext hf
    refine ⟨hf', (source_bytes n F r a _ arity owner i j g).mpr ?_⟩
    exact (route_source_at n F r a _ arity owner i j f hf').trans hb
  · rintro ⟨hf, hg⟩
    refine ⟨congrArg Fin.val hf, ?_⟩
    exact (route_source_at n F r a _ arity owner i j f hf).symm.trans
      ((source_bytes n F r a _ arity owner i j g).mp hg)

/-- Every ACTUAL global mode belongs to exactly one actual packet/target family. -/
theorem unique_target (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length) :
    ∃! fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
      j.val ∈ targetSet (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) fg.1 i fg.2) := by
  let actual := (packet n F r a _ arity owner i j, target n F r a _ arity owner i j)
  refine ⟨actual, (target_mask n F r a u p arity owner i actual.1 actual.2 j).mpr ⟨rfl,rfl⟩, ?_⟩
  intro fg hf
  have h := (target_mask n F r a u p arity owner i fg.1 fg.2 j).mp hf
  exact Prod.ext h.1.symm h.2.symm

/-- Every ACTUAL global mode likewise belongs to exactly one packet/source family. -/
theorem unique_source (n F r a u p : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) (i : Fin a)
    (j : Fin (modes n F r a (cutoff n F r a u p arity owner i) arity owner i).length) :
    ∃! fg : Fin (original n F r a arity owner).state.packets.length × Fin r,
      j.val ∈ sourceSet (SemiprimeD1PacketModeMask.fromModes (node n F r a u p arity owner i) fg.1 i fg.2) := by
  let actual := (packet n F r a _ arity owner i j, source n F r a _ arity owner i j)
  refine ⟨actual, (source_mask n F r a u p arity owner i actual.1 actual.2 j).mpr ⟨rfl,rfl⟩, ?_⟩
  intro fg hf
  have h := (source_mask n F r a u p arity owner i fg.1 fg.2 j).mp hf
  exact Prod.ext h.1.symm h.2.symm

end RiemannGaussian.SemiprimeD1GlobalModeFibres
