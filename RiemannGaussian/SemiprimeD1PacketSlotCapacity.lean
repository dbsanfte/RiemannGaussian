/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketCapacity

/-! # Sparse capacity for the actual finite orientation slot type -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PacketSlotCapacity

/-- Every observed packet's complete finite slot family fits in the finite image.
All types and maps in this argument are erased; no source catalogue executes. -/
theorem observed_capacity_slots {A S : Type*} [Fintype A] [Fintype S]
    (observed : List (List Bool)) (hn : observed.Nodup)
    (encode : A→List Bool×S)
    (hcover : ∀ key∈observed,∀ slot : S,∃ x : A,encode x=(key,slot)) :
    observed.length*Fintype.card S≤Fintype.card A := by
  classical
  let target := observed.toFinset ×ˢ (Finset.univ : Finset S)
  have hsub : target⊆(Finset.univ : Finset A).image encode := by
    intro value hvalue
    obtain ⟨hkey,_⟩ := Finset.mem_product.mp hvalue
    obtain ⟨x,hx⟩ := hcover value.1 (List.mem_toFinset.mp hkey) value.2
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ x,hx⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simpa only [target,Finset.card_product,List.toFinset_card_of_nodup hn,
    Finset.card_univ] using hc

/-- Boolean coordinate slots yield exactly the original dyadic packet size. -/
theorem boolean_capacity {A : Type*} [Fintype A]
    (observed : List (List Bool)) (hn : observed.Nodup) (a : ℕ)
    (encode : A→List Bool×(Fin a→Bool))
    (hcover : ∀ key∈observed,∀ slot : Fin a→Bool,∃ x : A,encode x=(key,slot)) :
    observed.length*2^a≤Fintype.card A := by
  simpa using observed_capacity_slots observed hn encode hcover

end RiemannGaussian.SemiprimeD1PacketSlotCapacity
