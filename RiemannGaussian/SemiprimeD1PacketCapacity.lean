/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OrientationForward

/-! # Sparse observed packets do not require an orbit catalogue

This is an erased finite counting argument. Full-slot coverage is supplied by
the original orientation theorem at its later inventory join. No enumeration
of the palette or of unused packets occurs in the executable inventory.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PacketCapacity

/-- Full slots of observed packets fit in the image of the finite padded inputs.
Determinism suffices: no inverse oracle or runtime orbit catalogue is needed. -/
theorem observed_capacity {A : Type*} [Fintype A]
    (observed : List (List Bool)) (hn : observed.Nodup) (L : ℕ)
    (encode : A→List Bool×Fin L)
    (hcover : ∀ key∈observed,∀ slot : Fin L,∃ x : A,encode x=(key,slot)) :
    observed.length*L≤Fintype.card A := by
  classical
  let target := observed.toFinset ×ˢ (Finset.univ : Finset (Fin L))
  have hsub : target⊆(Finset.univ : Finset A).image encode := by
    intro value hvalue
    obtain ⟨hkey,_⟩ := Finset.mem_product.mp hvalue
    obtain ⟨x,hx⟩ := hcover value.1 (List.mem_toFinset.mp hkey) value.2
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ x,hx⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simpa only [target,Finset.card_product,List.toFinset_card_of_nodup hn,
    Finset.card_univ,Fintype.card_fin] using hc

/-- For the original r^a labels on each side, padding gives the exact Darr factor. -/
theorem palette_capacity (observed : List (List Bool)) (hn : observed.Nodup)
    (r a H : ℕ)
    (encode : (Fin (r^a)×Fin (r^a))×Fin H→List Bool×Fin (2^a))
    (hcover : ∀ key∈observed,∀ slot : Fin (2^a),∃ x,encode x=(key,slot)) :
    observed.length*2^a≤r^(2*a)*H := by
  simpa only [Fintype.card_prod,Fintype.card_fin,←pow_add,←two_mul] using
    observed_capacity observed hn (2^a) encode hcover

/-- The actual acquired padding bound then yields the original three-M capacity. -/
theorem threeM_capacity (observed : List (List Bool)) (hn : observed.Nodup)
    (r a H M : ℕ)
    (encode : (Fin (r^a)×Fin (r^a))×Fin H→List Bool×Fin (2^a))
    (hcover : ∀ key∈observed,∀ slot : Fin (2^a),∃ x,encode x=(key,slot))
    (hpad : r^(2*a)*H≤3*M) : observed.length*2^a≤3*M :=
  (palette_capacity observed hn r a H encode hcover).trans hpad

end RiemannGaussian.SemiprimeD1PacketCapacity
