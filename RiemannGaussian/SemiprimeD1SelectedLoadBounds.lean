/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1LoadBounds
import RiemannGaussian.SemiprimeD1SelectedCollision

/-! # Complete-family maximum load of the actual original physical selector -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1SelectedLoadBounds
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeD1LoadBounds SemiprimeD1SelectedCollision SemiprimeD1CollisionOriginal
open SemiprimeSourceHistogramGrouping

/-- Complete head/slot label family has the original D.3 cardinality. -/
theorem card_labels (r a : ℕ) : Fintype.card (Word r a × Word r a)=r^(2*a) := by
  simp [Word,←pow_add,two_mul]

/-- Actual selected collision mass equals the complete load-square sum. -/
theorem selected_collision_eq (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) :
    collision (ports n F a arity) (selectedLabel n F r a arity owner)=
      collisionSum n F r a arity owner :=
  collision_pairs _ _

/-- Every original universal label, including absent labels, has load at most2M/D.
The labels come from the actual executed selector, never supplied label advice. -/
theorem selected_load_le (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a arity,
      multiplicity (fun i => (owner i).val) (ports n F a arity) (owner i).val≤Δ)
    (hf : ∀ i∈ports n F a arity,
      multiplicity (fun i => n+i.1.val) (ports n F a arity) (n+i.1.val)≤Δ)
    (hsmall : 2*(r^(2*a))^2*Δ≤(ports n F a arity).length)
    (label : Word r a × Word r a) :
    ((r^(2*a):ℕ):ℚ)*load (ports n F a arity) (selectedLabel n F r a arity owner) label≤
      2*(ports n F a arity).length := by
  have hp : (0:ℚ)<(r^a:ℕ) := Nat.cast_pos.mpr (pow_pos (NeZero.pos r) a)
  have hd : ((r^(2*a):ℕ):ℚ)=((r^a:ℕ):ℚ)^2 := by
    norm_cast
    simp [pow_mul,Nat.mul_comm]
  have hcoll := selected_collision_le n F r a arity owner Δ ho hf
  have hc : (Fintype.card (Word r a × Word r a):ℚ)*
      collision (ports n F a arity) (selectedLabel n F r a arity owner)≤
      ((ports n F a arity).length:ℚ)^2+
        2*(ports n F a arity).length*Δ*Fintype.card (Word r a × Word r a) := by
    rw [selected_collision_eq,card_labels,hd]
    have h:=mul_le_mul_of_nonneg_left hcoll (show 0≤((r^a:ℕ):ℚ)^2 by positivity)
    have he : ((r^a:ℕ):ℚ)^2*
        (((ports n F a arity).length:ℚ)^2/((r^a:ℕ):ℚ)^2+
          2*(ports n F a arity).length*Δ)=
        ((ports n F a arity).length:ℚ)^2+
          2*(ports n F a arity).length*Δ*((r^a:ℕ):ℚ)^2 := by field_simp
    rwa [he] at h
  have hs : 2*(Fintype.card (Word r a × Word r a))^2*Δ≤
      (ports n F a arity).length := by simpa only [card_labels] using hsmall
  simpa only [card_labels] using load_le_twice _ _ Δ hc hs label

/-- Natural integer form used by the actual acquired padding maximum. -/
theorem selected_load_nat_le (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (Δ : ℕ)
    (ho : ∀ i∈ports n F a arity,
      multiplicity (fun i => (owner i).val) (ports n F a arity) (owner i).val≤Δ)
    (hf : ∀ i∈ports n F a arity,
      multiplicity (fun i => n+i.1.val) (ports n F a arity) (n+i.1.val)≤Δ)
    (hsmall : 2*(r^(2*a))^2*Δ≤(ports n F a arity).length)
    (label : Word r a × Word r a) :
    r^(2*a)*SemiprimeSourceHistogramGrouping.multiplicity
      (selectedLabel n F r a arity owner) (ports n F a arity) label≤
        2*(ports n F a arity).length := by
  have h:=selected_load_le n F r a arity owner Δ ho hf hsmall label
  unfold load at h
  exact_mod_cast h

end RiemannGaussian.SemiprimeD1SelectedLoadBounds
