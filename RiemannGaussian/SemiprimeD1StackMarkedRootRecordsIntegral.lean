/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootOwnerTables
import RiemannGaussian.SemiprimeD1PackedMomentPrecision
/-! # Integer and canonical-shape facts for physically relayed root tables
These proofs inspect original literal coefficient words over the natural
numbers. They do not transfer equality modulo four to a larger modulus.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsIntegral
open SemiprimeBitArithmetic SemiprimeD1TensorTables
namespace O
export SemiprimeD1RootOwnerTables (producer weight rootContext)
end O
/-- Each Boolean contribution is at most one, including empty incident scopes. -/
theorem bitNat_le_one (b : Bool) : bitNat b ≤ 1 := by cases b <;> decide
/-- The original owner entry is the exact integer sum zero, one or two. -/
theorem owner_value {n : Nat} (fixed : List (Fin n × Bool)) (v : Fin n) (bits : List Bool) :
    (O.producer fixed v bits).words.map bitValue=[O.weight fixed v bits] := by
  have hb (low high : Bool) : (bitValue [low]+bitValue [high]) < 2^2 := by
    cases low <;> cases high <;> decide
  change [bitValue (SemiprimeD1JetScalarBits.add 2 _ _).bits]=_
  rw [SemiprimeD1JetScalarBits.add_value,Nat.mod_eq_of_lt (hb _ _),
    SemiprimeD1RootOwnerTables.prefixRun_value,SemiprimeD1RootOwnerTables.prefixRun_value,
    SemiprimeD1RootOwnerTables.sameRun_value,SemiprimeD1RootOwnerTables.sameRun_value]
  rfl
/-- The retained owner multiplicity has an exact natural-number upper bound. -/
theorem owner_weight_le_two {n : Nat} (fixed : List (Fin n × Bool)) (v : Fin n) (bits : List Bool) :
    O.weight fixed v bits ≤ 2 := by
  unfold O.weight
  exact Nat.add_le_add (bitNat_le_one _) (bitNat_le_one _)
/-- Increasing scalar precision preserves every word's compactness and rank. -/
theorem goodWords_mono (axes : List Nat) (p q : Nat) (hp : p ≤ q)
    (words : List (List Bool)) (h : GoodWords ⟨axes,p⟩ words) : GoodWords ⟨axes,q⟩ words := by
  refine ⟨h.1,?_⟩
  intro word hw
  exact ⟨(h.2 word hw).1,((h.2 word hw).2).trans hp⟩
/-- A complete relayed table remains Good after an actual precision increase. -/
theorem good_mono (axes : List Nat) (p q : Nat) (hp : p ≤ q)
    {n : Nat} (table : Table n) (h : Good ⟨axes,p⟩ table) : Good ⟨axes,q⟩ table := by
  induction table with
  | leaf words => exact goodWords_mono axes p q hp words h
  | fork low high ihlow ihhigh => exact ⟨ihlow h.1,ihhigh h.2⟩
/-- Every original owner producer is canonical at any scalar precision at least two. -/
theorem owner_good {n : Nat} (fixed : List (Fin n × Bool)) (v : Fin n) (bits : List Bool)
    (p : Nat) (hp : 2 ≤ p) : GoodWords ⟨[],p⟩ (O.producer fixed v bits).words :=
  goodWords_mono [] 2 p hp _ (SemiprimeD1RootOwnerTables.producer_good fixed v bits)
/-- All original owner materializations can be relayed without changing a byte. -/
theorem owner_table_good {n : Nat} (fixed : List (Fin n × Bool)) (v : Fin n)
    (degree p : Nat) (hp : 2 ≤ p) :
    Good ⟨[],p⟩ (SemiprimeD1RootOwnerTables.acquire fixed v degree).table :=
  good_mono [] 2 p hp _ (SemiprimeD1RootOwnerTables.acquire_good fixed v degree)
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsIntegral
