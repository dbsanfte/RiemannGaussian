/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedMomentOriginal

/-! # Exact packed count and factor sum for EVERY semiprime
The algorithmic scalar expression depends only on N. Unknown primes occur
only in universal correctness theorems, never as advice to a source program.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedMomentSemiprime
open scoped BigOperators
open SemiprimePublicFactorCount SemiprimeD1PackedMomentOriginal SemiprimeD1PackedMomentAlgebra
open SemiprimeMacroParameters

/-- The natural orientation (p,q) is a valid ordinary pair, including p=q. -/
def forward (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) : OrdinaryFactors (p*q) :=
  ⟨(⟨p,by have h:=Nat.le_mul_of_pos_right p hq.pos;omega⟩,
    ⟨q,by have h:=Nat.le_mul_of_pos_left q hp.pos;omega⟩),hp.two_le,hq.two_le,rfl⟩

/-- Both orientations are kept in the SAME original N-bound finite type. -/
def backward (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) : OrdinaryFactors (p*q) :=
  ⟨(⟨q,by have h:=Nat.le_mul_of_pos_left q hp.pos;omega⟩,
    ⟨p,by have h:=Nat.le_mul_of_pos_right p hq.pos;omega⟩),hq.two_le,hp.two_le,Nat.mul_comm q p⟩

/-- The prime on the left can divide only the entire first factor in its
orientation: the remaining prime cannot split into two nontrivial factors. -/
theorem pair_of_left_divides (p q a b : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hb : 2 ≤ b) (hab : a*b=p*q) (hpa : p∣a) : a=p ∧ b=q := by
  obtain ⟨k,hk⟩ := hpa
  have hkb : k*b=q := by
    apply Nat.eq_of_mul_eq_mul_left hp.pos
    rw [←Nat.mul_assoc,←hk]
    exact hab
  have hd : b∣q := ⟨k,by rw [←hkb,Nat.mul_comm]⟩
  have hbq : b=q := (hq.eq_one_or_self_of_dvd b hd).resolve_left (by omega)
  refine ⟨?_,hbq⟩
  apply Nat.eq_of_mul_eq_mul_right hq.pos
  simpa only [hbq] using hab

/-- Exhaustive arithmetic classification, with no factor-pair coverage premise. -/
theorem pair_classification (p q a b : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a*b=p*q) :
    (a=p ∧ b=q) ∨ (a=q ∧ b=p) := by
  have hd : p∣a*b := by rw [hab];exact Nat.dvd_mul_right p q
  rcases hp.dvd_mul.mp hd with hpa|hpb
  · exact Or.inl (pair_of_left_divides p q a b hp hq hb hab hpa)
  · have h := pair_of_left_divides p q b a hp hq ha (by rw [Nat.mul_comm b a];exact hab) hpb
    exact Or.inr ⟨h.2,h.1⟩

/-- Ordinary-pair equality retains both numerical components. -/
theorem pair_ext {N : ℕ} {a b : OrdinaryFactors N}
    (hl : a.val.1.val=b.val.1.val) (hr : a.val.2.val=b.val.2.val) : a=b := by
  apply Subtype.ext
  exact Prod.ext (Fin.ext hl) (Fin.ext hr)

/-- The entire original bounded factor set consists of precisely these two
orientations; Finset deduplication retains ONE model for a square. -/
theorem all_pairs (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    (Finset.univ : Finset (OrdinaryFactors (p*q)))={forward p q hp hq,backward p q hp hq} := by
  classical
  ext f
  simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_iff]
  rcases pair_classification p q f.val.1.val f.val.2.val hp hq f.property.1 f.property.2.1 f.property.2.2 with h|h
  · exact Or.inl (pair_ext h.1 h.2)
  · exact Or.inr (pair_ext h.1 h.2)

/-- Equal primes have one orientation and unequal primes have exactly two,
with the exact sum of their original first operands. -/
theorem moments (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    Fintype.card (OrdinaryFactors (p*q))=(if p=q then 1 else 2) ∧
      factorSum (p*q)=(if p=q then p else p+q) := by
  classical
  have he : forward p q hp hq=backward p q hp hq ↔ p=q := by
    constructor
    · exact fun h => congrArg (fun f : OrdinaryFactors (p*q) => f.val.1.val) h
    · intro h
      exact pair_ext h h.symm
  constructor
  · rw [←Finset.card_univ,all_pairs p q hp hq]
    by_cases h : p=q
    · simp only [he.mpr h,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.card_singleton,ite_eq_left h]
    · have hn : forward p q hp hq ∉ ({backward p q hp hq} : Finset (OrdinaryFactors (p*q))) := by
        simpa only [Finset.mem_singleton,he] using h
      rw [Finset.card_insert_of_notMem hn,Finset.card_singleton,ite_eq_right h]
  · unfold factorSum
    rw [all_pairs p q hp hq]
    by_cases h : p=q
    · simp only [he.mpr h,Finset.insert_eq_of_mem (Finset.mem_singleton_self _),Finset.sum_singleton,
        ite_eq_left h,backward]
      exact h.symm
    · rw [Finset.sum_insert (by simpa only [Finset.mem_singleton,he] using h),Finset.sum_singleton,ite_eq_right h]
      rfl

/-- Both retained moment channels are bounded before the square modulus is
read. In particular distinct factor sums satisfy p+q≤N, even at p=2. -/
theorem moments_below_base (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    Fintype.card (OrdinaryFactors (p*q))<2^bitLength (p*q) ∧
      factorSum (p*q)<2^bitLength (p*q) := by
  have hN : p*q<2^bitLength (p*q) := input_lt_bitLength_power (p*q)
  have hM := moments p q hp hq
  rw [hM.1,hM.2]
  have h2 : 2 ≤ p*q := hp.two_le.trans (Nat.le_mul_of_pos_right p hq.pos)
  by_cases he : p=q
  · rw [ite_eq_left he,ite_eq_left he]
    exact ⟨by omega,(Nat.le_mul_of_pos_right p hq.pos).trans_lt hN⟩
  · rw [ite_eq_right he,ite_eq_right he]
    exact ⟨by omega,(Nat.add_le_mul hp.two_le hq.two_le).trans_lt hN⟩

/-- Canonical scalar readout of ONE actual local weighted contraction;
only the public original N chooses its base and modulus. -/
def packedValue (N : ℕ) (hN : 0<N) : ℕ :=
  (contraction (publicConfig N hN) ((2^bitLength N : ℕ) : ZMod ((2^bitLength N)^2))).val

/-- ONE local weighted graph contraction contains the exact model count and
factor sum for EVERY semiprime, including squares and even semiprimes. -/
theorem readout (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    packedValue (p*q) (Nat.mul_pos hp.pos hq.pos) % (2^bitLength (p*q))=(if p=q then 1 else 2) ∧
    packedValue (p*q) (Nat.mul_pos hp.pos hq.pos) / (2^bitLength (p*q))=(if p=q then p else p+q) := by
  have hm := moments p q hp hq
  have hb := moments_below_base p q hp hq
  have hu := residue_unpack (2^bitLength (p*q)) (Fintype.card (OrdinaryFactors (p*q))) (factorSum (p*q)) hb.1 hb.2
  unfold packedValue
  rw [public_square_modulus]
  exact ⟨hu.2.1.trans hm.1,hu.2.2.trans hm.2⟩

end RiemannGaussian.SemiprimeD1PackedMomentSemiprime
