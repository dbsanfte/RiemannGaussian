/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRationalBits

/-!
# Streamed rational dot products with actual bit arithmetic

One recursive suffix result is computed and retained once. Each frame executes
the proved Boolean rational multiply and add, including reduction and physical
width copies. Common input denominators bound every partial sum independently
of cancellation. Acquiring the input word pairs is separate from this loop.
-/
set_option autoImplicit false
set_option maxRecDepth 2000
namespace RiemannGaussian.SemiprimeDotBits
open SemiprimeRationalBits SemiprimeJetArrayHeight

/-- The literal recursive dot-product implementation on physical word pairs. -/
def dotBits (template : List Bool) : List (RationalWord × RationalWord) → RationalReport
  | [] => ⟨zeroWord,4⟩
  | pair :: rest =>
    let suffix := dotBits template rest
    let product := executeOperation .mul pair.1 pair.2 template
    let sum := executeOperation .add product.word suffix.word template
    ⟨sum.word, suffix.clock+product.clock+sum.clock+4⟩

/-- Specification only: the sum of the interpreted input products. -/
def dotValue (pairs : List (RationalWord × RationalWord)) : ℚ :=
  (pairs.map (fun pair => pair.1.value*pair.2.value)).sum

theorem zeroWord_value : zeroWord.value = 0 := by
  simp [zeroWord, RationalWord.value, SemiprimeBitIndexClipping.SignedWord.value,
    SemiprimeBitArithmetic.bitValue, SemiprimeBitArithmetic.bitNat]

theorem zeroWord_valid : zeroWord.Valid := by
  change 0 < 1
  decide

/-- The physical output bound does not assume that arithmetic results fit;
fitting itself always returns the specified number of physical cells. -/
theorem dotBits_width (template : List Bool) (ht : 0<template.length)
    (pairs : List (RationalWord × RationalWord)) : Width (dotBits template pairs).word template.length := by
  cases pairs with
  | nil =>
    simp only [dotBits, zeroWord, Width, List.length_nil, List.length_cons]
    omega
  | cons pair rest =>
    have h := fitRationalBits_width
      (rawOperation .add (executeOperation .mul pair.1 pair.2 template).word
        (dotBits template rest).word).word template
    exact ⟨h.1.le,h.2.le⟩

/-- Common denominators and a bound on the whole input count control every
actual multiply and every partial sum. The output height is derived. -/
theorem dotBits_correct (template : List Bool)
    (pairs : List (RationalWord × RationalWord)) (d e B C : ℕ)
    (hd : 0<d) (he : 0<e) (hden : d*e<2^template.length)
    (hnum : pairs.length*B*C<2^template.length)
    (hp : ∀ pair ∈ pairs, pair.1.Valid ∧ pair.2.Valid ∧
      Representation pair.1.value d B ∧ Representation pair.2.value e C) :
    (dotBits template pairs).word.value = dotValue pairs ∧
      (dotBits template pairs).word.Valid ∧
      Representation (dotBits template pairs).word.value (d*e) (pairs.length*B*C) := by
  induction pairs with
  | nil =>
    simp only [dotBits, dotValue, List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul]
    refine ⟨zeroWord_value,zeroWord_valid,?_⟩
    rw [zeroWord_value]
    exact ⟨0,by simp,by simp⟩
  | cons pair rest ih =>
    have hrest : rest.length*B*C<2^template.length := by
      exact (Nat.mul_le_mul_right C (Nat.mul_le_mul_right B (by simp))).trans_lt hnum
    have hc := ih hrest (fun p hp' => hp p (List.mem_cons_of_mem _ hp'))
    have hp' := hp pair List.mem_cons_self
    have hm := representation_mul hp'.2.2.1 hp'.2.2.2
    have hmB : B*C < 2^template.length := by
      have hlen : 1 ≤ (pair::rest).length := by simp
      have hbound := Nat.mul_le_mul_right (B*C) hlen
      have hnum' : (pair::rest).length*(B*C)<2^template.length := by
        simpa only [Nat.mul_assoc] using hnum
      simpa only [Nat.one_mul] using hbound.trans_lt hnum'
    have hmfit : Fits (Operation.mul.value pair.1.value pair.2.value) template.length :=
      fits_of_representation (Nat.mul_pos hd he) hm hmB hden
    have hmc := executeOperation_correct .mul pair.1 pair.2 template hp'.1 hp'.2.1 hmfit
    have hm' : Representation (executeOperation .mul pair.1 pair.2 template).word.value (d*e) (B*C) := by
      rw [hmc.1]
      exact hm
    have hs := representation_add hm' hc.2.2
    have hsize : B*C+rest.length*B*C = (pair::rest).length*B*C := by simp;ring
    rw [hsize] at hs
    have hsfit : Fits (Operation.add.value
        (executeOperation .mul pair.1 pair.2 template).word.value
        (dotBits template rest).word.value) template.length :=
      fits_of_representation (Nat.mul_pos hd he) hs hnum hden
    have hsc := executeOperation_correct .add _ _ template hmc.2.1 hc.2.1 hsfit
    change (executeOperation .add (executeOperation .mul pair.1 pair.2 template).word
      (dotBits template rest).word template).word.value = _ ∧ _
    refine ⟨?_,hsc.2.1,?_⟩
    · rw [hsc.1]
      change (executeOperation .mul pair.1 pair.2 template).word.value +
        (dotBits template rest).word.value = _
      rw [hmc.1,hc.1]
      rfl
    · change Representation (executeOperation .add
        (executeOperation .mul pair.1 pair.2 template).word
        (dotBits template rest).word template).word.value _ _
      rw [hsc.1]
      exact hs

/-- The exact loop's Boolean/cell cost is linear in the number of terms and
cubic in physical rational word width. Each suffix is computed once. -/
theorem dotBits_cost (template : List Bool) (ht : 0<template.length)
    (pairs : List (RationalWord × RationalWord))
    (hp : ∀ pair ∈ pairs, Width pair.1 template.length ∧ Width pair.2 template.length) :
    (dotBits template pairs).clock ≤ pairs.length*(40000*(template.length+1)^3+4)+4 := by
  induction pairs with
  | nil => simp [dotBits]
  | cons pair rest ih =>
    have hh := hp pair List.mem_cons_self
    have hc := ih (fun p h => hp p (List.mem_cons_of_mem _ h))
    have hm := executeOperation_cost .mul pair.1 pair.2 template hh.1 hh.2 (by rfl)
    have hmW := fitRationalBits_width (rawOperation .mul pair.1 pair.2).word template
    have hs := executeOperation_cost .add (executeOperation .mul pair.1 pair.2 template).word
      (dotBits template rest).word template ⟨hmW.1.le,hmW.2.le⟩ (dotBits_width template ht rest) (by rfl)
    dsimp only [dotBits]
    simp only [List.length_cons]
    nlinarith

end RiemannGaussian.SemiprimeDotBits
