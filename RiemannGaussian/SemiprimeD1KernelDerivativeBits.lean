/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1KernelProductBits
import RiemannGaussian.SemiprimeD1RecoveryIntegerBits
import RiemannGaussian.SemiprimeBitPrimeScan

/-! # Physical unit-grid derivative product from literal grid words
Each equality test and signed difference executes its Boolean program. The
cancelled central factor is omitted using that actual equality flag. Full exact
signed multiplication then produces the derivative without native big integers.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1KernelDerivativeBits
open SemiprimeBitArithmetic SemiprimeBitIndexClipping SemiprimeBitPrimeScan
open SemiprimeD1RecoveryIntegerBits (positive positive_value)

/-- Actual noncentral signed differences and their acquisition report. -/
structure Factors where
  /-- Literal signed difference bytes, in the original grid order. -/
  words : List SignedWord
  /-- Every comparison, subtraction, copy and finite list decision. -/
  clock : ℕ

/-- Acquire signed grid differences, skipping only the actual equal word. -/
def factors (center : List Bool) : List (List Bool) → Factors
  | [] => ⟨[],1⟩
  | q::qs =>
    let tail := factors center qs
    let test := orderWords center q
    if test.equal then ⟨tail.words,tail.clock+test.clock+3⟩
    else
      let difference := subSignedBits (positive center) (positive q)
      ⟨difference.word::tail.words,tail.clock+test.clock+difference.clock+5⟩

/-- Literal acquired factors have exactly the original derivative-product
meaning. Natural evaluations occur only in this specification. -/
theorem factors_value (center : List Bool) (qs : List (List Bool)) :
    ((factors center qs).words.map SignedWord.value).prod =
      (qs.map (fun q => if bitValue center=bitValue q then (1:ℤ)
        else (bitValue center:ℤ)-(bitValue q:ℤ))).prod := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    dsimp only [factors]
    split
    · rename_i h
      have he := (orderWords_equal center q).mp h
      simp only [List.map_cons,List.prod_cons,ite_eq_left he,one_mul,ih]
    · rename_i h
      have he : bitValue center ≠ bitValue q := by
        intro he
        exact h ((orderWords_equal center q).mpr he)
      simp only [List.map_cons,List.prod_cons,ite_eq_right he,subSignedBits_value,
        positive_value,ih]

/-- Physical acquisition never emits more than the original number of factors. -/
theorem factors_length (center : List Bool) (qs : List (List Bool)) :
    (factors center qs).words.length ≤ qs.length := by
  induction qs with
  | nil => simp only [factors,List.length_nil,le_refl]
  | cons q qs ih =>
    dsimp only [factors]
    split <;> dsimp only [List.length_cons] <;> omega

/-- All signed difference bytes have the derived original grid-word width. -/
theorem factors_width (center : List Bool) (qs : List (List Bool)) (W : ℕ)
    (hc : center.length ≤ W) (hq : ∀ q∈qs,q.length ≤ W) :
    ∀ x∈(factors center qs).words,x.magnitude.length ≤ W+1 := by
  induction qs with
  | nil => simp only [factors,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons q qs ih =>
    have hh := hq q List.mem_cons_self
    have ht := ih (fun x hx => hq x (List.mem_cons_of_mem q hx))
    have hs := (subSignedBits_cost_width (left:=positive center) (right:=positive q) hc hh).2
    dsimp only [factors]
    split
    · exact ht
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hs
      · exact ht x hx

/-- Complete physical factor acquisition is linear in original grid cardinality
times actual input width. No decoded difference or valuation is supplied. -/
theorem factors_clock (center : List Bool) (qs : List (List Bool)) (W : ℕ)
    (hc : center.length ≤ W) (hq : ∀ q∈qs,q.length ≤ W) :
    (factors center qs).clock ≤ qs.length*(56*(W+1)+15)+1 := by
  induction qs with
  | nil => simp only [factors,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons q qs ih =>
    have hh := hq q List.mem_cons_self
    have ht := ih (fun x hx => hq x (List.mem_cons_of_mem q hx))
    have he := orderWords_cost hc hh
    have hs := (subSignedBits_cost_width (left:=positive center) (right:=positive q) hc hh).1
    dsimp only [factors]
    split <;> dsimp only <;> simp only [List.length_cons] <;> nlinarith

/-- Actual full derivative bytes and every acquisition/product contribution. -/
def run (center : List Bool) (qs : List (List Bool)) : SemiprimeD1KernelProductBits.Run :=
  let acquired := factors center qs
  let out := SemiprimeD1KernelProductBits.run acquired.words
  ⟨out.word,acquired.clock+out.clock+3⟩

/-- Exact full signed derivative, with no native integer product executed. -/
theorem run_value (center : List Bool) (qs : List (List Bool)) :
    (run center qs).word.value =
      (qs.map (fun q => if bitValue center=bitValue q then (1:ℤ)
        else (bitValue center:ℤ)-(bitValue q:ℤ))).prod := by
  exact (SemiprimeD1KernelProductBits.run_value (factors center qs).words).trans (factors_value center qs)

/-- Actual full denominator bytes fit one polynomial original grid-width cap. -/
theorem run_width (center : List Bool) (qs : List (List Bool)) (W : ℕ)
    (hc : center.length ≤ W) (hq : ∀ q∈qs,q.length ≤ W) :
    (run center qs).word.magnitude.length ≤ 2*qs.length*(W+1)+1 := by
  have h := SemiprimeD1KernelProductBits.run_width (factors center qs).words (W+1)
    (factors_width center qs W hc hq)
  exact h.trans (by gcongr;exact factors_length center qs)

/-- Complete physical derivative report, with every factor and full intermediate
integer width paid by a fixed original-dimension polynomial. -/
theorem run_clock (center : List Bool) (qs : List (List Bool)) (W : ℕ)
    (hc : center.length ≤ W) (hq : ∀ q∈qs,q.length ≤ W) :
    (run center qs).clock ≤ qs.length*(56*(W+1)+15)+1+
      SemiprimeD1KernelProductBits.budget qs.length (W+1)+3 := by
  have hf := factors_clock center qs W hc hq
  have hp := SemiprimeD1KernelProductBits.run_clock (factors center qs).words (W+1)
    (factors_width center qs W hc hq)
  have hn := factors_length center qs
  have hm : SemiprimeD1KernelProductBits.budget (factors center qs).words.length (W+1) ≤
      SemiprimeD1KernelProductBits.budget qs.length (W+1) := by
    unfold SemiprimeD1KernelProductBits.budget
    gcongr
  change (factors center qs).clock+(SemiprimeD1KernelProductBits.run (factors center qs).words).clock+3 ≤ _
  omega

end RiemannGaussian.SemiprimeD1KernelDerivativeBits
