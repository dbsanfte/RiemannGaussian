/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLocalBitsCorrectness

/-! # Derived polynomial word widths and actual local bit clocks -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeLocalBitsBounds
open SemiprimeLocalBits SemiprimeLocalBitsCorrectness SemiprimeJetBits SemiprimeRationalBits
open SemiprimeLocalArrayFrontend SemiprimeLocalExecutionHeight SemiprimeLocalExecutionBitBounds
open SemiprimeBitIndexClipping SemiprimeJetArrayHeight

/-- Public polynomial buffer width, from initial bit exponents and local arity. -/
def bufferWidth (b w : ℕ) : ℕ := (2*b+3)*(w+1)+3

/-- The numeric scalar cap follows from initial port heights at this public width. -/
theorem cap_dyadic (J d B b w : ℕ) (hJ : J ≤ 2^b) (hd : d ≤ 2^b) (hB : B ≤ 2^b) :
    cap J d B w < 2^(bufferWidth b w) := by
  let E := (2*b+3)*(w+1)
  have hp : 1 ≤ 2^b := Nat.one_le_pow _ _ (by decide)
  have hd1 : d+1 ≤ 2^(b+1) := by rw [pow_succ]; omega
  have hc := localBase_le J d B b hJ hd hB
  have hc1 : localBase J d B+1 ≤ 2^(2*b+3) := by
    rw [show 2*b+3=(2*b+2)+1 by omega,pow_succ]
    have hh : 1 ≤ 2^(2*b+2) := Nat.one_le_pow _ _ (by decide)
    omega
  have h₁ : (d+1)^w ≤ 2^E := by
    have h := Nat.pow_le_pow_left hd1 w
    rw [← pow_mul] at h
    exact h.trans (Nat.pow_le_pow_right (by decide) (by dsimp [E]; nlinarith))
  have h₂ : (localBase J d B+1)^w ≤ 2^E := by
    have h := Nat.pow_le_pow_left hc1 w
    rw [← pow_mul] at h
    exact h.trans (Nat.pow_le_pow_right (by decide) (by dsimp [E]; nlinarith))
  have hrest : d+B+2 ≤ 2^E := by
    have h : d+B+2 ≤ 2^(b+2) := by
      rw [show b+2=b+1+1 by omega,pow_succ,pow_succ]
      omega
    exact h.trans (Nat.pow_le_pow_right (by decide) (by dsimp [E]; nlinarith))
  have hpos : 0<2^E := pow_pos (by decide) _
  change cap J d B w<2^(E+3)
  rw [pow_add]
  norm_num
  unfold cap
  omega

/-- Only input representations and dimension bit bounds are needed for correctness. -/
theorem local_correct_at_public_width (template : List Bool) (J d B b w : ℕ)
    (hwidth : bufferWidth b w ≤ template.length) (hd : 0<d)
    (hJ : J ≤ 2^b) (hden : d ≤ 2^b) (hB : B ≤ 2^b)
    (T : (Fin w → Bool) → EntryWord) (inputs : Fin w → Array RationalWord)
    (hT : ∀ eta, (T eta).bits.value.natAbs ≤ 1)
    (hinputs : ∀ v, ArrayBound (decode (inputs v)) J d B)
    (hvalid : ∀ v, Valid (inputs v)) :
    EqualBelow J (decode (localEvaluateBits template J w T inputs).words)
      (localEvaluate J w (table T) (fun v => decode (inputs v))).coefficients ∧
    Valid (localEvaluateBits template J w T inputs).words ∧
    ArrayBound (decode (localEvaluateBits template J w T inputs).words) J (d^w) (localBase J d B^w) :=
  local_correct template J d B hd w T inputs
    ((cap_dyadic J d B b w hJ hden hB).trans_le (Nat.pow_le_pow_right (by decide) hwidth)) hT hinputs hvalid

/-- Flat coefficient-access envelope when all arrays have width at most J. -/
def accessBudget (J W : ℕ) : ℕ := (J+1)*(2*W+3)
/-- Executed coefficient scaling budget. -/
def scaleBudget (J W : ℕ) : ℕ := J*(20000*(W+1)^3+accessBudget J W+(2*W+3))+(2*J+1)
/-- Executed coefficient addition budget. -/
def addBudget (J W : ℕ) : ℕ := J*(20000*(W+1)^3+2*accessBudget J W)+(2*J+1)
/-- Executed convolution dot budget. -/
def multiplyBudget (J W : ℕ) : ℕ :=
  J*(J*(40000*(W+1)^3+4)+4+J*(2*accessBudget J W))+(2*J+1)
/-- All five physical stages and literal-one construction at one local node. -/
def nodeBudget (J W : ℕ) : ℕ := scaleBudget J W+2*addBudget J W+2*multiplyBudget J W+3*J+12

/-- Actual array access costs are covered by their physical array sizes. -/
theorem access_le (template : List Bool) (J : ℕ) (a : Array RationalWord) (h : a.size ≤ J) :
    accessCost template a ≤ accessBudget J template.length := by
  unfold accessCost accessBudget
  exact Nat.mul_le_mul_right _ (Nat.add_le_add_right h 1)

/-- Physical scaling instruction and addressing clocks are bounded without output advice. -/
theorem scale_budget (template : List Bool) (ht : 0<template.length) (J : ℕ)
    (a : Array RationalWord) (c : RationalWord)
    (ha : Bounded a template.length) (hc : Width c template.length) (hs : a.size ≤ J) :
    (scaleBits template a c J).clock ≤ scaleBudget J template.length := by
  apply (scaleBits_cost template ht a c J ha hc).trans
  unfold scaleBudget
  gcongr
  exact access_le template J a hs

/-- Physical addition instruction and addressing clocks. -/
theorem add_budget (template : List Bool) (ht : 0<template.length) (J : ℕ)
    (a c : Array RationalWord) (ha : Bounded a template.length) (hc : Bounded c template.length)
    (hs : a.size ≤ J) (hts : c.size ≤ J) :
    (addBits template a c J).clock ≤ addBudget J template.length := by
  apply (addBits_cost template ht a c J ha hc).trans
  have h₁ := access_le template J a hs
  have h₂ := access_le template J c hts
  unfold addBudget
  nlinarith

/-- All actual convolution dots and their flat accesses. -/
theorem multiply_budget (template : List Bool) (ht : 0<template.length) (J : ℕ)
    (a c : Array RationalWord) (ha : Bounded a template.length) (hc : Bounded c template.length)
    (hs : a.size ≤ J) (hts : c.size ≤ J) :
    (multiplyBits template a c J).clock ≤ multiplyBudget J template.length := by
  apply (multiplyBits_cost template ht a c J ha hc).trans
  have h₁ := access_le template J a hs
  have h₂ := access_le template J c hts
  unfold multiplyBudget
  have hsum : accessCost template a+accessCost template c ≤ 2*accessBudget J template.length := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul_left J
    (Nat.add_le_add_left (Nat.mul_le_mul_left J hsum)
      (J*(40000*(template.length+1)^3+4)+4))) (2*J+1)

/-- The actual integer callback words have denominator-one physical widths. -/
theorem entry_width (template : List Bool) (ht : 0<template.length) (e : EntryWord)
    (h : e.bits.magnitude.length ≤ template.length) : Width e.rational template.length :=
  ⟨h,ht⟩

/-- The whole local physical clock charges both branches, all actual arithmetic,
flat jet accesses, literal buffers, and every leaf's integer callback clock. -/
theorem local_clock (template : List Bool) (J w E : ℕ) (ht : 0<template.length)
    (T : (Fin w → Bool) → EntryWord) (inputs : Fin w → Array RationalWord)
    (hT : ∀ eta, (T eta).clock ≤ E)
    (hentry : ∀ eta, (T eta).bits.magnitude.length ≤ template.length)
    (hinputs : ∀ v, Bounded (inputs v) template.length) (hsize : ∀ v, (inputs v).size ≤ J) :
    (localEvaluateBits template J w T inputs).clock ≤ 
      2^w*(E+(w+1)*nodeBudget J template.length) := by
  induction w with
  | zero =>
    have hc := scale_budget template ht J (oneArray J) (T Fin.elim0).rational
      (oneArray_bounded J _ ht) (entry_width template ht _ (hentry _)) (by simp)
    have he := hT Fin.elim0
    change (T Fin.elim0).clock+(scaleBits template (oneArray J) (T Fin.elim0).rational J).clock+3*J+4 ≤ _
    simp only [pow_zero,one_mul,Nat.zero_add]
    unfold nodeBudget
    omega
  | succ w ih =>
    let l := localEvaluateBits template J w (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ)
    let h := localEvaluateBits template J w (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ)
    have hl := ih _ _ (fun eta => hT (Fin.cons false eta)) (fun eta => hentry (Fin.cons false eta))
      (fun i => hinputs i.succ) (fun i => hsize i.succ)
    have hh := ih _ _ (fun eta => hT (Fin.cons true eta)) (fun eta => hentry (Fin.cons true eta))
      (fun i => hinputs i.succ) (fun i => hsize i.succ)
    let neg := scaleBits template (inputs 0) negOneWord J
    let no := addBits template (oneArray J) neg.words J
    let left := multiplyBits template no.words l.words J
    let right := multiplyBits template (inputs 0) h.words J
    have hn := scale_budget template ht J (inputs 0) negOneWord (hinputs 0) (negOneWord_width ht) (hsize 0)
    have hno := add_budget template ht J (oneArray J) neg.words (oneArray_bounded J _ ht)
      (scaleBits_bounded _ _ _ _) (by simp) (by simp [neg])
    have hleft := multiply_budget template ht J no.words l.words
      (addBits_bounded _ _ _ _) (localEvaluateBits_bounded _ _ _ _ _) (by simp [no]) (by simp [l,localEvaluateBits_size])
    have hright := multiply_budget template ht J (inputs 0) h.words
      (hinputs 0) (localEvaluateBits_bounded _ _ _ _ _) (hsize 0) (by simp [h,localEvaluateBits_size])
    have hout := add_budget template ht J left.words right.words
      (multiplyBits_bounded _ ht _ _ _) (multiplyBits_bounded _ ht _ _ _)
      (by simp [left]) (by simp [right])
    change l.clock+h.clock+neg.clock+no.clock+left.clock+right.clock+
      (addBits template left.words right.words J).clock+3*J+12 ≤ _
    change neg.clock ≤ scaleBudget J template.length at hn
    change no.clock ≤ addBudget J template.length at hno
    change left.clock ≤ multiplyBudget J template.length at hleft
    change right.clock ≤ multiplyBudget J template.length at hright
    change l.clock ≤ 2^w*(E+(w+1)*nodeBudget J template.length) at hl
    change h.clock ≤ 2^w*(E+(w+1)*nodeBudget J template.length) at hh
    have hstage : neg.clock+no.clock+left.clock+right.clock+
        (addBits template left.words right.words J).clock+3*J+12 ≤ nodeBudget J template.length := by
      unfold nodeBudget
      omega
    rw [pow_succ]
    have hp : 1 ≤ 2^w := Nat.one_le_pow _ _ (by decide)
    nlinarith
end RiemannGaussian.SemiprimeLocalBitsBounds
