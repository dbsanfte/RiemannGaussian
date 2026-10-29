/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteEvaluationBits

/-! # Derived physical widths and clocks for Hermite evaluation

The width is polynomial in the ORIGINAL dyadic input exponent and requested
length. All operation fits follow from original-data numerical caps.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeHermiteEvaluationBitsBounds
open SemiprimeRationalBits SemiprimeJetBits SemiprimeDotBits SemiprimeJetArrayHeight
open SemiprimeHermiteEvaluationBits

/-- One public physical width for scalar evaluation and affine products. -/
def evaluationWidth (b J : ℕ) : ℕ := 8*(b+J+2)*(J+1)

/-- Original coefficient and integer bounds imply ALL core numerical caps. -/
theorem numeric_bounds (b J d B T : ℕ)
    (hdb : d≤2^b) (hBb : B≤2^b) (hTb : T≤2^b) :
    d<2^evaluationWidth b J ∧
    (J+1)*(B+1)*(T+1)^(J+1)<2^evaluationWidth b J ∧
    d^J<2^evaluationWidth b J ∧
    (d+B*T+1)^(J+1)<2^evaluationWidth b J := by
  have htwo : 1≤2^b := Nat.one_le_pow _ _ (by decide)
  have hb : B+1≤2^(b+1) := by rw [pow_succ]; omega
  have ht : T+1≤2^(b+1) := by rw [pow_succ]; omega
  have hj : J+1≤2^(J+1) := (Nat.lt_two_pow_self (n:=J+1)).le
  have hbase : d+B*T+1≤2^(2*b+2) := by
    have hm := Nat.mul_le_mul hBb hTb
    have hb2 : 2^b≤2^(2*b) := Nat.pow_le_pow_right (by decide) (by omega)
    have hp : 2^(2*b)=2^b*2^b := by rw [two_mul,pow_add]
    rw [show 2*b+2=2*b+1+1 by omega,pow_succ,pow_succ]
    rw [hp] at hb2 ⊢
    nlinarith
  have heval : (J+1)*(B+1)*(T+1)^(J+1)≤
      2^((J+1)+(b+1)+(b+1)*(J+1)) := by
    calc
      _ ≤ 2^(J+1)*2^(b+1)*(2^(b+1))^(J+1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hj hb) (Nat.pow_le_pow_left ht _)
      _ = _ := by rw [← pow_mul,← pow_add,← pow_add]
  have hdp : d^J≤2^(b*J) := by simpa only [pow_mul] using Nat.pow_le_pow_left hdb J
  have hap : (d+B*T+1)^(J+1)≤2^((2*b+2)*(J+1)) := by
    simpa only [pow_mul] using Nat.pow_le_pow_left hbase (J+1)
  have he1 : b<evaluationWidth b J := by unfold evaluationWidth; nlinarith
  have he2 : (J+1)+(b+1)+(b+1)*(J+1)<evaluationWidth b J := by unfold evaluationWidth; nlinarith
  have he3 : b*J<evaluationWidth b J := by unfold evaluationWidth; nlinarith
  have he4 : (2*b+2)*(J+1)<evaluationWidth b J := by unfold evaluationWidth; nlinarith
  exact ⟨hdb.trans_lt (Nat.pow_lt_pow_right (by decide) he1),
    heval.trans_lt (Nat.pow_lt_pow_right (by decide) he2),
    hdp.trans_lt (Nat.pow_lt_pow_right (by decide) he3),
    hap.trans_lt (Nat.pow_lt_pow_right (by decide) he4)⟩

/-- Physical fitting always returns the literal template length, independently of semantics. -/
theorem operation_width (op : Operation) (x y : RationalWord) (template : List Bool) :
    Width (executeOperation op x y template).word template.length := by
  have h := fitRationalBits_width (rawOperation op x y).word template
  exact ⟨h.1.le,h.2.le⟩

/-- Both retained evaluation words have bounded physical storage. -/
theorem evalPrefix_width (template : List Bool) (a : Array RationalWord) (x : RationalWord)
    (len : ℕ) (ht : 0<template.length) :
    Width (evalPrefix template a x len).word template.length ∧
    Width (evalPrefix template a x len).power template.length := by
  cases len with
  | zero => exact ⟨⟨Nat.zero_le _,ht⟩,
      oneWord_width ht⟩
  | succ len => exact ⟨operation_width _ _ _ _,operation_width _ _ _ _⟩

/-- The affine output has a fixed physical width. -/
theorem affineValue_width (template : List Bool) (x : RationalWord)
    (cs : List RationalWord) (ht : 0<template.length) :
    Width (affineValue template x cs).word template.length := by
  cases cs with
  | nil => exact oneWord_width ht
  | cons c cs => exact operation_width _ _ _ _

/-- Actual bit operations, physical coefficient lookup and cached-word copies are retained. -/
theorem evalPrefix_clock (template : List Bool) (a : Array RationalWord) (x : RationalWord)
    (len : ℕ) (ht : 0<template.length) (ha : Bounded a template.length)
    (hx : Width x template.length) :
    (evalPrefix template a x len).clock≤4+len*
      (60000*(template.length+1)^3+accessCost template a+8*template.length+12) := by
  induction len with
  | zero => simp [evalPrefix]
  | succ len ih =>
    have hw := evalPrefix_width template a x len ht
    have hc := executeOperation_cost .mul (wordAt a len) (evalPrefix template a x len).power template
      (wordAt_width a ht ha len) hw.2 (le_refl _)
    have hv := executeOperation_cost .add (evalPrefix template a x len).word
      (executeOperation .mul (wordAt a len) (evalPrefix template a x len).power template).word
      template hw.1 (operation_width _ _ _ _) (le_refl _)
    have hp := executeOperation_cost .mul (evalPrefix template a x len).power x template hw.2 hx (le_refl _)
    simp only [evalPrefix]
    nlinarith

/-- Actual affine product clock; acquisition of the supplied slope list is separate. -/
theorem affineValue_clock (template : List Bool) (x : RationalWord) (cs : List RationalWord)
    (ht : 0<template.length) (hx : Width x template.length)
    (hc : ∀ c∈cs,Width c template.length) :
    (affineValue template x cs).clock≤4+cs.length*
      (60000*(template.length+1)^3+8*template.length+12) := by
  induction cs with
  | nil => simp [affineValue]
  | cons c cs ih =>
    have hi := ih (fun z hz => hc z (List.mem_cons_of_mem c hz))
    have hm := executeOperation_cost .mul c x template (hc c List.mem_cons_self) hx (le_refl _)
    have hf := executeOperation_cost .add oneWord (executeOperation .mul c x template).word template
      (oneWord_width ht) (operation_width _ _ _ _) (le_refl _)
    have ho := executeOperation_cost .mul (affineValue template x cs).word
      (executeOperation .add oneWord (executeOperation .mul c x template).word template).word template
      (affineValue_width template x cs ht) (operation_width _ _ _ _) (le_refl _)
    simp only [affineValue,List.length_cons]
    nlinarith

/-- Polynomial width suffices for the actual scalar evaluation, from original inputs only. -/
theorem evalPrefix_at_width (template : List Bool) (a : Array RationalWord)
    (xw : RationalWord) (x : ℤ) (b d B T J len : ℕ)
    (hw : evaluationWidth b J≤template.length)
    (hd : 0<d) (ha : Valid a) (hxw : xw.Valid) (hxval : xw.value=(x:ℚ))
    (hx : x.natAbs≤T) (hlen : len≤J)
    (hcoeff : ∀ i<J,Representation (SemiprimeJetArray.coefficient (decode a) i) d B)
    (hdb : d≤2^b) (hBb : B≤2^b) (hTb : T≤2^b) :
    (evalPrefix template a xw len).word.value=
      (SemiprimeHermiteArrayHeight.evalPrefix (decode a) x len).value ∧
    (evalPrefix template a xw len).power.value=(x:ℚ)^len ∧
    (evalPrefix template a xw len).word.Valid ∧
    (evalPrefix template a xw len).power.Valid := by
  have hn := numeric_bounds b J d B T hdb hBb hTb
  have hp := Nat.pow_le_pow_right (by decide : 0<2) hw
  exact evalPrefix_correct template a xw x d B T J len hd ha hxw hxval hx hlen hcoeff
    (hn.1.trans_le hp) (hn.2.1.trans_le hp)

/-- Polynomial width suffices for every affine-product suffix and temporary. -/
theorem affineValue_at_width (template : List Bool) (xw : RationalWord) (x : ℤ)
    (cs : List RationalWord) (b d B T J : ℕ)
    (hw : evaluationWidth b J≤template.length) (hd : 0<d)
    (hxw : xw.Valid) (hxval : xw.value=(x:ℚ)) (hx : x.natAbs≤T)
    (hlen : cs.length≤J) (hc : ∀ c∈cs,c.Valid ∧ Representation c.value d B)
    (hdb : d≤2^b) (hBb : B≤2^b) (hTb : T≤2^b) :
    (affineValue template xw cs).word.value=
      (SemiprimeHermiteArrayHeight.affineValue x (cs.map RationalWord.value)).value ∧
    (affineValue template xw cs).word.Valid ∧
    Representation (affineValue template xw cs).word.value
      (d^cs.length) ((d+B*T+1)^cs.length) := by
  have hn := numeric_bounds b J d B T hdb hBb hTb
  have hp := Nat.pow_le_pow_right (by decide : 0<2) hw
  exact affineValue_correct template xw x cs d B T J hd hxw hxval hx hlen hc
    (hn.2.2.1.trans_le hp) (hn.2.2.2.trans_le hp)

end RiemannGaussian.SemiprimeHermiteEvaluationBitsBounds
