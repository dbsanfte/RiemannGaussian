/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNativeGroupBits
import RiemannGaussian.SemiprimeHermiteArrayHeight

/-! # Physical intrinsic affine cardinal products
The recursive suffix is executed once and retained. Common slope representations
bound every convolution prefix; no intermediate fit or product is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeAffineJetBits
open SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeLocalExecutionHeight

/-- Literal physical affine factor. -/
def affine (c : RationalWord) : Array RationalWord := #[oneWord,c]

/-- Exact interpretation of the literal two-word factor. -/
theorem affine_decode (c : RationalWord) :
    decode (affine c)=SemiprimeHermiteArrayHeight.affineArray c.value := by
  simp [decode,affine,SemiprimeHermiteArrayHeight.affineArray]

/-- The literal unit and acquired slope have legal denominators. -/
theorem affine_valid (c : RationalWord) (hc : c.Valid) : Valid (affine c) := by
  intro i hi
  have hi' : i<2 := hi
  interval_cases i
  · exact oneWord_valid
  · exact hc

/-- The physical factor fits whenever its acquired slope and unit fit. -/
theorem affine_bounded (c : RationalWord) {W : ℕ} (hW : 0<W) (hc : Width c W) :
    Bounded (affine c) W := by
  intro i hi
  have hi' : i<2 := hi
  interval_cases i
  · exact oneWord_width hW
  · exact hc

/-- Same-order physical version of the intrinsic cardinal array builder. -/
def build (template : List Bool) (J : ℕ) : List RationalWord → JetReport
  | [] => ⟨#[oneWord],4⟩
  | c::cs =>
      let old := build template J cs
      let out := multiplyBits template old.words (affine c) J
      ⟨out.words,old.clock+out.clock+4*template.length+10⟩

/-- Explicit fixed-polynomial width in slope bits and actual factor count. -/
def width (b L : ℕ) : ℕ := (2*b+1)*(L+1)+1

/-- The width covers every power denominator and convolution-prefix numerator. -/
theorem powers_fit (b J d L W : ℕ) (hdb : d≤2^b) (hJb : J≤2^b)
    (hW : width b L≤W) : d^L<2^W ∧ (J*d)^L<2^W := by
  have hd : d^L≤2^(b*L) := by simpa only [← pow_mul] using Nat.pow_le_pow_left hdb L
  have hn : J*d≤2^(2*b) := by
    calc
      J*d≤2^b*2^b := Nat.mul_le_mul hJb hdb
      _=2^(2*b) := by rw [← pow_add]; congr 1; omega
  have hp : (J*d)^L≤2^((2*b)*L) := by simpa only [← pow_mul] using Nat.pow_le_pow_left hn L
  have he : (2*b)*L<W := by unfold width at hW; nlinarith
  exact ⟨hd.trans_lt (Nat.pow_lt_pow_right (by decide) (by nlinarith)),
    hp.trans_lt (Nat.pow_lt_pow_right (by decide) he)⟩

/-- Exact physical cardinal product and common representations from original slopes. -/
theorem build_correct (template : List Bool) (b J d : ℕ) (cs : List RationalWord)
    (hd : 0<d) (hdb : d≤2^b) (hJb : J≤2^b)
    (hwidth : width b cs.length≤template.length)
    (hc : ∀ c∈cs,c.Valid ∧ Representation c.value d d) :
    decode (build template J cs).words=
      (SemiprimeHermiteArrayHeight.buildAffine J (cs.map RationalWord.value)).coefficients ∧
    Valid (build template J cs).words ∧
    ArrayBound (decode (build template J cs).words) J (d^cs.length) ((J*d)^cs.length) := by
  induction cs with
  | nil =>
    refine ⟨by simp [build,decode,SemiprimeHermiteArrayHeight.buildAffine],?_,?_⟩
    · intro i hi
      have hi' : i<1 := hi
      have he : i=0 := by omega
      subst i
      exact oneWord_valid
    · intro i hi
      have h := SemiprimeHermiteArrayHeight.buildAffine_representation J d hd [] (by simp) i hi
      simpa [build,decode,SemiprimeHermiteArrayHeight.buildAffine] using h
  | cons c cs ih =>
    have ht : width b cs.length≤template.length := by
      unfold width at hwidth ⊢
      simp only [List.length_cons] at hwidth
      nlinarith
    have hs := ih ht (fun z hz => hc z (List.mem_cons_of_mem c hz))
    have hv := hc c List.mem_cons_self
    have hf := powers_fit b J d (c::cs).length template.length hdb hJb hwidth
    have hden : d^cs.length*d<2^template.length := by
      simpa only [List.length_cons,pow_succ] using hf.1
    have hnum : J*(J*d)^cs.length*d<2^template.length := by
      have he : J*(J*d)^cs.length*d=(J*d)^(cs.length+1) := by rw [pow_succ]; ring
      rw [he]
      exact hf.2
    have hm := multiplyBits_correct template (build template J cs).words (affine c)
      J (d^cs.length) d ((J*d)^cs.length) d hs.2.1 (affine_valid c hv.1)
      (pow_pos hd _) hd hden hnum hs.2.2 (by
        intro i _
        rw [affine_decode]
        exact SemiprimeHermiteArrayHeight.affineArray_representation c.value d hd hv.2 i)
    have heq : decode (multiplyBits template (build template J cs).words (affine c) J).words=
        (multiply (decode (build template J cs).words) (decode (affine c)) J).coefficients := by
      apply SemiprimeCorrectedPortBits.array_eq_of_coeff J
      · simp only [decode_size,multiplyBits_size]
      · exact multiply_size _ _ _
      · exact hm.1
    have hout : decode (build template J (c::cs)).words=
        (SemiprimeHermiteArrayHeight.buildAffine J ((c::cs).map RationalWord.value)).coefficients := by
      change decode (multiplyBits template (build template J cs).words (affine c) J).words=_
      rw [heq,hs.1,affine_decode]
      rfl
    refine ⟨hout,hm.2,?_⟩
    intro i hi
    rw [hout]
    have hr := SemiprimeHermiteArrayHeight.buildAffine_representation J d hd
      ((c::cs).map RationalWord.value) (by
        intro q hq
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hq
        exact (hc z hz).2) i hi
    simpa only [List.length_map] using hr

/-- Structural output size keeps the true singleton empty product. -/
theorem build_size (template : List Bool) (J : ℕ) (cs : List RationalWord) :
    (build template J cs).words.size=if cs=[] then 1 else J := by
  cases cs <;> simp [build]

/-- Every actual suffix output occupies the selected physical width. -/
theorem build_bounded (template : List Bool) (J : ℕ) (cs : List RationalWord)
    (ht : 0<template.length) : Bounded (build template J cs).words template.length := by
  cases cs with
  | nil =>
    intro i hi
    have hi' : i<1 := hi
    have he : i=0 := by omega
    subst i
    exact oneWord_width ht
  | cons c cs => exact multiplyBits_bounded template ht _ _ J

/-- Fixed physical multiplication and literal factor construction budget. -/
def stepBudget (W J : ℕ) : ℕ :=
  J*(J*(40000*(W+1)^3+4)+4+J*((J+2)*(2*W+3)+3*(2*W+3)))+
    (2*J+1)+4*W+10

/-- Every cached suffix, physical multiply, factor copy and access remains paid. -/
theorem build_clock (template : List Bool) (J : ℕ) (cs : List RationalWord)
    (ht : 0<template.length) (hc : ∀ c∈cs,Width c template.length) :
    (build template J cs).clock≤4+cs.length*stepBudget template.length J := by
  induction cs with
  | nil => simp [build]
  | cons c cs ih =>
    have hs := ih (fun z hz => hc z (List.mem_cons_of_mem c hz))
    have hm := multiplyBits_cost template ht (build template J cs).words (affine c) J
      (build_bounded template J cs ht) (affine_bounded c ht (hc c List.mem_cons_self))
    have hsize : (build template J cs).words.size≤J+1 := by
      rw [build_size]
      split_ifs <;> omega
    have ha : accessCost template (build template J cs).words≤(J+2)*(2*template.length+3) := by
      unfold accessCost
      exact Nat.mul_le_mul_right _ (by omega)
    have haf : accessCost template (affine c)=3*(2*template.length+3) := rfl
    rw [haf] at hm
    have hm' := hm.trans (show _≤J*(J*(40000*(template.length+1)^3+4)+4+
        J*((J+2)*(2*template.length+3)+3*(2*template.length+3)))+(2*J+1) by
      gcongr)
    change (build template J cs).clock+(multiplyBits template (build template J cs).words (affine c) J).clock+
      4*template.length+10≤_
    simp only [List.length_cons]
    unfold stepBudget at hs ⊢
    nlinarith only [hs,hm']

end RiemannGaussian.SemiprimeAffineJetBits
