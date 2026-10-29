/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeJetBits
import RiemannGaussian.SemiprimeHermiteArrayHeight
import RiemannGaussian.SemiprimeLocalArrayFrontend

/-! # Executed cached normalized inverse
Only physical words occur in the runtime path. The sole recursive call retains
the complete prefix. The ledger includes pair reads, allocation and prefix copying;
source acquisition and physical natural-number/address administration are separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
namespace RiemannGaussian.SemiprimeNormalizedInverseBits
open scoped BigOperators
open SemiprimeRationalBits SemiprimeDotBits SemiprimeJetBits SemiprimeJetArray
open SemiprimeJetArrayHeight

/-- Actual ordered coefficient pairs, read from the two cached arrays. -/
def pairs (a b : Array RationalWord) (n : ℕ) : List (RationalWord × RationalWord) :=
  List.ofFn (fun i : Fin n => (wordAt a (i.val+1),wordAt b (n-1-i.val)))

/-- One cached prefix extension, including its physical dot and negation. -/
def extend (template : List Bool) (a : Array RationalWord) (n : ℕ) (old : JetReport) : JetReport :=
  if n=0 then ⟨old.words.push oneWord,old.clock+2*template.length+5⟩ else
    let ps := pairs a old.words n
    let s := dotBits template ps
    let out := executeOperation .neg s.word zeroWord template
    ⟨old.words.push out.word,old.clock+s.clock+out.clock+
      n*(accessCost template a+accessCost template old.words+5)+
      (old.words.size+1)*(2*template.length+3)+5⟩

/-- Actual inverse construction. No recursive coefficient is recomputed. -/
def build (template : List Bool) (a : Array RationalWord) : ℕ → JetReport
  | 0 => ⟨#[],1⟩
  | n+1 => let old := build template a n; extend template a n old

@[simp] theorem pairs_length (a b : Array RationalWord) (n : ℕ) : (pairs a b n).length=n := by
  simp [pairs]

@[simp] theorem extend_size (template : List Bool) (a : Array RationalWord) (n : ℕ) (old : JetReport) :
    (extend template a n old).words.size=old.words.size+1 := by
  simp [extend]; split <;> simp

@[simp] theorem build_size (template : List Bool) (a : Array RationalWord) (n : ℕ) :
    (build template a n).words.size=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [build,extend_size,ih]

/-- The physical dot has exactly the scalar cached recurrence's ordering. -/
theorem pairs_value (a b : Array RationalWord) (n : ℕ) :
    dotValue (pairs a b n)=
      (dotPrefix (decode a) (decode b) (n-1) n).value := by
  rw [dotPrefix_value]
  simp only [dotValue,pairs,List.map_ofFn,List.sum_ofFn,coefficient_decode]
  change (∑ i : Fin n, (wordAt a (i.val+1)).value*(wordAt b (n-1-i.val)).value) = _
  exact Fin.sum_univ_eq_sum_range (fun i : ℕ => (wordAt a (i+1)).value*(wordAt b (n-1-i)).value) n

/-- Appending a bounded physical output preserves the cached bound. -/
theorem bounded_push (a : Array RationalWord) (x : RationalWord) (W : ℕ)
    (ha : Bounded a W) (hx : Width x W) : Bounded (a.push x) W := by
  intro i hi
  by_cases h : i<a.size
  · simpa only [Array.getElem_push, dite_eq_left h] using ha i h
  · have he : i=a.size := by simp only [Array.size_push] at hi; omega
    subst i
    simpa only [Array.getElem_push, dite_eq_right (Nat.lt_irrefl _)] using hx

/-- Every output is physically width-truncated, independently of semantic fitting. -/
theorem build_bounded (template : List Bool) (ht : 0<template.length)
    (a : Array RationalWord) (n : ℕ) : Bounded (build template a n).words template.length := by
  induction n with
  | zero => intro i hi; simp [build] at hi
  | succ n ih =>
    simp only [build,extend]
    split
    · exact bounded_push _ _ _ ih (oneWord_width ht)
    · apply bounded_push _ _ _ ih
      exact ⟨(fitRationalBits_width _ template).1.le,(fitRationalBits_width _ template).2.le⟩

/-- Physical validity is preserved by appending a legal scalar. -/
theorem valid_push (a : Array RationalWord) (x : RationalWord)
    (ha : Valid a) (hx : x.Valid) : Valid (a.push x) := by
  intro i hi
  by_cases h : i<a.size
  · simpa only [Array.getElem_push, dite_eq_left h] using ha i h
  · have he : i=a.size := by simp only [Array.size_push] at hi; omega
    subst i
    simpa only [Array.getElem_push, dite_eq_right (Nat.lt_irrefl _)] using hx

/-- Original coefficient bounds suffice for every executed inverse prefix.
The displayed numeric envelopes are ordinary constructor inputs, not intermediate
word-fitting or inverse-value advice. -/
theorem build_correct (template : List Bool) (a : Array RationalWord) (d B J : ℕ)
    (hd : 0<d) (ha : Valid a) (ha0 : coefficient (decode a) 0=1)
    (hrep : ∀ i<J, Representation (coefficient (decode a) i) d B)
    (hden : d*d^J<2^template.length)
    (hnum : J*B*inverseBase J d B^J<2^template.length) :
    ∀ n≤J, decode (build template a n).words=(buildInverse (decode a) 1 n).coefficients ∧
      Valid (build template a n).words := by
  intro n hn
  induction n with
  | zero => exact ⟨by simp [build,decode,buildInverse],by intro i hi; simp [build] at hi⟩
  | succ n ih =>
    obtain ⟨he,hv⟩ := ih (by omega)
    by_cases hz : n=0
    · subst n
      simp only [build,extend,ite_true]
      refine ⟨?_,valid_push _ _ hv oneWord_valid⟩
      simp [decode,buildInverse,nextCoefficient]
    · have hp (p) (hm : p∈pairs a (build template a n).words n) :
          p.1.Valid ∧ p.2.Valid ∧ Representation p.1.value d B ∧
            Representation p.2.value (d^J) (inverseBase J d B^J) := by
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
        refine ⟨wordAt_valid a ha _,wordAt_valid _ hv _,?_,?_⟩
        · rw [← coefficient_decode]; exact hrep _ (by omega)
        · rw [← coefficient_decode,he]
          have hc : coefficient (buildInverse (decode a) 1 n).coefficients (n-1-i.val)=
              coefficient (inverse (decode a) J).coefficients (n-1-i.val) := by
            rw [inverse_coefficient _ _ _ (by omega)]
            simpa [ha0] using buildInverse_coefficient (decode a) n (n-1-i.val) (by omega)
          rw [hc]
          exact cached_inverse_common_representation _ d B J hd ha0 hrep _ (by omega)
      have hsize : (pairs a (build template a n).words n).length=n := pairs_length _ _ _
      have hc := dotBits_correct template (pairs a (build template a n).words n)
        d (d^J) B (inverseBase J d B^J) hd (pow_pos hd _) hden
        (by rw [hsize]; exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right B (show n≤J by omega))) hnum) hp
      have hr := SemiprimeLocalArrayFrontend.representation_neg hc.2.2
      have hf := fits_of_representation (Nat.mul_pos hd (pow_pos hd _)) hr
        (by rw [hsize]; exact lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right B (show n≤J by omega))) hnum) hden
      have hcneg := executeOperation_correct .neg _ zeroWord template hc.2.1 zeroWord_valid hf
      refine ⟨?_,?_⟩
      · simp only [build,extend,ite_eq_right hz,decode,Array.map_push]
        rw [hcneg.1]
        change (decode (build template a n).words).push (- (dotBits template
          (pairs a (build template a n).words n)).word.value)=_
        rw [hc.1,pairs_value,he]
        cases n with
        | zero => contradiction
        | succ k => simp only [buildInverse,nextCoefficient,neg_one_mul,Nat.add_sub_cancel,decode]
      · simpa only [build,extend,ite_eq_right hz] using valid_push _ _ hv hcneg.2.1

/-- Polynomial physical capacity for normalized inversion. -/
def inverseWidth (b J : ℕ) : ℕ := b*(J+1)+J+b+(J+b+3)*J+1

/-- Literal common envelopes fit the polynomial capacity. -/
theorem inverse_numeric_bounds (d B b J : ℕ) (hd : d≤2^b) (hB : B≤2^b) :
    d*d^J<2^(inverseWidth b J) ∧ J*B*inverseBase J d B^J<2^(inverseWidth b J) := by
  have hJ : J≤2^J := Nat.le_of_lt (Nat.lt_two_pow_self (n := J))
  have hpos : 1≤2^b := Nat.one_le_pow _ _ (by decide)
  have hpJ : 1≤2^J := Nat.one_le_pow _ _ (by decide)
  have hb : inverseBase J d B≤2^(J+b+3) := by
    have hm := Nat.mul_le_mul hJ (Nat.add_le_add_right (Nat.add_le_add hd hB) 1)
    unfold inverseBase
    have he : 2^(J+b+3)=8*2^J*2^b := by rw [pow_add,pow_add]; norm_num; ring
    rw [he]
    nlinarith
  have hn : J*B*inverseBase J d B^J≤2^(J+b+(J+b+3)*J) := by
    have hm := Nat.mul_le_mul (Nat.mul_le_mul hJ hB) (Nat.pow_le_pow_left hb J)
    simpa only [← pow_mul,← pow_add] using hm
  have hdd : d*d^J≤2^(b*(J+1)) := by
    have hm := Nat.mul_le_mul hd (Nat.pow_le_pow_left hd J)
    convert hm using 1; simp [← pow_mul,← pow_add,Nat.mul_add,Nat.add_comm]
  exact ⟨hdd.trans_lt (Nat.pow_lt_pow_right (by decide) (by unfold inverseWidth; omega)),
    hn.trans_lt (Nat.pow_lt_pow_right (by decide) (by unfold inverseWidth; omega))⟩

/-- Public original-input correctness, with no intermediate fit hypotheses. -/
theorem build_correct_dyadic (a : Array RationalWord) (d B b J : ℕ)
    (hd : 0<d) (ha : Valid a) (ha0 : coefficient (decode a) 0=1)
    (hrep : ∀ i<J, Representation (coefficient (decode a) i) d B)
    (hdb : d≤2^b) (hBb : B≤2^b) :
    decode (build (List.replicate (inverseWidth b J) false) a J).words=
        (buildInverse (decode a) 1 J).coefficients ∧
      Valid (build (List.replicate (inverseWidth b J) false) a J).words := by
  have hh := inverse_numeric_bounds d B b J hdb hBb
  exact build_correct _ a d B J hd ha ha0 hrep (by simpa using hh.1)
    (by simpa using hh.2) J le_rfl

/-- Any larger common physical template is legal for the same original inputs. -/
theorem build_correct_of_width (template : List Bool) (a : Array RationalWord) (d B b J : ℕ)
    (hd : 0<d) (ha : Valid a) (ha0 : coefficient (decode a) 0=1)
    (hrep : ∀ i<J, Representation (coefficient (decode a) i) d B)
    (hdb : d≤2^b) (hBb : B≤2^b) (hwidth : inverseWidth b J≤template.length) :
    decode (build template a J).words=(buildInverse (decode a) 1 J).coefficients ∧
      Valid (build template a J).words := by
  have hh := inverse_numeric_bounds d B b J hdb hBb
  have hm : 2^inverseWidth b J≤2^template.length := Nat.pow_le_pow_right (by decide) hwidth
  exact build_correct template a d B J hd ha ha0 hrep (hh.1.trans_le hm) (hh.2.trans_le hm) J le_rfl

end RiemannGaussian.SemiprimeNormalizedInverseBits
