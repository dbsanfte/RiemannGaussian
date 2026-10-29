/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeDotBits
import RiemannGaussian.SemiprimeArrayOps

/-! # Actual physical-word jet arithmetic
Every scalar output is produced by the Boolean rational instructions. Arrays
cache the scalar reports before collecting their outputs/clocks. The additional
cell ledger charges flat input addressing and physical output copying; it does
not assume constant-time arbitrary rational access. Input word acquisition and
the cost of executing the natural-number clock bookkeeping are separate.
-/
set_option autoImplicit false
set_option maxRecDepth 2000
namespace RiemannGaussian.SemiprimeJetBits
open scoped BigOperators
open SemiprimeRationalBits SemiprimeDotBits SemiprimeJetArray SemiprimeJetArrayHeight

/-- Literal positive one. -/
def oneWord : RationalWord := ⟨⟨false,[true]⟩,[true]⟩
/-- Literal negative one. -/
def negOneWord : RationalWord := ⟨⟨true,[true]⟩,[true]⟩

@[simp] theorem oneWord_value : oneWord.value=1 := by
  norm_num [oneWord,RationalWord.value,SemiprimeBitIndexClipping.SignedWord.value,
    SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat]
@[simp] theorem negOneWord_value : negOneWord.value= -1 := by
  norm_num [negOneWord,RationalWord.value,SemiprimeBitIndexClipping.SignedWord.value,
    SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat]
theorem oneWord_valid : oneWord.Valid := by
  change 0 < 1
  decide
theorem negOneWord_valid : negOneWord.Valid := by
  change 0 < 1
  decide
theorem oneWord_width {W : ℕ} (hW : 0<W) : Width oneWord W := by
  exact ⟨hW,hW⟩
theorem negOneWord_width {W : ℕ} (hW : 0<W) : Width negOneWord W := by
  exact ⟨hW,hW⟩

/-- Physical arrays with an actual execution/cell report. -/
structure JetReport where
  /-- The actual retained physical rational outputs. -/
  words : Array RationalWord
  /-- Summed Boolean instruction and array-cell work. -/
  clock : ℕ

/-- Zero-extended physical lookup. -/
def wordAt (a : Array RationalWord) (i : ℕ) : RationalWord := a[i]?.getD zeroWord
/-- Interpretation only, not part of the arithmetic data path. -/
def decode (a : Array RationalWord) : Array ℚ := a.map RationalWord.value
/-- Every actual stored word has a legal denominator. -/
def Valid (a : Array RationalWord) : Prop := ∀ i (hi : i<a.size), (a[i]).Valid
/-- Every actual stored word occupies at most W magnitude/denominator cells. -/
def Bounded (a : Array RationalWord) (W : ℕ) : Prop :=
  ∀ i (hi : i<a.size), Width (a[i]) W

@[simp] theorem decode_size (a : Array RationalWord) : (decode a).size=a.size := by
  simp [decode]
@[simp] theorem coefficient_decode (a : Array RationalWord) (i : ℕ) :
    coefficient (decode a) i=(wordAt a i).value := by
  by_cases h : i<a.size
  · simp [coefficient,decode,wordAt,h]
  · simp [coefficient,decode,wordAt,h,zeroWord_value]

theorem wordAt_valid (a : Array RationalWord) (h : Valid a) (i : ℕ) : (wordAt a i).Valid := by
  by_cases hi : i<a.size
  · simpa [wordAt,hi] using h i hi
  · simpa [wordAt,hi] using zeroWord_valid

theorem wordAt_width (a : Array RationalWord) {W : ℕ} (hW : 0<W)
    (h : Bounded a W) (i : ℕ) : Width (wordAt a i) W := by
  by_cases hi : i<a.size
  · simpa [wordAt,hi] using h i hi
  · simp only [wordAt,Array.getElem?_eq_none (Nat.le_of_not_gt hi),Option.getD_none,zeroWord,Width,
      List.length_nil,List.length_cons]
    omega

/-- Conservative cell cost of flat addressing and copying one retrieved word.
The template length is a runtime word, not a supplied semantic height bound. -/
def accessCost (template : List Bool) (a : Array RationalWord) : ℕ :=
  (a.size+1)*(2*template.length+3)

/-- Materialize each scalar report once, then collect its words and summed cost. -/
def collect (J : ℕ) (f : Fin J → RationalReport) : JetReport :=
  let frames := Array.ofFn f
  ⟨frames.map (fun x => x.word),
    (∑ i : Fin J, (frames[i.val]'(by simp [frames])).clock)+(2*J+1)⟩

@[simp] theorem collect_size (J : ℕ) (f : Fin J → RationalReport) :
    (collect J f).words.size=J := by simp [collect]
@[simp] theorem collect_word (J : ℕ) (f : Fin J → RationalReport) (i : ℕ) (hi : i<J) :
    wordAt (collect J f).words i=(f ⟨i,hi⟩).word := by
  simp [collect,wordAt,hi]
@[simp] theorem collect_clock (J : ℕ) (f : Fin J → RationalReport) :
    (collect J f).clock=(∑ i : Fin J, (f i).clock)+(2*J+1) := by simp [collect]

theorem collect_valid (J : ℕ) (f : Fin J → RationalReport)
    (h : ∀ i, (f i).word.Valid) : Valid (collect J f).words := by
  intro i hi
  simpa [collect] using h ⟨i,by simpa using hi⟩
theorem collect_bounded (J : ℕ) (f : Fin J → RationalReport) (W : ℕ)
    (h : ∀ i, Width (f i).word W) : Bounded (collect J f).words W := by
  intro i hi
  simpa [collect] using h ⟨i,by simpa using hi⟩

/-- Actual coefficientwise addition on physical rational words. -/
def addBits (template : List Bool) (a b : Array RationalWord) (J : ℕ) : JetReport :=
  collect J (fun i =>
    let run := executeOperation .add (wordAt a i.val) (wordAt b i.val) template
    ⟨run.word,run.clock+accessCost template a+accessCost template b⟩)

/-- Actual coefficientwise scaling on physical rational words. -/
def scaleBits (template : List Bool) (a : Array RationalWord) (c : RationalWord) (J : ℕ) : JetReport :=
  collect J (fun i =>
    let run := executeOperation .mul c (wordAt a i.val) template
    ⟨run.word,run.clock+accessCost template a+(2*template.length+3)⟩)

/-- The finite physical input to one convolution coefficient. -/
def convolutionPairs (a b : Array RationalWord) (i : ℕ) : List (RationalWord × RationalWord) :=
  List.ofFn (fun k : Fin (i+1) => (wordAt a k.val,wordAt b (i-k.val)))

/-- Actual truncated convolution; each coefficient executes the cached dot loop. -/
def multiplyBits (template : List Bool) (a b : Array RationalWord) (J : ℕ) : JetReport :=
  collect J (fun i =>
    let run := dotBits template (convolutionPairs a b i.val)
    ⟨run.word,run.clock+(i.val+1)*(accessCost template a+accessCost template b)⟩)

/-- Input common representations make every physical addition fit. -/
theorem addBits_correct (template : List Bool) (a b : Array RationalWord) (J d B C : ℕ)
    (ha : Valid a) (hb : Valid b) (hd : 0<d)
    (hden : d<2^template.length) (hnum : B+C<2^template.length)
    (hra : ∀ i<J, Representation (coefficient (decode a) i) d B)
    (hrb : ∀ i<J, Representation (coefficient (decode b) i) d C) :
    (∀ i<J, coefficient (decode (addBits template a b J).words) i=
      coefficient (SemiprimeArrayOps.addJet (decode a) (decode b) J).coefficients i) ∧
      Valid (addBits template a b J).words := by
  have hc (i : Fin J) := executeOperation_correct .add (wordAt a i.val) (wordAt b i.val) template
    (wordAt_valid a ha _) (wordAt_valid b hb _)
    (fits_of_representation hd (representation_add (by simpa using hra i.val i.isLt) (by simpa using hrb i.val i.isLt)) hnum hden)
  refine ⟨?_,collect_valid J _ (fun i => (hc i).2.1)⟩
  intro i hi
  rw [coefficient_decode,show wordAt (addBits template a b J).words i=
    (executeOperation .add (wordAt a i) (wordAt b i) template).word by simp [addBits,hi],(hc ⟨i,hi⟩).1]
  simpa [Operation.value,coefficient_decode] using (SemiprimeArrayOps.addJet_coefficient (decode a) (decode b) J i hi).symm

/-- Input common representations make every physical scalar multiplication fit. -/
theorem scaleBits_correct (template : List Bool) (a : Array RationalWord) (c : RationalWord)
    (J d e B C : ℕ) (ha : Valid a) (hc : c.Valid) (hd : 0<d) (he : 0<e)
    (hden : e*d<2^template.length) (hnum : C*B<2^template.length)
    (hra : ∀ i<J, Representation (coefficient (decode a) i) d B)
    (hrc : Representation c.value e C) :
    (∀ i<J, coefficient (decode (scaleBits template a c J).words) i=
      coefficient (SemiprimeArrayOps.scaleJet (decode a) c.value J).coefficients i) ∧
      Valid (scaleBits template a c J).words := by
  have hrun (i : Fin J) := executeOperation_correct .mul c (wordAt a i.val) template hc (wordAt_valid a ha _)
    (fits_of_representation (Nat.mul_pos he hd) (representation_mul hrc (by simpa using hra i.val i.isLt)) hnum hden)
  refine ⟨?_,collect_valid J _ (fun i => (hrun i).2.1)⟩
  intro i hi
  rw [coefficient_decode,show wordAt (scaleBits template a c J).words i=
    (executeOperation .mul c (wordAt a i) template).word by simp [scaleBits,hi],(hrun ⟨i,hi⟩).1]
  simpa [Operation.value,coefficient_decode] using (SemiprimeArrayOps.scaleJet_coefficient (decode a) c.value J i hi).symm

/-- The actual physical dot's value is the frozen convolution coefficient. -/
theorem convolutionPairs_value (a b : Array RationalWord) (i : ℕ) :
    dotValue (convolutionPairs a b i)=
      ∑ k ∈ Finset.range (i+1), coefficient (decode a) k*coefficient (decode b) (i-k) := by
  simp only [dotValue,convolutionPairs,List.map_ofFn,List.sum_ofFn,coefficient_decode]
  exact Fin.sum_univ_eq_sum_range (fun k : ℕ => (wordAt a k).value*(wordAt b (i-k)).value) (i+1)

/-- Truncated physical convolution agrees with the frozen array implementation.
Common representations bound every product and every partial dot sum. -/
theorem multiplyBits_correct (template : List Bool) (a b : Array RationalWord)
    (J d e B C : ℕ) (ha : Valid a) (hb : Valid b) (hd : 0<d) (he : 0<e)
    (hden : d*e<2^template.length) (hnum : J*B*C<2^template.length)
    (hra : ∀ i<J, Representation (coefficient (decode a) i) d B)
    (hrb : ∀ i<J, Representation (coefficient (decode b) i) e C) :
    (∀ i<J, coefficient (decode (multiplyBits template a b J).words) i=
      coefficient (multiply (decode a) (decode b) J).coefficients i) ∧
      Valid (multiplyBits template a b J).words := by
  have hrun (i : Fin J) := dotBits_correct template (convolutionPairs a b i.val) d e B C hd he hden
    (by simpa [convolutionPairs] using
      (Nat.mul_le_mul_right C (Nat.mul_le_mul_right B i.isLt)).trans_lt hnum)
    (by
      intro pair hp
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hp
      refine ⟨wordAt_valid a ha _,wordAt_valid b hb _,?_,?_⟩
      · simpa using hra k.val (by omega)
      · simpa using hrb (i.val-k.val) (by omega))
  refine ⟨?_,collect_valid J _ (fun i => (hrun i).2.1)⟩
  intro i hi
  rw [coefficient_decode,show wordAt (multiplyBits template a b J).words i=
    (dotBits template (convolutionPairs a b i)).word by simp [multiplyBits,hi],(hrun ⟨i,hi⟩).1,
    convolutionPairs_value,multiply_coefficient _ _ J i hi]

@[simp] theorem addBits_size (template : List Bool) (a b : Array RationalWord) (J : ℕ) :
    (addBits template a b J).words.size=J := by simp [addBits]
@[simp] theorem scaleBits_size (template : List Bool) (a : Array RationalWord) (c : RationalWord) (J : ℕ) :
    (scaleBits template a c J).words.size=J := by simp [scaleBits]
@[simp] theorem multiplyBits_size (template : List Bool) (a b : Array RationalWord) (J : ℕ) :
    (multiplyBits template a b J).words.size=J := by simp [multiplyBits]

theorem addBits_bounded (template : List Bool) (a b : Array RationalWord) (J : ℕ) :
    Bounded (addBits template a b J).words template.length := by
  apply collect_bounded
  intro i
  exact (fitRationalBits_width (rawOperation .add (wordAt a i.val) (wordAt b i.val)).word template).imp
    Nat.le_of_eq Nat.le_of_eq

theorem scaleBits_bounded (template : List Bool) (a : Array RationalWord) (c : RationalWord) (J : ℕ) :
    Bounded (scaleBits template a c J).words template.length := by
  apply collect_bounded
  intro i
  exact (fitRationalBits_width (rawOperation .mul c (wordAt a i.val)).word template).imp
    Nat.le_of_eq Nat.le_of_eq

theorem multiplyBits_bounded (template : List Bool) (ht : 0<template.length)
    (a b : Array RationalWord) (J : ℕ) :
    Bounded (multiplyBits template a b J).words template.length := by
  apply collect_bounded
  intro i
  exact dotBits_width template ht _

/-- Summing cached frame clocks retains the actual scalar execution costs. -/
theorem collect_cost (J C : ℕ) (f : Fin J → RationalReport) (h : ∀ i, (f i).clock≤C) :
    (collect J f).clock≤J*C+(2*J+1) := by
  rw [collect_clock]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using
    Nat.add_le_add_right hs (2*J+1)

/-- Actual addition instruction clocks plus explicit flat-access/copy charges. -/
theorem addBits_cost (template : List Bool) (ht : 0<template.length)
    (a b : Array RationalWord) (J : ℕ)
    (ha : Bounded a template.length) (hb : Bounded b template.length) :
    (addBits template a b J).clock≤
      J*(20000*(template.length+1)^3+accessCost template a+accessCost template b)+(2*J+1) := by
  apply collect_cost
  intro i
  have h := executeOperation_cost .add (wordAt a i.val) (wordAt b i.val) template
    (wordAt_width a ht ha _) (wordAt_width b ht hb _) (by rfl)
  exact Nat.add_le_add_right (Nat.add_le_add_right h _) _

/-- Actual multiplication instructions for all scaling coefficients. -/
theorem scaleBits_cost (template : List Bool) (ht : 0<template.length)
    (a : Array RationalWord) (c : RationalWord) (J : ℕ)
    (ha : Bounded a template.length) (hc : Width c template.length) :
    (scaleBits template a c J).clock≤
      J*(20000*(template.length+1)^3+accessCost template a+(2*template.length+3))+(2*J+1) := by
  apply collect_cost
  intro i
  have h := executeOperation_cost .mul c (wordAt a i.val) template hc (wordAt_width a ht ha _) (by rfl)
  exact Nat.add_le_add_right (Nat.add_le_add_right h _) _

/-- All physical convolution dots and all their actual input read addresses are
charged. This intentionally uses J² instead of an optimized triangular sum. -/
theorem multiplyBits_cost (template : List Bool) (ht : 0<template.length)
    (a b : Array RationalWord) (J : ℕ)
    (ha : Bounded a template.length) (hb : Bounded b template.length) :
    (multiplyBits template a b J).clock≤
      J*(J*(40000*(template.length+1)^3+4)+4+
        J*(accessCost template a+accessCost template b))+(2*J+1) := by
  apply collect_cost
  intro i
  have hc := dotBits_cost template ht (convolutionPairs a b i.val) (by
    intro pair hp
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hp
    exact ⟨wordAt_width a ht ha _,wordAt_width b ht hb _⟩)
  have hpLength : (convolutionPairs a b i.val).length=i.val+1 := by simp [convolutionPairs]
  rw [hpLength] at hc
  have hlen : i.val+1≤J := i.isLt
  have h₁ := Nat.mul_le_mul_right (40000*(template.length+1)^3+4) hlen
  have h₂ := Nat.mul_le_mul_right (accessCost template a+accessCost template b) hlen
  change (dotBits template (convolutionPairs a b i.val)).clock+
    (i.val+1)*(accessCost template a+accessCost template b)≤_
  omega

end RiemannGaussian.SemiprimeJetBits
