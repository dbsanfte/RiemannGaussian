/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeJetBits
import RiemannGaussian.SemiprimeSourceCodeArrays

/-! # Physical-word polynomial expression compiler
Constants are physical input words, not requested output coefficients. Each
internal node executes the proved jet instructions and retains both children
once. Structural integer budgets derive all intermediate fitting conditions.
Acquiring the input constant words is separate from this compiler.
-/
set_option autoImplicit false
set_option maxRecDepth 2000
namespace RiemannGaussian.SemiprimePolynomialCodeBits
open scoped BigOperators
open Polynomial SemiprimeRationalBits SemiprimeDotBits SemiprimeJetBits SemiprimeJetArrayHeight
open SemiprimeJetArray
open OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation

/-- Physical copies of a truncated constant, including explicit zero cells. -/
def constantBits (c : RationalWord) (J : ℕ) : JetReport :=
  collect J (fun i =>
    let w := if i.val=0 then c else zeroWord
    ⟨w,w.numerator.magnitude.length+w.denominator.length+4⟩)

/-- The semantic expression is proof-only; no rational interpretation is used
by the physical compiler. -/
def valueCode : PolynomialCode RationalWord → PolynomialCode ℚ
  | .constant w => .constant w.value
  | .indeterminate => .indeterminate
  | .add a b => .add (valueCode a) (valueCode b)
  | .mul a b => .mul (valueCode a) (valueCode b)

/-- Literal compiler on word-valued expressions. No desired coefficients or
polynomial objects are runtime arguments. -/
def compile (template : List Bool) (J : ℕ) : PolynomialCode RationalWord → JetReport
  | .constant w => constantBits w J
  | .indeterminate =>
      collect J (fun i => ⟨if i.val=1 then oneWord else zeroWord,6⟩)
  | .add a b =>
      let left := compile template J a
      let right := compile template J b
      let out := addBits template left.words right.words J
      ⟨out.words,left.clock+right.clock+out.clock+3⟩
  | .mul a b =>
      let left := compile template J a
      let right := compile template J b
      let out := multiplyBits template left.words right.words J
      ⟨out.words,left.clock+right.clock+out.clock+3⟩

/-- Structural common denominator/numerator bounds. These are computed from
input word magnitudes and the expression tree, never from output coefficients. -/
def budget (J : ℕ) : PolynomialCode RationalWord → ℕ × ℕ
  | .constant w => (SemiprimeBitArithmetic.bitValue w.denominator,
      SemiprimeBitArithmetic.bitValue w.numerator.magnitude)
  | .indeterminate => (1,1)
  | .add a b =>
      let x := budget J a
      let y := budget J b
      (x.1*y.1,x.2*y.1+y.2*x.1)
  | .mul a b =>
      let x := budget J a
      let y := budget J b
      (x.1*y.1,J*x.2*y.2)

/-- The explicit template accommodates every structural budget and original
physical constant, including supplied leading zero padding. -/
def Safe (template : List Bool) (J : ℕ) : PolynomialCode RationalWord → Prop
  | .constant w => w.Valid ∧ Width w template.length ∧
      (budget J (.constant w)).1<2^template.length ∧ (budget J (.constant w)).2<2^template.length
  | .indeterminate => 0<template.length
  | .add a b => Safe template J a ∧ Safe template J b ∧
      (budget J (.add a b)).1<2^template.length ∧ (budget J (.add a b)).2<2^template.length
  | .mul a b => Safe template J a ∧ Safe template J b ∧
      (budget J (.mul a b)).1<2^template.length ∧ (budget J (.mul a b)).2<2^template.length

/-- A larger common denominator can be introduced by a known positive integer. -/
theorem representation_extend {q : ℚ} {d B : ℕ} (h : Representation q d B)
    (e : ℕ) (he : 0<e) : Representation q (d*e) (B*e) := by
  obtain ⟨z,hz,hB⟩ := h
  refine ⟨z*(e : ℤ),?_,?_⟩
  · rw [hz]
    have hEq : (e : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
    push_cast
    field_simp
  · simpa only [Int.natAbs_mul,Int.natAbs_natCast] using Nat.mul_le_mul_right e hB

theorem budget_pos (template : List Bool) (J : ℕ) (p : PolynomialCode RationalWord)
    (h : Safe template J p) : 0<(budget J p).1 := by
  induction p with
  | constant w => exact h.1
  | indeterminate => exact Nat.zero_lt_one
  | add a b ha hb => exact Nat.mul_pos (ha h.1) (hb h.2.1)
  | mul a b ha hb => exact Nat.mul_pos (ha h.1) (hb h.2.1)

@[simp] theorem compile_size (template : List Bool) (J : ℕ) (p : PolynomialCode RationalWord) :
    (compile template J p).words.size=J := by
  cases p <;> simp [compile,constantBits]

/-- Physical input words already have their literal common representation. -/
theorem word_representation (w : RationalWord) :
    Representation w.value (SemiprimeBitArithmetic.bitValue w.denominator)
      (SemiprimeBitArithmetic.bitValue w.numerator.magnitude) := by
  refine ⟨w.numerator.value,rfl,?_⟩
  exact (SemiprimeBitIndexGeometry.signedWord_natAbs w.numerator).le

/-- All physical outputs, all intermediate common budgets, and the actual
source-expression coefficients are proved together by structural induction. -/
theorem compile_correct (template : List Bool) (J : ℕ) (p : PolynomialCode RationalWord)
    (ht : 0<template.length) (h : Safe template J p) :
    Valid (compile template J p).words ∧ Bounded (compile template J p).words template.length ∧
    (∀ i<J, Representation (coefficient (decode (compile template J p).words) i)
      (budget J p).1 (budget J p).2) ∧
    (∀ i<J, coefficient (decode (compile template J p).words) i=(valueCode p).denote.coeff i) := by
  induction p with
  | constant w =>
    refine ⟨collect_valid J _ (fun i => ?_),collect_bounded J _ _ (fun i => ?_),?_,?_⟩
    · split_ifs
      · exact h.1
      · exact zeroWord_valid
    · split_ifs
      · exact h.2.1
      · exact ⟨by change 0≤template.length;omega,by change 1≤template.length;omega⟩
    · intro i hi
      simp only [compile,constantBits,coefficient_decode,collect_word J _ i hi]
      split_ifs
      · exact word_representation w
      · exact ⟨0,by simp [zeroWord_value],by simp⟩
    · intro i hi
      simp only [compile,constantBits,coefficient_decode,collect_word J _ i hi,valueCode,PolynomialCode.denote,coeff_C]
      split_ifs <;> simp [zeroWord_value]
  | indeterminate =>
    refine ⟨collect_valid J _ (fun i => ?_),collect_bounded J _ _ (fun i => ?_),?_,?_⟩
    · split_ifs
      · exact oneWord_valid
      · exact zeroWord_valid
    · split_ifs
      · exact oneWord_width ht
      · exact ⟨by change 0≤template.length;omega,by change 1≤template.length;omega⟩
    · intro i hi
      simp only [compile,coefficient_decode,collect_word J _ i hi]
      split_ifs
      · exact ⟨1,by simp [budget],by simp [budget]⟩
      · exact ⟨0,by simp [zeroWord_value],by simp⟩
    · intro i hi
      simp only [compile,coefficient_decode,collect_word J _ i hi,valueCode,PolynomialCode.denote,coeff_X]
      by_cases hi1 : i=1 <;> simp [hi1,eq_comm,zeroWord_value]
  | add a b ha hb =>
    obtain ⟨hva,hwa,hra,hca⟩ := ha h.1
    obtain ⟨hvb,hwb,hrb,hcb⟩ := hb h.2.1
    have hd := budget_pos template J a h.1
    have he := budget_pos template J b h.2.1
    have hra' (i) (hi : i<J) := representation_extend (hra i hi) (budget J b).1 he
    have hrb' (i) (hi : i<J) : Representation (coefficient (decode (compile template J b).words) i)
        ((budget J a).1*(budget J b).1) ((budget J b).2*(budget J a).1) := by
      simpa only [Nat.mul_comm] using representation_extend (hrb i hi) (budget J a).1 hd
    have hout := addBits_correct template (compile template J a).words (compile template J b).words
      J ((budget J a).1*(budget J b).1) ((budget J a).2*(budget J b).1)
      ((budget J b).2*(budget J a).1) hva hvb (Nat.mul_pos hd he) h.2.2.1 h.2.2.2 hra' hrb'
    refine ⟨hout.2,addBits_bounded _ _ _ _,?_,?_⟩
    · intro i hi
      rw [show coefficient (decode (compile template J (.add a b)).words) i=
        coefficient (SemiprimeArrayOps.addJet (decode (compile template J a).words)
          (decode (compile template J b).words) J).coefficients i from hout.1 i hi]
      exact SemiprimeArrayOps.addJet_representation _ _ J _ _ _ hra' hrb' i hi
    · intro i hi
      rw [show coefficient (decode (compile template J (.add a b)).words) i=
        coefficient (SemiprimeArrayOps.addJet (decode (compile template J a).words)
          (decode (compile template J b).words) J).coefficients i from hout.1 i hi,
        SemiprimeArrayOps.addJet_coefficient _ _ J i hi,hca i hi,hcb i hi]
      rfl
  | mul a b ha hb =>
    obtain ⟨hva,hwa,hra,hca⟩ := ha h.1
    obtain ⟨hvb,hwb,hrb,hcb⟩ := hb h.2.1
    have hout := multiplyBits_correct template (compile template J a).words (compile template J b).words
      J (budget J a).1 (budget J b).1 (budget J a).2 (budget J b).2 hva hvb
      (budget_pos template J a h.1) (budget_pos template J b h.2.1) h.2.2.1 h.2.2.2 hra hrb
    refine ⟨hout.2,multiplyBits_bounded _ ht _ _ _,?_,?_⟩
    · intro i hi
      rw [show coefficient (decode (compile template J (.mul a b)).words) i=
        coefficient (multiply (decode (compile template J a).words)
          (decode (compile template J b).words) J).coefficients i from hout.1 i hi]
      exact multiply_representation _ _ _ _ _ _ J hra hrb i hi
    · intro i hi
      rw [show coefficient (decode (compile template J (.mul a b)).words) i=
        coefficient (multiply (decode (compile template J a).words)
          (decode (compile template J b).words) J).coefficients i from hout.1 i hi,
        multiply_coefficient _ _ J i hi]
      simp only [valueCode,PolynomialCode.denote,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hca k (by have := Finset.mem_range.mp hk;omega),hcb (i-k) (by omega)]

/-- Literal syntax-tree size, not a supplied complexity certificate. -/
def nodes : PolynomialCode RationalWord → ℕ
  | .constant _ => 1
  | .indeterminate => 1
  | .add a b => nodes a+nodes b+1
  | .mul a b => nodes a+nodes b+1

/-- A common per-node envelope sums the actual leaf, addition and convolution
loop bounds. No scalar callback cost is supplied to the compiler. -/
def nodeCost (J W : ℕ) : ℕ :=
  (J*(2*W+4)+(2*J+1))+
  (J*(20000*(W+1)^3+(J+1)*(2*W+3)+(J+1)*(2*W+3))+(2*J+1))+
  (J*(J*(40000*(W+1)^3+4)+4+J*((J+1)*(2*W+3)+(J+1)*(2*W+3)))+(2*J+1))+3

/-- Exact compiler refinement to the existing rational source-code compiler. -/
theorem compile_refines (template : List Bool) (J : ℕ) (p : PolynomialCode RationalWord)
    (ht : 0<template.length) (h : Safe template J p) (i : ℕ) (hi : i<J) :
    coefficient (decode (compile template J p).words) i=
      coefficient (SemiprimeSourceCodeArrays.compile J (valueCode p)).coefficients i := by
  rw [(compile_correct template J p ht h).2.2.2 i hi,
    SemiprimeSourceCodeArrays.compile_coefficient J (valueCode p) i hi]

/-- The actual cached physical compiler has polynomial-in-width work per
literal syntax node. The clock includes its child computations exactly once. -/
theorem compile_cost (template : List Bool) (J : ℕ) (p : PolynomialCode RationalWord)
    (ht : 0<template.length) (h : Safe template J p) :
    (compile template J p).clock≤nodes p*nodeCost J template.length := by
  induction p with
  | constant w =>
    have hc : (constantBits w J).clock≤J*(2*template.length+4)+(2*J+1) := by
      apply collect_cost
      intro i
      change (if i.val=0 then w else zeroWord).numerator.magnitude.length+
        (if i.val=0 then w else zeroWord).denominator.length+4≤_
      split_ifs
      · have hw := h.2.1
        change w.numerator.magnitude.length≤template.length ∧ w.denominator.length≤template.length at hw
        omega
      · simp only [zeroWord,List.length_nil,List.length_cons]
        omega
    change (constantBits w J).clock≤1*nodeCost J template.length
    dsimp only [nodeCost]
    omega
  | indeterminate =>
    have hc : (compile template J (.indeterminate : PolynomialCode RationalWord)).clock≤
        J*(2*template.length+4)+(2*J+1) := by
      apply collect_cost
      intro i
      change 6≤2*template.length+4
      omega
    change (compile template J (.indeterminate : PolynomialCode RationalWord)).clock≤1*nodeCost J template.length
    dsimp only [nodeCost]
    omega
  | add a b ha hb =>
    have ha' := ha h.1
    have hb' := hb h.2.1
    have hwa := (compile_correct template J a ht h.1).2.1
    have hwb := (compile_correct template J b ht h.2.1).2.1
    have hc := addBits_cost template ht (compile template J a).words (compile template J b).words J hwa hwb
    simp only [accessCost,compile_size] at hc
    have ho : (addBits template (compile template J a).words (compile template J b).words J).clock+3≤
        nodeCost J template.length := by
      dsimp only [nodeCost]
      omega
    change (compile template J a).clock+(compile template J b).clock+
      (addBits template (compile template J a).words (compile template J b).words J).clock+3≤
        (nodes a+nodes b+1)*nodeCost J template.length
    nlinarith
  | mul a b ha hb =>
    have ha' := ha h.1
    have hb' := hb h.2.1
    have hwa := (compile_correct template J a ht h.1).2.1
    have hwb := (compile_correct template J b ht h.2.1).2.1
    have hc := multiplyBits_cost template ht (compile template J a).words (compile template J b).words J hwa hwb
    simp only [accessCost,compile_size] at hc
    have ho : (multiplyBits template (compile template J a).words (compile template J b).words J).clock+3≤
        nodeCost J template.length := by
      dsimp only [nodeCost]
      omega
    change (compile template J a).clock+(compile template J b).clock+
      (multiplyBits template (compile template J a).words (compile template J b).words J).clock+3≤
        (nodes a+nodes b+1)*nodeCost J template.length
    nlinarith

/-- The only input-validity requirement: literal constants have nonzero physical denominators. -/
def ConstantsValid : PolynomialCode RationalWord → Prop
  | .constant w => w.Valid
  | .indeterminate => True
  | .add a b => ConstantsValid a ∧ ConstantsValid b
  | .mul a b => ConstantsValid a ∧ ConstantsValid b

/-- Binary sizes of the structural integer budget suffice at one node. -/
def rootWidth (J : ℕ) (p : PolynomialCode RationalWord) : ℕ :=
  1+(budget J p).1.size+(budget J p).2.size

/-- An explicit sufficient physical width, computed solely from the syntax and
input words. Computing this schedule/template is separate from compile.clock. -/
def requiredWidth (J : ℕ) : PolynomialCode RationalWord → ℕ
  | .constant w => max (rootWidth J (.constant w))
      (max w.numerator.magnitude.length w.denominator.length)
  | .indeterminate => 1
  | .add a b => max (requiredWidth J a) (max (requiredWidth J b) (rootWidth J (.add a b)))
  | .mul a b => max (requiredWidth J a) (max (requiredWidth J b) (rootWidth J (.mul a b)))

theorem requiredWidth_pos (J : ℕ) (p : PolynomialCode RationalWord) : 0<requiredWidth J p := by
  induction p with
  | constant w =>
    have hroot : 0<rootWidth J (.constant w) := by simp [rootWidth]
    exact hroot.trans_le (le_max_left _ _)
  | indeterminate => exact Nat.zero_lt_one
  | add a b ha hb => exact ha.trans_le (le_max_left _ _)
  | mul a b ha hb => exact ha.trans_le (le_max_left _ _)

/-- This is derived fitting for every node, not a supplied output-height oracle. -/
theorem safe_of_requiredWidth (template : List Bool) (J : ℕ) (p : PolynomialCode RationalWord)
    (hv : ConstantsValid p) (hw : requiredWidth J p≤template.length) : Safe template J p := by
  induction p with
  | constant w =>
    change max (rootWidth J (.constant w))
      (max w.numerator.magnitude.length w.denominator.length)≤_ at hw
    have hroot := (max_le_iff.mp hw).1
    have hphys := max_le_iff.mp (max_le_iff.mp hw).2
    refine ⟨hv,hphys,?_,?_⟩
    · apply Nat.size_le.mp
      dsimp only [rootWidth] at hroot
      omega
    · apply Nat.size_le.mp
      dsimp only [rootWidth] at hroot
      omega
  | indeterminate => exact (requiredWidth_pos J (.indeterminate : PolynomialCode RationalWord)).trans_le hw
  | add a b ha hb =>
    obtain ⟨haW,hrest⟩ := max_le_iff.mp hw
    obtain ⟨hbW,hroot⟩ := max_le_iff.mp hrest
    refine ⟨ha hv.1 haW,hb hv.2 hbW,?_,?_⟩
    · apply Nat.size_le.mp
      dsimp only [rootWidth] at hroot
      omega
    · apply Nat.size_le.mp
      dsimp only [rootWidth] at hroot
      omega
  | mul a b ha hb =>
    obtain ⟨haW,hrest⟩ := max_le_iff.mp hw
    obtain ⟨hbW,hroot⟩ := max_le_iff.mp hrest
    refine ⟨ha hv.1 haW,hb hv.2 hbW,?_,?_⟩
    · apply Nat.size_le.mp
      dsimp only [rootWidth] at hroot
      omega
    · apply Nat.size_le.mp
      dsimp only [rootWidth] at hroot
      omega

/-- A completely explicit width schedule initializes the physical compiler.
Only the validity of original input words is required. -/
theorem compile_initialized (J : ℕ) (p : PolynomialCode RationalWord) (hv : ConstantsValid p) :
    Valid (compile (List.replicate (requiredWidth J p) false) J p).words ∧
    (∀ i<J, coefficient (decode (compile (List.replicate (requiredWidth J p) false) J p).words) i=
      coefficient (SemiprimeSourceCodeArrays.compile J (valueCode p)).coefficients i) := by
  have ht : 0<(List.replicate (requiredWidth J p) false).length := by
    simpa only [List.length_replicate] using requiredWidth_pos J p
  have hs := safe_of_requiredWidth (List.replicate (requiredWidth J p) false) J p hv (by simp)
  exact ⟨(compile_correct _ J p ht hs).1,fun i hi => compile_refines _ J p ht hs i hi⟩

end RiemannGaussian.SemiprimePolynomialCodeBits
