/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitFermatTransform

/-!
# Actual normalized inverse transform and exact coefficient recovery

Physical template pairing constructs the normalization-depth word.
The inverse reuses the actual forward transform, reflects its actual
frequency list and executes one Boolean halving pass per computed level.
Fourier orthogonality and coefficient evaluation remain proof-side only.
Recursive packed multiplication, parameter/carry production, varying-seed
acquisition and complete public bit-time/memory remain separate obligations.
-/

namespace RiemannGaussian.SemiprimeBitFermatInterpolation

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitFermatArithmetic
open SemiprimeBitFermatTransform
open scoped BigOperators

/-- Actual half-template cells, a computed even-length gate and all
constructor/reference/new-bit primitives used by the pairing pass. -/
structure TemplateHalvingReport where
  /-- One false output cell per actual source pair. -/
  half : List Bool
  /-- True exactly when there is no unmatched last source cell. -/
  even : Bool
  /-- Every actual pair visit and terminal shape test. -/
  clock : ℕ

/-- Halves a physical template by inspecting actual pairs of cells.
Neither native length nor division controls the executable. -/
def halveTemplatePairsBits : List Bool→TemplateHalvingReport
  | [] => ⟨[],true,2⟩
  | [_] => ⟨[],false,4⟩
  | _::_::tail =>
    let child := halveTemplatePairsBits tail
    ⟨false::child.half,child.even,child.clock+10⟩

/-- Pairing has the exact physical half length and actual parity gate,
with every traversed cell and new false cell included in its clock. -/
theorem halveTemplatePairsBits_counts (template : List Bool) :
    (halveTemplatePairsBits template).half.length=template.length/2 ∧
    ((halveTemplatePairsBits template).even=true ↔ template.length%2=0) ∧
    (halveTemplatePairsBits template).clock≤5*template.length+4 := by
  induction template using List.twoStepInduction with
  | nil => norm_num [halveTemplatePairsBits]
  | singleton bit => norm_num [halveTemplatePairsBits]
  | cons_cons first second tail ih _ =>
    have hl := ih.1
    have he := ih.2.1
    have hc := ih.2.2
    rw [halveTemplatePairsBits]
    dsimp only
    simp only [List.length_cons]
    refine ⟨by omega,?_,by omega⟩
    constructor
    · intro hg
      have hp := he.mp hg
      omega
    · intro hp
      apply he.mpr
      omega

/-- Actual physical normalization levels, the computed dyadic-shape
gate and the entire template-pairing recursion clock. -/
structure FermatDepthReport where
  /-- One false cell per actual nontrivial halving level. -/
  levels : List Bool
  /-- Conjunction of actual no-unmatched-cell gates and singleton stop. -/
  accepted : Bool
  /-- Every executed pairing, level cell, gate and recursive primitive. -/
  clock : ℕ

/-- Derives depth from actual template constructors. Empty and odd
intermediate templates retain false gates; singleton is the real stop.
The physical length below is erased termination evidence only. -/
def fermatDepthBits (template : List Bool) : FermatDepthReport :=
  match template with
  | [] => ⟨[],false,2⟩
  | [_] => ⟨[],true,3⟩
  | first::second::tail =>
    let paired := halveTemplatePairsBits (first::second::tail)
    let child := fermatDepthBits paired.half
    ⟨false::child.levels,Bool.and paired.even child.accepted,
      paired.clock+child.clock+5⟩
termination_by template.length
decreasing_by
  have hc := halveTemplatePairsBits_counts (first::second::tail)
  simp only [List.length_cons] at hc ⊢
  omega

/-- Every dyadic physical template produces its ACTUAL logarithmic
level word, passes the actual gates and costs only linear template work.
The natural depth is theorem evidence, never executable advice. -/
theorem fermatDepthBits_exact (d : ℕ) (template : List Bool)
    (hK : template.length=2^d) :
    (fermatDepthBits template).levels.length=d ∧
    (fermatDepthBits template).accepted=true ∧
    (fermatDepthBits template).clock≤20*template.length+20 := by
  induction d generalizing template with
  | zero =>
    cases template with
    | nil => simp only [List.length_nil,pow_zero] at hK; omega
    | cons bit tail =>
      have ht : tail=[] := List.length_eq_zero_iff.mp (by
        simp only [List.length_cons,pow_zero] at hK; omega)
      subst tail
      simp only [fermatDepthBits,List.length_nil,List.length_cons]
      exact ⟨trivial,trivial,by omega⟩
  | succ d ih =>
    have hp : 0<2^d := by positivity
    cases template with
    | nil => simp only [List.length_nil,pow_succ] at hK; omega
    | cons first tail =>
      cases tail with
      | nil => simp only [List.length_nil,List.length_cons,pow_succ] at hK; omega
      | cons second tail =>
        have hc := halveTemplatePairsBits_counts (first::second::tail)
        have hhalf : (halveTemplatePairsBits (first::second::tail)).half.length=2^d := by
          rw [hK,pow_succ] at hc; omega
        have heven : (halveTemplatePairsBits (first::second::tail)).even=true := by
          apply hc.2.1.mpr
          rw [hK,pow_succ]
          omega
        have ht := ih (halveTemplatePairsBits (first::second::tail)).half hhalf
        rw [fermatDepthBits]
        dsimp only
        refine ⟨by rw [List.length_cons,ht.1],?_,?_⟩
        · rw [heven,ht.2.1]; rfl
        · have hsource : (first::second::tail).length=2*2^d := by rw [hK,pow_succ]; omega
          nlinarith only [hc.2.2,ht.2.2,hhalf,hsource,hp]

/-- Actual reversed word references and their complete traversal clock. -/
structure WordReverseReport where
  /-- Actual new reverse-order list cells. -/
  words : List (List Bool)
  /-- Every visited source/output reference and list test. -/
  clock : ℕ

/-- Tail-recursive reference reversal, using only real list cells. -/
def reverseWordRefsBits : List (List Bool)→List (List Bool)→WordReverseReport
  | [],acc => ⟨acc,2⟩
  | word::tail,acc =>
    let child := reverseWordRefsBits tail (word::acc)
    ⟨child.words,child.clock+5⟩

/-- Reversal retains every actual original reference and pays every
source visit; the mathematical reverse is only its specification. -/
theorem reverseWordRefsBits_exact (words acc : List (List Bool)) :
    (reverseWordRefsBits words acc).words=words.reverse++acc ∧
    (reverseWordRefsBits words acc).clock=5*words.length+2 := by
  induction words generalizing acc with
  | nil => simp only [reverseWordRefsBits,List.reverse_nil,List.nil_append,List.length_nil,
      Nat.mul_zero,Nat.zero_add,and_self]
  | cons word tail ih =>
    have ht := ih (word::acc)
    simp only [reverseWordRefsBits,List.reverse_cons,List.append_assoc,List.singleton_append,
      List.length_cons] at ht ⊢
    exact ⟨ht.1,by omega⟩

/-- Reflects the Fourier frequencies by retaining the actual zero
slot and reversing its actual tail. No index computes this ordering. -/
def reflectFFTWordsBits (words : List (List Bool)) : WordReverseReport :=
  match words with
  | [] => ⟨[],2⟩
  | zero::tail =>
    let reversed := reverseWordRefsBits tail []
    ⟨zero::reversed.words,reversed.clock+5⟩

/-- Actual reflection has its precise zero-plus-reversed-tail order,
retains the original count/membership and has a linear full clock. -/
theorem reflectFFTWordsBits_exact (words : List (List Bool)) :
    (reflectFFTWordsBits words).words=
      (match words with | [] => [] | zero::tail => zero::tail.reverse) ∧
    (reflectFFTWordsBits words).words.length=words.length ∧
    (∀ word∈(reflectFFTWordsBits words).words,word∈words) ∧
    (reflectFFTWordsBits words).clock≤5*words.length+7 := by
  cases words with
  | nil =>
    refine ⟨rfl,rfl,?_,?_⟩
    · simp only [reflectFFTWordsBits,List.not_mem_nil,false_implies,implies_true]
    · change 2≤7
      omega
  | cons zero tail =>
    have hr := reverseWordRefsBits_exact tail []
    simp only [reflectFFTWordsBits]
    rw [hr.1,List.append_nil]
    refine ⟨rfl,by simp only [List.length_cons,List.length_reverse],?_,?_⟩
    · intro word hw
      simpa only [List.mem_cons,List.mem_reverse] using hw
    · simp only [List.length_cons]
      omega

/-- Literal zero frequency is preserved by actual reflection. -/
theorem reflectFFTWordsBits_zero (M : ℕ) (words : List (List Bool)) :
    wordCoefficient M (reflectFFTWordsBits words).words 0=wordCoefficient M words 0 := by
  cases words with
  | nil => rfl
  | cons zero tail => rw [reflectFFTWordsBits]; dsimp only; rw [wordCoefficient_cons_zero,wordCoefficient_cons_zero]

/-- Every positive reflected position is the original frequency n-j.
The natural subtraction is proof-side, never an executable index. -/
theorem reflectFFTWordsBits_positive (M : ℕ) (words : List (List Bool))
    {j : ℕ} (hj : 0<j ∧ j<words.length) :
    wordCoefficient M (reflectFFTWordsBits words).words j=wordCoefficient M words (words.length-j) := by
  cases words with
  | nil => simp only [List.length_nil] at hj; omega
  | cons zero tail =>
    have hr := (reflectFFTWordsBits_exact (zero::tail)).1
    rw [hr]
    have hj1 : j=(j-1)+1 := by omega
    have htail : j-1<tail.length := by simp only [List.length_cons] at hj; omega
    have hindex : (zero::tail).length-j=(tail.length-1-(j-1))+1 := by
      simp only [List.length_cons] at hj ⊢
      omega
    rw [hj1,wordCoefficient_cons_succ]
    unfold wordCoefficient
    rw [List.getElem?_reverse htail]
    have he : (zero::tail).length-((j-1)+1)=(tail.length-1-(j-1))+1 := by rw [←hj1]; exact hindex
    rw [he,List.getElem?_cons_succ]

/-- Actual normalized word list and its complete primitive clock. -/
structure HalvedWordsReport where
  /-- Actual output words, preserving all source slots in order. -/
  words : List (List Bool)
  /-- Every halving, output reference and recursive primitive. -/
  clock : ℕ

/-- Executes the proved Boolean Fermat half on each actual source
word. No coefficient value or modular inverse is advice. -/
def halveWordRunBits (template : List Bool) : List (List Bool)→HalvedWordsReport
  | [] => ⟨[],2⟩
  | word::tail =>
    let half := fermatHalfBits template word
    let child := halveWordRunBits template tail
    ⟨half.output.bits::child.words,half.clock+child.clock+6⟩

/-- Repeats actual whole-word halving once per physical level cell.
The input level word will be computed by template pairing. -/
def normalizeFFTWordsBits (template : List Bool) : List Bool→List (List Bool)→HalvedWordsReport
  | [],words => ⟨words,1⟩
  | _::levels,words =>
    let halves := halveWordRunBits template words
    let child := normalizeFFTWordsBits template levels halves.words
    ⟨child.words,halves.clock+child.clock+4⟩

/-- Each executed halving pass preserves every source slot in order,
returns canonical fixed-width words and pays every Boolean half and
reference operation, including prospective carry computations. -/
theorem halveWordRunBits_words {template : List Bool} (hK : 0<template.length)
    (words : List (List Bool))
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1)
    (hwidth : ∀ word∈words,word.length≤template.length+1) :
    (halveWordRunBits template words).words.length=words.length ∧
    (∀ word∈(halveWordRunBits template words).words,
      word.length=template.length+1 ∧ bitValue word<2^template.length+1) ∧
    (halveWordRunBits template words).clock≤(words.length+1)*(18*template.length+44) := by
  revert hcanon hwidth
  induction words with
  | nil =>
    intro hcanon hwidth
    refine ⟨rfl,?_,?_⟩
    · simp only [halveWordRunBits,List.not_mem_nil,false_implies,implies_true]
    · change 2≤(0+1)*(18*template.length+44)
      omega
  | cons word tail ih =>
    intro hcanon hwidth
    have ht := ih
      (fun w hw => hcanon w (by simp only [List.mem_cons]; exact Or.inr hw))
      (fun w hw => hwidth w (by simp only [List.mem_cons]; exact Or.inr hw))
    have hc := (fermatHalfBits_exact hK (hcanon word (by simp))).1
    have hh := fermatHalfBits_width_cost hK (hwidth word (by simp))
    rw [halveWordRunBits]
    dsimp only
    refine ⟨by simp only [List.length_cons]; omega,?_,?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl|hw
      · exact ⟨hh.1,hc⟩
      · exact ht.2.1 w hw
    · simp only [List.length_cons]
      nlinarith only [ht.2.2,hh.2]

/-- Every actual half word solves its original multiplication-by-two
equation at its unchanged physical position. -/
theorem halveWordRunBits_values {template : List Bool} (hK : 0<template.length)
    (words : List (List Bool))
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1) :
    ∀ j, j<words.length →
      (2 : ZMod (2^template.length+1))*
          wordCoefficient (2^template.length+1) (halveWordRunBits template words).words j=
        wordCoefficient (2^template.length+1) words j := by
  revert hcanon
  induction words with
  | nil => intro hcanon j hj; simp only [List.length_nil] at hj; omega
  | cons word tail ih =>
    intro hcanon j hj
    have ht := ih (fun w hw => hcanon w (by simp only [List.mem_cons]; exact Or.inr hw))
    rw [halveWordRunBits]
    dsimp only
    cases j with
    | zero =>
      rw [wordCoefficient_cons_zero,wordCoefficient_cons_zero]
      exact fermatHalfBits_cast hK (hcanon word (by simp))
    | succ j =>
      rw [wordCoefficient_cons_succ,wordCoefficient_cons_succ]
      exact ht j (by simp only [List.length_cons] at hj; omega)

/-- Actual normalization preserves all source slots and canonical
widths. Its whole cost is linear in source bits times the number of
physically supplied level cells; the caller computes those cells. -/
theorem normalizeFFTWordsBits_words {template : List Bool} (hK : 0<template.length)
    (levels : List Bool) (words : List (List Bool))
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1)
    (hwidth : ∀ word∈words,word.length=template.length+1) :
    (normalizeFFTWordsBits template levels words).words.length=words.length ∧
    (∀ word∈(normalizeFFTWordsBits template levels words).words,
      word.length=template.length+1 ∧ bitValue word<2^template.length+1) ∧
    (normalizeFFTWordsBits template levels words).clock≤
      (levels.length+1)*(words.length+1)*(18*template.length+50) := by
  induction levels generalizing words with
  | nil =>
    refine ⟨rfl,fun word hw => ⟨hwidth word hw,hcanon word hw⟩,?_⟩
    change 1≤(0+1)*(words.length+1)*(18*template.length+50)
    nlinarith only [Nat.zero_le words.length,Nat.zero_le template.length,
      Nat.zero_le (words.length*template.length)]
  | cons level levels ih =>
    have hh := halveWordRunBits_words hK words hcanon (fun word hw => (hwidth word hw).le)
    have ht := ih (halveWordRunBits template words).words
      (fun word hw => (hh.2.1 word hw).2) (fun word hw => (hh.2.1 word hw).1)
    rw [normalizeFFTWordsBits]
    dsimp only
    refine ⟨ht.1.trans hh.1,ht.2.1,?_⟩
    have hc := ht.2.2
    rw [hh.1] at hc
    simp only [List.length_cons]
    nlinarith only [hc,hh.2.2,Nat.zero_le words.length,Nat.zero_le template.length,
      Nat.zero_le (words.length*template.length)]

/-- The actual repeated halves solve the exact dyadic normalization
equation at every ORIGINAL source position. No inverse word is advice. -/
theorem normalizeFFTWordsBits_values {template : List Bool} (hK : 0<template.length)
    (levels : List Bool) (words : List (List Bool))
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1)
    (hwidth : ∀ word∈words,word.length=template.length+1) :
    ∀ j, j<words.length →
      (2 : ZMod (2^template.length+1))^levels.length*
          wordCoefficient (2^template.length+1) (normalizeFFTWordsBits template levels words).words j=
        wordCoefficient (2^template.length+1) words j := by
  induction levels generalizing words with
  | nil => intro j hj; simp only [normalizeFFTWordsBits,List.length_nil,pow_zero,one_mul]
  | cons level levels ih =>
    have hh := halveWordRunBits_words hK words hcanon (fun word hw => (hwidth word hw).le)
    have ht := ih (halveWordRunBits template words).words
      (fun word hw => (hh.2.1 word hw).2) (fun word hw => (hh.2.1 word hw).1)
    intro j hj
    have hhalf := halveWordRunBits_values hK words hcanon j hj
    have htail := ht j (by rw [hh.1]; exact hj)
    rw [normalizeFFTWordsBits]
    dsimp only
    rw [List.length_cons,pow_succ]
    calc
      _ = (2 : ZMod (2^template.length+1))*
          ((2 : ZMod (2^template.length+1))^levels.length*
            wordCoefficient (2^template.length+1)
              (normalizeFFTWordsBits template levels (halveWordRunBits template words).words).words j) := by ring
      _ = (2 : ZMod (2^template.length+1))*
          wordCoefficient (2^template.length+1) (halveWordRunBits template words).words j := by rw [htail]
      _ = _ := hhalf

/-- Actual forward transform, computed physical depth, reflected
frequencies and normalized inverse words, with every component retained
and the complete composed primitive clock. -/
structure FermatInterpolationReport where
  /-- Executed forward transform on the actual supplied frequencies. -/
  forward : FermatFFTReport
  /-- Executed pairing producer for the actual modulus template. -/
  depth : FermatDepthReport
  /-- Actual zero-preserving frequency reflection. -/
  reflected : WordReverseReport
  /-- Actual full-word halving passes controlled by computed levels. -/
  normalized : HalvedWordsReport
  /-- Computed conjunction of transform and template-shape gates. -/
  accepted : Bool
  /-- All four component clocks and wrapper/level/gate primitives. -/
  clock : ℕ

/-- Actual normalized inverse transform. A new physical level for the
extra factor two is prefixed to the depth producer's computed word.
Neither a depth, reflection index nor inverse coefficient is supplied. -/
def fermatInterpolationBits (template : List Bool) (words : List (List Bool)) :
    FermatInterpolationReport :=
  let forward := fermatFFTBits template words
  let depth := fermatDepthBits template
  let reflected := reflectFFTWordsBits forward.words
  let normalized := normalizeFFTWordsBits template (false::depth.levels) reflected.words
  ⟨forward,depth,reflected,normalized,Bool.and forward.accepted depth.accepted,
    forward.clock+depth.clock+reflected.clock+normalized.clock+12⟩

/-- The recursive ORIGINAL coefficient evaluation is the ordinary
finite coefficient sum. This identity has no executable counterpart. -/
theorem wordEvaluation_eq_sum (M : ℕ) (words : List (List Bool)) (x : ZMod M) :
    wordEvaluation M words x=
      ∑ i∈Finset.range words.length,wordCoefficient M words i*x^i := by
  induction words with
  | nil => simp only [wordEvaluation,List.length_nil,Finset.range_zero,Finset.sum_empty]
  | cons word tail ih =>
    rw [wordEvaluation,ih,List.length_cons,Finset.sum_range_succ']
    rw [wordCoefficient_cons_zero,pow_zero,mul_one]
    conv_rhs => rw [add_comm]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [wordCoefficient_cons_succ,pow_succ]
    ring

/-- A complete Fourier character period may be removed term by term.
No division or field hypothesis is used in this proof-side identity. -/
theorem character_sum_period {R : Type*} [CommRing R] (w : R) (n l : ℕ)
    (hperiod : w^n=1) :
    (∑ r∈Finset.range n,w^(r*(l+n)))=∑ r∈Finset.range n,w^(r*l) := by
  apply Finset.sum_congr rfl
  intro r hr
  have he : w^(r*n)=1 := by rw [Nat.mul_comm r n,pow_mul,hperiod,one_pow]
  rw [Nat.mul_add,pow_add,he,mul_one]

/-- All reflected Fourier characters cancel except the ORIGINAL
matching coefficient. This includes zero frequency and every wraparound
case, in the Fermat ring even when its modulus is composite. -/
theorem fermat_character_delta (d : ℕ) {i j : ℕ}
    (hi : i<2^(d+1)) (hj : j<2^(d+1)) :
    (∑ r∈Finset.range (2^(d+1)),
      (2 : ZMod (2^(2^d)+1))^(r*(i+(if j=0 then 0 else 2^(d+1)-j))))=
        if i=j then ((2^(d+1) : ℕ) : ZMod (2^(2^d)+1)) else 0 := by
  by_cases hj0 : j=0
  · subst j
    simp only [ite_true,Nat.add_zero]
    by_cases hi0 : i=0
    · subst i
      simp only [ite_true,Nat.mul_zero,pow_zero,Finset.sum_const,Finset.card_range,
        nsmul_eq_mul,mul_one]
    · rw [if_neg hi0]
      exact fermat_fourier_cancellation d ⟨by omega,hi⟩
  · rw [if_neg hj0]
    by_cases hij : i=j
    · subst i
      rw [if_pos rfl]
      have he : j+(2^(d+1)-j)=2^(d+1) := by omega
      rw [he]
      simp only [Nat.mul_comm _ (2^(d+1)),pow_mul,fermat_fourier_period,
        one_pow,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    · rw [if_neg hij]
      by_cases hlt : i<j
      · exact fermat_fourier_cancellation d ⟨by omega,by omega⟩
      · have he : i+(2^(d+1)-j)=(i-j)+2^(d+1) := by omega
        rw [he,character_sum_period _ _ _ (fermat_fourier_period d)]
        exact fermat_fourier_cancellation d ⟨by omega,by omega⟩

/-- The actual inverse accepts every canonical dyadic input, constructs
every normalization level, preserves exact canonical physical widths and
solves the ORIGINAL reflected evaluation equation at every position.
All four executed component clocks, including frequency traversal and
depth acquisition, appear in the complete primitive bound. -/
theorem fermatInterpolationBits_exact {template : List Bool} (d : ℕ)
    (hK : template.length=2^d) (words : List (List Bool))
    (hcount : words.length=2^(d+1))
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1) :
    (fermatInterpolationBits template words).accepted=true ∧
    (fermatInterpolationBits template words).normalized.words.length=2^(d+1) ∧
    (∀ word∈(fermatInterpolationBits template words).normalized.words,
      word.length=template.length+1 ∧ bitValue word<2^template.length+1) ∧
    (fermatInterpolationBits template words).clock≤
      1000*2^(d+1)*(d+2)*(template.length+2)+
        (d+2)*(2^(d+1)+1)*(18*template.length+50)+
        20*template.length+5*2^(d+1)+44 ∧
    ∀ j, j<2^(d+1) →
      (((2^(d+1) : ℕ) : ZMod (2^template.length+1)))*
          wordCoefficient (2^template.length+1)
            (fermatInterpolationBits template words).normalized.words j=
        wordEvaluation (2^template.length+1) words
          ((2 : ZMod (2^template.length+1))^(if j=0 then 0 else 2^(d+1)-j)) := by
  have hp : 0<template.length := by rw [hK]; positivity
  have hf := fermatFFTBits_exact d hK words hcount hcanon
  have hd := fermatDepthBits_exact d template hK
  have hr := reflectFFTWordsBits_exact (fermatFFTBits template words).words
  have hc : ∀ word∈(reflectFFTWordsBits (fermatFFTBits template words).words).words,
      bitValue word<2^template.length+1 :=
    fun word hw => (hf.2.2.1 word (hr.2.2.1 word hw)).2
  have hw : ∀ word∈(reflectFFTWordsBits (fermatFFTBits template words).words).words,
      word.length=template.length+1 :=
    fun word hmem => (hf.2.2.1 word (hr.2.2.1 word hmem)).1
  have hn := normalizeFFTWordsBits_words hp (false::(fermatDepthBits template).levels)
    (reflectFFTWordsBits (fermatFFTBits template words).words).words hc hw
  have hl : (false::(fermatDepthBits template).levels).length=d+1 := by
    rw [List.length_cons,hd.1]
  have hrlen : (reflectFFTWordsBits (fermatFFTBits template words).words).words.length=2^(d+1) :=
    hr.2.1.trans hf.2.1
  dsimp only [fermatInterpolationBits]
  refine ⟨?_,hn.1.trans hrlen,hn.2.1,?_,?_⟩
  · rw [hf.1,hd.2.1]; rfl
  · have hnclock := hn.2.2
    have hrclock := hr.2.2.2
    rw [hl,hrlen] at hnclock
    rw [hf.2.1] at hrclock
    have hnext : d+1+1=d+2 := by omega
    rw [hnext] at hnclock
    omega
  · intro j hj
    have hv := normalizeFFTWordsBits_values hp (false::(fermatDepthBits template).levels)
      (reflectFFTWordsBits (fermatFFTBits template words).words).words hc hw j
      (by rw [hrlen]; exact hj)
    rw [hl] at hv
    have hscaled : (((2^(d+1) : ℕ) : ZMod (2^template.length+1)))*
        wordCoefficient (2^template.length+1)
          (normalizeFFTWordsBits template (false::(fermatDepthBits template).levels)
            (reflectFFTWordsBits (fermatFFTBits template words).words).words).words j=
          wordCoefficient (2^template.length+1)
            (reflectFFTWordsBits (fermatFFTBits template words).words).words j := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hv
    rw [hscaled]
    by_cases hj0 : j=0
    · subst j
      rw [if_pos rfl,reflectFFTWordsBits_zero,hf.2.2.2.2 0 (by positivity)]
      simp only [Nat.cast_pow,Nat.cast_ofNat]
    · rw [if_neg hj0,reflectFFTWordsBits_positive _ _ ⟨by omega,by rw [hf.2.1]; exact hj⟩]
      rw [hf.2.1,hf.2.2.2.2 (2^(d+1)-j) (by omega)]
      simp only [Nat.cast_pow,Nat.cast_ofNat]

/-- The two ORIGINAL Fourier phases combine into the character whose
universal delta was proved above. This is proof-side ring algebra. -/
theorem fourier_term {R : Type*} [CommRing R] (w c : R) (r i k : ℕ) :
    c*(w^r)^i*(w^k)^r=c*w^(r*(i+k)) := by
  rw [←pow_mul,←pow_mul,mul_assoc,←pow_add]
  congr 1
  congr 1
  ring

/-- Every ORIGINAL coefficient survives the reflected double Fourier
evaluation with exactly the transform-length factor. The input values
are the actual original evaluations, rather than a substituted family
or an assumed pointwise inverse. -/
theorem fermat_double_transform {K : ℕ} (d : ℕ) (hK : K=2^d)
    (source frequencies : List (List Bool))
    (hsource : source.length=2^(d+1)) (hfreq : frequencies.length=2^(d+1))
    (hvalues : ∀ r, r<2^(d+1) →
      wordCoefficient (2^K+1) frequencies r=
        wordEvaluation (2^K+1) source ((2 : ZMod (2^K+1))^r))
    {j : ℕ} (hj : j<2^(d+1)) :
    wordEvaluation (2^K+1) frequencies
        ((2 : ZMod (2^K+1))^(if j=0 then 0 else 2^(d+1)-j))=
      (((2^(d+1) : ℕ) : ZMod (2^K+1)))*
        wordCoefficient (2^K+1) source j := by
  subst K
  rw [wordEvaluation_eq_sum,hfreq]
  calc
    _ = ∑ r∈Finset.range (2^(d+1)),
        (∑ i∈Finset.range (2^(d+1)),
          wordCoefficient (2^(2^d)+1) source i*(2 : ZMod (2^(2^d)+1))^(r*(i+
            (if j=0 then 0 else 2^(d+1)-j)))) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hvalues r (Finset.mem_range.mp hr),wordEvaluation_eq_sum,hsource,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      exact fourier_term _ _ _ _ _
    _ = ∑ i∈Finset.range (2^(d+1)),
        wordCoefficient (2^(2^d)+1) source i*
          (∑ r∈Finset.range (2^(d+1)),
            (2 : ZMod (2^(2^d)+1))^(r*(i+(if j=0 then 0 else 2^(d+1)-j)))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ = ∑ i∈Finset.range (2^(d+1)),
        (if i=j then wordCoefficient (2^(2^d)+1) source i*
          (((2^(d+1) : ℕ) : ZMod (2^(2^d)+1))) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [fermat_character_delta d (Finset.mem_range.mp hi) hj]
      simp only [mul_ite,mul_zero]
    _ = wordCoefficient (2^(2^d)+1) source j*
        (((2^(d+1) : ℕ) : ZMod (2^(2^d)+1))) := by
      simp only [Finset.sum_ite_eq',Finset.mem_range,hj,ite_true]
    _ = _ := mul_comm _ _

/-- The complete actual inverse, including physical depth construction,
frequency reflection and all normalization passes, costs O(n*K*log n)
in the inherited Boolean/reference primitive model. This is a component
bound and is not the full semiprime bit-machine or memory theorem. -/
theorem fermatInterpolationBits_cost {template : List Bool} (d : ℕ)
    (hK : template.length=2^d) (words : List (List Bool))
    (hcount : words.length=2^(d+1))
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1) :
    (fermatInterpolationBits template words).clock≤
      2000*2^(d+1)*(d+2)*(template.length+3) := by
  have hc := (fermatInterpolationBits_exact d hK words hcount hcanon).2.2.2.1
  have hn : 1≤2^(d+1) := by
    have hp : 0<2^(d+1) := by positivity
    omega
  have hnormal : (d+2)*(2^(d+1)+1)*(18*template.length+50)≤
      100*2^(d+1)*(d+2)*(template.length+3) := by
    calc
      _ ≤ (d+2)*(2*2^(d+1))*(50*(template.length+3)) := by
        apply Nat.mul_le_mul
        · apply Nat.mul_le_mul_left
          omega
        · omega
      _ = _ := by ring
  have hcount2 : 2^(d+1)+1≤2^(d+1)*(d+2) := by
    calc
      _ ≤ 2^(d+1)*2 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hextra : 20*template.length+5*2^(d+1)+44≤
      100*2^(d+1)*(d+2)*(template.length+3) := by
    calc
      _ ≤ 100*(2^(d+1)+1)*(template.length+3) := by
        nlinarith only [Nat.zero_le (2^(d+1)*template.length),
          Nat.zero_le template.length,Nat.zero_le (2^(d+1))]
      _ ≤ 100*(2^(d+1)*(d+2))*(template.length+3) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcount2)
      _ = _ := by ring
  have hforward : 1000*2^(d+1)*(d+2)*(template.length+2)≤
      1000*2^(d+1)*(d+2)*(template.length+3) :=
    Nat.mul_le_mul_left _ (by omega)
  calc
    _ ≤ 1000*2^(d+1)*(d+2)*(template.length+2)+
        (d+2)*(2^(d+1)+1)*(18*template.length+50)+
        (20*template.length+5*2^(d+1)+44) := by
      convert hc using 1; ring
    _ ≤ 1000*2^(d+1)*(d+2)*(template.length+3)+
        100*2^(d+1)*(d+2)*(template.length+3)+
        100*2^(d+1)*(d+2)*(template.length+3) := by
      exact Nat.add_le_add (Nat.add_le_add hforward hnormal) hextra
    _ = 1200*2^(d+1)*(d+2)*(template.length+3) := by ring
    _ ≤ _ := by gcongr; norm_num

/-- The actual normalized inverse of the ACTUAL original forward
transform recovers every ORIGINAL ring coefficient. Character
cancellation supplies the arithmetic reason; the transform-length unit
comes from the computed Boolean half of one. No field or successful
finite example is used. -/
theorem fermatInterpolationBits_roundtrip_coefficients {template : List Bool} (d : ℕ)
    (hK : template.length=2^d) (words : List (List Bool))
    (hcount : words.length=2^(d+1))
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1) :
    ∀ j, j<2^(d+1) →
      wordCoefficient (2^template.length+1)
          (fermatInterpolationBits template (fermatFFTBits template words).words).normalized.words j=
        wordCoefficient (2^template.length+1) words j := by
  have hf := fermatFFTBits_exact d hK words hcount hcanon
  have hi := fermatInterpolationBits_exact d hK (fermatFFTBits template words).words hf.2.1
    (fun word hw => (hf.2.2.1 word hw).2)
  intro j hj
  have hd := fermat_double_transform d hK words (fermatFFTBits template words).words hcount hf.2.1
    (fun r hr => by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using hf.2.2.2.2 r hr) hj
  have he : (((2^(d+1) : ℕ) : ZMod (2^template.length+1)))*
      wordCoefficient (2^template.length+1)
        (fermatInterpolationBits template (fermatFFTBits template words).words).normalized.words j=
      (((2^(d+1) : ℕ) : ZMod (2^template.length+1)))*
        wordCoefficient (2^template.length+1) words j :=
    (hi.2.2.2.2 j hj).trans hd
  obtain ⟨u,hu⟩ := fermat_transform_length_unit (show 0<template.length by rw [hK]; positivity) d
  exact (show IsUnit (((2^(d+1) : ℕ) : ZMod (2^template.length+1))) from ⟨u,hu⟩).mul_left_cancel he

/-- Every valid ORIGINAL slot inherits its actual word's canonical
natural value. The lookup and decoded value are specifications only. -/
theorem wordCoefficient_canonical {M : ℕ} (words : List (List Bool))
    (hcanon : ∀ word∈words,bitValue word<M) {j : ℕ} (hj : j<words.length) :
    bitValue (words[j]?.getD [])<M := by
  rw [List.getElem?_eq_getElem hj]
  simp only [Option.getD_some]
  exact hcanon _ (List.getElem_mem hj)

/-- Canonical values turn the universal ORIGINAL ring roundtrip into
exact natural coefficient recovery, including zero coefficients and
arbitrary leading-zero padding on the original words. -/
theorem fermatInterpolationBits_roundtrip_values {template : List Bool} (d : ℕ)
    (hK : template.length=2^d) (words : List (List Bool))
    (hcount : words.length=2^(d+1))
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1) :
    ∀ j, j<2^(d+1) →
      bitValue ((fermatInterpolationBits template
        (fermatFFTBits template words).words).normalized.words[j]?.getD [])=
        bitValue (words[j]?.getD []) := by
  have hf := fermatFFTBits_exact d hK words hcount hcanon
  have hi := fermatInterpolationBits_exact d hK (fermatFFTBits template words).words hf.2.1
    (fun word hw => (hf.2.2.1 word hw).2)
  intro j hj
  have hout := wordCoefficient_canonical
    (fermatInterpolationBits template (fermatFFTBits template words).words).normalized.words
    (fun word hw => (hi.2.2.1 word hw).2) (by rw [hi.2.1]; exact hj)
  have hin := wordCoefficient_canonical words hcanon (by rw [hcount]; exact hj)
  have hv := congrArg ZMod.val
    (fermatInterpolationBits_roundtrip_coefficients d hK words hcount hcanon j hj)
  dsimp only [wordCoefficient] at hv
  rw [ZMod.val_natCast_of_lt hout,ZMod.val_natCast_of_lt hin] at hv
  exact hv

/-- The entire actual forward/inverse roundtrip retains both executed
clocks and has the same n*K*log(n) primitive rate. No recursive pointwise
integer products or full machine costs are hidden in this contract. -/
theorem fermatInterpolationBits_roundtrip_cost {template : List Bool} (d : ℕ)
    (hK : template.length=2^d) (words : List (List Bool))
    (hcount : words.length=2^(d+1))
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1) :
    (fermatFFTBits template words).clock+
        (fermatInterpolationBits template (fermatFFTBits template words).words).clock≤
      3000*2^(d+1)*(d+2)*(template.length+3)+5 := by
  have hf := fermatFFTBits_exact d hK words hcount hcanon
  have hi := fermatInterpolationBits_cost d hK (fermatFFTBits template words).words hf.2.1
    (fun word hw => (hf.2.2.1 word hw).2)
  have hm : 1000*2^(d+1)*(d+2)*(template.length+2)≤
      1000*2^(d+1)*(d+2)*(template.length+3) := Nat.mul_le_mul_left _ (by omega)
  calc
    _ ≤ (1000*2^(d+1)*(d+2)*(template.length+2)+5)+
        2000*2^(d+1)*(d+2)*(template.length+3) := Nat.add_le_add hf.2.2.2.1 hi
    _ ≤ (1000*2^(d+1)*(d+2)*(template.length+3)+5)+
        2000*2^(d+1)*(d+2)*(template.length+3) :=
      Nat.add_le_add_right (Nat.add_le_add_right hm _) _
    _ = _ := by ring

end RiemannGaussian.SemiprimeBitFermatInterpolation
