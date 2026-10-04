/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitFermatArithmetic

/-!
# Actual radix-two transform over a composite Fermat ring

The data path splits actual coefficient references into even/odd lists,
doubles a physical step template, recursively transforms both computed
lists, and combines them with actual Boolean butterflies. Twiddle offsets
are produced by physical-template prefixes, not decoded exponents.
Polynomial evaluation and natural indices are proof specifications only.
Recursive pointwise multiplication, inverse convolution and the full
public factorizer's bit-time/memory proof remain separate obligations.
-/

namespace RiemannGaussian.SemiprimeBitFermatTransform

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitFermatArithmetic
open scoped BigOperators

/-- Actual copied word references followed by a shared suffix, with
every source reference, output cell and list test charged. -/
structure WordAppendReport where
  /-- Actual concatenated coefficient-word references. -/
  words : List (List Bool)
  /-- Complete primitive reference/cell/test clock. -/
  clock : ℕ

/-- Structural reference concatenation without a decoded list length. -/
def appendWordRefsBits : List (List Bool)→List (List Bool)→WordAppendReport
  | [],right => ⟨right,1⟩
  | word::left,right =>
    let child := appendWordRefsBits left right
    ⟨word::child.words,child.clock+6⟩

/-- The executed append has exact order and pays every visited cell. -/
theorem appendWordRefsBits_exact (left right : List (List Bool)) :
    (appendWordRefsBits left right).words=left++right ∧
    (appendWordRefsBits left right).clock=6*left.length+1 := by
  induction left with
  | nil => exact ⟨rfl,rfl⟩
  | cons word left ih =>
    simp only [appendWordRefsBits,List.cons_append,List.length_cons] at ih ⊢
    exact ⟨by rw [ih.1],by omega⟩

/-- The actual even and odd coefficient references, with all visits
and newly constructed list cells charged. -/
structure ParityWordsReport where
  /-- Original coefficients at even physical positions, in order. -/
  evens : List (List Bool)
  /-- Original coefficients at odd physical positions, in order. -/
  odds : List (List Bool)
  /-- Every source/reference/list-cell/test primitive. -/
  clock : ℕ

/-- Traverses two actual coefficient constructors per recursive step.
No position word, division or supplied parity partition is used. -/
def splitParityWordsBits : List (List Bool)→ParityWordsReport
  | [] => ⟨[],[],2⟩
  | [word] => ⟨[word],[],6⟩
  | even::odd::tail =>
    let child := splitParityWordsBits tail
    ⟨even::child.evens,odd::child.odds,child.clock+10⟩

/-- The actual partition has its exact two half counts, including a
possible last even coefficient, and a linear complete reference clock. -/
theorem splitParityWordsBits_counts (words : List (List Bool)) :
    (splitParityWordsBits words).evens.length=(words.length+1)/2 ∧
    (splitParityWordsBits words).odds.length=words.length/2 ∧
    (splitParityWordsBits words).clock≤6*(words.length+1) := by
  induction words using List.twoStepInduction with
  | nil => exact ⟨rfl,rfl,by decide⟩
  | singleton word => norm_num [splitParityWordsBits]
  | cons_cons even odd tail ih _ =>
    simp only [splitParityWordsBits,List.length_cons] at ih ⊢
    exact ⟨by omega,by omega,by omega⟩

/-- Both actual partitions contain only original coefficient words;
no coefficient values or new arithmetic inputs are supplied. -/
theorem splitParityWordsBits_mem (words : List (List Bool)) :
    (∀ word∈(splitParityWordsBits words).evens,word∈words) ∧
    (∀ word∈(splitParityWordsBits words).odds,word∈words) := by
  induction words using List.twoStepInduction with
  | nil => simp only [splitParityWordsBits,List.not_mem_nil,false_implies,implies_true,and_self]
  | singleton word => simp [splitParityWordsBits]
  | cons_cons even odd tail ih _ =>
    constructor
    · intro word hw
      simp only [splitParityWordsBits,List.mem_cons] at hw ⊢
      rcases hw with rfl|ht
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (ih.1 word ht))
    · intro word hw
      simp only [splitParityWordsBits,List.mem_cons] at hw ⊢
      rcases hw with rfl|ht
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (ih.2 word ht))

/-- Proof-only coefficient lookup; the transform data path never calls
this natural-index or natural-value specification. -/
noncomputable def wordCoefficient (M : ℕ) (words : List (List Bool)) (j : ℕ) : ZMod M :=
  (bitValue (words[j]?.getD []) : ZMod M)

/-- The proof-only original polynomial evaluation, by its unchanged
coefficient order. No such Horner loop executes in the transform. -/
noncomputable def wordEvaluation (M : ℕ) : List (List Bool)→ZMod M→ZMod M
  | [],_ => 0
  | word::tail,x => (bitValue word : ZMod M)+x*wordEvaluation M tail x

/-- Original even/odd coefficients give the exact radix-two evaluation
identity, over every composite modulus and at every ring point. -/
theorem splitParityWordsBits_evaluation (M : ℕ) (words : List (List Bool)) (x : ZMod M) :
    wordEvaluation M words x=
      wordEvaluation M (splitParityWordsBits words).evens (x*x)+
        x*wordEvaluation M (splitParityWordsBits words).odds (x*x) := by
  induction words using List.twoStepInduction with
  | nil => simp only [splitParityWordsBits,wordEvaluation,mul_zero,zero_add]
  | singleton word => simp only [splitParityWordsBits,wordEvaluation,mul_zero,add_zero]
  | cons_cons even odd tail ih _ =>
    simp only [splitParityWordsBits,wordEvaluation]
    rw [ih]
    ring

/-- Proof-side low-position lookup exposes the literal first word. -/
theorem wordCoefficient_cons_zero (M : ℕ) (word : List Bool) (tail : List (List Bool)) :
    wordCoefficient M (word::tail) 0=(bitValue word : ZMod M) := rfl

/-- Proof-side successor lookup follows the actual remaining list. -/
theorem wordCoefficient_cons_succ (M : ℕ) (word : List Bool) (tail : List (List Bool)) (j : ℕ) :
    wordCoefficient M (word::tail) (j+1)=wordCoefficient M tail j := rfl

/-- Lookup in the first actual appended block preserves its order. -/
theorem wordCoefficient_append_left (M : ℕ) (left right : List (List Bool))
    {j : ℕ} (hj : j<left.length) :
    wordCoefficient M (left++right) j=wordCoefficient M left j := by
  unfold wordCoefficient
  rw [List.getElem?_append_left hj]

/-- Lookup in the second actual appended block retains its absolute
position and its correct relative index. -/
theorem wordCoefficient_append_right (M : ℕ) (left right : List (List Bool))
    {j : ℕ} (hj : left.length≤j) :
    wordCoefficient M (left++right) j=wordCoefficient M right (j-left.length) := by
  unfold wordCoefficient
  rw [List.getElem?_append_right hj]

/-- Actual upper/lower butterfly output lists, a computed shape gate
and the complete traversal/twiddle/butterfly/reference clock. -/
structure ButterflyRowReport where
  /-- Actual canonical upper outputs, in physical pair order. -/
  upper : List (List Bool)
  /-- Actual canonical lower outputs in that same order. -/
  lower : List (List Bool)
  /-- True exactly when neither pair list has an unmatched tail. -/
  accepted : Bool
  /-- Every primitive, including the final unused offset update. -/
  clock : ℕ

/-- Combines actual transformed parity lists. Each next twiddle offset
is a computed physical-template prefix; no exponent/index is advice.
Mismatched lists retain a false shape gate, rather than a silent success. -/
def butterflyRowBits (template step offset : List Bool) :
    List (List Bool)→List (List Bool)→ButterflyRowReport
  | [],[] => ⟨[],[],true,3⟩
  | left::lefts,right::rights =>
    let butterfly := fermatButterflyBits template offset left right
    let advance := shiftTemplateBits step offset
    let child := butterflyRowBits template step advance.bits lefts rights
    ⟨butterfly.upper.output.bits::child.upper,butterfly.lower.output.bits::child.lower,
      child.accepted,butterfly.clock+bitCost advance+child.clock+12⟩
  | _,_ => ⟨[],[],false,3⟩

/-- Equal actual pair-list lengths pass the executed shape gate and
produce one output in each channel per physical pair. -/
theorem butterflyRowBits_counts (template step offset : List Bool)
    (lefts rights : List (List Bool)) (hlen : lefts.length=rights.length) :
    (butterflyRowBits template step offset lefts rights).accepted=true ∧
    (butterflyRowBits template step offset lefts rights).upper.length=lefts.length ∧
    (butterflyRowBits template step offset lefts rights).lower.length=lefts.length := by
  induction lefts generalizing rights offset with
  | nil =>
    have hr : rights=[] := List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using hlen.symm)
    subst rights
    exact ⟨rfl,rfl,rfl⟩
  | cons left lefts ih =>
    cases rights with
    | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
    | cons right rights =>
      have ht := ih (shiftTemplateBits step offset).bits rights (by simp only [List.length_cons] at hlen; omega)
      simp only [butterflyRowBits,List.length_cons]
      exact ⟨ht.1,by omega,by omega⟩

/-- Every actual row output is canonical and has exactly K+1 cells.
The bound on the computed offset covers every visited twiddle. -/
theorem butterflyRowBits_words {template step offset : List Bool}
    (hK : 0<template.length) (lefts rights : List (List Bool))
    (hlen : lefts.length=rights.length)
    (hcap : offset.length+lefts.length*step.length≤template.length)
    (hl : ∀ word∈lefts,bitValue word<2^template.length+1)
    (hr : ∀ word∈rights,bitValue word<2^template.length+1)
    (hw : ∀ word∈lefts,word.length≤template.length+1) :
    (∀ word∈(butterflyRowBits template step offset lefts rights).upper,
      word.length=template.length+1 ∧ bitValue word<2^template.length+1) ∧
    (∀ word∈(butterflyRowBits template step offset lefts rights).lower,
      word.length=template.length+1 ∧ bitValue word<2^template.length+1) := by
  induction lefts generalizing rights offset with
  | nil =>
    have hrnil : rights=[] := List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using hlen.symm)
    subst rights
    simp only [butterflyRowBits,List.not_mem_nil,false_implies,implies_true,and_self]
  | cons left lefts ih =>
    cases rights with
    | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
    | cons right rights =>
      have hoff : offset.length≤template.length := by
        simp only [List.length_cons,Nat.succ_mul] at hcap
        omega
      have hb := fermatButterflyBits_exact hK hoff (hl left (by simp)) (hr right (by simp))
      have hbw := fermatButterflyBits_width_cost (right:=right) hK hoff (hw left (by simp))
      have ha := (shiftTemplateBits_exact step offset).2.1
      have ht := ih rights (by simp only [List.length_cons] at hlen; omega)
        (by rw [ha]; simp only [List.length_cons,Nat.succ_mul] at hcap; omega)
        (fun word hm => hl word (by simp only [List.mem_cons]; exact Or.inr hm))
        (fun word hm => hr word (by simp only [List.mem_cons]; exact Or.inr hm))
        (fun word hm => hw word (by simp only [List.mem_cons]; exact Or.inr hm))
      constructor
      · intro word hm
        simp only [butterflyRowBits,List.mem_cons] at hm
        rcases hm with rfl|hm
        · exact ⟨hbw.1,hb.2.2.1⟩
        · exact ht.1 word hm
      · intro word hm
        simp only [butterflyRowBits,List.mem_cons] at hm
        rcases hm with rfl|hm
        · exact ⟨hbw.2.1,hb.2.2.2⟩
        · exact ht.2 word hm

/-- All row traversal work is linear in pair count times physical
modulus width, including the actually constructed unused final offset. -/
theorem butterflyRowBits_cost {template step offset : List Bool}
    (hK : 0<template.length) (hs : step.length≤template.length)
    (lefts rights : List (List Bool)) (hlen : lefts.length=rights.length)
    (hcap : offset.length+lefts.length*step.length≤template.length)
    (hw : ∀ word∈lefts,word.length≤template.length+1) :
    (butterflyRowBits template step offset lefts rights).clock≤
      (lefts.length+1)*(129*template.length+216) := by
  induction lefts generalizing rights offset with
  | nil =>
    have hrnil : rights=[] := List.length_eq_zero_iff.mp (by simpa only [List.length_nil] using hlen.symm)
    subst rights
    simp only [butterflyRowBits,List.length_nil,Nat.zero_add,Nat.one_mul]
    omega
  | cons left lefts ih =>
    cases rights with
    | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
    | cons right rights =>
      have hoff : offset.length≤template.length := by
        simp only [List.length_cons,Nat.succ_mul] at hcap
        omega
      have hb := (fermatButterflyBits_width_cost (right:=right) hK hoff (hw left (by simp))).2.2
      have ha := shiftTemplateBits_exact step offset
      have ht := ih rights (by simp only [List.length_cons] at hlen; omega)
        (by rw [ha.2.1]; simp only [List.length_cons,Nat.succ_mul] at hcap; omega)
        (fun word hm => hw word (by simp only [List.mem_cons]; exact Or.inr hm))
      simp only [butterflyRowBits,List.length_cons]
      nlinarith only [hb,ha.2.2,ht,hs]

/-- Both actual output lists contain their literal original child
values mixed with the computed power-of-two phase at each position. -/
theorem butterflyRowBits_values {template step offset : List Bool}
    (hK : 0<template.length) (lefts rights : List (List Bool))
    (hlen : lefts.length=rights.length)
    (hcap : offset.length+lefts.length*step.length≤template.length)
    (hl : ∀ word∈lefts,bitValue word<2^template.length+1)
    (hr : ∀ word∈rights,bitValue word<2^template.length+1) :
    ∀ j, j<lefts.length →
      wordCoefficient (2^template.length+1) (butterflyRowBits template step offset lefts rights).upper j=
        wordCoefficient (2^template.length+1) lefts j+
          ((2^(offset.length+j*step.length) : ℕ) : ZMod (2^template.length+1))*
            wordCoefficient (2^template.length+1) rights j ∧
      wordCoefficient (2^template.length+1) (butterflyRowBits template step offset lefts rights).lower j=
        wordCoefficient (2^template.length+1) lefts j-
          ((2^(offset.length+j*step.length) : ℕ) : ZMod (2^template.length+1))*
            wordCoefficient (2^template.length+1) rights j := by
  induction lefts generalizing rights offset with
  | nil => intro j hj; simp only [List.length_nil] at hj; omega
  | cons left lefts ih =>
    cases rights with
    | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
    | cons right rights =>
      have hoff : offset.length≤template.length := by
        simp only [List.length_cons,Nat.succ_mul] at hcap
        omega
      have hb := fermatButterflyBits_exact hK hoff (hl left (by simp)) (hr right (by simp))
      have ha := (shiftTemplateBits_exact step offset).2.1
      have ht := ih rights (by simp only [List.length_cons] at hlen; omega)
        (by rw [ha]; simp only [List.length_cons,Nat.succ_mul] at hcap; omega)
        (fun word hm => hl word (by simp only [List.mem_cons]; exact Or.inr hm))
        (fun word hm => hr word (by simp only [List.mem_cons]; exact Or.inr hm))
      intro j hj
      cases j with
      | zero =>
        simp only [butterflyRowBits,wordCoefficient_cons_zero,Nat.zero_mul,Nat.add_zero]
        exact ⟨hb.1,hb.2.1⟩
      | succ j =>
        have hjt : j<lefts.length := by simp only [List.length_cons] at hj; omega
        have hc := ht j hjt
        rw [ha] at hc
        have hindex : step.length+offset.length+j*step.length=
            offset.length+(j+1)*step.length := by ring
        rw [hindex] at hc
        simp only [butterflyRowBits,wordCoefficient_cons_succ]
        exact hc

/-- Actual transform outputs, a computed shape gate, and the complete
recursive split/twiddle/butterfly/reference primitive clock. Child
reports are not retained as a transform tree. -/
structure FermatFFTReport where
  /-- Actual canonical transform words in ordinary Fourier order. -/
  words : List (List Bool)
  /-- Actual conjunction of leaf and pair-shape gates. -/
  accepted : Bool
  /-- Every executed primitive in both recursive children and assembly. -/
  clock : ℕ

/-- The actual even/odd radix-two transform. Only actual coefficient
constructors choose the base/recursive branch. Child inputs and steps
are computed, and both recursive results feed the actual butterflies.
The list-length measure below is erased termination evidence only. -/
def fermatFFTLoopBits (template step : List Bool) (words : List (List Bool)) : FermatFFTReport :=
  match words with
  | [] => ⟨[],false,2⟩
  | [word] =>
    let modulus := fermatModulusBits template
    let fitted := fitBits word modulus.bits
    ⟨[fitted.bits],true,bitCost modulus+bitCost fitted+6⟩
  | even::odd::tail =>
    let split := splitParityWordsBits (even::odd::tail)
    let doubled := shiftTemplateBits step step
    let evens := fermatFFTLoopBits template doubled.bits split.evens
    let odds := fermatFFTLoopBits template doubled.bits split.odds
    let mixed := butterflyRowBits template step [] evens.words odds.words
    let joined := appendWordRefsBits mixed.upper mixed.lower
    ⟨joined.words,Bool.and evens.accepted (Bool.and odds.accepted mixed.accepted),
      split.clock+bitCost doubled+evens.clock+odds.clock+mixed.clock+joined.clock+14⟩
termination_by words.length
decreasing_by
  all_goals
    have hc := splitParityWordsBits_counts (even::odd::tail)
    simp only [List.length_cons] at hc ⊢
    omega

/-- The public transform starts with the actual one-cell step for
root two. Its creation/reference and wrapper primitives are paid. -/
def fermatFFTBits (template : List Bool) (words : List (List Bool)) : FermatFFTReport :=
  let child := fermatFFTLoopBits template [false] words
  ⟨child.words,child.accepted,child.clock+5⟩

/-- Exact half-period scale needed by every recursively constructed
twiddle row. This arithmetic is a proof of physical widths only. -/
theorem dyadic_half_scale {K t d : ℕ} (hs : t*2^(d+1)=2*K) : t*2^d=K := by
  rw [pow_succ] at hs
  nlinarith only [hs]

/-- Every valid dyadic recursion passes its actual gates, retains the
original transform count, and returns canonical K+1-cell words.
All child canonicality premises are inherited from actual parity lists. -/
theorem fermatFFTLoopBits_words {template : List Bool} (hK : 0<template.length)
    (d : ℕ) (step : List Bool) (words : List (List Bool))
    (hcount : words.length=2^d) (hscale : step.length*2^d=2*template.length)
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1) :
    (fermatFFTLoopBits template step words).accepted=true ∧
    (fermatFFTLoopBits template step words).words.length=2^d ∧
    ∀ word∈(fermatFFTLoopBits template step words).words,
      word.length=template.length+1 ∧ bitValue word<2^template.length+1 := by
  induction d generalizing step words with
  | zero =>
    cases words with
    | nil => simp only [List.length_nil,pow_zero] at hcount; omega
    | cons word tail =>
      have ht : tail=[] := List.length_eq_zero_iff.mp (by
        simp only [List.length_cons,pow_zero] at hcount; omega)
      subst tail
      have hm := fermatModulusBits_value template
      have hw := (fermatModulusBits_width_cost hK).1
      have hmw := bitValue_lt_width (fermatModulusBits template).bits
      have hc := hcanon word (by simp)
      have hf := fitBits_value (xs:=word) (ys:=(fermatModulusBits template).bits)
        (by rw [hm] at hmw; omega)
      rw [fermatFFTLoopBits]
      dsimp only
      refine ⟨rfl,rfl,?_⟩
      intro out hout
      have he : out=(fitBits word (fermatModulusBits template).bits).bits := List.mem_singleton.mp hout
      subst out
      exact ⟨(fitBits_counts _ _).1.trans hw,by rw [hf]; exact hc⟩
  | succ d ih =>
    have hp : 0<2^d := by positivity
    have hhalf := dyadic_half_scale hscale
    cases words with
    | nil => simp only [List.length_nil,pow_succ] at hcount; omega
    | cons even tail =>
      cases tail with
      | nil => simp only [List.length_cons,List.length_nil,pow_succ] at hcount; omega
      | cons odd tail =>
        have hc := splitParityWordsBits_counts (even::odd::tail)
        have hm := splitParityWordsBits_mem (even::odd::tail)
        have hecount : (splitParityWordsBits (even::odd::tail)).evens.length=2^d := by
          rw [hcount,pow_succ] at hc; omega
        have hocount : (splitParityWordsBits (even::odd::tail)).odds.length=2^d := by
          rw [hcount,pow_succ] at hc; omega
        have hd := (shiftTemplateBits_exact step step).2.1
        have hdscale : (shiftTemplateBits step step).bits.length*2^d=2*template.length := by
          rw [hd,Nat.add_mul,hhalf]; omega
        have he := ih (shiftTemplateBits step step).bits
          (splitParityWordsBits (even::odd::tail)).evens hecount hdscale
          (fun word hw => hcanon word (hm.1 word hw))
        have ho := ih (shiftTemplateBits step step).bits
          (splitParityWordsBits (even::odd::tail)).odds hocount hdscale
          (fun word hw => hcanon word (hm.2 word hw))
        have hpair : (fermatFFTLoopBits template (shiftTemplateBits step step).bits
            (splitParityWordsBits (even::odd::tail)).evens).words.length=
          (fermatFFTLoopBits template (shiftTemplateBits step step).bits
            (splitParityWordsBits (even::odd::tail)).odds).words.length := he.2.1.trans ho.2.1.symm
        have hcap : ([] : List Bool).length+(fermatFFTLoopBits template (shiftTemplateBits step step).bits
            (splitParityWordsBits (even::odd::tail)).evens).words.length*step.length≤template.length := by
          rw [List.length_nil,Nat.zero_add,he.2.1,Nat.mul_comm,hhalf]
        have hr := butterflyRowBits_counts template step [] _ _ hpair
        have hrw := butterflyRowBits_words (step:=step) (offset:=[]) hK _ _ hpair hcap
          (fun word hw => (he.2.2 word hw).2) (fun word hw => (ho.2.2 word hw).2)
          (fun word hw => (he.2.2 word hw).1.le)
        have hj := appendWordRefsBits_exact
          (butterflyRowBits template step []
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).evens).words
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).odds).words).upper
          (butterflyRowBits template step []
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).evens).words
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).odds).words).lower
        rw [fermatFFTLoopBits]
        dsimp only
        refine ⟨?_,?_,?_⟩
        · rw [he.1,ho.1,hr.1]; rfl
        · rw [hj.1,List.length_append,hr.2.1,hr.2.2,he.2.1,pow_succ]
          omega
        · rw [hj.1]
          intro word hw
          rcases List.mem_append.mp hw with hu|hl
          · exact hrw.1 word hu
          · exact hrw.2 word hl

/-- Squaring a computed child evaluation point doubles its literal
power-of-two step, exactly matching the actual doubled template. -/
theorem doubled_twiddle (M t j : ℕ) :
    ((2^((t+t)*j) : ℕ) : ZMod M)=
      ((2^(t*j) : ℕ) : ZMod M)*((2^(t*j) : ℕ) : ZMod M) := by
  rw [←Nat.cast_mul,←pow_add]
  congr 1
  congr 1
  ring

/-- Moving to the second output half negates the evaluation point.
The step/half-size product is the physical Fermat radix K. -/
theorem second_half_twiddle {K t n : ℕ} (hhalf : t*n=K) (j : ℕ) :
    ((2^(t*(n+j)) : ℕ) : ZMod (2^K+1))=
      -((2^(t*j) : ℕ) : ZMod (2^K+1)) := by
  rw [Nat.mul_add,pow_add,Nat.cast_mul,hhalf,fermat_radix,neg_one_mul]

/-- Every actual transform slot equals the ORIGINAL polynomial at its
exact power-of-two Fourier point. The second half retains its sign;
zero/nonunit coefficients and evaluated values are never discarded. -/
theorem fermatFFTLoopBits_values {template : List Bool} (hK : 0<template.length)
    (d : ℕ) (step : List Bool) (words : List (List Bool))
    (hcount : words.length=2^d) (hscale : step.length*2^d=2*template.length)
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1) :
    ∀ j, j<2^d →
      wordCoefficient (2^template.length+1) (fermatFFTLoopBits template step words).words j=
        wordEvaluation (2^template.length+1) words
          (((2^(step.length*j) : ℕ) : ZMod (2^template.length+1))) := by
  induction d generalizing step words with
  | zero =>
    cases words with
    | nil => simp only [List.length_nil,pow_zero] at hcount; omega
    | cons word tail =>
      have ht : tail=[] := List.length_eq_zero_iff.mp (by
        simp only [List.length_cons,pow_zero] at hcount; omega)
      subst tail
      have hm := fermatModulusBits_value template
      have hmw := bitValue_lt_width (fermatModulusBits template).bits
      have hc := hcanon word (by simp)
      have hf := fitBits_value (xs:=word) (ys:=(fermatModulusBits template).bits)
        (by rw [hm] at hmw; omega)
      intro j hj
      have hj0 : j=0 := by simp only [pow_zero] at hj; omega
      subst j
      rw [fermatFFTLoopBits]
      dsimp only
      rw [wordCoefficient_cons_zero,hf]
      simp only [wordEvaluation,mul_zero,add_zero]
  | succ d ih =>
    have hp : 0<2^d := by positivity
    have hhalf := dyadic_half_scale hscale
    cases words with
    | nil => simp only [List.length_nil,pow_succ] at hcount; omega
    | cons even tail =>
      cases tail with
      | nil => simp only [List.length_cons,List.length_nil,pow_succ] at hcount; omega
      | cons odd tail =>
        have hc := splitParityWordsBits_counts (even::odd::tail)
        have hm := splitParityWordsBits_mem (even::odd::tail)
        have hecount : (splitParityWordsBits (even::odd::tail)).evens.length=2^d := by
          rw [hcount,pow_succ] at hc; omega
        have hocount : (splitParityWordsBits (even::odd::tail)).odds.length=2^d := by
          rw [hcount,pow_succ] at hc; omega
        have hd := (shiftTemplateBits_exact step step).2.1
        have hdscale : (shiftTemplateBits step step).bits.length*2^d=2*template.length := by
          rw [hd,Nat.add_mul,hhalf]; omega
        have hecanon : ∀ word∈(splitParityWordsBits (even::odd::tail)).evens,
            bitValue word<2^template.length+1 := fun word hw => hcanon word (hm.1 word hw)
        have hocanon : ∀ word∈(splitParityWordsBits (even::odd::tail)).odds,
            bitValue word<2^template.length+1 := fun word hw => hcanon word (hm.2 word hw)
        have he := fermatFFTLoopBits_words hK d (shiftTemplateBits step step).bits
          (splitParityWordsBits (even::odd::tail)).evens hecount hdscale hecanon
        have ho := fermatFFTLoopBits_words hK d (shiftTemplateBits step step).bits
          (splitParityWordsBits (even::odd::tail)).odds hocount hdscale hocanon
        have hev := ih (shiftTemplateBits step step).bits
          (splitParityWordsBits (even::odd::tail)).evens hecount hdscale hecanon
        have hov := ih (shiftTemplateBits step step).bits
          (splitParityWordsBits (even::odd::tail)).odds hocount hdscale hocanon
        have hpair : (fermatFFTLoopBits template (shiftTemplateBits step step).bits
            (splitParityWordsBits (even::odd::tail)).evens).words.length=
          (fermatFFTLoopBits template (shiftTemplateBits step step).bits
            (splitParityWordsBits (even::odd::tail)).odds).words.length := he.2.1.trans ho.2.1.symm
        have hcap : ([] : List Bool).length+
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).evens).words.length*step.length≤template.length := by
          rw [List.length_nil,Nat.zero_add,he.2.1,Nat.mul_comm,hhalf]
        have hr := butterflyRowBits_counts template step [] _ _ hpair
        have hrv := butterflyRowBits_values (step:=step) (offset:=[]) hK _ _ hpair hcap
          (fun word hw => (he.2.2 word hw).2) (fun word hw => (ho.2.2 word hw).2)
        have hj := appendWordRefsBits_exact
          (butterflyRowBits template step []
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).evens).words
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).odds).words).upper
          (butterflyRowBits template step []
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).evens).words
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).odds).words).lower
        intro j hbound
        rw [fermatFFTLoopBits]
        dsimp only
        rw [hj.1]
        by_cases hfirst : j<2^d
        · have hrowj : j<(fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).evens).words.length := by rw [he.2.1]; exact hfirst
          have hv := hrv j hrowj
          have hphase : ((2^(([] : List Bool).length+j*step.length) : ℕ) : ZMod (2^template.length+1))=
              ((2^(step.length*j) : ℕ) : ZMod (2^template.length+1)) := by
            rw [List.length_nil,Nat.zero_add,Nat.mul_comm j step.length]
          have hpoint : ((2^((shiftTemplateBits step step).bits.length*j) : ℕ) : ZMod (2^template.length+1))=
              ((2^(step.length*j) : ℕ) : ZMod (2^template.length+1))*
                ((2^(step.length*j) : ℕ) : ZMod (2^template.length+1)) := by rw [hd,doubled_twiddle]
          rw [hev j hfirst,hov j hfirst,hphase,hpoint] at hv
          rw [wordCoefficient_append_left _ _ _ (by rw [hr.2.1]; exact hrowj),hv.1]
          exact (splitParityWordsBits_evaluation _ _ _).symm
        · have hsecond : j-2^d<2^d := by rw [pow_succ] at hbound; omega
          have hrowj : j-2^d<(fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).evens).words.length := by rw [he.2.1]; exact hsecond
          have hv := hrv (j-2^d) hrowj
          have hphase : ((2^(([] : List Bool).length+(j-2^d)*step.length) : ℕ) : ZMod (2^template.length+1))=
              ((2^(step.length*(j-2^d)) : ℕ) : ZMod (2^template.length+1)) := by
            rw [List.length_nil,Nat.zero_add,Nat.mul_comm (j-2^d) step.length]
          have hpoint : ((2^((shiftTemplateBits step step).bits.length*(j-2^d)) : ℕ) : ZMod (2^template.length+1))=
              ((2^(step.length*(j-2^d)) : ℕ) : ZMod (2^template.length+1))*
                ((2^(step.length*(j-2^d)) : ℕ) : ZMod (2^template.length+1)) := by rw [hd,doubled_twiddle]
          rw [hev (j-2^d) hsecond,hov (j-2^d) hsecond,hphase,hpoint] at hv
          have hphase2 : ((2^(step.length*j) : ℕ) : ZMod (2^template.length+1))=
              -((2^(step.length*(j-2^d)) : ℕ) : ZMod (2^template.length+1)) := by
            conv_lhs => rw [show j=2^d+(j-2^d) by omega]
            exact second_half_twiddle hhalf (j-2^d)
          rw [wordCoefficient_append_right _ _ _ (by rw [hr.2.1,he.2.1]; omega),
            hr.2.1,he.2.1,hphase2,splitParityWordsBits_evaluation]
          simpa only [neg_mul,mul_neg,neg_neg,←sub_eq_add_neg] using hv.2

/-- The entire actual transform has the radix-two primitive recurrence,
including both children, parity copying, every computed step/offset,
every Boolean butterfly and ordinary-order reference assembly. -/
theorem fermatFFTLoopBits_cost {template : List Bool} (hK : 0<template.length)
    (d : ℕ) (step : List Bool) (words : List (List Bool))
    (hcount : words.length=2^d) (hscale : step.length*2^d=2*template.length)
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1) :
    (fermatFFTLoopBits template step words).clock≤
      1000*2^d*(d+1)*(template.length+2) := by
  induction d generalizing step words with
  | zero =>
    cases words with
    | nil => simp only [List.length_nil,pow_zero] at hcount; omega
    | cons word tail =>
      have ht : tail=[] := List.length_eq_zero_iff.mp (by
        simp only [List.length_cons,pow_zero] at hcount; omega)
      subst tail
      have hm := fermatModulusBits_width_cost hK
      have hf := fitBits_cost word (fermatModulusBits template).bits
      rw [fermatFFTLoopBits]
      dsimp only
      simp only [pow_zero,Nat.zero_add,Nat.mul_one]
      omega
  | succ d ih =>
    have hp : 0<2^d := by positivity
    have hhalf := dyadic_half_scale hscale
    have hmono := Nat.mul_le_mul_left step.length (Nat.succ_le_of_lt hp)
    rw [Nat.mul_one,hhalf] at hmono
    cases words with
    | nil => simp only [List.length_nil,pow_succ] at hcount; omega
    | cons even tail =>
      cases tail with
      | nil => simp only [List.length_cons,List.length_nil,pow_succ] at hcount; omega
      | cons odd tail =>
        have hc := splitParityWordsBits_counts (even::odd::tail)
        have hm := splitParityWordsBits_mem (even::odd::tail)
        have hecount : (splitParityWordsBits (even::odd::tail)).evens.length=2^d := by
          rw [hcount,pow_succ] at hc; omega
        have hocount : (splitParityWordsBits (even::odd::tail)).odds.length=2^d := by
          rw [hcount,pow_succ] at hc; omega
        have hd := shiftTemplateBits_exact step step
        have hdscale : (shiftTemplateBits step step).bits.length*2^d=2*template.length := by
          rw [hd.2.1,Nat.add_mul,hhalf]; omega
        have hecanon : ∀ word∈(splitParityWordsBits (even::odd::tail)).evens,
            bitValue word<2^template.length+1 := fun word hw => hcanon word (hm.1 word hw)
        have hocanon : ∀ word∈(splitParityWordsBits (even::odd::tail)).odds,
            bitValue word<2^template.length+1 := fun word hw => hcanon word (hm.2 word hw)
        have he := fermatFFTLoopBits_words hK d (shiftTemplateBits step step).bits
          (splitParityWordsBits (even::odd::tail)).evens hecount hdscale hecanon
        have ho := fermatFFTLoopBits_words hK d (shiftTemplateBits step step).bits
          (splitParityWordsBits (even::odd::tail)).odds hocount hdscale hocanon
        have hecost := ih (shiftTemplateBits step step).bits
          (splitParityWordsBits (even::odd::tail)).evens hecount hdscale hecanon
        have hocost := ih (shiftTemplateBits step step).bits
          (splitParityWordsBits (even::odd::tail)).odds hocount hdscale hocanon
        have hpair : (fermatFFTLoopBits template (shiftTemplateBits step step).bits
            (splitParityWordsBits (even::odd::tail)).evens).words.length=
          (fermatFFTLoopBits template (shiftTemplateBits step step).bits
            (splitParityWordsBits (even::odd::tail)).odds).words.length := he.2.1.trans ho.2.1.symm
        have hcap : ([] : List Bool).length+
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).evens).words.length*step.length≤template.length := by
          rw [List.length_nil,Nat.zero_add,he.2.1,Nat.mul_comm,hhalf]
        have hr := butterflyRowBits_counts template step [] _ _ hpair
        have hrcost := butterflyRowBits_cost (step:=step) (offset:=[]) hK hmono _ _ hpair hcap
          (fun word hw => (he.2.2 word hw).1.le)
        have hj := appendWordRefsBits_exact
          (butterflyRowBits template step []
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).evens).words
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).odds).words).upper
          (butterflyRowBits template step []
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).evens).words
            (fermatFFTLoopBits template (shiftTemplateBits step step).bits
              (splitParityWordsBits (even::odd::tail)).odds).words).lower
        have hsplit := hc.2.2
        rw [hcount,pow_succ] at hsplit
        rw [he.2.1] at hrcost
        have happend := hj.2
        rw [hr.2.1,he.2.1] at happend
        have hprod := Nat.mul_le_mul_right template.length (Nat.succ_le_of_lt hp)
        simp only [Nat.one_mul] at hprod
        have hover : (splitParityWordsBits (even::odd::tail)).clock+
            bitCost (shiftTemplateBits step step)+
            (butterflyRowBits template step []
              (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                (splitParityWordsBits (even::odd::tail)).evens).words
              (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                (splitParityWordsBits (even::odd::tail)).odds).words).clock+
            (appendWordRefsBits
              (butterflyRowBits template step []
                (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                  (splitParityWordsBits (even::odd::tail)).evens).words
                (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                  (splitParityWordsBits (even::odd::tail)).odds).words).upper
              (butterflyRowBits template step []
                (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                  (splitParityWordsBits (even::odd::tail)).evens).words
                (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                  (splitParityWordsBits (even::odd::tail)).odds).words).lower).clock+14≤
              1000*(2^d+2^d)*(template.length+2) := by
          nlinarith only [hsplit,hd.2.2,hrcost,happend,hmono,hprod,hp,Nat.zero_le template.length]
        rw [fermatFFTLoopBits]
        dsimp only
        calc
          _ = (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                  (splitParityWordsBits (even::odd::tail)).evens).clock+
                (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                  (splitParityWordsBits (even::odd::tail)).odds).clock+
                ((splitParityWordsBits (even::odd::tail)).clock+bitCost (shiftTemplateBits step step)+
                  (butterflyRowBits template step []
                    (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                      (splitParityWordsBits (even::odd::tail)).evens).words
                    (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                      (splitParityWordsBits (even::odd::tail)).odds).words).clock+
                  (appendWordRefsBits
                    (butterflyRowBits template step []
                      (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                        (splitParityWordsBits (even::odd::tail)).evens).words
                      (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                        (splitParityWordsBits (even::odd::tail)).odds).words).upper
                    (butterflyRowBits template step []
                      (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                        (splitParityWordsBits (even::odd::tail)).evens).words
                      (fermatFFTLoopBits template (shiftTemplateBits step step).bits
                        (splitParityWordsBits (even::odd::tail)).odds).words).lower).clock+14) := by ring
          _ ≤ 1000*2^d*(d+1)*(template.length+2)+1000*2^d*(d+1)*(template.length+2)+
                1000*(2^d+2^d)*(template.length+2) :=
            Nat.add_le_add (Nat.add_le_add hecost hocost) hover
          _ = 1000*2^(d+1)*(d+1+1)*(template.length+2) := by rw [pow_succ]; ring

/-- The actual root-two transform accepts every canonical dyadic
input, preserves every original Fourier evaluation in ordinary order,
returns exact physical widths and has the complete n*K*log(n) primitive
bound. The depth is proof evidence, never an executable argument. -/
theorem fermatFFTBits_exact {template : List Bool} (d : ℕ)
    (hK : template.length=2^d) (words : List (List Bool))
    (hcount : words.length=2^(d+1))
    (hcanon : ∀ word∈words,bitValue word<2^template.length+1) :
    (fermatFFTBits template words).accepted=true ∧
    (fermatFFTBits template words).words.length=2^(d+1) ∧
    (∀ word∈(fermatFFTBits template words).words,
      word.length=template.length+1 ∧ bitValue word<2^template.length+1) ∧
    (fermatFFTBits template words).clock≤
      1000*2^(d+1)*(d+2)*(template.length+2)+5 ∧
    ∀ j, j<2^(d+1) →
      wordCoefficient (2^template.length+1) (fermatFFTBits template words).words j=
        wordEvaluation (2^template.length+1) words (((2^j : ℕ) : ZMod (2^template.length+1))) := by
  have hp : 0<template.length := by rw [hK]; positivity
  have hs : [false].length*2^(d+1)=2*template.length := by
    simp only [List.length_cons,List.length_nil,Nat.zero_add,Nat.one_mul,hK,pow_succ]
    ring
  have hw := fermatFFTLoopBits_words hp (d+1) [false] words hcount hs hcanon
  have hc := fermatFFTLoopBits_cost hp (d+1) [false] words hcount hs hcanon
  have hv := fermatFFTLoopBits_values hp (d+1) [false] words hcount hs hcanon
  refine ⟨hw.1,hw.2.1,hw.2.2,?_,?_⟩
  · dsimp only [fermatFFTBits]
    have hdepth : d+1+1=d+2 := by omega
    rw [hdepth] at hc
    omega
  · intro j hj
    dsimp only [fermatFFTBits]
    simpa only [List.length_cons,List.length_nil,Nat.zero_add,Nat.one_mul] using hv j hj

end RiemannGaussian.SemiprimeBitFermatTransform
