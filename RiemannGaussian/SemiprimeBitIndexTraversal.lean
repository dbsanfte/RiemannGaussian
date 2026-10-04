/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitIndexGeometry

/-!
# Actual word traversal of original signed index intervals

Computed count words control full nonzero scans and decrements. Signed
increments and paid physical copies emit original coordinates in order;
the original endpoint bounds prove those copies lossless. Mathematical
values in termination arguments are erased proof measures, not branches
or serialization oracles. Full machine/memory and jet acquisition costs
remain separate.
-/

namespace RiemannGaussian.SemiprimeBitIndexTraversal

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitPrimeScan
open SemiprimeBitIndexRoots SemiprimeBitIndexClipping SemiprimeBitIndexGeometry
open SemiprimeBitIndexBasis SemiprimeIndexEnumeration SemiprimeIndexLattice
open SemiprimeGroupSelection

/-- Full subtraction of one from a nonzero counter does not underflow
and computes its exact natural predecessor. -/
theorem decrementBits_value {remaining : List Bool} (hp : 0<bitValue remaining) :
    (subBits remaining [true] false).borrow=false ∧
      bitValue (subBits remaining [true] false).result.bits=bitValue remaining-1 := by
  have hb : (subBits remaining [true] false).borrow=false :=
    (subBits_borrow_false _ _).mpr (by
      simp only [bitValue,bitNat,if_true,Nat.mul_zero,Nat.add_zero]
      omega)
  refine ⟨hb,?_⟩
  have he := subBits_difference hb
  simpa only [bitValue,bitNat,if_true,Nat.mul_zero,Nat.add_zero] using he

/-- Actual paid magnitude copy and its retained original sign. -/
structure SignedCopyWordReport where
  /-- Full existing Boolean copy/padding circuit report. -/
  copy : BitReport
  /-- Actual copied word with the unchanged Boolean sign. -/
  word : SignedWord
  /-- Full copy work and retained sign/output decisions. -/
  clock : ℕ

/-- Copy to the actual supplied physical template, paying every cell.
Value preservation is proved from bounds, never assumed by the data path. -/
def fitSignedBits (word : SignedWord) (template : List Bool) : SignedCopyWordReport :=
  let copy := fitBits word.magnitude template
  ⟨copy,⟨word.negative,copy.bits⟩,bitCost copy+3⟩

/-- An actual bounded signed value is preserved by its paid width copy,
including either sign representation of zero. -/
theorem fitSignedBits_value {word : SignedWord} {template : List Bool}
    (hw : word.value.natAbs<2^template.length) :
    (fitSignedBits word template).word.value=word.value := by
  rw [signedWord_natAbs] at hw
  have he := fitBits_value hw
  dsimp only [fitSignedBits,SignedWord.value]
  rw [he]

/-- Paid signed fitting has linear physical work and exact template width. -/
theorem fitSignedBits_cost_width (word : SignedWord) (template : List Bool) :
    (fitSignedBits word template).clock≤4*template.length+4 ∧
      (fitSignedBits word template).word.magnitude.length=template.length := by
  have hc := fitBits_cost word.magnitude template
  have hw := (fitBits_counts word.magnitude template).1
  exact ⟨by dsimp only [fitSignedBits]; omega,hw⟩

/-- One executed coordinate visit and all its actual counter/update work. -/
structure RangeWordFrame where
  /-- Full scan of the original remaining-counter word. -/
  nonzero : NonzeroReport
  /-- Full subtraction computing the remaining predecessor word. -/
  decrement : SubReport
  /-- Full signed coordinate increment. -/
  increment : SignedSumReport
  /-- Full paid width copy of the computed successor. -/
  fitting : SignedCopyWordReport

/-- Actual emitted coordinates, every executed frame and final counter scan. -/
structure RangeWordReport where
  /-- Original coordinate words in increasing value order when bounds fit. -/
  words : List SignedWord
  /-- Every executed visit frame, in original order. -/
  frames : List RangeWordFrame
  /-- Actual full final zero-counter scan, including supplied padding. -/
  finalScan : NonzeroReport
  /-- All scans, decrements, signed increments, width copies and branches. -/
  clock : ℕ

/-- Actual bit-counter-controlled coordinate traversal. Every visit computes
and pays its successor, including after the final emitted endpoint.
The natural measure occurs only in erased termination proofs. -/
def rangeWordsBits (template : List Bool) (current : SignedWord) (remaining : List Bool) :
    RangeWordReport :=
  let nonzero := nonzeroBits remaining
  if hn : nonzero.nonzero=true then
    let decrement := subBits remaining [true] false
    let increment := addSignedBits current oneWord
    let fitting := fitSignedBits increment.word template
    let child := rangeWordsBits template fitting.word decrement.result.bits
    ⟨current::child.words,⟨nonzero,decrement,increment,fitting⟩::child.frames,child.finalScan,
      nonzero.clock+bitCost decrement.result+increment.clock+fitting.clock+child.clock+11⟩
  else ⟨[],[],nonzero,nonzero.clock+3⟩
termination_by bitValue remaining
decreasing_by
  have hp := (nonzeroBits_correct remaining).mp hn
  have he := (decrementBits_value hp).2
  rw [he]
  omega

/-- Full original consecutive coordinate order whenever the whole span,
including the last successor, fits the supplied actual template. -/
theorem rangeWordsBits_values (template : List Bool) (current : SignedWord) (remaining : List Bool)
    (hfit : ∀ k : ℕ, k≤bitValue remaining→
      (current.value+(k : ℤ)).natAbs<2^template.length) :
    (rangeWordsBits template current remaining).words.map SignedWord.value=
      (List.range (bitValue remaining)).map (fun k : ℕ => current.value+(k : ℤ)) := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing current remaining with
  | h n ih =>
    by_cases hn : (nonzeroBits remaining).nonzero=true
    · have hp := (nonzeroBits_correct remaining).mp hn
      let decrement := subBits remaining [true] false
      let increment := addSignedBits current oneWord
      let fitting := fitSignedBits increment.word template
      have hd := (decrementBits_value hp).2
      have hsmall : bitValue decrement.result.bits<n := by
        dsimp only [decrement]
        omega
      have hincrement : increment.word.value=current.value+1 := by
        rw [addSignedBits_value,oneWord_value]
      have hcopy : fitting.word.value=current.value+1 := by
        rw [fitSignedBits_value (by rw [hincrement]; exact hfit 1 (by omega))]
        exact hincrement
      have hchildFit : ∀ k : ℕ, k≤bitValue decrement.result.bits→
          (fitting.word.value+(k : ℤ)).natAbs<2^template.length := by
        intro k hk
        have hk' : k+1≤n := by dsimp only [decrement] at hk; omega
        have hh := hfit (k+1) hk'
        rw [hcopy]
        simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hh
      have hchild := ih (bitValue decrement.result.bits) hsmall fitting.word
        decrement.result.bits rfl hchildFit
      have hcount : n=bitValue decrement.result.bits+1 := by dsimp only [decrement]; omega
      rw [rangeWordsBits,dif_pos hn]
      dsimp only
      rw [List.map_cons,hchild,hcount,List.range_succ_eq_map,List.map_cons,List.map_map]
      simp only [Nat.cast_zero,add_zero]
      congr 1
      apply List.map_congr_left
      intro k _
      rw [hcopy]
      simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one]
      ring
    · have hz := (nonzeroBits_false_iff remaining).mp (Bool.eq_false_of_not_eq_true hn)
      have hn0 : n=0 := by omega
      rw [rangeWordsBits,dif_neg hn,hn0]
      rfl

/-- Compute a physical endpoint template by actual bit copying, finishing
with one additional false cell. No integer word is serialized. -/
def spanTemplateBits : List Bool→List Bool→BitReport
  | [],[] => ⟨[false],0,0,1,3⟩
  | [],b::bs =>
    let child := spanTemplateBits [] bs
    ⟨b::child.bits,child.gates,child.reads+1,child.writes+1,child.tests+2⟩
  | a::as,bs =>
    let child := spanTemplateBits as bs
    ⟨a::child.bits,child.gates,child.reads+1,child.writes+1,child.tests+2⟩
termination_by first second => first.length+second.length

/-- Actual template output, physical width and all executed bit-cell counts. -/
theorem spanTemplateBits_counts (first second : List Bool) :
    (spanTemplateBits first second).bits=first++(second++[false]) ∧
      (spanTemplateBits first second).bits.length=first.length+second.length+1 ∧
      (spanTemplateBits first second).gates=0 ∧
      (spanTemplateBits first second).reads=first.length+second.length ∧
      (spanTemplateBits first second).writes=first.length+second.length+1 ∧
      (spanTemplateBits first second).tests=2*(first.length+second.length)+3 := by
  induction first with
  | nil =>
    induction second with
    | nil => simp [spanTemplateBits]
    | cons b bs ih =>
      simp only [spanTemplateBits,List.cons_append,List.nil_append,List.length_cons]
      rcases ih with ⟨hb,hw,hg,hr,hwr,ht⟩
      rw [hw,hg,hr,hwr,ht,hb]
      constructor
      · rfl
      · constructor <;> omega
  | cons a as ih =>
    simp only [spanTemplateBits,List.cons_append,List.length_cons]
    rcases ih with ⟨hb,hw,hg,hr,hwr,ht⟩
    rw [hw,hg,hr,hwr,ht,hb]
    constructor
    · rfl
    · constructor <;> omega

/-- Every template read, new bit write, list-case test and extra cell is paid. -/
theorem spanTemplateBits_cost (first second : List Bool) :
    bitCost (spanTemplateBits first second)=4*(first.length+second.length)+4 := by
  rcases spanTemplateBits_counts first second with ⟨_,_,hg,hr,hw,ht⟩
  simp only [bitCost,hg,hr,hw,ht]
  omega

/-- Actual signed span arithmetic, positivity test and unsigned count word. -/
structure CounterWordReport where
  /-- Full original upper-minus-lower signed subtraction. -/
  difference : SignedSumReport
  /-- Actual span plus one, retained even for empty bounds. -/
  increment : SignedSumReport
  /-- Complete actual signed nonnegative test. -/
  nonnegative : SignedOrderReport
  /-- Original positive-part count as an actual magnitude word. -/
  bits : List Bool
  /-- All signed arithmetic, full order work, literal cell and decisions. -/
  clock : ℕ

/-- Acquire the count from actual endpoints. Empty bounds select literal
zero; nonnegative spans share their computed magnitude, including signed zero. -/
def intervalCounterBits (bounds : WordInterval) : CounterWordReport :=
  let difference := subSignedBits bounds.upper bounds.lower
  let increment := addSignedBits difference.word oneWord
  let nonnegative := leSignedBits zeroWord increment.word
  let bits := if nonnegative.le=true then increment.word.magnitude else []
  ⟨difference,increment,nonnegative,bits,
    difference.clock+increment.clock+nonnegative.clock+6⟩

/-- Exact original interval count, including empty, reversed, negative and
signed-zero bounds. Native toNat is specification only. -/
theorem intervalCounterBits_value (bounds : WordInterval) :
    bitValue (intervalCounterBits bounds).bits=
      (bounds.upper.value+1-bounds.lower.value).toNat := by
  have hv : (addSignedBits (subSignedBits bounds.upper bounds.lower).word oneWord).word.value=
      bounds.upper.value+1-bounds.lower.value := by
    rw [addSignedBits_value,subSignedBits_value,oneWord_value]
    ring
  by_cases hn : (leSignedBits zeroWord
      (addSignedBits (subSignedBits bounds.upper bounds.lower).word oneWord).word).le=true
  · have hnonnegative := (leSignedBits_exact _ _).mp hn
    rw [zeroWord_value] at hnonnegative
    have hm := signedWord_magnitude_of_nonneg hnonnegative
    have ht := congrArg Int.toNat hm
    unfold intervalCounterBits
    dsimp only
    rw [if_pos hn]
    simpa only [Int.toNat_natCast,hv] using ht
  · have hnegative : (addSignedBits (subSignedBits bounds.upper bounds.lower).word oneWord).word.value<0 := by
      have hh : ¬zeroWord.value≤
          (addSignedBits (subSignedBits bounds.upper bounds.lower).word oneWord).word.value :=
        fun hh => hn ((leSignedBits_exact _ _).mpr hh)
      rw [zeroWord_value] at hh
      omega
    unfold intervalCounterBits
    dsimp only
    rw [if_neg hn]
    change 0=(bounds.upper.value+1-bounds.lower.value).toNat
    rw [hv] at hnegative
    omega

/-- Actual interval counter acquisition has linear physical work, with
bounded computed padding even when the bounds are reversed. -/
theorem intervalCounterBits_cost_width {W : ℕ} {bounds : WordInterval}
    (hl : bounds.lower.magnitude.length≤W) (hu : bounds.upper.magnitude.length≤W) :
    (intervalCounterBits bounds).clock≤500*(W+1) ∧
      (intervalCounterBits bounds).bits.length≤W+2 := by
  have hd := subSignedBits_cost_width hu hl
  have hone : oneWord.magnitude.length≤W+1 := by
    change ([true] : List Bool).length≤W+1
    simp only [List.length_cons,List.length_nil]
    omega
  have hi := addSignedBits_cost_width hd.2 hone
  have hz := leSignedBits_cost (left:=zeroWord)
    (right:=(addSignedBits (subSignedBits bounds.upper bounds.lower).word oneWord).word)
    (Nat.zero_le _) hi.2
  unfold intervalCounterBits
  dsimp only
  constructor
  · omega
  · split
    · exact hi.2
    · exact Nat.zero_le _

/-- The acquired counter's full span, including the final successor,
fits the template actually constructed from both endpoint words. -/
theorem intervalCounterBits_span (bounds : WordInterval) :
    ∀ k : ℕ, k≤bitValue (intervalCounterBits bounds).bits→
      (bounds.lower.value+(k : ℤ)).natAbs<
        2^(spanTemplateBits bounds.lower.magnitude bounds.upper.magnitude).bits.length := by
  intro k hk
  let K := bounds.lower.magnitude.length+bounds.upper.magnitude.length
  have hlo : bounds.lower.value.natAbs<2^K := by
    rw [signedWord_natAbs]
    exact (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hhi : bounds.upper.value.natAbs<2^K := by
    rw [signedWord_natAbs]
    exact (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hloZ : |bounds.lower.value|<((2^K : ℕ) : ℤ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast hlo
  have hhiZ : |bounds.upper.value|<((2^K : ℕ) : ℤ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast hhi
  have hp : (0 : ℤ)<((2^K : ℕ) : ℤ) := by positivity
  have hwidth := (spanTemplateBits_counts bounds.lower.magnitude bounds.upper.magnitude).2.1
  rw [intervalCounterBits_value] at hk
  have hab : |bounds.lower.value+(k : ℤ)|<((2^(K+1) : ℕ) : ℤ) := by
    rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    have h0 := abs_lt.mp hloZ
    have h1 := abs_lt.mp hhiZ
    by_cases hn : 0≤bounds.upper.value+1-bounds.lower.value
    · have hc : ((bounds.upper.value+1-bounds.lower.value).toNat : ℤ)=
          bounds.upper.value+1-bounds.lower.value := Int.toNat_of_nonneg hn
      have hkZ : (k : ℤ)≤bounds.upper.value+1-bounds.lower.value := by omega
      exact abs_lt.mpr ⟨by omega,by omega⟩
    · have hk0 : k=0 := by omega
      rw [hk0,Nat.cast_zero,add_zero]
      exact abs_lt.mpr ⟨by omega,by omega⟩
  rw [hwidth]
  change (bounds.lower.value+(k : ℤ)).natAbs<2^(K+1)
  rw [←Int.natCast_natAbs] at hab
  exact_mod_cast hab

/-- Complete actual interval count, endpoint template and emitted word stream. -/
structure IntervalWordReport where
  /-- Actual count construction, retaining failed signed work. -/
  counter : CounterWordReport
  /-- Actual copied physical template, with its additional cell. -/
  template : BitReport
  /-- Actual counter-controlled coordinate traversal and every frame. -/
  traversal : RangeWordReport
  /-- Every constructor and every traversal primitive. -/
  clock : ℕ

/-- Construct and visit the original signed interval entirely as words.
Its own endpoint template makes every paid coordinate copy lossless. -/
def intervalWordsBits (bounds : WordInterval) : IntervalWordReport :=
  let counter := intervalCounterBits bounds
  let template := spanTemplateBits bounds.lower.magnitude bounds.upper.magnitude
  let traversal := rangeWordsBits template.bits bounds.lower counter.bits
  ⟨counter,template,traversal,counter.clock+bitCost template+traversal.clock+3⟩

/-- Complete original coordinate order, including all empty/negative/signed
zero cases. No supplied encoding of a native entries list is used. -/
theorem intervalWordsBits_values (bounds : WordInterval) :
    (intervalWordsBits bounds).traversal.words.map SignedWord.value=bounds.interpret.entries := by
  have he := rangeWordsBits_values
    (spanTemplateBits bounds.lower.magnitude bounds.upper.magnitude).bits
    bounds.lower (intervalCounterBits bounds).bits (intervalCounterBits_span bounds)
  rw [intervalCounterBits_value] at he
  exact he

/-- Every actual visit has one retained frame. Paid copying prevents padding
growth, so full traversal work is linear in visits times physical width,
including the final zero scan and the last unused successor. -/
theorem rangeWordsBits_cost_width {W : ℕ} (hW : 1≤W) {template : List Bool}
    (ht : template.length≤W) {current : SignedWord} {remaining : List Bool}
    (hc : current.magnitude.length≤W) (hr : remaining.length≤W) :
    (rangeWordsBits template current remaining).words.length=bitValue remaining ∧
      (rangeWordsBits template current remaining).frames.length=bitValue remaining ∧
      (rangeWordsBits template current remaining).clock≤(bitValue remaining+1)*(100*(W+1)) ∧
      ∀ word∈(rangeWordsBits template current remaining).words, word.magnitude.length≤W := by
  generalize he : bitValue remaining=n at *
  induction n using Nat.strong_induction_on generalizing current remaining with
  | h n ih =>
    have hnonzero := nonzeroBits_cost remaining
    by_cases hn : (nonzeroBits remaining).nonzero=true
    · have hp := (nonzeroBits_correct remaining).mp hn
      let decrement := subBits remaining [true] false
      let increment := addSignedBits current oneWord
      let fitting := fitSignedBits increment.word template
      let child := rangeWordsBits template fitting.word decrement.result.bits
      have hd := (decrementBits_value hp).2
      have hsmall : bitValue decrement.result.bits<n := by dsimp only [decrement]; omega
      have hcount : bitValue decrement.result.bits+1=n := by dsimp only [decrement]; omega
      have hdecrementWidth : decrement.result.bits.length≤W := by
        change (subBits remaining [true] false).result.bits.length≤W
        rw [(subBits_counts remaining [true] false).2.2.2.2]
        simp only [List.length_cons,List.length_nil]
        omega
      have hone : oneWord.magnitude.length≤W := by
        change ([true] : List Bool).length≤W
        simp only [List.length_cons,List.length_nil]
        exact hW
      have hincrement := addSignedBits_cost_width hc hone
      have hfitting := fitSignedBits_cost_width increment.word template
      have hfittingWidth : fitting.word.magnitude.length≤W := hfitting.2.le.trans ht
      have hchild : child.words.length=bitValue decrement.result.bits ∧
          child.frames.length=bitValue decrement.result.bits ∧
          child.clock≤(bitValue decrement.result.bits+1)*(100*(W+1)) ∧
          ∀ word∈child.words, word.magnitude.length≤W := by
        apply ih (bitValue decrement.result.bits) hsmall
        · exact hfittingWidth
        · exact hdecrementWidth
        · rfl
      have hchildClock : child.clock≤n*(100*(W+1)) := by
        rw [←hcount]
        exact hchild.2.2.1
      have hdecrementCost := subBits_cost remaining [true] false
      have hstep : (nonzeroBits remaining).clock+bitCost decrement.result+
          increment.clock+fitting.clock+11≤100*(W+1) := by
        dsimp only [decrement,increment,fitting] at *
        simp only [List.length_cons,List.length_nil] at hdecrementCost
        omega
      rw [rangeWordsBits,dif_pos hn]
      dsimp only
      refine ⟨?_,?_,?_,?_⟩
      · change child.words.length+1=n
        omega
      · change child.frames.length+1=n
        omega
      · change (nonzeroBits remaining).clock+bitCost decrement.result+
          increment.clock+fitting.clock+child.clock+11≤(n+1)*(100*(W+1))
        calc
          _≤100*(W+1)+n*(100*(W+1)) := by omega
          _=(n+1)*(100*(W+1)) := by ring
      · change ∀ word∈current::child.words, word.magnitude.length≤W
        intro word hw
        rcases List.mem_cons.mp hw with rfl|hw
        · exact hc
        · exact hchild.2.2.2 word hw
    · have hz := (nonzeroBits_false_iff remaining).mp (Bool.eq_false_of_not_eq_true hn)
      have hn0 : n=0 := by omega
      rw [rangeWordsBits,dif_neg hn]
      dsimp only
      refine ⟨by simp only [List.length_nil]; omega,
        by simp only [List.length_nil]; omega,?_,?_⟩
      · rw [hn0]
        simp only [Nat.zero_add,Nat.one_mul]
        omega
      · intro word hw
        cases hw

/-- Full interval construction and actual traversal pay linearly for physical
width and every emitted coordinate. Every output word has bounded padding. -/
theorem intervalWordsBits_cost_width {W : ℕ} {bounds : WordInterval}
    (hl : bounds.lower.magnitude.length≤W) (hu : bounds.upper.magnitude.length≤W) :
    (intervalWordsBits bounds).clock≤
        (bounds.interpret.entries.length+1)*(1000*(W+1)) ∧
      (intervalWordsBits bounds).traversal.words.length=bounds.interpret.entries.length ∧
      (intervalWordsBits bounds).traversal.frames.length=bounds.interpret.entries.length ∧
      ∀ word∈(intervalWordsBits bounds).traversal.words,
        word.magnitude.length≤3*(W+1) := by
  let counter := intervalCounterBits bounds
  let template := spanTemplateBits bounds.lower.magnitude bounds.upper.magnitude
  let traversal := rangeWordsBits template.bits bounds.lower counter.bits
  have hcounter := intervalCounterBits_cost_width hl hu
  have htemplateWidth := (spanTemplateBits_counts bounds.lower.magnitude bounds.upper.magnitude).2.1
  have htemplateCost := spanTemplateBits_cost bounds.lower.magnitude bounds.upper.magnitude
  have htraversal := rangeWordsBits_cost_width (W:=3*(W+1)) (by omega)
    (template:=template.bits) (by rw [htemplateWidth]; omega)
    (current:=bounds.lower) (remaining:=counter.bits) (hl.trans (by omega))
    (hcounter.2.trans (by omega))
  have hcount : bitValue counter.bits=bounds.interpret.entries.length := by
    rw [intervalCounterBits_value,interval_entries_length]
  have hscale : 100*(3*(W+1)+1)≤400*(W+1) := by omega
  have htraversalClock : traversal.clock≤
      (bounds.interpret.entries.length+1)*(400*(W+1)) := by
    have hm := Nat.mul_le_mul_left (bitValue counter.bits+1) hscale
    rw [hcount] at hm
    rw [hcount] at htraversal
    exact htraversal.2.2.1.trans hm
  have hconstructor : counter.clock+bitCost template+3≤600*(W+1) := by
    dsimp only [counter,template]
    omega
  have hbase : 600*(W+1)≤(bounds.interpret.entries.length+1)*(600*(W+1)) :=
    (Nat.le_mul_of_pos_left _ (by omega))
  constructor
  · change counter.clock+bitCost template+traversal.clock+3≤
      (bounds.interpret.entries.length+1)*(1000*(W+1))
    calc
      _≤(bounds.interpret.entries.length+1)*(600*(W+1))+
          (bounds.interpret.entries.length+1)*(400*(W+1)) := by omega
      _=(bounds.interpret.entries.length+1)*(1000*(W+1)) := by ring
  · change traversal.words.length=bounds.interpret.entries.length ∧
      traversal.frames.length=bounds.interpret.entries.length ∧
      ∀ word∈traversal.words, word.magnitude.length≤3*(W+1)
    rw [hcount] at htraversal
    exact ⟨htraversal.1,htraversal.2.1,htraversal.2.2.2⟩

/-- Actual word coordinates and coefficient magnitudes emitted on one line. -/
structure PointStreamWordReport where
  /-- Original signed coordinate pairs, in occurrence order. -/
  coordinates : List (SignedWord×SignedWord)
  /-- Actual unsigned coefficient words for the original root reader. -/
  points : List (List Bool×List Bool)
  /-- Every full executed affine point report. -/
  reports : List PointWordReport
  /-- All point primitives and retained list/occurrence decisions. -/
  clock : ℕ

/-- Emit one actual affine point for each actual coordinate word.
No native point list or supplied coefficient encoding is consulted. -/
def emitPointsBits (rectangle : RectangleWordReport) (basis : BasisLoopWordReport)
    (j : SignedWord) : List SignedWord→PointStreamWordReport
  | [] => ⟨[],[],[],1⟩
  | i::indices =>
    let point := coefficientPointBits rectangle basis i j
    let child := emitPointsBits rectangle basis j indices
    ⟨(i,j)::child.coordinates,point.magnitudes::child.points,point::child.reports,
      point.clock+child.clock+10⟩

/-- Point emission preserves every coordinate and occurrence in input order. -/
theorem emitPointsBits_coordinates (rectangle : RectangleWordReport) (basis : BasisLoopWordReport)
    (j : SignedWord) (indices : List SignedWord) :
    (emitPointsBits rectangle basis j indices).coordinates.map
        (fun t => (t.1.value,t.2.value))=
      indices.map (fun i => (i.value,j.value)) := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp only [emitPointsBits,List.map_cons,ih]

/-- A complete emitted line retains its exact original nonnegative point
values and order. Membership comes from actual interval iteration. -/
theorem emitPointsBits_values (decoded bound : List Bool) (basis : BasisLoopWordReport)
    (j : SignedWord) (indices : List SignedWord) (hu : 0<basis.interpret.coefficient)
    (hi : ∀ i∈indices, i.value∈
      (lineIntervalBits (rectangleBits decoded bound) basis j).bounds.interpret.entries) :
    (emitPointsBits (rectangleBits decoded bound) basis j indices).points.map
        (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ)))=
      indices.map (fun i => coefficientPoint (bitValue decoded) basis.interpret (i.value,j.value)) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    have hhead := clipped_point_magnitudes decoded bound basis i j hu
      (hi i (List.mem_cons_self))
    have htail := ih (fun word hw => hi word (List.mem_cons_of_mem _ hw))
    simp only [emitPointsBits,List.map_cons,hhead,htail]

/-- Every original coordinate creates exactly one point and retained report. -/
theorem emitPointsBits_counts (rectangle : RectangleWordReport) (basis : BasisLoopWordReport)
    (j : SignedWord) (indices : List SignedWord) :
    (emitPointsBits rectangle basis j indices).coordinates.length=indices.length ∧
      (emitPointsBits rectangle basis j indices).points.length=indices.length ∧
      (emitPointsBits rectangle basis j indices).reports.length=indices.length := by
  induction indices with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons i indices ih =>
    simp only [emitPointsBits,List.length_cons]
    exact ⟨by omega,by omega,by omega⟩

/-- Full point emission pays quadratic word work for every occurrence and
derives both actual reader widths, rather than assuming coefficient encodings. -/
theorem emitPointsBits_cost_width {W : ℕ} {decoded bound : List Bool} {basis : BasisLoopWordReport}
    {j : SignedWord} (hs : decoded.length≤W) (hL : bound.length≤W)
    (hj : j.magnitude.length≤W)
    (hc : basis.coefficient.length≤W) (hr : basis.remainder.length≤W)
    (hp : basis.previousCoefficient.length≤W) (hpr : basis.previousRemainder.length≤W)
    (indices : List SignedWord) (hi : ∀ i∈indices, i.magnitude.length≤W) :
    (emitPointsBits (rectangleBits decoded bound) basis j indices).clock≤
        indices.length*(2000*(W+1)^2+10)+1 ∧
      ∀ pair∈(emitPointsBits (rectangleBits decoded bound) basis j indices).points,
        pair.1.length≤8*(W+1) ∧ pair.2.length≤8*(W+1) := by
  induction indices with
  | nil =>
    constructor
    · simp only [emitPointsBits,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
    · intro pair hpair
      cases hpair
  | cons i indices ih =>
    have hpoint := coefficientPointBits_cost_width hs hL (hi i List.mem_cons_self) hj hc hr hp hpr
    have hchild := ih (fun word hw => hi word (List.mem_cons_of_mem _ hw))
    dsimp only [emitPointsBits]
    constructor
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · intro pair hpair
      rcases List.mem_cons.mp hpair with rfl|hpair
      · exact hpoint.2
      · exact hchild.2 pair hpair

/-- One complete executed line, including empty-line initialization. -/
structure LineStreamWordFrame where
  /-- The actual original signed band coordinate. -/
  coordinate : SignedWord
  /-- Actual affine offsets and original line clipping. -/
  line : LineWordReport
  /-- Actual acquired count, template and coordinate stream for the line. -/
  interval : IntervalWordReport
  /-- Every emitted coefficient word and point diagnostic. -/
  emission : PointStreamWordReport

/-- Complete nested original coordinate and coefficient-word stream. -/
structure LineStreamWordReport where
  /-- Original signed coordinates in complete nested occurrence order. -/
  coordinates : List (SignedWord×SignedWord)
  /-- Actual coefficient magnitudes, with every original occurrence retained. -/
  points : List (List Bool×List Bool)
  /-- Every initialized line, including empty ones, in original band order. -/
  lines : List LineStreamWordFrame
  /-- Every line, coordinate/point primitive and paid list concatenation walk. -/
  clock : ℕ

/-- Visit each actual band word, construct and traverse its original line,
then append its emitted points in original order. The append charge includes
three walks of the emitted head lists, rather than repeated tail copying. -/
def emitLinesBits (rectangle : RectangleWordReport) (basis : BasisLoopWordReport) :
    List SignedWord→LineStreamWordReport
  | [] => ⟨[],[],[],1⟩
  | j::bands =>
    let line := lineIntervalBits rectangle basis j
    let interval := intervalWordsBits line.bounds
    let emission := emitPointsBits rectangle basis j interval.traversal.words
    let child := emitLinesBits rectangle basis bands
    ⟨emission.coordinates++child.coordinates,emission.points++child.points,
      ⟨j,line,interval,emission⟩::child.lines,
      line.clock+interval.clock+emission.clock+child.clock+3*emission.points.length+12⟩

/-- Complete original nested coordinate order, with every empty line and
every occurrence accounted for by the actual emitted coordinate stream. -/
theorem emitLinesBits_coordinates (decoded bound : List Bool) (basis : BasisLoopWordReport)
    (bands : List SignedWord) :
    (emitLinesBits (rectangleBits decoded bound) basis bands).coordinates.map
        (fun t => (t.1.value,t.2.value))=
      (bands.map SignedWord.value).flatMap (fun j =>
        (lineInterval (bitValue decoded) (bitValue bound) basis.interpret j).entries.map
          (fun i => (i,j))) := by
  induction bands with
  | nil => rfl
  | cons j bands ih =>
    have hinterval := intervalWordsBits_values
      (lineIntervalBits (rectangleBits decoded bound) basis j).bounds
    have hhead := congrArg (fun xs : List ℤ => xs.map (fun i => (i,j.value))) hinterval
    simp only [List.map_map,Function.comp_def] at hhead
    rw [lineIntervalBits_value] at hhead
    simp only [emitLinesBits,List.map_append,emitPointsBits_coordinates,
      List.map_cons,List.flatMap_cons,ih,hhead]

/-- Complete original point order and values for every actual emitted line.
No oracle-supplied point stream or coefficient serializer appears. -/
theorem emitLinesBits_values (decoded bound : List Bool) (basis : BasisLoopWordReport)
    (bands : List SignedWord) (hu : 0<basis.interpret.coefficient) :
    (emitLinesBits (rectangleBits decoded bound) basis bands).points.map
        (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ)))=
      (bands.map SignedWord.value).flatMap (fun j =>
        (lineInterval (bitValue decoded) (bitValue bound) basis.interpret j).entries.map
          (fun i => coefficientPoint (bitValue decoded) basis.interpret (i,j))) := by
  induction bands with
  | nil => rfl
  | cons j bands ih =>
    have hinterval := intervalWordsBits_values
      (lineIntervalBits (rectangleBits decoded bound) basis j).bounds
    have hemit := emitPointsBits_values decoded bound basis j
      (intervalWordsBits (lineIntervalBits (rectangleBits decoded bound) basis j).bounds).traversal.words hu
      (fun i hi => hinterval ▸ List.mem_map.mpr ⟨i,hi,rfl⟩)
    have hhead := congrArg (fun xs : List ℤ => xs.map
      (fun i => coefficientPoint (bitValue decoded) basis.interpret (i,j.value))) hinterval
    simp only [List.map_map,Function.comp_def] at hhead
    rw [lineIntervalBits_value] at hhead
    simp only [emitLinesBits,List.map_append,hemit,List.map_cons,List.flatMap_cons,ih,hhead]

/-- Actual line initialization count and emitted coordinate/point equality,
including empty lines and repeated source occurrences. -/
theorem emitLinesBits_counts (rectangle : RectangleWordReport) (basis : BasisLoopWordReport)
    (bands : List SignedWord) :
    (emitLinesBits rectangle basis bands).lines.length=bands.length ∧
      (emitLinesBits rectangle basis bands).coordinates.length=
        (emitLinesBits rectangle basis bands).points.length := by
  induction bands with
  | nil => exact ⟨rfl,rfl⟩
  | cons j bands ih =>
    have hpoint := emitPointsBits_counts rectangle basis j
      (intervalWordsBits (lineIntervalBits rectangle basis j).bounds).traversal.words
    simp only [emitLinesBits,List.length_cons,List.length_append]
    exact ⟨by omega,by omega⟩

/-- One original initialized line pays all clipping, interval acquisition,
coordinate traversal, affine point arithmetic and concatenation head walks. -/
theorem emitted_line_cost_width {W : ℕ} {decoded bound : List Bool} {basis : BasisLoopWordReport}
    {j : SignedWord} (hs : decoded.length≤W) (hL : bound.length≤W)
    (hj : j.magnitude.length≤W)
    (hc : basis.coefficient.length≤W) (hr : basis.remainder.length≤W)
    (hp : basis.previousCoefficient.length≤W) (hpr : basis.previousRemainder.length≤W) :
    let line := lineIntervalBits (rectangleBits decoded bound) basis j
    let interval := intervalWordsBits line.bounds
    let emission := emitPointsBits (rectangleBits decoded bound) basis j interval.traversal.words
    line.clock+interval.clock+emission.clock+3*emission.points.length+12≤
        (emission.points.length+1)*(4000000*(W+1)^2) ∧
      ∀ pair∈emission.points, pair.1.length≤320*(W+1) ∧ pair.2.length≤320*(W+1) := by
  let line := lineIntervalBits (rectangleBits decoded bound) basis j
  let interval := intervalWordsBits line.bounds
  let emission := emitPointsBits (rectangleBits decoded bound) basis j interval.traversal.words
  have hline := lineIntervalBits_cost_width hs hL hj hc hr hp hpr
  have hinterval := intervalWordsBits_cost_width hline.2.1 hline.2.2
  have hi : ∀ i∈interval.traversal.words, i.magnitude.length≤39*(W+1) := by
    intro i hi
    exact (hinterval.2.2.2 i hi).trans (by omega)
  have hscale : W≤39*(W+1) := by omega
  have hemission := emitPointsBits_cost_width (hs.trans hscale) (hL.trans hscale)
    (hj.trans hscale) (hc.trans hscale) (hr.trans hscale) (hp.trans hscale) (hpr.trans hscale)
    interval.traversal.words hi
  have hcounts := emitPointsBits_counts (rectangleBits decoded bound) basis j interval.traversal.words
  have hcount : emission.points.length=line.bounds.interpret.entries.length :=
    hcounts.2.1.trans hinterval.2.1
  have hpower : W+1≤(W+1)^2 := by nlinarith only []
  have hpointBudget : 2000*(39*(W+1)+1)^2+10≤3200010*(W+1)^2 := by
    have hh := Nat.pow_le_pow_left (by omega : 39*(W+1)+1≤40*(W+1)) 2
    rw [mul_pow] at hh
    norm_num only at hh
    have hpositive : 1≤(W+1)^2 := by
      have hh' : 0<(W+1)^2 := by positivity
      omega
    omega
  have hintervalBudget : 1000*(12*(W+1)+1)≤13000*(W+1)^2 := by
    omega
  have hemClock : emission.clock≤emission.points.length*(3200010*(W+1)^2)+1 := by
    have hh := Nat.mul_le_mul_left interval.traversal.words.length hpointBudget
    calc
      _ ≤ interval.traversal.words.length*(2000*(39*(W+1)+1)^2+10)+1 := hemission.1
      _ ≤ interval.traversal.words.length*(3200010*(W+1)^2)+1 := by omega
      _=emission.points.length*(3200010*(W+1)^2)+1 := by rw [hcounts.2.1]
  have hintClock : interval.clock≤(emission.points.length+1)*(13000*(W+1)^2) := by
    have hh := Nat.mul_le_mul_left (emission.points.length+1) hintervalBudget
    calc
      _≤(line.bounds.interpret.entries.length+1)*(1000*(12*(W+1)+1)) := hinterval.1
      _=(emission.points.length+1)*(1000*(12*(W+1)+1)) := by rw [hcount]
      _≤(emission.points.length+1)*(13000*(W+1)^2) := hh
  have hlineClock : line.clock≤500000*(W+1)^2 := hline.1
  have hbase : 500000*(W+1)^2≤(emission.points.length+1)*(500000*(W+1)^2) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hextra : 3*emission.points.length+13≤(emission.points.length+1)*(20*(W+1)^2) := by
    have hpositive : 1≤(W+1)^2 := by
      have hh' : 0<(W+1)^2 := by positivity
      omega
    have hh := Nat.mul_le_mul_left (20*(emission.points.length+1)) hpositive
    nlinarith only [hh]
  constructor
  · change line.clock+interval.clock+emission.clock+3*emission.points.length+12≤_
    calc
      _≤(emission.points.length+1)*(500000*(W+1)^2)+
          (emission.points.length+1)*(13000*(W+1)^2)+
          emission.points.length*(3200010*(W+1)^2)+
          (emission.points.length+1)*(20*(W+1)^2) := by omega
      _≤(emission.points.length+1)*(4000000*(W+1)^2) := by nlinarith only []
  · intro pair hpair
    have hw := hemission.2 pair hpair
    constructor <;> omega

/-- Complete nested emission is bounded by initialized lines plus actual
point visits, with no source-word or source-encoding oracle premise. -/
theorem emitLinesBits_cost_width {W : ℕ} {decoded bound : List Bool} {basis : BasisLoopWordReport}
    (hs : decoded.length≤W) (hL : bound.length≤W)
    (hc : basis.coefficient.length≤W) (hr : basis.remainder.length≤W)
    (hp : basis.previousCoefficient.length≤W) (hpr : basis.previousRemainder.length≤W)
    (bands : List SignedWord) (hj : ∀ j∈bands, j.magnitude.length≤W) :
    (emitLinesBits (rectangleBits decoded bound) basis bands).clock≤
        (bands.length+(emitLinesBits (rectangleBits decoded bound) basis bands).points.length+1)*
          (4000000*(W+1)^2) ∧
      ∀ pair∈(emitLinesBits (rectangleBits decoded bound) basis bands).points,
        pair.1.length≤320*(W+1) ∧ pair.2.length≤320*(W+1) := by
  induction bands with
  | nil =>
    constructor
    · change 1≤(0+0+1)*(4000000*(W+1)^2)
      have hh : 0<(W+1)^2 := by positivity
      omega
    · intro pair hpair
      cases hpair
  | cons j bands ih =>
    have hhead := emitted_line_cost_width hs hL (hj j List.mem_cons_self) hc hr hp hpr
    have hchild := ih (fun j hj' => hj j (List.mem_cons_of_mem _ hj'))
    let line := lineIntervalBits (rectangleBits decoded bound) basis j
    let interval := intervalWordsBits line.bounds
    let emission := emitPointsBits (rectangleBits decoded bound) basis j interval.traversal.words
    let child := emitLinesBits (rectangleBits decoded bound) basis bands
    constructor
    · change line.clock+interval.clock+emission.clock+child.clock+3*emission.points.length+12≤
        (bands.length+1+(emission.points++child.points).length+1)*(4000000*(W+1)^2)
      have hh : line.clock+interval.clock+emission.clock+3*emission.points.length+12≤
          (emission.points.length+1)*(4000000*(W+1)^2) := hhead.1
      have ht : child.clock≤(bands.length+child.points.length+1)*(4000000*(W+1)^2) := hchild.1
      simp only [List.length_append]
      calc
        _≤(emission.points.length+1)*(4000000*(W+1)^2)+
            (bands.length+child.points.length+1)*(4000000*(W+1)^2) := by omega
        _=(bands.length+1+(emission.points.length+child.points.length)+1)*
            (4000000*(W+1)^2) := by ring
    · change ∀ pair∈emission.points++child.points,
        pair.1.length≤320*(W+1) ∧ pair.2.length≤320*(W+1)
      intro pair hpair
      rcases List.mem_append.mp hpair with hh|ht
      · exact hhead.2 pair hh
      · exact hchild.2 pair ht

/-- Complete actually acquired original coefficient-word source. -/
structure CoefficientSourceWordReport where
  /-- Once-only original Boolean basis, rectangle and signed band acquisition. -/
  geometry : GeometryWordReport
  /-- Actual signed band counter, template and emitted coordinate words. -/
  band : IntervalWordReport
  /-- Complete nested line/point emission, retaining every original occurrence. -/
  stream : LineStreamWordReport
  /-- All source construction and traversal clocks, including empty lines. -/
  clock : ℕ

/-- Acquire the FULL original coefficient source from N, decoded residue
and bound words. No encoded native source or source callback is supplied. -/
def coefficientSourceBits (modulus decoded bound : List Bool) : CoefficientSourceWordReport :=
  let geometry := indexGeometryBits modulus decoded bound
  let band := intervalWordsBits geometry.band.bounds
  let stream := emitLinesBits geometry.rectangle geometry.basis.basis band.traversal.words
  ⟨geometry,band,stream,geometry.clock+band.clock+stream.clock+4⟩

/-- Complete original coordinate ORDER, on every input representation.
The source is computed by word counts and paid copies, not serialized. -/
theorem coefficientSourceBits_coordinates (modulus decoded bound : List Bool) :
    (coefficientSourceBits modulus decoded bound).stream.coordinates.map
        (fun t => (t.1.value,t.2.value))=
      (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).coordinates := by
  have hgeometry := indexGeometryBits_value modulus decoded bound
  have hband := intervalWordsBits_values (indexGeometryBits modulus decoded bound).band.bounds
  have he := emitLinesBits_coordinates decoded bound
    (indexGeometryBits modulus decoded bound).basis.basis
    (intervalWordsBits (indexGeometryBits modulus decoded bound).band.bounds).traversal.words
  rw [hband,hgeometry.1,hgeometry.2] at he
  exact he

/-- Positive original public inputs supply complete original POINT order
and every actual reader magnitude, with no source-encoding premise. -/
theorem coefficientSourceBits_values {modulus bound : List Bool}
    (hN : 0<bitValue modulus) (hL : 0<bitValue bound) (decoded : List Bool) :
    (coefficientSourceBits modulus decoded bound).stream.points.map
        (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ)))=
      (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).points := by
  have hgeometry := indexGeometryBits_value modulus decoded bound
  have hband := intervalWordsBits_values (indexGeometryBits modulus decoded bound).band.bounds
  have he := emitLinesBits_values decoded bound
    (indexGeometryBits modulus decoded bound).basis.basis
    (intervalWordsBits (indexGeometryBits modulus decoded bound).band.bounds).traversal.words
    (indexGeometryBits_coefficient_positive hN hL decoded)
  rw [hband,hgeometry.1,hgeometry.2] at he
  simp only [enumerateCoefficients,List.map_flatMap,List.map_map]
  exact he

/-- Actual word line/point counts equal the original native initialized
lines and visits. Native cardinality bounds now apply to a constructed source. -/
theorem coefficientSourceBits_counts (modulus decoded bound : List Bool) :
    (coefficientSourceBits modulus decoded bound).stream.lines.length=
        (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).lines ∧
      (coefficientSourceBits modulus decoded bound).stream.points.length=
        (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).visits := by
  have hgeometry := indexGeometryBits_value modulus decoded bound
  have hband := intervalWordsBits_values (indexGeometryBits modulus decoded bound).band.bounds
  have hbandCount := congrArg List.length hband
  simp only [List.length_map] at hbandCount
  have hlines := emitLinesBits_counts (indexGeometryBits modulus decoded bound).rectangle
    (indexGeometryBits modulus decoded bound).basis.basis
    (intervalWordsBits (indexGeometryBits modulus decoded bound).band.bounds).traversal.words
  have hcoords := congrArg List.length (coefficientSourceBits_coordinates modulus decoded bound)
  simp only [List.length_map] at hcoords
  constructor
  · change (emitLinesBits _ _ _).lines.length=_
    rw [hlines.1,hbandCount,hgeometry.2]
    rfl
  · change (emitLinesBits _ _ _).points.length=_
    rw [←hlines.2]
    exact hcoords

/-- Complete source acquisition has cubic once-only construction and
quadratic physical work per original initialized line/point visit. All
reader words are produced with a factor-independent public physical width. -/
theorem coefficientSourceBits_cost_width {W : ℕ} {modulus decoded bound : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤W)
    (hs : decoded.length≤W) (hL : bound.length≤W) :
    let original := enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)
    (coefficientSourceBits modulus decoded bound).clock≤
        2000000*(W+1)^3+(original.lines+original.visits+1)*(20000000000*(W+1)^2) ∧
      ∀ pair∈(coefficientSourceBits modulus decoded bound).stream.points,
        pair.1.length≤22528*(W+1) ∧ pair.2.length≤22528*(W+1) := by
  let geometry := indexGeometryBits modulus decoded bound
  let band := intervalWordsBits geometry.band.bounds
  let stream := emitLinesBits geometry.rectangle geometry.basis.basis band.traversal.words
  let original := enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)
  have hgeometry := indexGeometryBits_cost_width hN hm hs hL
  have hband := intervalWordsBits_cost_width hgeometry.2.1 hgeometry.2.2
  have hj : ∀ j∈band.traversal.words, j.magnitude.length≤69*(W+1) := by
    intro j hj
    exact (hband.2.2.2 j hj).trans (by omega)
  have hscale : W≤69*(W+1) := by omega
  have hw := indexBasisBits_width hN decoded bound
  have hstream := emitLinesBits_cost_width (hs.trans hscale) (hL.trans hscale)
    (hw.1.trans (hm.trans hscale)) (hw.2.1.trans (hm.trans hscale))
    (hw.2.2.1.trans (hm.trans hscale)) (hw.2.2.2.trans (hm.trans hscale)) band.traversal.words hj
  have hsourceCounts := coefficientSourceBits_counts modulus decoded bound
  have hlineCounts := emitLinesBits_counts geometry.rectangle geometry.basis.basis band.traversal.words
  have hbandCount : band.traversal.words.length=original.lines :=
    hlineCounts.1.symm.trans hsourceCounts.1
  have hpointCount : stream.points.length=original.visits := hsourceCounts.2
  have hbandEntries : geometry.band.bounds.interpret.entries.length=original.lines :=
    hband.2.1.symm.trans hbandCount
  have hstreamBudget : 4000000*(69*(W+1)+1)^2≤19600000000*(W+1)^2 := by
    have hh := Nat.pow_le_pow_left (by omega : 69*(W+1)+1≤70*(W+1)) 2
    rw [mul_pow] at hh
    norm_num only at hh
    omega
  have hpower : W+1≤(W+1)^2 := by nlinarith only []
  have hpositive : 1≤(W+1)^2 := by
    have hh : 0<(W+1)^2 := by positivity
    omega
  have hbandBudget : 1000*(22*(W+1)+1)≤23000*(W+1)^2 := by omega
  have hstreamClock : stream.clock≤
      (original.lines+original.visits+1)*(19600000000*(W+1)^2) := by
    have hh := Nat.mul_le_mul_left (original.lines+original.visits+1) hstreamBudget
    calc
      _≤(band.traversal.words.length+stream.points.length+1)*(4000000*(69*(W+1)+1)^2) := hstream.1
      _=(original.lines+original.visits+1)*(4000000*(69*(W+1)+1)^2) := by rw [hbandCount,hpointCount]
      _≤(original.lines+original.visits+1)*(19600000000*(W+1)^2) := hh
  have hbandClock : band.clock≤(original.lines+1)*(23000*(W+1)^2) := by
    have hh := Nat.mul_le_mul_left (original.lines+1) hbandBudget
    calc
      _≤(geometry.band.bounds.interpret.entries.length+1)*(1000*(22*(W+1)+1)) := hband.1
      _=(original.lines+1)*(1000*(22*(W+1)+1)) := by rw [hbandEntries]
      _≤(original.lines+1)*(23000*(W+1)^2) := hh
  have hgeometryClock : geometry.clock≤2000000*(W+1)^3 := hgeometry.1
  have hbands : (original.lines+1)*(23000*(W+1)^2)≤
      (original.lines+original.visits+1)*(23000*(W+1)^2) :=
    Nat.mul_le_mul_right _ (by omega)
  have hfour : 4≤(original.lines+original.visits+1)*(4*(W+1)^2) := by
    have hh := Nat.mul_le_mul (by omega : 1≤original.lines+original.visits+1) hpositive
    nlinarith only [hh]
  constructor
  · change geometry.clock+band.clock+stream.clock+4≤_
    calc
      _≤2000000*(W+1)^3+(original.lines+original.visits+1)*(19600000000*(W+1)^2)+
          (original.lines+original.visits+1)*(23000*(W+1)^2)+
          (original.lines+original.visits+1)*(4*(W+1)^2) := by omega
      _≤2000000*(W+1)^3+(original.lines+original.visits+1)*(20000000000*(W+1)^2) := by
        nlinarith only []
  · intro pair hpair
    have hh := hstream.2 pair hpair
    constructor <;> omega

/-- Actual complete source and the existing Boolean first-success factor scan. -/
structure ConstructedFactorWordReport where
  /-- Fully acquired original source, with all construction diagnostics. -/
  source : CoefficientSourceWordReport
  /-- Actual original root/read/GCD scan over the computed coefficient words. -/
  scan : SemiprimeBitIndexFactors.FactorScanWordReport
  /-- Source acquisition, complete first-success scan and retained decisions. -/
  clock : ℕ

/-- Construct the complete original coefficient stream, then execute the
existing Boolean first-success reader. No source callback is accepted. -/
def constructedFactorBits (modulus decoded bound : List Bool) : ConstructedFactorWordReport :=
  let source := coefficientSourceBits modulus decoded bound
  let scan := SemiprimeBitIndexFactors.scanCoefficientsBits modulus decoded bound source.stream.points
  ⟨source,scan,source.clock+scan.clock+4⟩

/-- Public mixed-index extraction now includes ACTUAL source construction,
full original point order, reader physical widths and the first-success
scan with at most one scan GCD. Jet acquisition and full controller remain separate. -/
theorem public_constructed_factor {p q k l W : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (modulus decoded bound : List Bool)
    (hmodulus : bitValue modulus=p*q) (hs : bitValue decoded<bitValue modulus)
    (hbound : bitValue bound=SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hk : k<bitValue bound) (hl : l<bitValue bound) (hLp : bitValue bound≤p) (hkl : k≠l)
    (hP : (bitValue decoded : ZMod p)=(k : ZMod p))
    (hQ : (bitValue decoded : ZMod q)=(l : ZMod q))
    (hmWidth : modulus.length≤W) (hsWidth : decoded.length≤W) (hbWidth : bound.length≤W) :
    let V := 524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q))
    let K := 22528*(W+1)
    (∃ divisor, (constructedFactorBits modulus decoded bound).scan.factor=some divisor ∧
      ProperDivisor (bitValue modulus) (bitValue divisor)) ∧
      (constructedFactorBits modulus decoded bound).scan.gcdCalls≤1 ∧
      (constructedFactorBits modulus decoded bound).clock≤
        2000000*(W+1)^3+(524290+V+1)*(20000000000*(W+1)^2)+
          V*(20000*(K+1)^2+9)+625000*(K+1)^3+5 := by
  have hN : 0<bitValue modulus := by rw [hmodulus]; exact Nat.mul_pos hp.pos hq.pos
  have hL : 0<bitValue bound := by omega
  have hsource := coefficientSourceBits_cost_width hN hmWidth hsWidth hbWidth
  have hencoding := coefficientSourceBits_values hN hL decoded
  have hscale : W≤22528*(W+1) := by omega
  have hreader := SemiprimeBitIndexFactors.public_encoded_factor_scan hp hq hpq hB
    modulus decoded bound (coefficientSourceBits modulus decoded bound).stream.points
    hmodulus hs hbound hk hl hLp hkl hP hQ hencoding
    (hmWidth.trans hscale) (hsWidth.trans hscale) (hbWidth.trans hscale) hsource.2
  have hcounts := public_mixed_index_enumeration_counts hp hq hpq.le hB
    (hbound ▸ hk) (hbound ▸ hl) (hbound ▸ hLp) hkl hP hQ
  have hlines : (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).lines≤524290 := by
    rw [hmodulus,hbound]
    exact hcounts.1
  have hvisits : (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).visits≤
      524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)) := by
    rw [hmodulus,hbound]
    exact hcounts.2
  have hprice := Nat.mul_le_mul_right (20000000000*(W+1)^2)
    (show (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).lines+
      (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).visits+1≤
        524290+524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q))+1 by omega)
  dsimp only
  refine ⟨hreader.1,hreader.2.1,?_⟩
  change (coefficientSourceBits modulus decoded bound).clock+
    (SemiprimeBitIndexFactors.scanCoefficientsBits modulus decoded bound
      (coefficientSourceBits modulus decoded bound).stream.points).clock+4≤_
  omega

/-- Every successful constructed reader is a checked proper divisor on
arbitrary input words, independently of collision or source premises. -/
theorem constructedFactorBits_sound {modulus decoded bound divisor : List Bool}
    (h : (constructedFactorBits modulus decoded bound).scan.factor=some divisor) :
    ProperDivisor (bitValue modulus) (bitValue divisor) :=
  SemiprimeBitIndexFactors.scanCoefficientsBits_sound h

/-- Actual decoder and optional fully constructed source/reader handoff. -/
structure MarkedConstructedWordReport where
  /-- Full actual decoder, retaining its computed GCD and unit decision. -/
  decoder : SemiprimeBitInverse.MarkedBitsReport
  /-- Full acquired source and reader, only after actual decoder acceptance. -/
  reader : Option ConstructedFactorWordReport
  /-- Actual checked factor, absent after rejection or reader failure. -/
  factor : Option (List Bool)
  /-- Every decoder/source/reader primitive and actual outcome branch. -/
  clock : ℕ

/-- Feed the ACTUAL decoder output to the ACTUAL complete source and scan.
Rejected inverses retain diagnostics and construct no coefficient source. -/
def markedConstructedFactorBits (modulus target targetD baseD bound : List Bool) :
    MarkedConstructedWordReport :=
  let decoder := SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD
  match decoder.index with
  | none => ⟨decoder,none,none,decoder.clock+3⟩
  | some word =>
    let reader := constructedFactorBits modulus word bound
    ⟨decoder,some reader,reader.scan.factor,decoder.clock+reader.clock+4⟩

/-- Actual decoder acceptance installs precisely the fully acquired reader,
its factor result and the sum of every executed stage clock. -/
theorem markedConstructedFactorBits_at_index {modulus target targetD baseD bound word : List Bool}
    (hword : (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index=some word) :
    (markedConstructedFactorBits modulus target targetD baseD bound).reader=
        some (constructedFactorBits modulus word bound) ∧
      (markedConstructedFactorBits modulus target targetD baseD bound).factor=
        (constructedFactorBits modulus word bound).scan.factor ∧
      (markedConstructedFactorBits modulus target targetD baseD bound).clock=
        (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).clock+
          (constructedFactorBits modulus word bound).clock+4 := by
  simp only [markedConstructedFactorBits,hword]
  trivial

/-- Every full marked-stage success is checked proper, on all word inputs. -/
theorem markedConstructedFactorBits_sound {modulus target targetD baseD bound divisor : List Bool}
    (h : (markedConstructedFactorBits modulus target targetD baseD bound).factor=some divisor) :
    ProperDivisor (bitValue modulus) (bitValue divisor) := by
  cases hx : (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index with
  | none => simp only [markedConstructedFactorBits,hx] at h; cases h
  | some word =>
    rw [(markedConstructedFactorBits_at_index (bound:=bound) hx).2.1] at h
    exact constructedFactorBits_sound h

/-- Acquired original marked jets now drive an actual decoder, fully acquired
original coefficient stream and successful reader. Complete construction is
charged; no private decoded residue, encoded source or callback is supplied. -/
theorem public_marked_constructed_factor {p q k l W : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p<q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (modulus target targetD baseD bound : List Bool)
    (hmodulus : bitValue modulus=p*q)
    (hbound : bitValue bound=SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (alpha x : (ZMod (bitValue modulus))ˣ)
    (hx : (bitValue target : ZMod (bitValue modulus))=(x : ZMod (bitValue modulus)))
    (hD : (bitValue targetD : ZMod (bitValue modulus))=
      SemiprimeIntervalJet.targetDerivative
        (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) (bitValue bound))
    (hE : (bitValue baseD : ZMod (bitValue modulus))=
      SemiprimeIntervalJet.baseDerivative
        (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) (bitValue bound))
    (denom : (ZMod (bitValue modulus))ˣ)
    (hdenom : (denom : ZMod (bitValue modulus))=
      (x : ZMod (bitValue modulus))*SemiprimeIntervalJet.targetDerivative
        (alpha : ZMod (bitValue modulus)) (x : ZMod (bitValue modulus)) (bitValue bound))
    (hk : k<bitValue bound) (hl : l<bitValue bound) (hLp : bitValue bound≤p) (hkl : k≠l)
    (hP : ZMod.castHom (hmodulus.symm ▸ dvd_mul_right p q) (ZMod p)
        (x : ZMod (bitValue modulus))=
      (ZMod.castHom (hmodulus.symm ▸ dvd_mul_right p q) (ZMod p)
        (alpha : ZMod (bitValue modulus)))^k)
    (hQ : ZMod.castHom (hmodulus.symm ▸ dvd_mul_left q p) (ZMod q)
        (x : ZMod (bitValue modulus))=
      (ZMod.castHom (hmodulus.symm ▸ dvd_mul_left q p) (ZMod q)
        (alpha : ZMod (bitValue modulus)))^l)
    (hmWidth : modulus.length≤W) (hxWidth : target.length≤W)
    (hDWidth : targetD.length≤W) (hEWidth : baseD.length≤W) (hbWidth : bound.length≤W) :
    let V := 524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q))
    let K := 22528*(W+1)
    ∃ word, (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index=some word ∧
      (markedConstructedFactorBits modulus target targetD baseD bound).reader=
        some (constructedFactorBits modulus word bound) ∧
      (∃ divisor, (markedConstructedFactorBits modulus target targetD baseD bound).factor=some divisor ∧
        ProperDivisor (bitValue modulus) (bitValue divisor)) ∧
      (constructedFactorBits modulus word bound).scan.gcdCalls≤1 ∧
      (markedConstructedFactorBits modulus target targetD baseD bound).clock≤
        2005000*(W+1)^3+(524290+V+1)*(20000000000*(W+1)^2)+
          V*(20000*(K+1)^2+9)+625000*(K+1)^3+9 := by
  have hN : 0<bitValue modulus := by rw [hmodulus]; exact Nat.mul_pos hp.pos hq.pos
  obtain ⟨word,hword,hpr⟩ := SemiprimeBitInverse.decodeMarkedBits_at_local_root hN
    (ZMod.castHom (hmodulus.symm ▸ dvd_mul_right p q) (ZMod p))
    target targetD baseD alpha x (bitValue bound) hx hD hE denom hdenom hk hP
  obtain ⟨word',hword',hqr⟩ := SemiprimeBitInverse.decodeMarkedBits_at_local_root hN
    (ZMod.castHom (hmodulus.symm ▸ dvd_mul_left q p) (ZMod q))
    target targetD baseD alpha x (bitValue bound) hx hD hE denom hdenom hl hQ
  have he : word=word' := Option.some.inj (hword.symm.trans hword')
  rw [←he] at hqr
  have hsP : (bitValue word : ZMod p)=(k : ZMod p) := by simpa only [map_natCast] using hpr
  have hsQ : (bitValue word : ZMod q)=(l : ZMod q) := by simpa only [map_natCast] using hqr
  have hs := SemiprimeBitIndexFactors.marked_word_canonical hN hword
  have hwordWidth : word.length≤W :=
    (SemiprimeBitIndexFactors.marked_word_width hN hword).le.trans hmWidth
  have hreader := public_constructed_factor hp hq hpq hB modulus word bound
    hmodulus hs hbound hk hl hLp hkl hsP hsQ hmWidth hwordWidth hbWidth
  have hdecoder := SemiprimeBitInverse.decodeMarkedBits_cost hN hmWidth hxWidth hDWidth hEWidth
  have hinstall := markedConstructedFactorBits_at_index (bound:=bound) hword
  dsimp only
  refine ⟨word,hword,hinstall.1,?_,hreader.2.1,?_⟩
  · obtain ⟨divisor,hfactor,hproper⟩ := hreader.1
    exact ⟨divisor,hinstall.2.1.trans hfactor,hproper⟩
  · rw [hinstall.2.2]
    have hreaderClock := hreader.2.2
    omega

end RiemannGaussian.SemiprimeBitIndexTraversal
