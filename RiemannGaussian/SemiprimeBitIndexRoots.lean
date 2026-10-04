/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSeedLazyJets
import RiemannGaussian.SemiprimeBitPrimeScan

/-!
# Boolean restoring roots for original index coefficients

The restoring square-root data path reads physical Boolean digit pairs and
uses the existing full-borrow circuit. Its mathematical natural evaluation
is a specification, never an output-producing arithmetic call. All high
zero padding is processed and charged. Original coefficient construction,
signed enumeration, source serialization and whole factorizer costs remain
separate obligations.
-/

namespace RiemannGaussian.SemiprimeBitIndexRoots

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitPrimeScan
open SemiprimeIndexReader SemiprimeWindowSqrt

/-- Actual root and remainder words, executed bit clock and bit-cell writes. -/
structure BitSqrtReport where
  /-- Computed little-endian root, retaining physical high zero padding. -/
  root : List Bool
  /-- Computed little-endian square remainder. -/
  remainder : List Bool
  /-- All gates, bit reads/writes and constructor/Boolean tests. -/
  clock : ℕ
  /-- Every new bit-list cell, including discarded comparison differences. -/
  writes : ℕ
  /-- Actual restoring digit-pair steps, including high zero pairs. -/
  steps : ℕ

/-- Restore a literal low/high input digit pair. The expanded remainder
and trial use two newly written cells each; the output root uses one.
One full-borrow subtraction computes both the comparison and difference.
Its complete clock is charged even when its output difference is discarded. -/
def sqrtStep (low high : Bool) (child : BitSqrtReport) : BitSqrtReport :=
  let expanded := low::high::child.remainder
  let trial := true::false::child.root
  let difference := subBits expanded trial false
  let clock := child.clock+bitCost difference.result+6
  let writes := child.writes+difference.result.writes+5
  if difference.borrow=true then
    ⟨false::child.root,expanded,clock,writes,child.steps+1⟩
  else
    ⟨true::child.root,difference.result.bits,clock,writes,child.steps+1⟩

/-- Read all actual input pairs from the most significant end by structural
recursion on the supplied little-endian word. An odd final input bit uses
literal false as its high digit. Pair inspection charges two reads and two
list tests; the odd branch charges one read and two tests. -/
def sqrtBits : List Bool → BitSqrtReport
  | [] => ⟨[],[],1,0,0⟩
  | [low] =>
    let report := sqrtStep low false ⟨[],[],0,0,0⟩
    ⟨report.root,report.remainder,report.clock+3,report.writes,report.steps⟩
  | low::high::tail =>
    let report := sqrtStep low high (sqrtBits tail)
    ⟨report.root,report.remainder,report.clock+4,report.writes,report.steps⟩

/-- A literal input pair's natural value lies between zero and three. -/
theorem digitPair_bound (low high : Bool) : bitNat low+2*bitNat high≤3 := by
  cases low <;> cases high <;> decide

/-- Every Boolean restoring step preserves the original square/remainder
equation and the strict gap below the next root square. No natural square
root, quotient, comparison or subtraction computes a branch or output. -/
theorem sqrtStep_invariant (low high : Bool) (child : BitSqrtReport)
    (hgap : bitValue child.remainder≤2*bitValue child.root) :
    (bitValue (sqrtStep low high child).root)^2+
        bitValue (sqrtStep low high child).remainder=
      4*((bitValue child.root)^2+bitValue child.remainder)+bitNat low+2*bitNat high ∧
      bitValue (sqrtStep low high child).remainder≤
        2*bitValue (sqrtStep low high child).root := by
  have hcompare := subBits_borrow_iff (low::high::child.remainder)
    (true::false::child.root) false
  simp only [bitValue,bitNat,if_true,Bool.false_eq_true,if_false,
    Nat.add_zero,Nat.zero_add] at hcompare
  have hdigit := digitPair_bound low high
  simp only [bitNat] at hdigit
  by_cases hb : (subBits (low::high::child.remainder)
      (true::false::child.root) false).borrow=true
  · have hless := hcompare.mp hb
    simp only [sqrtStep,if_pos hb,bitValue,bitNat,Bool.false_eq_true,if_false,Nat.zero_add]
    constructor <;> nlinarith
  · have hfalse : (subBits (low::high::child.remainder)
        (true::false::child.root) false).borrow=false := by
      cases he : (subBits (low::high::child.remainder)
        (true::false::child.root) false).borrow with
      | false => rfl
      | true => exact False.elim (hb he)
    have hge : bitValue (true::false::child.root)≤bitValue (low::high::child.remainder) := by
      by_contra hn
      exact hb (hcompare.mpr (by simpa only [bitValue,bitNat,if_true,Bool.false_eq_true,
        if_false,Nat.add_zero,Nat.zero_add] using (show
          bitValue (low::high::child.remainder)<bitValue (true::false::child.root) by omega)))
    have hdiff := subBits_difference hfalse
    have he := Nat.sub_add_cancel hge
    simp only [bitValue,bitNat,if_true,Bool.false_eq_true,if_false,
      Nat.zero_add] at hdiff he
    simp only [sqrtStep,if_neg hb,bitValue,bitNat,if_true]
    constructor <;> nlinarith

/-- The complete actual Boolean run computes the original input's square
remainder and maximal integer root, including zero and padded zero words. -/
theorem sqrtBits_invariant (bits : List Bool) :
    (bitValue (sqrtBits bits).root)^2+bitValue (sqrtBits bits).remainder=bitValue bits ∧
      bitValue (sqrtBits bits).remainder≤2*bitValue (sqrtBits bits).root := by
  induction bits using sqrtBits.induct with
  | case1 => exact ⟨rfl,Nat.le_refl _⟩
  | case2 low =>
    have h := sqrtStep_invariant low false ⟨[],[],0,0,0⟩ (by decide)
    simpa [sqrtBits,bitValue,bitNat] using h
  | case3 low high tail ih =>
    have h := sqrtStep_invariant low high (sqrtBits tail) ih.2
    rw [ih.1] at h
    change (bitValue (sqrtStep low high (sqrtBits tail)).root)^2+
      bitValue (sqrtStep low high (sqrtBits tail)).remainder=
        bitNat low+2*(bitNat high+2*bitValue tail) ∧ _
    exact ⟨by nlinarith [h.1],h.2⟩

/-- Every computed Boolean root equals the mathematical integer square root. -/
theorem sqrtBits_correct (bits : List Bool) :
    bitValue (sqrtBits bits).root=Nat.sqrt (bitValue bits) := by
  obtain ⟨he,hgap⟩ := sqrtBits_invariant bits
  apply Nat.eq_sqrt'.mpr
  constructor <;> nlinarith

/-- Boolean root and remainder values preserve both original native
restoring outputs; physical high-zero processing may execute more frames. -/
theorem sqrtBits_native_outputs (bits : List Bool) :
    bitValue (sqrtBits bits).root=(countedSqrt (bitValue bits)).root ∧
      bitValue (sqrtBits bits).remainder=(countedSqrt (bitValue bits)).remainder := by
  obtain ⟨he,_⟩ := sqrtBits_invariant bits
  rw [sqrtBits_correct] at he
  exact ⟨(sqrtBits_correct bits).trans (countedSqrt_correct _).symm,
    by rw [countedSqrt_remainder]; omega⟩

/-- A restoring step constructs one root cell and keeps the actual
expanded or full-width difference remainder; zero padding is not trimmed. -/
theorem sqrtStep_widths (low high : Bool) (child : BitSqrtReport) :
    (sqrtStep low high child).root.length=child.root.length+1 ∧
      (sqrtStep low high child).remainder.length≤
        max child.root.length child.remainder.length+2 := by
  have hw := (subBits_counts (low::high::child.remainder)
    (true::false::child.root) false).2.2.2.2
  unfold sqrtStep
  dsimp only
  split <;> dsimp only [List.length_cons] at hw ⊢ <;> omega

/-- The actual root width is the executed pair count, and the physically
processed pair count includes every supplied high zero. -/
theorem sqrtBits_counts (bits : List Bool) :
    (sqrtBits bits).root.length=(sqrtBits bits).steps ∧
      (sqrtBits bits).steps=(bits.length+1)/2 := by
  induction bits using sqrtBits.induct with
  | case1 => simp only [sqrtBits,List.length_nil]; decide
  | case2 low =>
    have hw := (sqrtStep_widths low false ⟨[],[],0,0,0⟩).1
    have hs : (sqrtStep low false ⟨[],[],0,0,0⟩).steps=1 := by
      unfold sqrtStep
      dsimp only
      split <;> rfl
    change (sqrtStep low false ⟨[],[],0,0,0⟩).root.length=
      (sqrtStep low false ⟨[],[],0,0,0⟩).steps ∧
      (sqrtStep low false ⟨[],[],0,0,0⟩).steps=(1+1)/2
    rw [hs]
    exact ⟨hw,by decide⟩
  | case3 low high tail ih =>
    have hw := (sqrtStep_widths low high (sqrtBits tail)).1
    have hs : (sqrtStep low high (sqrtBits tail)).steps=(sqrtBits tail).steps+1 := by
      unfold sqrtStep
      dsimp only
      split <;> rfl
    change (sqrtStep low high (sqrtBits tail)).root.length=
      (sqrtStep low high (sqrtBits tail)).steps ∧
      (sqrtStep low high (sqrtBits tail)).steps=(tail.length+2+1)/2
    rw [hw,hs,ih.1,ih.2]
    exact ⟨rfl,by omega⟩

/-- Both actual output words remain bounded by physical input width,
including all intermediate comparison padding. -/
theorem sqrtBits_widths (bits : List Bool) :
    (sqrtBits bits).root.length≤bits.length ∧
      (sqrtBits bits).remainder.length≤bits.length+1 := by
  induction bits using sqrtBits.induct with
  | case1 => simp only [sqrtBits,List.length_nil,Nat.zero_le,and_self]
  | case2 low =>
    have hw := sqrtStep_widths low false ⟨[],[],0,0,0⟩
    change (sqrtStep low false ⟨[],[],0,0,0⟩).root.length≤1 ∧
      (sqrtStep low false ⟨[],[],0,0,0⟩).remainder.length≤2
    simpa only [List.length_nil,Nat.zero_add,Nat.max_self] using ⟨hw.1.le,hw.2⟩
  | case3 low high tail ih =>
    have hw := sqrtStep_widths low high (sqrtBits tail)
    change (sqrtStep low high (sqrtBits tail)).root.length≤tail.length+2 ∧
      (sqrtStep low high (sqrtBits tail)).remainder.length≤tail.length+2+1
    constructor
    · omega
    · have hm := max_le (ih.1.trans (Nat.le_succ _)) ih.2
      omega

/-- Complete step cost, including subtraction work on both padded words,
four shift cells, one root cell and the executed borrow branch. -/
theorem sqrtStep_cost (low high : Bool) (child : BitSqrtReport) :
    (sqrtStep low high child).clock≤child.clock+
      12*max child.root.length child.remainder.length+32 := by
  have hc := subBits_cost (low::high::child.remainder) (true::false::child.root) false
  unfold sqrtStep
  dsimp only
  split <;> dsimp only [List.length_cons] at hc ⊢ <;> omega

/-- All created bit-list cells, including discarded differences, are
included in the executed primitive clock. -/
theorem sqrtBits_writes_le_clock (bits : List Bool) :
    (sqrtBits bits).writes≤(sqrtBits bits).clock := by
  have hstep (low high : Bool) (child : BitSqrtReport)
      (hchild : child.writes≤child.clock) :
      (sqrtStep low high child).writes≤(sqrtStep low high child).clock := by
    unfold sqrtStep
    dsimp only
    split <;> dsimp only [bitCost] <;> omega
  induction bits using sqrtBits.induct with
  | case1 => decide
  | case2 low =>
    have h := hstep low false ⟨[],[],0,0,0⟩ (by decide)
    change (sqrtStep low false ⟨[],[],0,0,0⟩).writes≤
      (sqrtStep low false ⟨[],[],0,0,0⟩).clock+3
    omega
  | case3 low high tail ih =>
    have h := hstep low high (sqrtBits tail) ih
    change (sqrtStep low high (sqrtBits tail)).writes≤
      (sqrtStep low high (sqrtBits tail)).clock+4
    omega

/-- Fully charged restoring square root has quadratic bit work in the
physical input length. Natural clock arithmetic is instrumentation only. -/
theorem sqrtBits_cost (bits : List Bool) :
    (sqrtBits bits).clock≤20*(bits.length+1)^2 := by
  induction bits using sqrtBits.induct with
  | case1 => decide
  | case2 low =>
    have hc := sqrtStep_cost low false ⟨[],[],0,0,0⟩
    change (sqrtStep low false ⟨[],[],0,0,0⟩).clock+3≤80
    simp only [List.length_nil,Nat.zero_add,Nat.max_self,Nat.mul_zero] at hc
    omega
  | case3 low high tail ih =>
    have hw := sqrtBits_widths tail
    have hm : max (sqrtBits tail).root.length (sqrtBits tail).remainder.length≤tail.length+1 :=
      max_le (by omega) hw.2
    have hc := sqrtStep_cost low high (sqrtBits tail)
    have hh := Nat.mul_le_mul_left 12 hm
    change (sqrtStep low high (sqrtBits tail)).clock+4≤20*(tail.length+2+1)^2
    nlinarith

/-- Borrow false expresses the exact non-strict reverse comparison,
including unequal widths and arbitrary high zero padding. -/
theorem subBits_borrow_false (left right : List Bool) :
    (subBits left right false).borrow=false ↔ bitValue right≤bitValue left := by
  have h := subBits_borrow_iff left right false
  simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at h
  constructor
  · intro hb
    by_contra! hless
    have ht := h.mpr hless
    rw [hb] at ht
    cases ht
  · intro hge
    cases hb : (subBits left right false).borrow with
    | false => rfl
    | true => have ht := h.mp hb; omega

/-- One inspected low digit and its shared tail, with every inspection paid. -/
structure LowBitReport where
  /-- Actual low digit, or literal false for an empty word. -/
  low : Bool
  /-- Actual shared tail, computing division by two without a quotient call. -/
  rest : List Bool
  /-- One list test and, on a nonempty word, one actual bit-cell read. -/
  clock : ℕ

/-- Inspect one low cell; neither a native quotient nor a copied tail is used. -/
def cutLowBit : List Bool → LowBitReport
  | [] => ⟨false,[],1⟩
  | low::tail => ⟨low,tail,2⟩

/-- The shared tail has the exact mathematical quotient by two. -/
theorem cutLowBit_value (bits : List Bool) :
    bitValue (cutLowBit bits).rest=bitValue bits/2 := by
  cases bits with
  | nil => rfl
  | cons low tail => cases low <;> simp [cutLowBit,bitValue,bitNat,Nat.add_div]

/-- The inspected low bit is false exactly for an even original word. -/
theorem cutLowBit_even (bits : List Bool) :
    (cutLowBit bits).low=false ↔ bitValue bits%2=0 := by
  cases bits with
  | nil => simp only [cutLowBit,bitValue,Nat.zero_mod,iff_self]
  | cons low tail => cases low <;> simp [cutLowBit,bitValue,bitNat,Nat.add_mod]

/-- Every root-halving inspection has a fixed paid primitive cost. -/
theorem cutLowBit_cost (bits : List Bool) : (cutLowBit bits).clock≤2 := by
  cases bits <;> norm_num [cutLowBit]

/-- Both inspected output fields preserve the exact physical source tail. -/
theorem cutLowBit_length (bits : List Bool) :
    (cutLowBit bits).rest.length≤bits.length := by
  cases bits <;> simp only [cutLowBit,List.length_nil,List.length_cons,Nat.le_refl,
    Nat.le_succ]

/-- Rich checked root words, including both pre-check ordered candidates. -/
structure RootCheckReport where
  /-- Descending root candidate computed from the original sum word. -/
  high : List Bool
  /-- Ascending root candidate computed from the original difference word. -/
  low : List Bool
  /-- Seven original conditions evaluated using Boolean circuits. -/
  accepted : Bool
  /-- Both original candidate words, only when all conditions pass. -/
  roots : Option (List Bool×List Bool)
  /-- Every scalar arithmetic, comparison, parity and output branch cost. -/
  clock : ℕ
  /-- All created bit-list cells, including discarded check differences. -/
  writes : ℕ

/-- Check every condition of the original integer-root reader using the
supplied coefficient/bound words and computed root word. No natural value,
ordering, product or parity call computes any output. Failed conditions
still pay the composed scalar circuits and retain both candidate words. -/
def checkRootWords (bound a b delta root : List Bool) : RootCheckReport :=
  let square := mulBits root root
  let perfect := orderWords square.bits delta
  let sum := addBits a root false
  let difference := subBits a root false
  let high := cutLowBit sum.bits
  let low := cutLowBit difference.result.bits
  let highBound := subBits high.rest bound false
  let lowBound := subBits low.rest bound false
  let pairSum := addBits high.rest low.rest false
  let sumCheck := orderWords pairSum.bits a
  let pairProduct := mulBits high.rest low.rest
  let productCheck := orderWords pairProduct.bits b
  let accepted := perfect.equal && !difference.borrow && !high.low &&
    highBound.borrow && lowBound.borrow && sumCheck.equal && productCheck.equal
  let roots := if accepted=true then some (high.rest,low.rest) else none
  ⟨high.rest,low.rest,accepted,roots,
    bitCost square+perfect.clock+bitCost sum+bitCost difference.result+
      high.clock+low.clock+bitCost highBound.result+bitCost lowBound.result+
      bitCost pairSum+sumCheck.clock+bitCost pairProduct+productCheck.clock+20,
    square.writes+perfect.difference.result.writes+sum.writes+difference.result.writes+
      highBound.result.writes+lowBound.result.writes+pairSum.writes+
      sumCheck.difference.result.writes+pairProduct.writes+productCheck.difference.result.writes⟩

/-- Mathematical specification of the original seven scalar conditions.
This specification never computes the Boolean reader's branch or result. -/
abbrev originalRootCondition (L a b delta r : ℕ) : Prop :=
  r^2=delta ∧ r≤a ∧ (a+r)%2=0 ∧ (a+r)/2<L ∧ (a-r)/2<L ∧
    (a+r)/2+(a-r)/2=a ∧ ((a+r)/2)*((a-r)/2)=b

/-- All seven Boolean conditions preserve the original integer-root
condition exactly, including underflow and arbitrary padded word widths. -/
theorem checkRootWords_condition (bound a b delta root : List Bool) :
    (checkRootWords bound a b delta root).accepted=true ↔
      originalRootCondition (bitValue bound) (bitValue a) (bitValue b)
        (bitValue delta) (bitValue root) := by
  by_cases hb : (subBits a root false).borrow=false
  · have hd := subBits_difference hb
    have hge := (subBits_borrow_false a root).mp hb
    simp only [checkRootWords,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,
      hb,orderWords_equal,cutLowBit_even,cutLowBit_value,subBits_borrow_iff,
      addBits_correct,mulBits_correct,hd,bitNat,Bool.false_eq_true,if_false,
      Nat.add_zero,originalRootCondition,pow_two,hge,true_and]
    simp only [and_true,and_assoc]
  · have hge : ¬bitValue root≤bitValue a := by
      intro h
      exact hb ((subBits_borrow_false a root).mpr h)
    simp only [checkRootWords,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,hb,Bool.true_eq_false,
      originalRootCondition,hge,and_false,false_and]

/-- Ordered accepted words evaluate to the original native root formulas. -/
theorem checkRootWords_roots (bound a b delta root : List Bool) :
    (checkRootWords bound a b delta root).roots.map
        (fun pair => (bitValue pair.1,bitValue pair.2))=
      if originalRootCondition (bitValue bound) (bitValue a) (bitValue b)
          (bitValue delta) (bitValue root) then
        some ((bitValue a+bitValue root)/2,(bitValue a-bitValue root)/2)
      else none := by
  have hc := checkRootWords_condition bound a b delta root
  by_cases h : (checkRootWords bound a b delta root).accepted=true
  · have hp := hc.mp h
    have hb := (subBits_borrow_false a root).mpr hp.2.1
    have hd := subBits_difference hb
    change (if (checkRootWords bound a b delta root).accepted=true then
      some ((checkRootWords bound a b delta root).high,
        (checkRootWords bound a b delta root).low) else none).map _=_
    rw [if_pos h,if_pos hp]
    simp only [Option.map_some,checkRootWords,
      cutLowBit_value,addBits_correct,hd,bitNat,Bool.false_eq_true,if_false,Nat.add_zero]
  · have hp : ¬originalRootCondition (bitValue bound) (bitValue a) (bitValue b)
        (bitValue delta) (bitValue root) := fun hh => h (hc.mpr hh)
    change (if (checkRootWords bound a b delta root).accepted=true then
      some ((cutLowBit (addBits a root false).bits).rest,
        (cutLowBit (subBits a root false).result.bits).rest) else none).map _=_
    rw [if_neg h,if_neg hp,Option.map_none]

/-- Original coefficient words, actual optional restoring run and checked
root pair, with all scalar execution and bit-list allocations charged. -/
structure RootWordReport where
  /-- Retained original interval bound word. -/
  bound : List Bool
  /-- Retained original sum coefficient word. -/
  sumCoefficient : List Bool
  /-- Retained original product coefficient word. -/
  productCoefficient : List Bool
  /-- Actual Boolean restoring run; absent if the discriminant underflows. -/
  squareRoot : Option BitSqrtReport
  /-- Descending/ascending pair only after all original checks. -/
  roots : Option (List Bool×List Bool)
  /-- Full scalar primitive clock, including unsuccessful paths. -/
  clock : ℕ
  /-- All created bit-list cells, including discarded comparisons. -/
  writes : ℕ

/-- Execute the complete original unsigned coefficient root reader.
Construct the discriminant with Boolean multiplication and a paid two-cell
shift of the original product coefficient. Its borrow decides underflow
before square-root acquisition. The accepted pair uses all original checks. -/
def readIntegerRootsBits (bound a b : List Bool) : RootWordReport :=
  let square := mulBits a a
  let fourB := false::false::b
  let delta := subBits square.bits fourB false
  if delta.borrow=true then
    ⟨bound,a,b,none,none,bitCost square+bitCost delta.result+3,
      square.writes+delta.result.writes+2⟩
  else
    let root := sqrtBits delta.result.bits
    let check := checkRootWords bound a b delta.result.bits root.root
    ⟨bound,a,b,some root,check.roots,
      bitCost square+bitCost delta.result+root.clock+check.clock+3,
      square.writes+delta.result.writes+root.writes+check.writes+2⟩

/-- Original coefficient and interval words survive every reader branch. -/
theorem readIntegerRootsBits_source (bound a b : List Bool) :
    (readIntegerRootsBits bound a b).bound=bound ∧
      (readIntegerRootsBits bound a b).sumCoefficient=a ∧
      (readIntegerRootsBits bound a b).productCoefficient=b := by
  unfold readIntegerRootsBits
  dsimp only
  split <;> exact ⟨rfl,rfl,rfl⟩

/-- Full original native root reading is refined by actual Boolean words,
for all unsigned coefficient inputs, not only genuine root examples.
No serialization or signed-enumerator cost is supplied by this equality. -/
theorem readIntegerRootsBits_exact (bound a b : List Bool) :
    (readIntegerRootsBits bound a b).roots.map
        (fun pair => (bitValue pair.1,bitValue pair.2))=
      (readIntegerRoots (bitValue bound) ((bitValue a : ℤ),(bitValue b : ℤ))).roots := by
  have hsign : 0≤(bitValue a : ℤ) ∧ 0≤(bitValue b : ℤ) := ⟨by positivity,by positivity⟩
  have hc := subBits_borrow_iff (mulBits a a).bits (false::false::b) false
  simp only [mulBits_correct,bitValue,bitNat,Bool.false_eq_true,if_false,
    Nat.zero_add,Nat.add_zero,←pow_two] at hc
  by_cases hb : (subBits (mulBits a a).bits (false::false::b) false).borrow=true
  · have hsmall := hc.mp hb
    have hbad : ¬4*bitValue b≤(bitValue a)^2 := by omega
    simp only [readIntegerRootsBits,if_pos hb,Option.map_none,readIntegerRoots,
      if_pos hsign,Int.toNat_natCast,if_neg hbad]
  · have hfalse : (subBits (mulBits a a).bits (false::false::b) false).borrow=false := by
      cases he : (subBits (mulBits a a).bits (false::false::b) false).borrow with
      | false => rfl
      | true => exact False.elim (hb he)
    have hge : 4*bitValue b≤(bitValue a)^2 := by
      by_contra hn
      exact hb (hc.mpr (by omega))
    have hd := subBits_difference hfalse
    simp only [mulBits_correct,bitValue,bitNat,Bool.false_eq_true,if_false,
      Nat.zero_add,←pow_two] at hd
    have hfour : 2*(2*bitValue b)=4*bitValue b := by omega
    rw [hfour] at hd
    have hr := sqrtBits_correct (subBits (mulBits a a).bits (false::false::b) false).result.bits
    rw [hd] at hr
    simp only [readIntegerRootsBits,if_neg hb,checkRootWords_roots,hd,hr,
      readIntegerRoots,if_pos hsign,Int.toNat_natCast,if_pos hge,countedSqrt_correct,
      originalRootCondition]

/-- Every accepted Boolean pair satisfies the original short bounds and
both coefficient equations. Rejected words cannot fabricate a short pair. -/
theorem readIntegerRootsBits_sound {bound a b i j : List Bool}
    (h : (readIntegerRootsBits bound a b).roots=some (i,j)) :
    bitValue i<bitValue bound ∧ bitValue j<bitValue bound ∧
      bitValue i+bitValue j=bitValue a ∧ bitValue i*bitValue j=bitValue b := by
  have he := readIntegerRootsBits_exact bound a b
  rw [h,Option.map_some] at he
  obtain ⟨hi,hj,ha,hb⟩ := readIntegerRoots_sound he.symm
  dsimp only at ha hb
  refine ⟨hi,hj,?_,?_⟩
  · have hh : bitValue a=bitValue i+bitValue j := by exact_mod_cast ha
    exact hh.symm
  · have hh : bitValue b=bitValue i*bitValue j := by exact_mod_cast hb
    exact hh.symm

/-- Every original short sum/product pair is accepted in one of the two
retained descending root orientations, including zero and repeated indices. -/
theorem readIntegerRootsBits_genuine {bound a b : List Bool} {k l : ℕ}
    (hk : k<bitValue bound) (hl : l<bitValue bound)
    (ha : bitValue a=k+l) (hb : bitValue b=k*l) :
    (readIntegerRootsBits bound a b).roots.map
        (fun pair => (bitValue pair.1,bitValue pair.2))=some (l,k) ∨
      (readIntegerRootsBits bound a b).roots.map
        (fun pair => (bitValue pair.1,bitValue pair.2))=some (k,l) := by
  rw [readIntegerRootsBits_exact,ha,hb,Nat.cast_add,Nat.cast_mul]
  exact readIntegerRoots_pair hk hl

/-- Both pre-check candidate words have their actual physical widths
bounded by the original sum and root input widths. -/
theorem checkRootWords_widths (bound a b delta root : List Bool) :
    (checkRootWords bound a b delta root).high.length≤max a.length root.length+1 ∧
      (checkRootWords bound a b delta root).low.length≤max a.length root.length := by
  have hh := (cutLowBit_length (addBits a root false).bits).trans
    (addBits_counts a root false).2.2.2.2
  have hl := cutLowBit_length (subBits a root false).result.bits
  rw [(subBits_counts a root false).2.2.2.2] at hl
  exact ⟨hh,hl⟩

/-- Every check's allocated bit-list cell is included in its actual clock. -/
theorem checkRootWords_writes_le_clock (bound a b delta root : List Bool) :
    (checkRootWords bound a b delta root).writes≤
      (checkRootWords bound a b delta root).clock := by
  dsimp only [checkRootWords,orderWords,bitCost]
  omega

/-- All seven original root checks have quadratic charged bit cost in
physical input width; products and comparisons are not treated as unit work. -/
theorem checkRootWords_cost {W : ℕ} {bound a b delta root : List Bool}
    (hbound : bound.length≤W) (ha : a.length≤W) (hb : b.length≤W)
    (hdelta : delta.length≤W) (hr : root.length≤W) :
    (checkRootWords bound a b delta root).clock≤1000*(W+1)^2 := by
  have hsquare := bounded_mulBits hr hr
  have hperfect := orderWords_cost (W:=3*(W+1)) (by omega : (mulBits root root).bits.length≤3*(W+1))
    (by omega : delta.length≤3*(W+1))
  have hsum := bounded_addBits ha hr false
  have hdwidth : (subBits a root false).result.bits.length≤W := by
    rw [(subBits_counts a root false).2.2.2.2]
    exact max_le ha hr
  have hd := subBits_cost a root false
  have hmax : max a.length root.length≤W := max_le ha hr
  have hh : (cutLowBit (addBits a root false).bits).rest.length≤W+1 :=
    (cutLowBit_length _).trans hsum.2
  have hl : (cutLowBit (subBits a root false).result.bits).rest.length≤W :=
    (cutLowBit_length _).trans hdwidth
  have hhigh := cutLowBit_cost (addBits a root false).bits
  have hlow := cutLowBit_cost (subBits a root false).result.bits
  have hhbound := subBits_cost (cutLowBit (addBits a root false).bits).rest bound false
  have hlbound := subBits_cost (cutLowBit (subBits a root false).result.bits).rest bound false
  have hhb : max (cutLowBit (addBits a root false).bits).rest.length bound.length≤W+1 :=
    max_le hh (by omega)
  have hlb : max (cutLowBit (subBits a root false).result.bits).rest.length bound.length≤W :=
    max_le hl hbound
  have hpairSum := bounded_addBits hh (hl.trans (Nat.le_succ _)) false
  have hsumCheck := orderWords_cost (W:=W+2) hpairSum.2 (by omega : a.length≤W+2)
  have hpairProduct := bounded_mulBits hh (hl.trans (Nat.le_succ _))
  have hproductCheck := orderWords_cost (W:=3*(W+1)) hpairProduct.2
    (by omega : b.length≤3*(W+1))
  dsimp only [checkRootWords]
  nlinarith [hsquare.1,hsum.1,hpairSum.1,hpairProduct.1]

/-- Every complete reader bit allocation is included even on underflow
or failed candidate checks. Output references do not copy supplied words. -/
theorem readIntegerRootsBits_writes_le_clock (bound a b : List Bool) :
    (readIntegerRootsBits bound a b).writes≤(readIntegerRootsBits bound a b).clock := by
  have hs := sqrtBits_writes_le_clock (subBits (mulBits a a).bits (false::false::b) false).result.bits
  have hc := checkRootWords_writes_le_clock bound a b
    (subBits (mulBits a a).bits (false::false::b) false).result.bits
    (sqrtBits (subBits (mulBits a a).bits (false::false::b) false).result.bits).root
  unfold readIntegerRootsBits
  dsimp only
  split <;> dsimp only [bitCost] <;> omega

/-- The entire unsigned coefficient root reader, including discriminant
construction, restoring square root and all original validation conditions,
has a quadratic charged bit bound in physical coefficient/bound width. -/
theorem readIntegerRootsBits_cost {W : ℕ} {bound a b : List Bool}
    (hbound : bound.length≤W) (ha : a.length≤W) (hb : b.length≤W) :
    (readIntegerRootsBits bound a b).clock≤20000*(W+1)^2 := by
  have hsquare := bounded_mulBits ha ha
  have hdwidth : (subBits (mulBits a a).bits (false::false::b) false).result.bits.length≤3*(W+1) := by
    rw [(subBits_counts (mulBits a a).bits (false::false::b) false).2.2.2.2]
    apply max_le
    · omega
    · dsimp only [List.length_cons]
      omega
  have hrootWidth := (sqrtBits_widths
    (subBits (mulBits a a).bits (false::false::b) false).result.bits).1.trans hdwidth
  have hrootCost := (sqrtBits_cost
    (subBits (mulBits a a).bits (false::false::b) false).result.bits).trans
    (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (Nat.succ_le_succ hdwidth) 2))
  have hcheckCost := checkRootWords_cost (W:=3*(W+1)) (by omega : bound.length≤3*(W+1))
    (by omega : a.length≤3*(W+1)) (by omega : b.length≤3*(W+1)) hdwidth hrootWidth
  have hdelta := subBits_cost (mulBits a a).bits (false::false::b) false
  have hm : max (mulBits a a).bits.length (false::false::b).length≤3*(W+1) := by
    rw [←(subBits_counts (mulBits a a).bits (false::false::b) false).2.2.2.2]
    exact hdwidth
  unfold readIntegerRootsBits
  dsimp only
  split <;> nlinarith [hsquare.1]

/-- Accepted roots preserve physically bounded words as well as bounded
natural values; high zeros are not silently normalized for the cost proof. -/
theorem readIntegerRootsBits_width {W : ℕ} {bound a b i j : List Bool}
    (ha : a.length≤W) (hb : b.length≤W)
    (h : (readIntegerRootsBits bound a b).roots=some (i,j)) :
    i.length≤3*(W+1)+1 ∧ j.length≤3*(W+1) := by
  have hsquare := (bounded_mulBits ha ha).2
  have hd : (subBits (mulBits a a).bits (false::false::b) false).result.bits.length≤3*(W+1) := by
    rw [(subBits_counts (mulBits a a).bits (false::false::b) false).2.2.2.2]
    apply max_le
    · omega
    · dsimp only [List.length_cons]
      omega
  have hr := (sqrtBits_widths
    (subBits (mulBits a a).bits (false::false::b) false).result.bits).1.trans hd
  have hc := checkRootWords_widths bound a b
    (subBits (mulBits a a).bits (false::false::b) false).result.bits
    (sqrtBits (subBits (mulBits a a).bits (false::false::b) false).result.bits).root
  unfold readIntegerRootsBits at h
  dsimp only at h
  split at h
  · cases h
  · dsimp only [checkRootWords] at h
    split at h
    · cases h
      dsimp only [checkRootWords] at hc
      constructor <;> omega
    · cases h

/-- Every actual coefficient report, together with complete batch clocks. -/
structure RootBatchReport where
  /-- Original order and all successful or rejected word readers. -/
  entries : List RootWordReport
  /-- Scalar clocks plus each batch list test and output reference cell. -/
  clock : ℕ
  /-- Every scalar bit-list allocation, including failed checks. -/
  writes : ℕ

/-- Execute all encoded coefficient root checks in their original order.
Batching does not pool roots, change original coefficients or drop rejects. -/
def readRootWordsBatch (bound : List Bool) : List (List Bool×List Bool) → RootBatchReport
  | [] => ⟨[],1,0⟩
  | pair::tail =>
    let here := readIntegerRootsBits bound pair.1 pair.2
    let child := readRootWordsBatch bound tail
    ⟨here::child.entries,here.clock+child.clock+2,here.writes+child.writes⟩

/-- Every original coefficient word pair survives the executed batch,
including each failed reader and every original input occurrence. -/
theorem readRootWordsBatch_source (bound : List Bool) (pairs : List (List Bool×List Bool)) :
    (readRootWordsBatch bound pairs).entries.map
      (fun report => (report.sumCoefficient,report.productCoefficient))=pairs := by
  induction pairs with
  | nil => rfl
  | cons pair tail ih =>
    obtain ⟨_,ha,hb⟩ := readIntegerRootsBits_source bound pair.1 pair.2
    simp only [readRootWordsBatch,List.map_cons,ha,hb,ih,Prod.mk.eta]

/-- Complete Boolean root outcomes preserve the original native outcomes
point by point, with the same ordered sum/product source. -/
theorem readRootWordsBatch_exact (bound : List Bool) (pairs : List (List Bool×List Bool)) :
    (readRootWordsBatch bound pairs).entries.map (fun report =>
        report.roots.map (fun roots => (bitValue roots.1,bitValue roots.2)))=
      pairs.map (fun pair => (readIntegerRoots (bitValue bound)
        ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ))).roots) := by
  induction pairs with
  | nil => rfl
  | cons pair tail ih =>
    simp only [readRootWordsBatch,List.map_cons,readIntegerRootsBits_exact,ih]

/-- Total batch bit-list construction is bounded by its charged clock. -/
theorem readRootWordsBatch_writes_le_clock (bound : List Bool)
    (pairs : List (List Bool×List Bool)) :
    (readRootWordsBatch bound pairs).writes≤(readRootWordsBatch bound pairs).clock := by
  induction pairs with
  | nil => exact Nat.zero_le _
  | cons pair tail ih =>
    have hh := readIntegerRootsBits_writes_le_clock bound pair.1 pair.2
    dsimp only [readRootWordsBatch]
    omega

/-- The whole executed root batch has linear-many fully charged scalar
bit clocks, with every supplied physical word width included. -/
theorem readRootWordsBatch_cost {W : ℕ} (bound : List Bool)
    (pairs : List (List Bool×List Bool)) (hbound : bound.length≤W)
    (hwords : ∀ pair∈pairs, pair.1.length≤W ∧ pair.2.length≤W) :
    (readRootWordsBatch bound pairs).clock≤pairs.length*(20000*(W+1)^2+2)+1 := by
  induction pairs with
  | nil => simp only [readRootWordsBatch,List.length_nil,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | cons pair tail ih =>
    have hh := hwords pair List.mem_cons_self
    have hc := readIntegerRootsBits_cost hbound hh.1 hh.2
    have ht := ih (fun pair hp => hwords pair (List.mem_cons_of_mem _ hp))
    dsimp only [readRootWordsBatch,List.length_cons]
    nlinarith

/-- Exact encoding of the original executed mixed-index enumeration
retains a genuine accepted original root pair in the Boolean batch. The
encoding premise identifies source words, not supplied successful roots. -/
theorem encoded_enumeration_genuine {p q s k l : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p≠q) (bound : List Bool) (pairs : List (List Bool×List Bool))
    (hk : k<bitValue bound) (hl : l<bitValue bound)
    (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q))
    (hencoding : pairs.map (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ)))=
      (SemiprimeIndexEnumeration.enumerateCoefficients (p*q) s (bitValue bound)).points) :
    some (l,k)∈(readRootWordsBatch bound pairs).entries.map (fun report =>
        report.roots.map (fun roots => (bitValue roots.1,bitValue roots.2))) ∨
      some (k,l)∈(readRootWordsBatch bound pairs).entries.map (fun report =>
        report.roots.map (fun roots => (bitValue roots.1,bitValue roots.2))) := by
  have hpresent := SemiprimeIndexEnumeration.mixed_index_genuine_point_visited
    hp hq hpq hk hl hP hQ
  rw [←hencoding] at hpresent
  obtain ⟨pair,hpair,he⟩ := List.mem_map.mp hpresent
  have hroots : (readIntegerRoots (bitValue bound)
        ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ))).roots=some (l,k) ∨
      (readIntegerRoots (bitValue bound)
        ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ))).roots=some (k,l) := by
    rw [he]
    exact readIntegerRoots_pair hk hl
  rw [readRootWordsBatch_exact]
  rcases hroots with hroots | hroots
  · exact Or.inl (List.mem_map.mpr ⟨pair,hpair,hroots⟩)
  · exact Or.inr (List.mem_map.mpr ⟨pair,hpair,hroots⟩)

/-- The actual public mixed-index enumeration supports a linear root
batch with a complete quadratic scalar bit clock and total bit allocation
bound, conditional on its exact, physically bounded source encoding.
Acquiring and serializing that source are still separate costs. -/
theorem public_encoded_root_batch_cost {p q k l s W : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≤q)
    (hB : 4≤SemiprimeLehmanCoverage.sixthWidth (p*q))
    (bound : List Bool) (pairs : List (List Bool×List Bool))
    (hbound : bitValue bound=SemiprimeSeedSumAcquisition.seedLength
      (SemiprimeEuclidRowBudget.publicRowModulus (p*q)))
    (hk : k<bitValue bound) (hl : l<bitValue bound) (hLp : bitValue bound≤p)
    (hkl : k≠l) (hP : (s : ZMod p)=(k : ZMod p)) (hQ : (s : ZMod q)=(l : ZMod q))
    (hencoding : pairs.map (fun pair => ((bitValue pair.1 : ℤ),(bitValue pair.2 : ℤ)))=
      (SemiprimeIndexEnumeration.enumerateCoefficients (p*q) s (bitValue bound)).points)
    (hwidth : bound.length≤W) (hwords : ∀ pair∈pairs, pair.1.length≤W ∧ pair.2.length≤W) :
    (readRootWordsBatch bound pairs).clock≤
        (524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)))*
          (20000*(W+1)^2+2)+1 ∧
      (readRootWordsBatch bound pairs).writes≤
        (524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)))*
          (20000*(W+1)^2+2)+1 := by
  have hc := SemiprimeIndexEnumeration.public_mixed_index_enumeration_counts
    hp hq hpq hB (hbound ▸ hk) (hbound ▸ hl) (hbound ▸ hLp) hkl hP hQ
  have he := congrArg List.length hencoding
  simp only [List.length_map] at he
  have hn : pairs.length≤524290*(3+6144*SemiprimeLehmanCoverage.sixthWidth (p*q)) := by
    rw [he,(SemiprimeIndexEnumeration.enumerateCoefficients_counts
      (p*q) s (bitValue bound)).1,hbound]
    exact hc.2
  have hcost := (readRootWordsBatch_cost bound pairs hwidth hwords).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right (20000*(W+1)^2+2) hn) 1)
  exact ⟨hcost,(readRootWordsBatch_writes_le_clock bound pairs).trans hcost⟩

end RiemannGaussian.SemiprimeBitIndexRoots
