/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitIndexBasis

/-!
# Boolean signed clipping of original index-basis lines

Signed magnitudes retain every physical input bit. Borrow arithmetic,
sign flags and restoring division compute the original inclusive clipping
bounds. Mathematical integer interpretation is specification only. Actual
coordinate/point emission, acquisition and full machine/memory costs remain
separate obligations.
-/

namespace RiemannGaussian.SemiprimeBitIndexClipping

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitPrimeScan
open SemiprimeBitIndexRoots SemiprimeIndexEnumeration

/-- Original signed magnitude, allowing both encodings of zero. -/
structure SignedWord where
  /-- Boolean sign; true means negation of the unsigned magnitude. -/
  negative : Bool
  /-- Actual little-endian word, including its supplied high-zero padding. -/
  magnitude : List Bool

/-- Mathematical signed interpretation; executable word paths never call it. -/
abbrev SignedWord.value (word : SignedWord) : ℤ :=
  if word.negative=true then -(bitValue word.magnitude : ℤ) else bitValue word.magnitude

/-- Toggle the actual sign flag, sharing the original physical magnitude.
Every caller includes the one NOT gate in its own clock. -/
def negateWord (word : SignedWord) : SignedWord := ⟨!word.negative,word.magnitude⟩

/-- Sign toggling is exact even for the two zero encodings. -/
theorem negateWord_value (word : SignedWord) : (negateWord word).value= -word.value := by
  cases word with
  | mk negative magnitude => cases negative <;> simp [negateWord,SignedWord.value]

/-- Sign toggling preserves the actual physical input word. -/
theorem negateWord_magnitude (word : SignedWord) : (negateWord word).magnitude=word.magnitude := rfl

/-- Actual signed sum and all executed unsigned diagnostics. -/
structure SignedSumReport where
  /-- The actual addition, only when the two signs agree. -/
  addition : Option BitReport
  /-- First full subtraction when the signs differ. -/
  difference : Option SubReport
  /-- Reverse full subtraction, only after first underflow. -/
  reverse : Option SubReport
  /-- Computed signed magnitude, with no native integer output. -/
  word : SignedWord
  /-- All arithmetic, sign decisions and retained diagnostics. -/
  clock : ℕ

/-- Same signs add magnitudes. Opposite signs subtract in the original
orientation, reversing after actual borrow; failed first work remains paid. -/
def addSignedBits (left right : SignedWord) : SignedSumReport :=
  if left.negative=right.negative then
    let addition := addBits left.magnitude right.magnitude false
    ⟨some addition,none,none,⟨left.negative,addition.bits⟩,bitCost addition+4⟩
  else
    let difference := subBits left.magnitude right.magnitude false
    if difference.borrow=true then
      let reverse := subBits right.magnitude left.magnitude false
      ⟨none,some difference,some reverse,⟨right.negative,reverse.result.bits⟩,
        bitCost difference.result+bitCost reverse.result+8⟩
    else
      ⟨none,some difference,none,⟨left.negative,difference.result.bits⟩,
        bitCost difference.result+6⟩

/-- The signed sum preserves exact integer addition on arbitrary padded
words, including cancellation and either sign representation of zero. -/
theorem addSignedBits_value (left right : SignedWord) :
    (addSignedBits left right).word.value=left.value+right.value := by
  have ha := addBits_correct left.magnitude right.magnitude false
  simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at ha
  have hb := subBits_borrow_iff left.magnitude right.magnitude false
  simp only [bitNat,Bool.false_eq_true,if_false,Nat.add_zero] at hb
  by_cases hs : left.negative=right.negative
  · unfold addSignedBits
    rw [if_pos hs]
    dsimp only [SignedWord.value]
    rw [ha]
    rw [←hs]
    split <;> push_cast <;> ring
  · by_cases hc : (subBits left.magnitude right.magnitude false).borrow=true
    · have hl := hb.mp hc
      have hr : (subBits right.magnitude left.magnitude false).borrow=false :=
        (subBits_borrow_false _ _).mpr hl.le
      have hd := subBits_difference hr
      have hv : ((bitValue left.magnitude : ℤ)+(bitValue right.magnitude-bitValue left.magnitude : ℕ))=
          bitValue right.magnitude := by omega
      unfold addSignedBits
      rw [if_neg hs,if_pos hc]
      dsimp only [SignedWord.value]
      rw [hd]
      cases hn : left.negative <;> cases hm : right.negative <;>
        simp only [hn,hm,Bool.false_eq_true,reduceIte] at hs ⊢ <;> first | exact False.elim (hs (by trivial)) | omega
    · have hr : (subBits left.magnitude right.magnitude false).borrow=false := by
        cases hh : (subBits left.magnitude right.magnitude false).borrow with
        | false => rfl
        | true => exact False.elim (hc hh)
      have hle := (subBits_borrow_false _ _).mp hr
      have hd := subBits_difference hr
      have hv : ((bitValue right.magnitude : ℤ)+(bitValue left.magnitude-bitValue right.magnitude : ℕ))=
          bitValue left.magnitude := by omega
      unfold addSignedBits
      rw [if_neg hs,if_neg hc]
      dsimp only [SignedWord.value]
      rw [hd]
      cases hn : left.negative <;> cases hm : right.negative <;>
        simp only [hn,hm,Bool.false_eq_true,reduceIte] at hs ⊢ <;> first | exact False.elim (hs (by trivial)) | omega

/-- Every signed sum pays full physical arithmetic and grows width at
most one cell. Failed opposite-sign subtraction is included. -/
theorem addSignedBits_cost_width {W : ℕ} {left right : SignedWord}
    (hl : left.magnitude.length≤W) (hr : right.magnitude.length≤W) :
    (addSignedBits left right).clock≤40*(W+1) ∧
      (addSignedBits left right).word.magnitude.length≤W+1 := by
  have ha := bounded_addBits hl hr false
  have hd := subBits_cost left.magnitude right.magnitude false
  have hdw := (subBits_counts left.magnitude right.magnitude false).2.2.2.2
  have hb := subBits_cost right.magnitude left.magnitude false
  have hbw := (subBits_counts right.magnitude left.magnitude false).2.2.2.2
  unfold addSignedBits
  dsimp only
  split
  · dsimp only
    constructor <;> omega
  · split <;> dsimp only <;> constructor <;> omega

/-- Exact signed subtraction pays its actual sign NOT before addition. -/
def subSignedBits (left right : SignedWord) : SignedSumReport :=
  let child := addSignedBits left (negateWord right)
  {child with clock := child.clock+1}

/-- Signed subtraction preserves the original integer operation. -/
theorem subSignedBits_value (left right : SignedWord) :
    (subSignedBits left right).word.value=left.value-right.value := by
  rw [subSignedBits,addSignedBits_value,negateWord_value,sub_eq_add_neg]

/-- Subtraction's full clock and physical output include its sign gate. -/
theorem subSignedBits_cost_width {W : ℕ} {left right : SignedWord}
    (hl : left.magnitude.length≤W) (hr : right.magnitude.length≤W) :
    (subSignedBits left right).clock≤41*(W+1) ∧
      (subSignedBits left right).word.magnitude.length≤W+1 := by
  have hc := addSignedBits_cost_width (left:=left) (right:=negateWord right) hl hr
  dsimp only [subSignedBits]
  exact ⟨by omega,hc.2⟩

/-- Actual unsigned product and its computed signed output. -/
structure SignedProductReport where
  /-- Full Boolean multiplication report, including every intermediate write. -/
  product : BitReport
  /-- Magnitude is the computed product; sign is the actual XOR. -/
  word : SignedWord
  /-- Full multiplication, XOR gate and retained output decisions. -/
  clock : ℕ

/-- Compute signed multiplication with the existing Boolean circuit. -/
def mulSignedBits (left right : SignedWord) : SignedProductReport :=
  let product := mulBits left.magnitude right.magnitude
  ⟨product,⟨Bool.xor left.negative right.negative,product.bits⟩,bitCost product+3⟩

/-- Arbitrary signed magnitudes multiply exactly, including signed zeros. -/
theorem mulSignedBits_value (left right : SignedWord) :
    (mulSignedBits left right).word.value=left.value*right.value := by
  unfold mulSignedBits
  dsimp only [SignedWord.value]
  rw [mulBits_correct]
  cases hn : left.negative <;> cases hm : right.negative <;>
    simp only [Bool.xor_false,Bool.xor_true,Bool.false_eq_true,reduceIte,
      Bool.not_false,Bool.not_true] <;> push_cast <;> ring

/-- Complete signed multiplication remains quadratic in physical width. -/
theorem mulSignedBits_cost_width {W : ℕ} {left right : SignedWord}
    (hl : left.magnitude.length≤W) (hr : right.magnitude.length≤W) :
    (mulSignedBits left right).clock≤24*(W+1)^2+4 ∧
      (mulSignedBits left right).word.magnitude.length≤3*W := by
  have hc := bounded_mulBits hl hr
  dsimp only [mulSignedBits]
  exact ⟨by omega,hc.2⟩

/-- Both unsigned borrow comparisons and zero diagnostics for signed order. -/
structure SignedOrderReport where
  /-- right magnitude minus left, recognizing the nonnegative-sign order. -/
  forward : SubReport
  /-- left magnitude minus right, recognizing the reversed negative order. -/
  backward : SubReport
  /-- Actual full scans, required to treat both signed zeros equally. -/
  leftNonzero : NonzeroReport
  /-- The original right magnitude's actual full nonzero scan. -/
  rightNonzero : NonzeroReport
  /-- Computed signed less-or-equal flag. -/
  le : Bool
  /-- All comparisons, full scans, sign gates and decisions. -/
  clock : ℕ

/-- Compare arbitrary signed magnitudes, explicitly retaining the zero
test on the positive-left/negative-right branch. No integer order is called. -/
def leSignedBits (left right : SignedWord) : SignedOrderReport :=
  let forward := subBits right.magnitude left.magnitude false
  let backward := subBits left.magnitude right.magnitude false
  let leftNonzero := nonzeroBits left.magnitude
  let rightNonzero := nonzeroBits right.magnitude
  let le := if left.negative=true then
      if right.negative=true then !backward.borrow else true
    else if right.negative=true then !leftNonzero.nonzero && !rightNonzero.nonzero
    else !forward.borrow
  ⟨forward,backward,leftNonzero,rightNonzero,le,
    bitCost forward.result+bitCost backward.result+leftNonzero.clock+rightNonzero.clock+8⟩

/-- Signed comparison is exact on every representation, including negative
zero and physically padded words. -/
theorem leSignedBits_exact (left right : SignedWord) :
    (leSignedBits left right).le=true ↔ left.value≤right.value := by
  have hf := subBits_borrow_false right.magnitude left.magnitude
  have hb := subBits_borrow_false left.magnitude right.magnitude
  cases hn : left.negative with
  | false =>
    cases hm : right.negative with
    | false =>
      simp only [leSignedBits,SignedWord.value,hn,hm,Bool.false_eq_true,reduceIte,
        Bool.not_eq,Bool.not_eq_true,hf]
      omega
    | true =>
      simp only [leSignedBits,SignedWord.value,hn,hm,Bool.false_eq_true,reduceIte,
        Bool.and_eq_true,Bool.not_eq,Bool.not_eq_true,nonzeroBits_false_iff]
      omega
  | true =>
    cases hm : right.negative with
    | false =>
      simp only [leSignedBits,SignedWord.value,hn,hm,Bool.false_eq_true,reduceIte]
      constructor
      · intro _
        omega
      · intro _
        trivial
    | true =>
      simp only [leSignedBits,SignedWord.value,hn,hm,reduceIte,Bool.not_eq,Bool.not_eq_true,hb]
      omega

/-- Every signed order operation includes both complete borrows and scans. -/
theorem leSignedBits_cost {W : ℕ} {left right : SignedWord}
    (hl : left.magnitude.length≤W) (hr : right.magnitude.length≤W) :
    (leSignedBits left right).clock≤40*(W+1) := by
  have hf := subBits_cost right.magnitude left.magnitude false
  have hb := subBits_cost left.magnitude right.magnitude false
  have hz0 := nonzeroBits_cost left.magnitude
  have hz1 := nonzeroBits_cost right.magnitude
  dsimp only [leSignedBits]
  omega

/-- Actual restoring division is physically bounded even at denominator
zero, where it retains the original dividend as the remainder. -/
theorem divideBits_all_width (xs ys : List Bool) :
    (divideBits xs ys).quotient.length≤xs.length ∧
      (divideBits xs ys).remainder.length≤max xs.length ys.length := by
  by_cases hb : (nonzeroBits ys).nonzero=true
  · have hw := divideBits_widths (xs:=xs) ((nonzeroBits_correct ys).mp hb)
    exact ⟨hw.2.le,hw.1.le.trans (Nat.le_max_right _ _)⟩
  · simp only [divideBits,if_neg hb,List.length_nil]
    exact ⟨Nat.zero_le _,Nat.le_max_left _ _⟩

/-- The arithmetic correction for negative floor division by a positive
unsigned denominator. Only the mathematical specification uses integers. -/
theorem negative_nat_floor (n d : ℕ) (hd : 0<d) :
    (-(n : ℤ))/(d : ℤ)=
      if n%d=0 then -((n/d : ℕ) : ℤ) else -((n/d+1 : ℕ) : ℤ) := by
  have hD : (0 : ℤ)<d := by exact_mod_cast hd
  have he : (n : ℤ)=(n%d : ℕ)+(d : ℤ)*(n/d : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n d).symm
  have hr : ((n%d : ℕ) : ℤ)<d := by exact_mod_cast Nat.mod_lt n hd
  by_cases hz : n%d=0
  · rw [if_pos hz,Int.ediv_eq_iff_of_pos hD]
    simp only [hz,Nat.cast_zero,zero_add] at he
    constructor <;> nlinarith
  · have hp : (0 : ℤ)<((n%d : ℕ) : ℤ) := by exact_mod_cast (show 0<n%d by omega)
    rw [if_neg hz,Int.ediv_eq_iff_of_pos hD]
    simp only [Nat.cast_add,Nat.cast_one]
    constructor <;> nlinarith

/-- Actual signed floor quotient, retaining full division and rounding work. -/
structure SignedFloorReport where
  /-- Full unsigned magnitude quotient/remainder circuit. -/
  division : DivisionReport
  /-- Actual divisor scan; denominator zero suppresses the correction. -/
  denominatorNonzero : NonzeroReport
  /-- Actual full remainder scan distinguishes exact divisibility. -/
  remainderNonzero : NonzeroReport
  /-- Executed quotient plus one; paid even when the output retains quotient. -/
  increment : BitReport
  /-- Computed signed floor word. -/
  word : SignedWord
  /-- All restoring work, both scans, increment, sign gates and decisions. -/
  clock : ℕ

/-- Negative nonintegral quotients round down by increasing the computed
magnitude. Both zero signs and zero denominators are handled by actual flags. -/
def floorSignedBits (numerator : SignedWord) (denominator : List Bool) : SignedFloorReport :=
  let division := divideBits numerator.magnitude denominator
  let denominatorNonzero := nonzeroBits denominator
  let remainderNonzero := nonzeroBits division.remainder
  let increment := addBits division.quotient [true] false
  let correction := numerator.negative && denominatorNonzero.nonzero && remainderNonzero.nonzero
  let word := ⟨numerator.negative,if correction=true then increment.bits else division.quotient⟩
  ⟨division,denominatorNonzero,remainderNonzero,increment,word,
    division.clock+denominatorNonzero.clock+remainderNonzero.clock+bitCost increment+8⟩

/-- The actual floor equals original integer Euclidean division for every
unsigned denominator word, including zero and arbitrary high-zero padding. -/
theorem floorSignedBits_value (numerator : SignedWord) (denominator : List Bool) :
    (floorSignedBits numerator denominator).word.value=
      numerator.value/(bitValue denominator : ℤ) := by
  have hq := (divideBits_correct numerator.magnitude denominator).1
  have hr := (divideBits_correct numerator.magnitude denominator).2
  have hi := addBits_correct (divideBits numerator.magnitude denominator).quotient [true] false
  simp only [bitValue,bitNat,if_true,Bool.false_eq_true,if_false,
    Nat.mul_zero,Nat.add_zero] at hi
  cases hn : numerator.negative
  · simp only [floorSignedBits,SignedWord.value,hn,Bool.false_and,Bool.false_eq_true,reduceIte]
    rw [hq,Int.natCast_ediv]
  · by_cases hD : 0<bitValue denominator
    · have hd := (nonzeroBits_correct denominator).mpr hD
      by_cases hR : bitValue numerator.magnitude%bitValue denominator=0
      · have hz := (nonzeroBits_false_iff (divideBits numerator.magnitude denominator).remainder).mpr
          (hr.trans hR)
        simp only [floorSignedBits,SignedWord.value,hn,hd,hz,Bool.true_and,Bool.and_false,
          Bool.false_eq_true,reduceIte]
        rw [hq,negative_nat_floor _ _ hD,if_pos hR]
      · have hp : 0<bitValue (divideBits numerator.magnitude denominator).remainder := by
          rw [hr]
          omega
        have hz := (nonzeroBits_correct _).mpr hp
        simp only [floorSignedBits,SignedWord.value,hn,hd,hz,Bool.true_and,reduceIte]
        rw [hi,hq,negative_nat_floor _ _ hD,if_neg hR]
    · have hzero : bitValue denominator=0 := by omega
      have hd := (nonzeroBits_false_iff denominator).mpr hzero
      simp only [floorSignedBits,SignedWord.value,hn,hd,Bool.and_false,Bool.false_and,
        Bool.false_eq_true,reduceIte]
      rw [hq,hzero,Nat.div_zero]
      simp only [Nat.cast_zero,Int.ediv_zero,neg_zero]

/-- Floor output and complete rounding clock stay physically bounded on
all inputs; the discarded increment is included. -/
theorem floorSignedBits_cost_width {W : ℕ} {numerator : SignedWord} {denominator : List Bool}
    (hn : numerator.magnitude.length≤W) (hd : denominator.length≤W) :
    (floorSignedBits numerator denominator).clock≤150*(W+1)^2 ∧
      (floorSignedBits numerator denominator).word.magnitude.length≤W+2 := by
  have hw := divideBits_all_width numerator.magnitude denominator
  have hq : (divideBits numerator.magnitude denominator).quotient.length≤W := hw.1.trans hn
  have hr : (divideBits numerator.magnitude denominator).remainder.length≤W := by omega
  have hdiv := bounded_divideBits (by omega : numerator.magnitude.length≤3*W) hd
  have hdn := nonzeroBits_cost denominator
  have hrn := nonzeroBits_cost (divideBits numerator.magnitude denominator).remainder
  have hadd := bounded_addBits (by omega : (divideBits numerator.magnitude denominator).quotient.length≤W+1)
    (by simp only [List.length_cons,List.length_nil]; omega : ([true] : List Bool).length≤W+1) false
  constructor
  · dsimp only [floorSignedBits]
    nlinarith [hadd.1]
  · unfold floorSignedBits
    dsimp only
    split <;> omega

/-- Actual floor on the negated input and the sign-toggled ceiling output. -/
structure SignedCeilReport where
  /-- Complete floor report, including actual quotient and rounding diagnostics. -/
  floor : SignedFloorReport
  /-- Computed signed ceiling word. -/
  word : SignedWord
  /-- Complete floor clock and the two actual sign NOT gates. -/
  clock : ℕ

/-- Construct ceiling by the original exact identity -floor(-a/d). -/
def ceilSignedBits (numerator : SignedWord) (denominator : List Bool) : SignedCeilReport :=
  let floor := floorSignedBits (negateWord numerator) denominator
  ⟨floor,negateWord floor.word,floor.clock+2⟩

/-- Actual ceiling preserves the original signed ceiling operation. -/
theorem ceilSignedBits_value (numerator : SignedWord) (denominator : List Bool) :
    (ceilSignedBits numerator denominator).word.value=
      ceilDivide numerator.value (bitValue denominator) := by
  dsimp only [ceilSignedBits]
  rw [negateWord_value,floorSignedBits_value,negateWord_value]
  rfl

/-- Ceiling's two sign gates and every floor primitive are included. -/
theorem ceilSignedBits_cost_width {W : ℕ} {numerator : SignedWord} {denominator : List Bool}
    (hn : numerator.magnitude.length≤W) (hd : denominator.length≤W) :
    (ceilSignedBits numerator denominator).clock≤160*(W+1)^2 ∧
      (ceilSignedBits numerator denominator).word.magnitude.length≤W+2 := by
  have hc := floorSignedBits_cost_width (numerator:=negateWord numerator) hn hd
  constructor
  · change (floorSignedBits (negateWord numerator) denominator).clock+2≤160*(W+1)^2
    nlinarith [hc.1]
  · exact hc.2

/-- Original inclusive signed bounds, retained as actual words. -/
structure WordInterval where
  /-- Actual lower endpoint word; it may be negative or zero. -/
  lower : SignedWord
  /-- Actual upper endpoint word, including impossible reversed bounds. -/
  upper : SignedWord

/-- Mathematical interpretation of original bounds, never a data-path call. -/
abbrev WordInterval.interpret (bounds : WordInterval) : IntegerInterval :=
  ⟨bounds.lower.value,bounds.upper.value⟩

/-- Original impossible [1,0] word bounds. The caller pays its one true cell. -/
def emptyWordInterval : WordInterval := ⟨⟨false,[true]⟩,⟨false,[]⟩⟩

/-- The literal impossible word interval preserves the original empty bounds. -/
theorem emptyWordInterval_value : emptyWordInterval.interpret=emptyInterval := rfl

/-- Both signed endpoint comparisons and the actually selected clipped bounds. -/
structure IntersectionWordReport where
  /-- Original lower endpoint order, used to select the signed maximum. -/
  lowerOrder : SignedOrderReport
  /-- Original upper endpoint order, used to select the signed minimum. -/
  upperOrder : SignedOrderReport
  /-- Selected original endpoint words, sharing their physical magnitudes. -/
  bounds : WordInterval
  /-- Both full signed comparisons and actual endpoint decisions. -/
  clock : ℕ

/-- Clip bounds before any coordinate list is constructed. Signed order
selects original endpoint words and does not serialize integer values. -/
def intersectIntervalsBits (first second : WordInterval) : IntersectionWordReport :=
  let lowerOrder := leSignedBits first.lower second.lower
  let upperOrder := leSignedBits first.upper second.upper
  let lower := if lowerOrder.le=true then second.lower else first.lower
  let upper := if upperOrder.le=true then first.upper else second.upper
  ⟨lowerOrder,upperOrder,⟨lower,upper⟩,lowerOrder.clock+upperOrder.clock+3⟩

/-- Actual endpoint selection preserves the full original signed intersection. -/
theorem intersectIntervalsBits_value (first second : WordInterval) :
    (intersectIntervalsBits first second).bounds.interpret=
      intersectInterval first.interpret second.interpret := by
  dsimp only [intersectIntervalsBits,WordInterval.interpret,intersectInterval,
    maxInteger,minInteger]
  split <;> split <;> simp_all only [leSignedBits_exact] <;> rfl

/-- Clipping pays both signed comparisons; selected physical endpoints
cannot exceed the original input widths. -/
theorem intersectIntervalsBits_cost_width {W : ℕ} {first second : WordInterval}
    (h0 : first.lower.magnitude.length≤W) (h1 : first.upper.magnitude.length≤W)
    (h2 : second.lower.magnitude.length≤W) (h3 : second.upper.magnitude.length≤W) :
    (intersectIntervalsBits first second).clock≤100*(W+1) ∧
      (intersectIntervalsBits first second).bounds.lower.magnitude.length≤W ∧
      (intersectIntervalsBits first second).bounds.upper.magnitude.length≤W := by
  have hlo := leSignedBits_cost h0 h2
  have hhi := leSignedBits_cost h1 h3
  constructor
  · dsimp only [intersectIntervalsBits]
    omega
  · unfold intersectIntervalsBits
    dsimp only
    constructor <;> split <;> omega

/-- Original offset differences and complete signed floor/ceiling reports. -/
structure PositiveLinearWordReport where
  /-- Actual lower-offset subtraction. -/
  lowerDifference : SignedSumReport
  /-- Actual upper-offset subtraction. -/
  upperDifference : SignedSumReport
  /-- Computed lower coordinate ceiling. -/
  lowerDivision : SignedCeilReport
  /-- Computed upper coordinate floor. -/
  upperDivision : SignedFloorReport
  /-- Original inclusive signed coordinate endpoints. -/
  bounds : WordInterval
  /-- Every subtraction, both rounded divisions and retained output decisions. -/
  clock : ℕ

/-- Compute the original positive-step coordinate bounds from actual
signed offsets. Rounding is performed by Boolean circuits on all words. -/
def positiveLinearBits (offset : SignedWord) (step : List Bool)
    (lower upper : SignedWord) : PositiveLinearWordReport :=
  let lo := subSignedBits lower offset
  let hi := subSignedBits upper offset
  let lowerDivision := ceilSignedBits lo.word step
  let upperDivision := floorSignedBits hi.word step
  ⟨lo,hi,lowerDivision,upperDivision,⟨lowerDivision.word,upperDivision.word⟩,
    lo.clock+hi.clock+lowerDivision.clock+upperDivision.clock+4⟩

/-- The actual signed coordinate bounds match the original floor/ceiling
construction for every denominator encoding, including zero. -/
theorem positiveLinearBits_value (offset : SignedWord) (step : List Bool)
    (lower upper : SignedWord) :
    (positiveLinearBits offset step lower upper).bounds.interpret=
      positiveLinearInterval offset.value (bitValue step) lower.value upper.value := by
  dsimp only [positiveLinearBits,WordInterval.interpret,positiveLinearInterval]
  apply congrArg₂ IntegerInterval.mk
  · rw [ceilSignedBits_value,subSignedBits_value]
  · rw [floorSignedBits_value,subSignedBits_value]

/-- Both coordinate divisions include negative rounding, discarded
increments and all original subtraction work in a quadratic physical clock. -/
theorem positiveLinearBits_cost_width {W : ℕ} {offset lower upper : SignedWord} {step : List Bool}
    (ho : offset.magnitude.length≤W) (hs : step.length≤W)
    (hl : lower.magnitude.length≤W) (hu : upper.magnitude.length≤W) :
    (positiveLinearBits offset step lower upper).clock≤1500*(W+1)^2 ∧
      (positiveLinearBits offset step lower upper).bounds.lower.magnitude.length≤W+3 ∧
      (positiveLinearBits offset step lower upper).bounds.upper.magnitude.length≤W+3 := by
  have hlo := subSignedBits_cost_width hl ho
  have hhi := subSignedBits_cost_width hu ho
  have hs' : step.length≤W+1 := by omega
  have hlower := ceilSignedBits_cost_width hlo.2 hs'
  have hupper := floorSignedBits_cost_width hhi.2 hs'
  dsimp only [positiveLinearBits]
  exact ⟨by nlinarith [hlo.1,hhi.1,hlower.1,hupper.1],hlower.2,hupper.2⟩

/-- Actual nonzero-step division/clipping or actual zero-step constant checks. -/
structure LinearClipWordReport where
  /-- Full original step-magnitude scan, recognizing both encodings of zero. -/
  stepNonzero : NonzeroReport
  /-- Exact rounded bounds, only for a nonzero signed step. -/
  positive : Option PositiveLinearWordReport
  /-- Actual original interval clipping, only after a nonzero step. -/
  intersection : Option IntersectionWordReport
  /-- Both actual constant-coordinate tests, only for a zero step. -/
  constantChecks : Option (SignedOrderReport×SignedOrderReport)
  /-- Final original inclusive signed bounds. -/
  bounds : WordInterval
  /-- Complete branch clock, including sign flips and literal empty bound. -/
  clock : ℕ

/-- Execute original signed line clipping before building any coordinates.
Negative steps negate offset/upper/lower and share the actual magnitude.
Zero steps request no rounded division and inspect both constant bounds. -/
def linearIntervalBits (offset step lower upper : SignedWord) (initial : WordInterval) :
    LinearClipWordReport :=
  let nonzero := nonzeroBits step.magnitude
  if nonzero.nonzero=true then
    if step.negative=true then
      let positive := positiveLinearBits (negateWord offset) step.magnitude
        (negateWord upper) (negateWord lower)
      let intersection := intersectIntervalsBits initial positive.bounds
      ⟨nonzero,some positive,some intersection,none,intersection.bounds,
        nonzero.clock+positive.clock+intersection.clock+7⟩
    else
      let positive := positiveLinearBits offset step.magnitude lower upper
      let intersection := intersectIntervalsBits initial positive.bounds
      ⟨nonzero,some positive,some intersection,none,intersection.bounds,
        nonzero.clock+positive.clock+intersection.clock+4⟩
  else
    let first := leSignedBits lower offset
    let second := leSignedBits offset upper
    let bounds := if (first.le && second.le)=true then initial else emptyWordInterval
    ⟨nonzero,none,none,some (first,second),bounds,nonzero.clock+first.clock+second.clock+6⟩

/-- Every original positive, negative and zero-step clipping outcome is
preserved exactly on arbitrary signed/padded words, with no canonicality
or valid-interval premise and no native integer branch in the data path. -/
theorem linearIntervalBits_value (offset step lower upper : SignedWord) (initial : WordInterval) :
    (linearIntervalBits offset step lower upper initial).bounds.interpret=
      linearInterval offset.value step.value lower.value upper.value initial.interpret := by
  by_cases hn : (nonzeroBits step.magnitude).nonzero=true
  · have hmag := (nonzeroBits_correct _).mp hn
    by_cases hs : step.negative=true
    · have hstep : step.value= -(bitValue step.magnitude : ℤ) := by
        simp only [SignedWord.value,if_pos hs]
      have hnegative : step.value<0 := by rw [hstep]; omega
      have hnotpositive : ¬0<step.value := by omega
      unfold linearIntervalBits
      rw [if_pos hn,if_pos hs]
      dsimp only
      rw [intersectIntervalsBits_value,positiveLinearBits_value,
        negateWord_value,negateWord_value,negateWord_value]
      unfold linearInterval
      rw [if_neg hnotpositive,if_pos hnegative,hstep,neg_neg]
    · have hstep : step.value=(bitValue step.magnitude : ℤ) := by
        simp only [SignedWord.value,if_neg hs]
      have hpositive : 0<step.value := by rw [hstep]; exact_mod_cast hmag
      unfold linearIntervalBits
      rw [if_pos hn,if_neg hs]
      dsimp only
      rw [intersectIntervalsBits_value,positiveLinearBits_value]
      unfold linearInterval
      rw [if_pos hpositive,hstep]
  · have hzero := (nonzeroBits_false_iff _).mp (Bool.eq_false_of_not_eq_true hn)
    have hstep : step.value=0 := by simp [SignedWord.value,hzero]
    by_cases hi : lower.value≤offset.value ∧ offset.value≤upper.value
    · have hc : ((leSignedBits lower offset).le && (leSignedBits offset upper).le)=true :=
        (Bool.and_eq_true _ _).mpr ⟨(leSignedBits_exact _ _).mpr hi.1,(leSignedBits_exact _ _).mpr hi.2⟩
      unfold linearIntervalBits
      rw [if_neg hn]
      dsimp only
      rw [if_pos hc]
      simp only [linearInterval,hstep,lt_self_iff_false,if_false,if_pos hi]
    · have hc : ¬((leSignedBits lower offset).le && (leSignedBits offset upper).le)=true := by
        intro h
        obtain ⟨h0,h1⟩ := (Bool.and_eq_true _ _).mp h
        exact hi ⟨(leSignedBits_exact _ _).mp h0,(leSignedBits_exact _ _).mp h1⟩
      unfold linearIntervalBits
      rw [if_neg hn]
      dsimp only
      rw [if_neg hc,emptyWordInterval_value]
      simp only [linearInterval,hstep,lt_self_iff_false,if_false,if_neg hi]

/-- Exact inclusive membership in the original clipped line, including
empty bounds and every constant-coordinate branch. This is a specification
of the bounds, not an implementation of coordinate-word emission. -/
theorem mem_linearIntervalBits (offset step lower upper : SignedWord)
    (initial : WordInterval) (i : ℤ) :
    i∈(linearIntervalBits offset step lower upper initial).bounds.interpret.entries ↔
      i∈initial.interpret.entries ∧ lower.value≤offset.value+i*step.value ∧
        offset.value+i*step.value≤upper.value := by
  rw [linearIntervalBits_value]
  exact mem_linearInterval _ _ _ _ _ _

/-- Full signed/zero-step clipping has quadratic physical bit work and
bounded output words. All comparisons, negative rounding, both zero-step
tests, sign gates and literal impossible bounds are included. -/
theorem linearIntervalBits_cost_width {W : ℕ} {offset step lower upper : SignedWord}
    {initial : WordInterval}
    (ho : offset.magnitude.length≤W) (hs : step.magnitude.length≤W)
    (hl : lower.magnitude.length≤W) (hu : upper.magnitude.length≤W)
    (hi0 : initial.lower.magnitude.length≤W) (hi1 : initial.upper.magnitude.length≤W) :
    (linearIntervalBits offset step lower upper initial).clock≤2000*(W+1)^2 ∧
      (linearIntervalBits offset step lower upper initial).bounds.lower.magnitude.length≤W+3 ∧
      (linearIntervalBits offset step lower upper initial).bounds.upper.magnitude.length≤W+3 := by
  have hbudget : 3*W+1+1500*(W+1)^2+100*(W+4)+7≤2000*(W+1)^2 := by
    nlinarith only []
  have hzeroBudget : 3*W+1+40*(W+1)+40*(W+1)+6≤2000*(W+1)^2 := by
    nlinarith only []
  have hp := positiveLinearBits_cost_width (offset:=offset) (step:=step.magnitude)
    (lower:=lower) (upper:=upper) ho hs hl hu
  have hn := positiveLinearBits_cost_width (offset:=negateWord offset) (step:=step.magnitude)
    (lower:=negateWord upper) (upper:=negateWord lower) ho hs hu hl
  have hi0' : initial.lower.magnitude.length≤W+3 := by omega
  have hi1' : initial.upper.magnitude.length≤W+3 := by omega
  have hpc := intersectIntervalsBits_cost_width (first:=initial)
    (second:=(positiveLinearBits offset step.magnitude lower upper).bounds)
    hi0' hi1' hp.2.1 hp.2.2
  have hnc := intersectIntervalsBits_cost_width (first:=initial)
    (second:=(positiveLinearBits (negateWord offset) step.magnitude
      (negateWord upper) (negateWord lower)).bounds) hi0' hi1' hn.2.1 hn.2.2
  have hz0 := leSignedBits_cost hl ho
  have hz1 := leSignedBits_cost ho hu
  have hz := nonzeroBits_cost step.magnitude
  unfold linearIntervalBits
  dsimp only
  split
  · split
    · dsimp only
      refine ⟨?_,hnc.2⟩
      omega
    · dsimp only
      refine ⟨?_,hpc.2⟩
      omega
  · dsimp only
    constructor
    · omega
    · split
      · exact ⟨by omega,by omega⟩
      · change ([true] : List Bool).length≤W+3 ∧ ([] : List Bool).length≤W+3
        simp only [List.length_cons,List.length_nil]
        exact ⟨by omega,by omega⟩

end RiemannGaussian.SemiprimeBitIndexClipping
