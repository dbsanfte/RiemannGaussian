/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitIndexClipping

/-!
# Boolean construction of the original signed index geometry

The computed early-Euclid basis supplies both signed vectors. Actual word
circuits construct the original rectangle extrema, determinant band, line
offsets and coefficient points, retaining the sign and affine origin.
Coordinate traversal, original jet acquisition and full machine/memory
composition remain separate obligations.
-/

namespace RiemannGaussian.SemiprimeBitIndexGeometry

open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitIndexBasis
open SemiprimeBitIndexClipping SemiprimeIndexLattice SemiprimeIndexEnumeration

/-- Share an actual unsigned word with the positive sign. Callers pay
their own constant sign and retained-field decisions. -/
def positiveWord (bits : List Bool) : SignedWord := ⟨false,bits⟩

/-- Original signed zero; its magnitude has no physical cells. -/
def zeroWord : SignedWord := positiveWord []

/-- Original signed one; each constructing caller pays its true cell. -/
def oneWord : SignedWord := positiveWord [true]

/-- Positive interpretation shares the original unsigned value. -/
theorem positiveWord_value (bits : List Bool) :
    (positiveWord bits).value=(bitValue bits : ℤ) := rfl

/-- The literal zero has its original integer interpretation. -/
theorem zeroWord_value : zeroWord.value=0 := rfl

/-- The literal one has its original integer interpretation. -/
theorem oneWord_value : oneWord.value=1 := rfl

/-- Both actual signed vectors projected from the computed basis report. -/
structure BasisWordsReport where
  /-- Original positive current coefficient word. -/
  coefficient : SignedWord
  /-- Original signed current remainder word. -/
  second : SignedWord
  /-- Original positive preceding coefficient word. -/
  previousCoefficient : SignedWord
  /-- Original opposite-signed preceding remainder word. -/
  companionSecond : SignedWord
  /-- Sign gate and retained-vector decisions. -/
  clock : ℕ

/-- Materialize both original signed vectors, sharing all four physical
magnitudes and paying the companion sign NOT. -/
def basisWordsBits (basis : BasisLoopWordReport) : BasisWordsReport :=
  ⟨positiveWord basis.coefficient,⟨basis.negative,basis.remainder⟩,
    positiveWord basis.previousCoefficient,⟨!basis.negative,basis.previousRemainder⟩,5⟩

/-- Every vector component preserves the actual original basis, including
either sign of a zero remainder and all high-zero padding. -/
theorem basisWordsBits_values (basis : BasisLoopWordReport) :
    (basisWordsBits basis).coefficient.value=(basis.interpret.coefficient : ℤ) ∧
      (basisWordsBits basis).second.value=basis.interpret.second ∧
      (basisWordsBits basis).previousCoefficient.value=(basis.interpret.previousCoefficient : ℤ) ∧
      (basisWordsBits basis).companionSecond.value=basis.interpret.companionSecond := by
  cases hn : basis.negative <;>
    simp [basisWordsBits,positiveWord,SignedWord.value,
      ShortRelationReport.second,ShortRelationReport.companionSecond,hn]

/-- Paid original rectangle powers, caps and affine origin. -/
structure RectangleWordReport where
  /-- Actual square of the supplied decoded residue word. -/
  squareS : BitReport
  /-- Actual square of the supplied interval bound word. -/
  squareL : BitReport
  /-- Original signed sum cap 2L-1, computed by full subtraction. -/
  sumLimit : SignedSumReport
  /-- Original signed product cap L²-1, computed by full subtraction. -/
  productLimit : SignedSumReport
  /-- Original lifted product cap s²+L²-1, computed by full addition. -/
  liftedProductLimit : SignedSumReport
  /-- Original negative affine origin -s², sharing the computed square. -/
  origin : SignedWord
  /-- Every power, cap, addition, literal cell and origin sign gate. -/
  clock : ℕ

/-- Compute the original rectangle data once from public words. Doubling
creates a paid false low cell; subtraction retains negative caps at L=0. -/
def rectangleBits (decoded bound : List Bool) : RectangleWordReport :=
  let squareS := mulBits decoded decoded
  let squareL := mulBits bound bound
  let sumLimit := subSignedBits (positiveWord (false::bound)) oneWord
  let productLimit := subSignedBits (positiveWord squareL.bits) oneWord
  let lifted := addSignedBits (positiveWord squareS.bits) productLimit.word
  ⟨squareS,squareL,sumLimit,productLimit,lifted,negateWord (positiveWord squareS.bits),
    bitCost squareS+bitCost squareL+sumLimit.clock+productLimit.clock+lifted.clock+6⟩

/-- Exact original powers, signed caps and affine origin on EVERY supplied
word, including L=0 and arbitrary high-zero padding. -/
theorem rectangleBits_values (decoded bound : List Bool) :
    bitValue (rectangleBits decoded bound).squareS.bits=(bitValue decoded)^2 ∧
      bitValue (rectangleBits decoded bound).squareL.bits=(bitValue bound)^2 ∧
      (rectangleBits decoded bound).sumLimit.word.value=2*(bitValue bound : ℤ)-1 ∧
      (rectangleBits decoded bound).productLimit.word.value=(bitValue bound : ℤ)^2-1 ∧
      (rectangleBits decoded bound).liftedProductLimit.word.value=
        (bitValue decoded : ℤ)^2+(bitValue bound : ℤ)^2-1 ∧
      (rectangleBits decoded bound).origin.value= -(bitValue decoded : ℤ)^2 := by
  simp only [rectangleBits,subSignedBits_value,addSignedBits_value,negateWord_value,
    positiveWord_value,oneWord_value,mulBits_correct,pow_two]
  simp only [bitValue,bitNat,Bool.false_eq_true,if_false,Nat.zero_add]
  push_cast
  constructor
  · trivial
  · constructor
    · trivial
    · constructor
      · rfl
      · constructor
        · rfl
        · constructor <;> ring

/-- Actual signed comparison splitting a word into its original zero extrema. -/
structure ZeroSplitWordReport where
  /-- Complete signed comparison with zero. -/
  order : SignedOrderReport
  /-- Actual minimum of zero and the original word. -/
  lower : SignedWord
  /-- Actual maximum of zero and the original word. -/
  upper : SignedWord
  /-- Full comparison and both retained endpoint decisions. -/
  clock : ℕ

/-- Select the original min/max with zero, without interpreting integers. -/
def splitZeroBits (word : SignedWord) : ZeroSplitWordReport :=
  let order := leSignedBits zeroWord word
  let lower := if order.le=true then zeroWord else word
  let upper := if order.le=true then word else zeroWord
  ⟨order,lower,upper,order.clock+3⟩

/-- Computed zero extrema preserve the original signed min/max. -/
theorem splitZeroBits_values (word : SignedWord) :
    (splitZeroBits word).lower.value=minInteger 0 word.value ∧
      (splitZeroBits word).upper.value=maxInteger 0 word.value := by
  dsimp only [splitZeroBits,minInteger,maxInteger]
  simp only [leSignedBits_exact,zeroWord_value]
  split <;> simp_all only [zeroWord_value] <;> trivial

/-- Complete computed determinant extrema and the rounded original band. -/
structure BandWordReport where
  /-- Both materialized original signed basis vectors. -/
  vectors : BasisWordsReport
  /-- Actual zero extrema of the negative short second coordinate. -/
  splitSecond : ZeroSplitWordReport
  /-- Original coefficient times s². -/
  lowerBase : SignedProductReport
  /-- Original coefficient times s²+L²-1. -/
  upperBase : SignedProductReport
  /-- Actual lower signed determinant correction. -/
  lowerCorrection : SignedProductReport
  /-- Actual upper signed determinant correction. -/
  upperCorrection : SignedProductReport
  /-- Full addition producing original lower determinant extremum. -/
  lower : SignedSumReport
  /-- Full addition producing original upper determinant extremum. -/
  upper : SignedSumReport
  /-- Original sign-oriented rounded coordinate band. -/
  division : PositiveLinearWordReport
  /-- Final inclusive original band endpoints. -/
  bounds : WordInterval
  /-- All vector signs, zero split, products, sums and rounded division. -/
  clock : ℕ

/-- Construct the actual signed determinant band from computed rectangle
and basis words. The original basis sign chooses its orientation. -/
def bandIntervalBits (modulus : List Bool) (rectangle : RectangleWordReport)
    (basis : BasisLoopWordReport) : BandWordReport :=
  let vectors := basisWordsBits basis
  let splitSecond := splitZeroBits (negateWord vectors.second)
  let lowerBase := mulSignedBits vectors.coefficient (positiveWord rectangle.squareS.bits)
  let upperBase := mulSignedBits vectors.coefficient rectangle.liftedProductLimit.word
  let lowerCorrection := mulSignedBits splitSecond.lower rectangle.sumLimit.word
  let upperCorrection := mulSignedBits splitSecond.upper rectangle.sumLimit.word
  let lower := addSignedBits lowerBase.word lowerCorrection.word
  let upper := addSignedBits upperBase.word upperCorrection.word
  let division := if basis.negative=true then
      positiveLinearBits zeroWord modulus lower.word upper.word
    else positiveLinearBits zeroWord modulus (negateWord upper.word) (negateWord lower.word)
  ⟨vectors,splitSecond,lowerBase,upperBase,lowerCorrection,upperCorrection,lower,upper,
    division,division.bounds,vectors.clock+splitSecond.clock+lowerBase.clock+upperBase.clock+
      lowerCorrection.clock+upperCorrection.clock+lower.clock+upper.clock+division.clock+
      (if basis.negative=true then 6 else 8)⟩

/-- Both computed determinant extrema equal the original formulas, with
their exact decoded origin and retained short-vector sign. -/
theorem bandIntervalBits_extrema (modulus decoded bound : List Bool)
    (basis : BasisLoopWordReport) :
    (bandIntervalBits modulus (rectangleBits decoded bound) basis).lower.word.value=
        rectangleDeterminantLower (bitValue decoded) (bitValue bound) basis.interpret ∧
      (bandIntervalBits modulus (rectangleBits decoded bound) basis).upper.word.value=
        rectangleDeterminantUpper (bitValue decoded) (bitValue bound) basis.interpret := by
  have hr := rectangleBits_values decoded bound
  have hb := basisWordsBits_values basis
  have hz := splitZeroBits_values (negateWord (basisWordsBits basis).second)
  rw [negateWord_value,hb.2.1] at hz
  dsimp only [bandIntervalBits]
  simp only [addSignedBits_value,mulSignedBits_value,positiveWord_value,hb.1,
    hr.1,hr.2.2.1,hr.2.2.2.2.1,hz.1,hz.2,
    rectangleDeterminantLower,rectangleDeterminantUpper,Nat.cast_pow]
  trivial

/-- Complete original band equality holds on every encoded input, even
zero modulus/interval words. Actual endpoint construction needs no oracle. -/
theorem bandIntervalBits_value (modulus decoded bound : List Bool)
    (basis : BasisLoopWordReport) :
    (bandIntervalBits modulus (rectangleBits decoded bound) basis).bounds.interpret=
      bandInterval (bitValue modulus) (bitValue decoded) (bitValue bound) basis.interpret := by
  have he := bandIntervalBits_extrema modulus decoded bound basis
  dsimp only [bandIntervalBits] at he
  unfold bandIntervalBits
  dsimp only
  split <;> rw [positiveLinearBits_value]
  · simp only [zeroWord_value,he.1,he.2,bandInterval,BasisLoopWordReport.interpret]
    rw [if_pos (by assumption)]
  · rw [negateWord_value,negateWord_value]
    simp only [zeroWord_value,he.1,he.2,bandInterval,BasisLoopWordReport.interpret]
    rw [if_neg (by assumption)]

/-- Every computed original offset and both stages of line clipping. -/
structure LineWordReport where
  /-- Materialized original signed basis vectors. -/
  vectors : BasisWordsReport
  /-- Actual first offset j times preceding coefficient. -/
  firstOffset : SignedProductReport
  /-- Exact first sum-coordinate floor/ceiling bounds. -/
  first : PositiveLinearWordReport
  /-- Actual j times signed companion second coordinate. -/
  secondProduct : SignedProductReport
  /-- Actual -s² plus the companion product. -/
  secondOffset : SignedSumReport
  /-- Full original signed product-coordinate clipping. -/
  clipping : LinearClipWordReport
  /-- Final inclusive line-coordinate endpoints. -/
  bounds : WordInterval
  /-- Both products, origin addition and every clipping primitive. -/
  clock : ℕ

/-- Construct the original line offsets and clip before any coordinates
are visited, including negative and zero signed short second coordinates. -/
def lineIntervalBits (rectangle : RectangleWordReport) (basis : BasisLoopWordReport)
    (j : SignedWord) : LineWordReport :=
  let vectors := basisWordsBits basis
  let firstOffset := mulSignedBits j vectors.previousCoefficient
  let first := positiveLinearBits firstOffset.word basis.coefficient zeroWord rectangle.sumLimit.word
  let secondProduct := mulSignedBits j vectors.companionSecond
  let secondOffset := addSignedBits rectangle.origin secondProduct.word
  let clipping := linearIntervalBits secondOffset.word vectors.second zeroWord
    rectangle.productLimit.word first.bounds
  ⟨vectors,firstOffset,first,secondProduct,secondOffset,clipping,clipping.bounds,
    vectors.clock+firstOffset.clock+first.clock+secondProduct.clock+secondOffset.clock+
      clipping.clock+4⟩

/-- Full original line equality, including affine origin, both signed
vectors, exact rounding and every constant-coordinate clipping branch. -/
theorem lineIntervalBits_value (decoded bound : List Bool) (basis : BasisLoopWordReport)
    (j : SignedWord) :
    (lineIntervalBits (rectangleBits decoded bound) basis j).bounds.interpret=
      lineInterval (bitValue decoded) (bitValue bound) basis.interpret j.value := by
  have hr := rectangleBits_values decoded bound
  have hb := basisWordsBits_values basis
  dsimp only [lineIntervalBits]
  rw [linearIntervalBits_value,positiveLinearBits_value]
  simp only [mulSignedBits_value,addSignedBits_value,hb.2.1,hb.2.2.1,hb.2.2.2,
    hr.2.2.1,hr.2.2.2.1,hr.2.2.2.2.2,zeroWord_value,
    lineInterval,BasisLoopWordReport.interpret]

/-- All actual signed products and additions producing one original point. -/
structure PointWordReport where
  /-- Materialized original signed basis vectors. -/
  vectors : BasisWordsReport
  /-- Computed i times the current positive coefficient. -/
  firstCurrent : SignedProductReport
  /-- Computed j times the previous positive coefficient. -/
  firstPrevious : SignedProductReport
  /-- Full addition giving original sum coefficient. -/
  sum : SignedSumReport
  /-- Computed i times the original signed second coordinate. -/
  secondCurrent : SignedProductReport
  /-- Actual affine origin plus current second product. -/
  shiftedCurrent : SignedSumReport
  /-- Computed j times the original signed companion coordinate. -/
  secondPrevious : SignedProductReport
  /-- Full addition giving original product coefficient. -/
  product : SignedSumReport
  /-- Both actual unsigned magnitudes for the original root reader. -/
  magnitudes : List Bool×List Bool
  /-- Every vector sign, product, origin addition and retained point field. -/
  clock : ℕ

/-- Construct one original point from actual signed coordinate words.
Unsigned reader inputs are the computed magnitudes, never serialized values. -/
def coefficientPointBits (rectangle : RectangleWordReport) (basis : BasisLoopWordReport)
    (i j : SignedWord) : PointWordReport :=
  let vectors := basisWordsBits basis
  let firstCurrent := mulSignedBits i vectors.coefficient
  let firstPrevious := mulSignedBits j vectors.previousCoefficient
  let sum := addSignedBits firstCurrent.word firstPrevious.word
  let secondCurrent := mulSignedBits i vectors.second
  let shiftedCurrent := addSignedBits rectangle.origin secondCurrent.word
  let secondPrevious := mulSignedBits j vectors.companionSecond
  let product := addSignedBits shiftedCurrent.word secondPrevious.word
  ⟨vectors,firstCurrent,firstPrevious,sum,secondCurrent,shiftedCurrent,secondPrevious,product,
    ⟨sum.word.magnitude,product.word.magnitude⟩,vectors.clock+firstCurrent.clock+
      firstPrevious.clock+sum.clock+secondCurrent.clock+shiftedCurrent.clock+
      secondPrevious.clock+product.clock+5⟩

/-- Exact original affine coefficient point for EVERY encoded coordinate,
including signed zeros, negative coordinates and arbitrary physical padding. -/
theorem coefficientPointBits_value (decoded bound : List Bool) (basis : BasisLoopWordReport)
    (i j : SignedWord) :
    ((coefficientPointBits (rectangleBits decoded bound) basis i j).sum.word.value,
      (coefficientPointBits (rectangleBits decoded bound) basis i j).product.word.value)=
        coefficientPoint (bitValue decoded) basis.interpret (i.value,j.value) := by
  have hr := rectangleBits_values decoded bound
  have hb := basisWordsBits_values basis
  dsimp only [coefficientPointBits]
  simp only [addSignedBits_value,mulSignedBits_value,hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,
    hr.2.2.2.2.2,coefficientPoint]

/-- Either signed representation has magnitude equal to absolute value. -/
theorem signedWord_natAbs (word : SignedWord) : word.value.natAbs=bitValue word.magnitude := by
  cases word with
  | mk negative magnitude => cases negative <;> simp [SignedWord.value]

/-- A nonnegative computed word supplies its unsigned reader value even
when its Boolean sign is negative zero. No normalization is executed. -/
theorem signedWord_magnitude_of_nonneg {word : SignedWord} (h : 0≤word.value) :
    (bitValue word.magnitude : ℤ)=word.value := by
  rw [←signedWord_natAbs,Int.natCast_natAbs,abs_of_nonneg h]

/-- A coordinate in the actually clipped line supplies EXACT original
nonnegative coefficient values to the existing Boolean root reader. -/
theorem clipped_point_magnitudes (decoded bound : List Bool) (basis : BasisLoopWordReport)
    (i j : SignedWord) (hu : 0<basis.interpret.coefficient)
    (hi : i.value∈(lineIntervalBits (rectangleBits decoded bound) basis j).bounds.interpret.entries) :
    ((bitValue (coefficientPointBits (rectangleBits decoded bound) basis i j).magnitudes.1 : ℤ),
      (bitValue (coefficientPointBits (rectangleBits decoded bound) basis i j).magnitudes.2 : ℤ))=
        coefficientPoint (bitValue decoded) basis.interpret (i.value,j.value) := by
  rw [lineIntervalBits_value] at hi
  have hrectangle := (mem_lineInterval hu i.value j.value).mp hi
  have he := coefficientPointBits_value decoded bound basis i j
  have hs : (coefficientPointBits (rectangleBits decoded bound) basis i j).sum.word.value=
      (coefficientPoint (bitValue decoded) basis.interpret (i.value,j.value)).1 :=
    congrArg Prod.fst he
  have hp : (coefficientPointBits (rectangleBits decoded bound) basis i j).product.word.value=
      (coefficientPoint (bitValue decoded) basis.interpret (i.value,j.value)).2 :=
    congrArg Prod.snd he
  have hsum := signedWord_magnitude_of_nonneg (word:=(coefficientPointBits
    (rectangleBits decoded bound) basis i j).sum.word) (by rw [hs]; exact hrectangle.1)
  have hproduct := signedWord_magnitude_of_nonneg (word:=(coefficientPointBits
    (rectangleBits decoded bound) basis i j).product.word) (by rw [hp]; exact hrectangle.2.2.1)
  change ((bitValue (coefficientPointBits (rectangleBits decoded bound) basis i j).sum.word.magnitude : ℤ),
    (bitValue (coefficientPointBits (rectangleBits decoded bound) basis i j).product.word.magnitude : ℤ))=_
  rw [hsum,hproduct,he]

/-- Materializing signs shares every original physical magnitude. -/
theorem basisWordsBits_width {W : ℕ} {basis : BasisLoopWordReport}
    (hc : basis.coefficient.length≤W) (hr : basis.remainder.length≤W)
    (hp : basis.previousCoefficient.length≤W) (hs : basis.previousRemainder.length≤W) :
    (basisWordsBits basis).coefficient.magnitude.length≤W ∧
      (basisWordsBits basis).second.magnitude.length≤W ∧
      (basisWordsBits basis).previousCoefficient.magnitude.length≤W ∧
      (basisWordsBits basis).companionSecond.magnitude.length≤W := ⟨hc,hr,hp,hs⟩

/-- Original rectangle construction pays every power, signed cap, discarded
borrow and literal cell. All retained physical words have public linear width. -/
theorem rectangleBits_cost_width {W : ℕ} {decoded bound : List Bool}
    (hs : decoded.length≤W) (hL : bound.length≤W) :
    (rectangleBits decoded bound).clock≤2000*(W+1)^2 ∧
      (rectangleBits decoded bound).squareS.bits.length≤6*(W+1) ∧
      (rectangleBits decoded bound).squareL.bits.length≤6*(W+1) ∧
      (rectangleBits decoded bound).sumLimit.word.magnitude.length≤6*(W+1) ∧
      (rectangleBits decoded bound).productLimit.word.magnitude.length≤6*(W+1) ∧
      (rectangleBits decoded bound).liftedProductLimit.word.magnitude.length≤6*(W+1) ∧
      (rectangleBits decoded bound).origin.magnitude.length≤6*(W+1) := by
  have hbudget : 2*(24*(W+1)^2+1)+41*(W+2)+41*(3*W+2)+40*(3*W+3)+6≤
      2000*(W+1)^2 := by nlinarith only []
  have hsqS := bounded_mulBits hs hs
  have hsqL := bounded_mulBits hL hL
  have hone : oneWord.magnitude.length≤W+1 := by
    change ([true] : List Bool).length≤W+1
    simp only [List.length_cons,List.length_nil]
    omega
  have hdouble : (positiveWord (false::bound)).magnitude.length≤W+1 := by
    change (false::bound).length≤W+1
    simp only [List.length_cons]
    omega
  have hsum := subSignedBits_cost_width hdouble hone
  have hsquare : (positiveWord (mulBits bound bound).bits).magnitude.length≤3*W+1 := by
    exact hsqL.2.trans (by omega)
  have hone' : oneWord.magnitude.length≤3*W+1 := by omega
  have hproduct := subSignedBits_cost_width hsquare hone'
  have hlift := addSignedBits_cost_width
    (left:=positiveWord (mulBits decoded decoded).bits)
    (right:=(subSignedBits (positiveWord (mulBits bound bound).bits) oneWord).word)
    (hsqS.2.trans (by omega : 3*W≤3*W+2)) hproduct.2
  dsimp only [rectangleBits]
  refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,?_⟩
  change (mulBits decoded decoded).bits.length≤6*(W+1)
  omega

/-- Signed zero splitting pays the full order circuit; selected words
cannot exceed the original input's physical width. -/
theorem splitZeroBits_cost_width {W : ℕ} {word : SignedWord}
    (hw : word.magnitude.length≤W) :
    (splitZeroBits word).clock≤50*(W+1) ∧
      (splitZeroBits word).lower.magnitude.length≤W ∧
      (splitZeroBits word).upper.magnitude.length≤W := by
  have hc := leSignedBits_cost (left:=zeroWord) (right:=word) (Nat.zero_le W) hw
  unfold splitZeroBits
  dsimp only
  constructor
  · omega
  · constructor <;> split
    · exact Nat.zero_le _
    · exact hw
    · exact hw
    · exact Nat.zero_le _

/-- Every determinant product, signed extremum, orientation gate and rounded
division is included. Public input widths imply bounded actual band endpoints. -/
theorem bandIntervalBits_cost_width {W : ℕ} {modulus decoded bound : List Bool}
    {basis : BasisLoopWordReport}
    (hm : modulus.length≤W) (hs : decoded.length≤W) (hL : bound.length≤W)
    (hc : basis.coefficient.length≤W) (hr : basis.remainder.length≤W)
    (hp : basis.previousCoefficient.length≤W) (hpr : basis.previousRemainder.length≤W) :
    (bandIntervalBits modulus (rectangleBits decoded bound) basis).clock≤1000000*(W+1)^2 ∧
      (bandIntervalBits modulus (rectangleBits decoded bound) basis).bounds.lower.magnitude.length≤22*(W+1) ∧
      (bandIntervalBits modulus (rectangleBits decoded bound) basis).bounds.upper.magnitude.length≤22*(W+1) := by
  have hbudget : 5+50*(W+1)+4*(24*(6*(W+1)+1)^2+4)+2*(40*(18*(W+1)+1))+
      1500*(19*(W+1)+1)^2+8≤1000000*(W+1)^2 := by nlinarith only []
  let rectangle := rectangleBits decoded bound
  let vectors := basisWordsBits basis
  let splitSecond := splitZeroBits (negateWord vectors.second)
  let lowerBase := mulSignedBits vectors.coefficient (positiveWord rectangle.squareS.bits)
  let upperBase := mulSignedBits vectors.coefficient rectangle.liftedProductLimit.word
  let lowerCorrection := mulSignedBits splitSecond.lower rectangle.sumLimit.word
  let upperCorrection := mulSignedBits splitSecond.upper rectangle.sumLimit.word
  let lower := addSignedBits lowerBase.word lowerCorrection.word
  let upper := addSignedBits upperBase.word upperCorrection.word
  let division := if basis.negative=true then
      positiveLinearBits zeroWord modulus lower.word upper.word
    else positiveLinearBits zeroWord modulus (negateWord upper.word) (negateWord lower.word)
  have hv := basisWordsBits_width hc hr hp hpr
  have hrectangle := rectangleBits_cost_width hs hL
  have hsplit := splitZeroBits_cost_width (word:=negateWord vectors.second) hv.2.1
  have hcoef : vectors.coefficient.magnitude.length≤6*(W+1) := hv.1.trans (by omega)
  have hslower : splitSecond.lower.magnitude.length≤6*(W+1) := hsplit.2.1.trans (by omega)
  have hsupper : splitSecond.upper.magnitude.length≤6*(W+1) := hsplit.2.2.trans (by omega)
  have hlb := mulSignedBits_cost_width (right:=positiveWord rectangle.squareS.bits) hcoef hrectangle.2.1
  have hub := mulSignedBits_cost_width hcoef hrectangle.2.2.2.2.2.1
  have hlc := mulSignedBits_cost_width hslower hrectangle.2.2.2.1
  have huc := mulSignedBits_cost_width hsupper hrectangle.2.2.2.1
  have hlo := addSignedBits_cost_width hlb.2 hlc.2
  have hhi := addSignedBits_cost_width hub.2 huc.2
  have hmodulus : modulus.length≤19*(W+1) := by omega
  have hzero : zeroWord.magnitude.length≤19*(W+1) := Nat.zero_le _
  have hlower : lower.word.magnitude.length≤19*(W+1) := hlo.2.trans (by omega)
  have hupper : upper.word.magnitude.length≤19*(W+1) := hhi.2.trans (by omega)
  have hpositive := positiveLinearBits_cost_width hzero hmodulus hlower hupper
  have hnegative := positiveLinearBits_cost_width (offset:=zeroWord)
    (lower:=negateWord upper.word) (upper:=negateWord lower.word)
    hzero hmodulus hupper hlower
  have hdivision : division.clock≤1500*(19*(W+1)+1)^2 ∧
      division.bounds.lower.magnitude.length≤19*(W+1)+3 ∧
      division.bounds.upper.magnitude.length≤19*(W+1)+3 := by
    dsimp only [division]
    split
    · exact hpositive
    · exact hnegative
  have horient : (if basis.negative=true then 6 else 8 : ℕ)≤8 := by split <;> omega
  constructor
  · change 5+splitSecond.clock+lowerBase.clock+upperBase.clock+lowerCorrection.clock+
      upperCorrection.clock+lower.clock+upper.clock+division.clock+
      (if basis.negative=true then 6 else 8)≤1000000*(W+1)^2
    dsimp only [rectangle,vectors,splitSecond,lowerBase,upperBase,lowerCorrection,
      upperCorrection,lower,upper,division] at *
    omega
  · change division.bounds.lower.magnitude.length≤22*(W+1) ∧
      division.bounds.upper.magnitude.length≤22*(W+1)
    constructor <;> omega

/-- Actual line initialization and clipping, with the computed affine origin,
has quadratic physical work. Empty and zero-step lines are included. -/
theorem lineIntervalBits_cost_width {W : ℕ} {decoded bound : List Bool}
    {basis : BasisLoopWordReport} {j : SignedWord}
    (hs : decoded.length≤W) (hL : bound.length≤W) (hj : j.magnitude.length≤W)
    (hc : basis.coefficient.length≤W) (hr : basis.remainder.length≤W)
    (hp : basis.previousCoefficient.length≤W) (hpr : basis.previousRemainder.length≤W) :
    (lineIntervalBits (rectangleBits decoded bound) basis j).clock≤500000*(W+1)^2 ∧
      (lineIntervalBits (rectangleBits decoded bound) basis j).bounds.lower.magnitude.length≤12*(W+1) ∧
      (lineIntervalBits (rectangleBits decoded bound) basis j).bounds.upper.magnitude.length≤12*(W+1) := by
  have hbudget : 5+2*(24*(W+1)^2+4)+1500*(6*(W+1)+1)^2+
      40*(6*(W+1)+1)+2000*(9*(W+1)+1)^2+4≤500000*(W+1)^2 := by
    nlinarith only []
  let rectangle := rectangleBits decoded bound
  let vectors := basisWordsBits basis
  let firstOffset := mulSignedBits j vectors.previousCoefficient
  let first := positiveLinearBits firstOffset.word basis.coefficient zeroWord rectangle.sumLimit.word
  let secondProduct := mulSignedBits j vectors.companionSecond
  let secondOffset := addSignedBits rectangle.origin secondProduct.word
  have hv := basisWordsBits_width hc hr hp hpr
  have hrectangle := rectangleBits_cost_width hs hL
  have hfirstOffset := mulSignedBits_cost_width hj hv.2.2.1
  have hsecondProduct := mulSignedBits_cost_width hj hv.2.2.2
  have hfirst := positiveLinearBits_cost_width
    (offset:=firstOffset.word) (step:=basis.coefficient) (lower:=zeroWord)
    (upper:=rectangle.sumLimit.word)
    (hfirstOffset.2.trans (by omega : 3*W≤6*(W+1))) (hc.trans (by omega))
    (Nat.zero_le _) hrectangle.2.2.2.1
  have hsecondOffset := addSignedBits_cost_width (left:=rectangle.origin)
    (right:=secondProduct.word) hrectangle.2.2.2.2.2.2 (hsecondProduct.2.trans (by omega))
  have hclip := linearIntervalBits_cost_width
    (offset:=secondOffset.word) (step:=vectors.second) (lower:=zeroWord)
    (upper:=rectangle.productLimit.word) (initial:=first.bounds)
    (hsecondOffset.2.trans (by omega : 6*(W+1)+1≤9*(W+1)))
    (hv.2.1.trans (by omega)) (Nat.zero_le _)
    (hrectangle.2.2.2.2.1.trans (by omega))
    (hfirst.2.1.trans (by omega)) (hfirst.2.2.trans (by omega))
  constructor
  · change 5+firstOffset.clock+first.clock+secondProduct.clock+secondOffset.clock+
      (linearIntervalBits secondOffset.word vectors.second zeroWord
        rectangle.productLimit.word first.bounds).clock+4≤500000*(W+1)^2
    dsimp only [rectangle,vectors,firstOffset,first,secondProduct,secondOffset] at *
    omega
  · change (linearIntervalBits secondOffset.word vectors.second zeroWord
      rectangle.productLimit.word first.bounds).bounds.lower.magnitude.length≤12*(W+1) ∧
        (linearIntervalBits secondOffset.word vectors.second zeroWord
          rectangle.productLimit.word first.bounds).bounds.upper.magnitude.length≤12*(W+1)
    constructor <;> omega

/-- Four full products and all original signed point additions are paid.
Both actually produced reader words have bounded physical width. -/
theorem coefficientPointBits_cost_width {W : ℕ} {decoded bound : List Bool}
    {basis : BasisLoopWordReport} {i j : SignedWord}
    (hs : decoded.length≤W) (hL : bound.length≤W)
    (hi : i.magnitude.length≤W) (hj : j.magnitude.length≤W)
    (hc : basis.coefficient.length≤W) (hr : basis.remainder.length≤W)
    (hp : basis.previousCoefficient.length≤W) (hpr : basis.previousRemainder.length≤W) :
    (coefficientPointBits (rectangleBits decoded bound) basis i j).clock≤2000*(W+1)^2 ∧
      (coefficientPointBits (rectangleBits decoded bound) basis i j).magnitudes.1.length≤8*(W+1) ∧
      (coefficientPointBits (rectangleBits decoded bound) basis i j).magnitudes.2.length≤8*(W+1) := by
  have hbudget : 5+4*(24*(W+1)^2+4)+40*(3*(W+1)+1)+40*(6*(W+1)+1)+
      40*(7*(W+1)+1)+5≤2000*(W+1)^2 := by nlinarith only []
  let rectangle := rectangleBits decoded bound
  let vectors := basisWordsBits basis
  let firstCurrent := mulSignedBits i vectors.coefficient
  let firstPrevious := mulSignedBits j vectors.previousCoefficient
  let secondCurrent := mulSignedBits i vectors.second
  let secondPrevious := mulSignedBits j vectors.companionSecond
  let sum := addSignedBits firstCurrent.word firstPrevious.word
  let shifted := addSignedBits rectangle.origin secondCurrent.word
  let product := addSignedBits shifted.word secondPrevious.word
  have hv := basisWordsBits_width hc hr hp hpr
  have hrectangle := rectangleBits_cost_width hs hL
  have hfc := mulSignedBits_cost_width hi hv.1
  have hfp := mulSignedBits_cost_width hj hv.2.2.1
  have hsc := mulSignedBits_cost_width hi hv.2.1
  have hsp := mulSignedBits_cost_width hj hv.2.2.2
  have hsum := addSignedBits_cost_width (left:=firstCurrent.word) (right:=firstPrevious.word)
    (hfc.2.trans (by omega : 3*W≤3*(W+1))) (hfp.2.trans (by omega))
  have hshift := addSignedBits_cost_width (left:=rectangle.origin) (right:=secondCurrent.word)
    hrectangle.2.2.2.2.2.2 (hsc.2.trans (by omega : 3*W≤6*(W+1)))
  have hproduct := addSignedBits_cost_width (left:=shifted.word) (right:=secondPrevious.word)
    (hshift.2.trans (by omega : 6*(W+1)+1≤7*(W+1)))
    (hsp.2.trans (by omega : 3*W≤7*(W+1)))
  constructor
  · change 5+firstCurrent.clock+firstPrevious.clock+sum.clock+secondCurrent.clock+
      shifted.clock+secondPrevious.clock+product.clock+5≤2000*(W+1)^2
    dsimp only [rectangle,vectors,firstCurrent,firstPrevious,secondCurrent,
      secondPrevious,sum,shifted,product] at *
    omega
  · change sum.word.magnitude.length≤8*(W+1) ∧ product.word.magnitude.length≤8*(W+1)
    dsimp only [rectangle,vectors,firstCurrent,firstPrevious,secondCurrent,
      secondPrevious,sum,shifted,product] at *
    constructor <;> omega

/-- Once-only public basis, rectangle and band construction. -/
structure GeometryWordReport where
  /-- The actual computed original early-Euclid basis, retaining all diagnostics. -/
  basis : BasisWordReport
  /-- The actual rectangle powers, signed caps and affine origin. -/
  rectangle : RectangleWordReport
  /-- The actual original signed determinant band. -/
  band : BandWordReport
  /-- Every public constructor's full clock and retained output decisions. -/
  clock : ℕ

/-- Acquire the complete original basis and signed determinant geometry
from N, decoded residue and interval bound words, with no supplied vectors. -/
def indexGeometryBits (modulus decoded bound : List Bool) : GeometryWordReport :=
  let basis := indexBasisBits modulus decoded bound
  let rectangle := rectangleBits decoded bound
  let band := bandIntervalBits modulus rectangle basis.basis
  ⟨basis,rectangle,band,basis.clock+rectangle.clock+band.clock+4⟩

/-- The once-only word constructor preserves the complete original basis
and original determinant band on EVERY input representation. -/
theorem indexGeometryBits_value (modulus decoded bound : List Bool) :
    (indexGeometryBits modulus decoded bound).basis.basis.interpret=
        (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).basis ∧
      (indexGeometryBits modulus decoded bound).band.bounds.interpret=
        bandInterval (bitValue modulus) (bitValue decoded) (bitValue bound)
          (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).basis := by
  constructor
  · exact indexBasisBits_exact modulus decoded bound
  · dsimp only [indexGeometryBits]
    rw [bandIntervalBits_value,indexBasisBits_exact]

/-- Full public geometry construction is cubic in physical input width,
including basis acquisition, rectangle construction and every band primitive. -/
theorem indexGeometryBits_cost_width {W : ℕ} {modulus decoded bound : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤W)
    (hs : decoded.length≤W) (hL : bound.length≤W) :
    (indexGeometryBits modulus decoded bound).clock≤2000000*(W+1)^3 ∧
      (indexGeometryBits modulus decoded bound).band.bounds.lower.magnitude.length≤22*(W+1) ∧
      (indexGeometryBits modulus decoded bound).band.bounds.upper.magnitude.length≤22*(W+1) := by
  have hpower : (W+1)^2≤(W+1)^3 := by
    calc
      (W+1)^2=(W+1)^2*1 := by omega
      _≤(W+1)^2*(W+1) := Nat.mul_le_mul_left _ (by omega)
      _=(W+1)^3 := by ring
  have hpositive : 1≤(W+1)^3 := by
    have hh : 0<(W+1)^3 := by positivity
    omega
  have hbudget : 25000*(W+1)^3+2000*(W+1)^2+1000000*(W+1)^2+4≤
      2000000*(W+1)^3 := by omega
  have hb := indexBasisBits_cost hN hm hs hL
  have hw := indexBasisBits_width hN decoded bound
  have hr := rectangleBits_cost_width hs hL
  have hg := bandIntervalBits_cost_width hm hs hL (hw.1.trans hm) (hw.2.1.trans hm)
    (hw.2.2.1.trans hm) (hw.2.2.2.trans hm)
  dsimp only [indexGeometryBits]
  exact ⟨by omega,hg.2⟩

/-- Actual public geometry supplies the positive short coefficient required
by line membership. No relation-vector or positivity advice is supplied. -/
theorem indexGeometryBits_coefficient_positive {modulus bound : List Bool}
    (hN : 0<bitValue modulus) (hL : 0<bitValue bound) (decoded : List Bool) :
    0<(indexGeometryBits modulus decoded bound).basis.basis.interpret.coefficient := by
  have hb := shortRelation_basis hN (show 0<2*bitValue bound by omega) (bitValue decoded)
  have he := (indexGeometryBits_value modulus decoded bound).1
  rw [he]
  exact hb.2.2.1

/-- A point on an actually constructed public line supplies the original
reader magnitudes without encoded-basis, private-index or sign premises. -/
theorem indexGeometryBits_clipped_point {modulus bound : List Bool}
    (hN : 0<bitValue modulus) (hL : 0<bitValue bound) (decoded : List Bool)
    (i j : SignedWord)
    (hi : i.value∈(lineIntervalBits (indexGeometryBits modulus decoded bound).rectangle
      (indexGeometryBits modulus decoded bound).basis.basis j).bounds.interpret.entries) :
    ((bitValue (coefficientPointBits (indexGeometryBits modulus decoded bound).rectangle
        (indexGeometryBits modulus decoded bound).basis.basis i j).magnitudes.1 : ℤ),
      (bitValue (coefficientPointBits (indexGeometryBits modulus decoded bound).rectangle
        (indexGeometryBits modulus decoded bound).basis.basis i j).magnitudes.2 : ℤ))=
      coefficientPoint (bitValue decoded)
        (enumerateCoefficients (bitValue modulus) (bitValue decoded) (bitValue bound)).basis
        (i.value,j.value) := by
  have he := clipped_point_magnitudes decoded bound
    (indexGeometryBits modulus decoded bound).basis.basis i j
    (indexGeometryBits_coefficient_positive hN hL decoded) hi
  rw [(indexGeometryBits_value modulus decoded bound).1] at he
  exact he

/-- Any coordinate admitted by actual signed endpoints fits their public
physical width in absolute value. This does not serialize a coordinate. -/
theorem interval_member_natAbs_lt {K : ℕ} {bounds : WordInterval} {i : ℤ}
    (hl : bounds.lower.magnitude.length≤K) (hu : bounds.upper.magnitude.length≤K)
    (hi : i∈bounds.interpret.entries) : i.natAbs<2^K := by
  have hlo : bounds.lower.value.natAbs<2^K := by
    rw [signedWord_natAbs]
    exact (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by omega) hl)
  have hhi : bounds.upper.value.natAbs<2^K := by
    rw [signedWord_natAbs]
    exact (bitValue_lt_width _).trans_le (Nat.pow_le_pow_right (by omega) hu)
  have hloZ : |bounds.lower.value|<((2^K : ℕ) : ℤ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast hlo
  have hhiZ : |bounds.upper.value|<((2^K : ℕ) : ℤ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast hhi
  have hmem := (mem_interval_entries bounds.interpret i).mp hi
  have hab : |i|<((2^K : ℕ) : ℤ) := abs_lt.mpr ⟨by
    have hh := (abs_lt.mp hloZ).1
    exact hh.trans_le hmem.1,by
    have hh := (abs_lt.mp hhiZ).2
    exact hmem.2.trans_lt hh⟩
  rw [←Int.natCast_natAbs] at hab
  exact_mod_cast hab

/-- Actual public band/line membership gives the full original coefficient
candidate, including its affine congruence, on the produced reader magnitudes. -/
theorem indexGeometryBits_candidate {modulus bound : List Bool}
    (hN : 0<bitValue modulus) (hL : 0<bitValue bound) (decoded : List Bool)
    (i j : SignedWord)
    (hj : j.value∈(indexGeometryBits modulus decoded bound).band.bounds.interpret.entries)
    (hi : i.value∈(lineIntervalBits (indexGeometryBits modulus decoded bound).rectangle
      (indexGeometryBits modulus decoded bound).basis.basis j).bounds.interpret.entries) :
    coefficientCandidate (bitValue decoded : ZMod (bitValue modulus)) (bitValue bound)
      (bitValue (coefficientPointBits (indexGeometryBits modulus decoded bound).rectangle
        (indexGeometryBits modulus decoded bound).basis.basis i j).magnitudes.1)
      (bitValue (coefficientPointBits (indexGeometryBits modulus decoded bound).rectangle
        (indexGeometryBits modulus decoded bound).basis.basis i j).magnitudes.2) := by
  have he := indexGeometryBits_value modulus decoded bound
  have hipublic := hi
  rw [he.2] at hj
  change i.value∈(lineIntervalBits (rectangleBits decoded bound)
    (indexGeometryBits modulus decoded bound).basis.basis j).bounds.interpret.entries at hi
  rw [lineIntervalBits_value,he.1] at hi
  have hcoords := (mem_enumerateCoordinates (bitValue modulus) (bitValue decoded)
    (bitValue bound) (enumerateCoefficients (bitValue modulus) (bitValue decoded)
      (bitValue bound)).basis (i.value,j.value)).mpr ⟨hj,hi⟩
  have hc := enumerateCoordinates_sound hN hL (i.value,j.value) hcoords
  have hp := indexGeometryBits_clipped_point hN hL decoded i j hipublic
  have hsum := congrArg Prod.fst hp
  have hproduct := congrArg Prod.snd hp
  dsimp only at hsum hproduct
  rw [hsum,hproduct]
  exact hc

/-- The next coordinate also fits one extra public cell, even after the
last admitted endpoint. A future paid width copy can therefore stay lossless. -/
theorem interval_member_successor_natAbs_lt {K : ℕ} {bounds : WordInterval} {i : ℤ}
    (hl : bounds.lower.magnitude.length≤K) (hu : bounds.upper.magnitude.length≤K)
    (hi : i∈bounds.interpret.entries) : (i+1).natAbs<2^(K+1) := by
  have hm := interval_member_natAbs_lt hl hu hi
  have hmZ : |i|<((2^K : ℕ) : ℤ) := by
    rw [←Int.natCast_natAbs]
    exact_mod_cast hm
  have hp : (0 : ℤ)<((2^K : ℕ) : ℤ) := by positivity
  have hab : |i+1|<((2^(K+1) : ℕ) : ℤ) := by
    rw [pow_succ,Nat.cast_mul,Nat.cast_ofNat]
    have hh := abs_lt.mp hmZ
    exact abs_lt.mpr ⟨by omega,by omega⟩
  rw [←Int.natCast_natAbs] at hab
  exact_mod_cast hab

/-- Every actual public band coordinate has a factor-independent magnitude
bound derived from the produced physical endpoints. -/
theorem indexGeometryBits_band_coordinate_width {W : ℕ} {modulus decoded bound : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤W)
    (hs : decoded.length≤W) (hL : bound.length≤W) {j : ℤ}
    (hj : j∈(indexGeometryBits modulus decoded bound).band.bounds.interpret.entries) :
    j.natAbs<2^(22*(W+1)) := by
  have hw := indexGeometryBits_cost_width hN hm hs hL
  exact interval_member_natAbs_lt hw.2.1 hw.2.2 hj

/-- The actual once-only public geometry supplies every bounded basis word
needed for a priced line; no encoded-basis width premise is supplied. -/
theorem indexGeometryBits_line_cost_width {W : ℕ} {modulus decoded bound : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤W)
    (hs : decoded.length≤W) (hL : bound.length≤W) {j : SignedWord}
    (hj : j.magnitude.length≤W) :
    (lineIntervalBits (indexGeometryBits modulus decoded bound).rectangle
      (indexGeometryBits modulus decoded bound).basis.basis j).clock≤500000*(W+1)^2 ∧
      (lineIntervalBits (indexGeometryBits modulus decoded bound).rectangle
        (indexGeometryBits modulus decoded bound).basis.basis j).bounds.lower.magnitude.length≤12*(W+1) ∧
      (lineIntervalBits (indexGeometryBits modulus decoded bound).rectangle
        (indexGeometryBits modulus decoded bound).basis.basis j).bounds.upper.magnitude.length≤12*(W+1) := by
  have hw := indexBasisBits_width hN decoded bound
  exact lineIntervalBits_cost_width hs hL hj (hw.1.trans hm) (hw.2.1.trans hm)
    (hw.2.2.1.trans hm) (hw.2.2.2.trans hm)

/-- The actually constructed public geometry also supplies every original
vector width for point emission. Coordinate word construction is separate. -/
theorem indexGeometryBits_point_cost_width {W : ℕ} {modulus decoded bound : List Bool}
    (hN : 0<bitValue modulus) (hm : modulus.length≤W)
    (hs : decoded.length≤W) (hL : bound.length≤W) {i j : SignedWord}
    (hi : i.magnitude.length≤W) (hj : j.magnitude.length≤W) :
    (coefficientPointBits (indexGeometryBits modulus decoded bound).rectangle
      (indexGeometryBits modulus decoded bound).basis.basis i j).clock≤2000*(W+1)^2 ∧
      (coefficientPointBits (indexGeometryBits modulus decoded bound).rectangle
        (indexGeometryBits modulus decoded bound).basis.basis i j).magnitudes.1.length≤8*(W+1) ∧
      (coefficientPointBits (indexGeometryBits modulus decoded bound).rectangle
        (indexGeometryBits modulus decoded bound).basis.basis i j).magnitudes.2.length≤8*(W+1) := by
  have hw := indexBasisBits_width hN decoded bound
  exact coefficientPointBits_cost_width hs hL hi hj (hw.1.trans hm) (hw.2.1.trans hm)
    (hw.2.2.1.trans hm) (hw.2.2.2.trans hm)

/-- Actually accepted marked residue words feed the complete public geometry
without re-encoding. Original jet acquisition remains separate. -/
theorem marked_geometry_cost {W : ℕ} {modulus target targetD baseD bound word : List Bool}
    (hN : 0<bitValue modulus)
    (hword : (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).index=some word)
    (hm : modulus.length≤W) (hx : target.length≤W)
    (hD : targetD.length≤W) (hE : baseD.length≤W) (hbound : bound.length≤W) :
    (SemiprimeBitInverse.decodeMarkedBits modulus target targetD baseD).clock+
      (indexGeometryBits modulus word bound).clock≤2005000*(W+1)^3 := by
  have hw : word.length≤W :=
    (SemiprimeBitIndexFactors.marked_word_width hN hword).le.trans hm
  have hd := SemiprimeBitInverse.decodeMarkedBits_cost hN hm hx hD hE
  have hg := indexGeometryBits_cost_width hN hm hw hbound
  omega

end RiemannGaussian.SemiprimeBitIndexGeometry
