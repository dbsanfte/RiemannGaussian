/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHistogramScales
import RiemannGaussian.SemiprimeSourceHistogramSquares
import RiemannGaussian.SemiprimeSourceIncidenceHistogram

/-! # Executed signed denominator-one histogram arithmetic
Static sixteen-feature summation retains every producer and raw arithmetic report.
No GCD/reduction, semantic decoding, or native signed-count subtraction is run.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHistogramArithmetic
open scoped BigOperators
open SemiprimeBitArithmetic SemiprimeRationalBits
open SemiprimeBitIndexClipping
open SemiprimeSourceIncidenceHistogram (Feature)

/-- Semantic denominator-one invariant of actual physical words. -/
def DenOne (word : RationalWord) : Prop := bitValue word.denominator=1

/-- Borrow an actual unsigned physical payload under literal denominator one. -/
def unsigned (bits : List Bool) : RationalWord := ⟨⟨false,bits⟩,[true]⟩

/-- Literal signed minus one, without integer-to-bits encoding. -/
def minusOne : RationalWord := ⟨⟨true,[true]⟩,[true]⟩

/-- Literal positive one. -/
def one : RationalWord := unsigned [true]

/-- Borrowed static word report; producer costs are retained at the owning caller. -/
def borrowed (word : RationalWord) : RationalReport := ⟨word,0⟩

/-- Raw physical addition with both actual lower reports retained. -/
def add (x y : RationalReport) : RationalReport :=
  let out := rawAddBits x.word y.word
  ⟨out.word,x.clock+y.clock+out.clock+3⟩

/-- Raw physical multiplication with both actual lower reports retained. -/
def mul (x y : RationalReport) : RationalReport :=
  let out := rawMulBits x.word y.word
  ⟨out.word,x.clock+y.clock+out.clock+3⟩

/-- Physical sign-bit negation retains its actual input report. -/
def neg (x : RationalReport) : RationalReport :=
  let out := rawNegBits x.word
  ⟨out.word,x.clock+out.clock+3⟩

/-- Every denominator-one word is valid, even when its numerator is negative. -/
theorem den_valid (word : RationalWord) (h : DenOne word) : word.Valid := by
  change 0<bitValue word.denominator
  rw [h]
  decide

/-- Literal unsigned word denominator. -/
theorem unsigned_den (bits : List Bool) : DenOne (unsigned bits) := rfl
/-- Literal negative word denominator. -/
theorem minusOne_den : DenOne minusOne := rfl
/-- Literal positive word denominator. -/
theorem one_den : DenOne one := rfl
/-- Literal zero word denominator. -/
theorem zero_den : DenOne zeroWord := rfl

/-- Unsigned interpretation is proof-only and agrees with the original payload. -/
theorem unsigned_value (bits : List Bool) : (unsigned bits).value=(bitValue bits:ℚ) := by
  simp [unsigned,RationalWord.value,SignedWord.value,bitValue,bitNat]
/-- Literal negative-one value. -/
theorem minusOne_value : minusOne.value=(-1:ℚ) := by
  norm_num [minusOne,RationalWord.value,SignedWord.value,bitValue,bitNat]
/-- Literal positive-one value. -/
theorem one_value : one.value=(1:ℚ) := by
  norm_num [one,unsigned_value,bitValue,bitNat]
/-- Literal zero value. -/
theorem zero_value : zeroWord.value=(0:ℚ) := by norm_num [zeroWord,RationalWord.value,SignedWord.value,bitValue,bitNat]

/-- Raw physical denominator products preserve the semantic value one. -/
theorem add_den (x y : RationalReport) (hx : DenOne x.word) (hy : DenOne y.word) :
    DenOne (add x y).word := by
  change bitValue x.word.denominator=1 at hx
  change bitValue y.word.denominator=1 at hy
  simp only [DenOne,add,rawAddBits,mulBits_correct,hx,hy,one_mul]
/-- Raw product denominator stays one without GCD reduction. -/
theorem mul_den (x y : RationalReport) (hx : DenOne x.word) (hy : DenOne y.word) :
    DenOne (mul x y).word := by
  change bitValue x.word.denominator=1 at hx
  change bitValue y.word.denominator=1 at hy
  simp only [DenOne,mul,rawMulBits,mulBits_correct,hx,hy,one_mul]
/-- Sign-bit negation leaves the actual denominator unchanged. -/
theorem neg_den (x : RationalReport) (hx : DenOne x.word) : DenOne (neg x).word := hx

/-- Signed addition correctness uses only the actual denominator-one invariant. -/
theorem add_value (x y : RationalReport) (hx : DenOne x.word) (hy : DenOne y.word) :
    (add x y).word.value=x.word.value+y.word.value :=
  rawAddBits_value _ _ (den_valid _ hx) (den_valid _ hy)
/-- Signed multiplication has no decoded data path. -/
theorem mul_value (x y : RationalReport) : (mul x y).word.value=x.word.value*y.word.value :=
  rawMulBits_value _ _
/-- Signed negation is the actual sign-bit gate. -/
theorem neg_value (x : RationalReport) : (neg x).word.value= -x.word.value := rawNegBits_value _

/-- Actual cached coefficient words, with L−1 acquired only once. -/
structure Coefficients where
  /-- Original borrowed compact L payload. -/
  alphabet : List Bool
  /-- Actual signed physical L−1 output. -/
  predecessor : RationalWord
  /-- Actual raw subtraction and finite setup work. -/
  clock : ℕ

/-- One actual signed addition acquires L−1, including the L=0 case. -/
def coefficients (L : List Bool) : Coefficients :=
  let out := rawAddBits (unsigned L) minusOne
  ⟨L,out.word,out.clock+5⟩

/-- Fixed four-way selector; it never acquires an original term list. -/
def coefficientWord (cache : Coefficients) (f : Feature) : RationalWord :=
  if f=0 then one else if f=1 then cache.predecessor
  else if f=2 then unsigned cache.alphabet else minusOne

/-- Every acquired coefficient is a valid semantic integer. -/
theorem coefficient_den (L : List Bool) (f : Feature) :
    DenOne (coefficientWord (coefficients L) f) := by
  have hp : DenOne (coefficients L).predecessor := by
    norm_num [coefficients,DenOne,rawAddBits,mulBits_correct,unsigned,minusOne,bitValue,bitNat]
  fin_cases f <;> simp [coefficientWord,one_den,unsigned_den,minusOne_den,hp]

/-- Actual coefficient values match the exact signed four-feature expansion. -/
theorem coefficient_value (L : List Bool) (f : Feature) :
    (coefficientWord (coefficients L) f).value=
      SemiprimeSourceIncidenceHistogram.coefficient (bitValue L:ℚ) f := by
  have hp : (coefficients L).predecessor.value=(bitValue L:ℚ)-1 := by
    change (rawAddBits (unsigned L) minusOne).word.value=_
    rw [rawAddBits_value _ _ (den_valid _ (unsigned_den L)) (den_valid _ minusOne_den),
      unsigned_value,minusOne_value]
    ring
  have ha : (coefficients L).alphabet=L := rfl
  fin_cases f <;> simp [coefficientWord,SemiprimeSourceIncidenceHistogram.coefficient,
    one_value,unsigned_value,minusOne_value,hp,ha]

/-- Static sixteen feature pairs, in literal row-major order. -/
def featurePairs : List (Feature × Feature) := ([(0:Feature),1,2,3]).product [0,1,2,3]

/-- Each actual histogram producer is called once for this literal feature pair. -/
def term (cache : Coefficients)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) (fg : Feature × Feature) : RationalReport :=
  let source := hist fg.1 fg.2
  let first := rawMulBits (coefficientWord cache fg.1) (coefficientWord cache fg.2)
  let out := rawMulBits first.word (unsigned source.bits)
  ⟨out.word,source.clock+first.clock+out.clock+10⟩

/-- Every term denominator is one; signed intermediate numerators remain legal. -/
theorem term_den (L : List Bool)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) (fg : Feature × Feature) :
    DenOne (term (coefficients L) hist fg).word := by
  have h1 := coefficient_den L fg.1
  have h2 := coefficient_den L fg.2
  unfold DenOne at h1 h2
  norm_num only [term,DenOne,rawMulBits,mulBits_correct,h1,h2,unsigned,bitValue,bitNat,ite_true]

/-- Exact physical signed feature term; only its actual acquired bits are interpreted. -/
theorem term_value (L : List Bool)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) (fg : Feature × Feature) :
    (term (coefficients L) hist fg).word.value=
      SemiprimeSourceIncidenceHistogram.coefficient (bitValue L:ℚ) fg.1*
        SemiprimeSourceIncidenceHistogram.coefficient (bitValue L:ℚ) fg.2*
          (bitValue (hist fg.1 fg.2).bits:ℚ) := by
  simp only [term,rawMulBits_value,unsigned_value,coefficient_value]

/-- Actual raw-add fold; its zero/done and every child/adder report is retained. -/
def sumTerms (cache : Coefficients)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) : List (Feature × Feature) → RationalReport
  | [] => ⟨zeroWord,1⟩
  | fg::pairs =>
    let first := term cache hist fg
    let rest := sumTerms cache hist pairs
    let out := rawAddBits first.word rest.word
    ⟨out.word,first.clock+rest.clock+out.clock+3⟩

/-- Every prefix/suffix raw sum retains actual denominator value one. -/
theorem sumTerms_den (L : List Bool)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) (pairs : List (Feature × Feature)) :
    DenOne (sumTerms (coefficients L) hist pairs).word := by
  induction pairs with
  | nil => exact zero_den
  | cons fg pairs ih =>
    have hf := term_den L hist fg
    unfold DenOne at hf ih
    simp only [sumTerms,DenOne,rawAddBits,mulBits_correct,hf,ih,one_mul]

/-- Signed linear fold equals the literal feature-list sum, not a modular cancellation. -/
theorem sumTerms_value (L : List Bool)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) (pairs : List (Feature × Feature)) :
    (sumTerms (coefficients L) hist pairs).word.value=
      (pairs.map (fun fg => SemiprimeSourceIncidenceHistogram.coefficient (bitValue L:ℚ) fg.1*
        SemiprimeSourceIncidenceHistogram.coefficient (bitValue L:ℚ) fg.2*
          (bitValue (hist fg.1 fg.2).bits:ℚ))).sum := by
  induction pairs with
  | nil => exact zero_value
  | cons fg pairs ih =>
    simp only [sumTerms,List.map_cons,List.sum_cons]
    rw [rawAddBits_value _ _ (den_valid _ (term_den L hist fg))
      (den_valid _ (sumTerms_den L hist pairs)),term_value,ih]

/-- Physical sixteen-term incidence combination and actual L² multiplication. -/
def incidence (cache : SemiprimeSourceHistogramScales.Cache)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) : RationalReport :=
  let cs := coefficients cache.alphabet
  let total := sumTerms cs hist featurePairs
  let out := rawMulBits (unsigned cache.square) total.word
  ⟨out.word,cs.clock+total.clock+out.clock+1000⟩

/-- Actual incidence output denominator remains one without normalization. -/
theorem incidence_den (cache : SemiprimeSourceHistogramScales.Cache)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) : DenOne (incidence cache hist).word := by
  have ht := sumTerms_den cache.alphabet hist featurePairs
  unfold DenOne at ht
  norm_num only [incidence,DenOne,rawMulBits,mulBits_correct,unsigned,bitValue,bitNat,ite_true,ht]

/-- Exact signed sixteen-feature value with every actual histogram payload retained. -/
theorem incidence_value (cache : SemiprimeSourceHistogramScales.Cache)
    (hist : Feature → Feature → SemiprimeSourceHistogramSquares.State) :
    (incidence cache hist).word.value=(bitValue cache.square:ℚ)*
      ∑ f : Feature,∑ g : Feature,
        SemiprimeSourceIncidenceHistogram.coefficient (bitValue cache.alphabet:ℚ) f*
        SemiprimeSourceIncidenceHistogram.coefficient (bitValue cache.alphabet:ℚ) g*
          (bitValue (hist f g).bits:ℚ) := by
  simp only [incidence,rawMulBits_value,unsigned_value,sumTerms_value]
  congr 1
  simp [featurePairs,List.product,Fin.sum_univ_succ,add_assoc]

/-- Convert an actual acquired histogram state, retaining its whole producer clock. -/
def fromState (state : SemiprimeSourceHistogramSquares.State) : RationalReport :=
  ⟨unsigned state.bits,state.clock+3⟩

/-- Every acquired state yields an actual denominator-one signed-arithmetic input. -/
theorem fromState_den (state : SemiprimeSourceHistogramSquares.State) :
    DenOne (fromState state).word := unsigned_den _

/-- State conversion is only a physical wrapper; no new count is encoded. -/
theorem fromState_value (state : SemiprimeSourceHistogramSquares.State) :
    (fromState state).word.value=(bitValue state.bits:ℚ) := unsigned_value _

/-- Actual signed head formula; original q,p,f and C producer reports are retained
once. Borrowed words only share already acquired payloads, never re-run producers. -/
def head (cache : SemiprimeSourceHistogramScales.Cache)
    (q p f : SemiprimeSourceCompactBits.Report) (C : RationalReport) : RationalReport :=
  let qw := borrowed (unsigned q.bits)
  let pw := borrowed (unsigned p.bits)
  let fw := borrowed (unsigned f.bits)
  let cw := borrowed C.word
  let A := borrowed (unsigned cache.fourth)
  let G := borrowed (unsigned cache.head)
  let two := borrowed (unsigned [false,true])
  let qf := mul qw fw
  let leftInner := add cw qf
  let left := mul A leftInner
  let twoP := mul two pw
  let twoPF := mul twoP fw
  let ff := mul fw fw
  let positive := add twoPF ff
  let inner := add positive (neg fw)
  let gq := mul G qw
  let right := mul gq inner
  let out := add left right
  ⟨out.word,q.clock+p.clock+f.clock+C.clock+out.clock+1000⟩

/-- Head subtraction is honest signed arithmetic and preserves denominator one. -/
theorem head_den (cache : SemiprimeSourceHistogramScales.Cache)
    (q p f : SemiprimeSourceCompactBits.Report) (C : RationalReport) (hC : DenOne C.word) :
    DenOne (head cache q p f C).word := by
  simp (config := {maxDischargeDepth := 100}) only [head,add_den,mul_den,neg_den,borrowed,unsigned_den,hC]

/-- Exact original padded-head expression, including f=0 without Nat underflow. -/
theorem head_value (cache : SemiprimeSourceHistogramScales.Cache)
    (q p f : SemiprimeSourceCompactBits.Report) (C : RationalReport) (hC : DenOne C.word) :
    (head cache q p f C).word.value=
      (bitValue cache.fourth:ℚ)*(C.word.value+(bitValue q.bits:ℚ)*(bitValue f.bits:ℚ))+
      (bitValue cache.head:ℚ)*(bitValue q.bits:ℚ)*
        (2*(bitValue p.bits:ℚ)*(bitValue f.bits:ℚ)+(bitValue f.bits:ℚ)^2-(bitValue f.bits:ℚ)) := by
  simp (config := {maxDischargeDepth := 100}) only [head,add_value,mul_value,neg_value,borrowed,unsigned_value,
    add_den,mul_den,neg_den,unsigned_den,hC]
  norm_num only [bitValue,bitNat,Bool.false_eq_true,ite_false,ite_true,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  ring

/-- Actual original-weight combination; both completed lane reports are retained. -/
def weighted (cache : SemiprimeSourceHistogramScales.Cache) (I H : RationalReport) : RationalReport :=
  add (mul (borrowed (unsigned cache.weights.incidence)) I)
    (mul (borrowed (unsigned cache.weights.head)) H)

/-- Weighted signed output remains valid denominator-one arithmetic. -/
theorem weighted_den (cache : SemiprimeSourceHistogramScales.Cache) (I H : RationalReport)
    (hI : DenOne I.word) (hH : DenOne H.word) : DenOne (weighted cache I H).word := by
  simp only [weighted,add_den,mul_den,borrowed,unsigned_den,hI,hH]

/-- Exact integer weighted score; no intermediate reduction or native decoding. -/
theorem weighted_value (cache : SemiprimeSourceHistogramScales.Cache) (I H : RationalReport)
    (hI : DenOne I.word) (hH : DenOne H.word) :
    (weighted cache I H).word.value=
      (bitValue cache.weights.incidence:ℚ)*I.word.value+(bitValue cache.weights.head:ℚ)*H.word.value := by
  simp only [weighted,add_value,mul_value,borrowed,unsigned_value,mul_den,unsigned_den,hI,hH]

/-- Actual weighted lane acquisition reports are never replaced by value-only clocks. -/
theorem weighted_retains (cache : SemiprimeSourceHistogramScales.Cache) (I H : RationalReport) :
    I.clock+H.clock ≤ (weighted cache I H).clock := by
  unfold weighted add mul borrowed
  dsimp only
  omega

end RiemannGaussian.SemiprimeSourceHistogramArithmetic
