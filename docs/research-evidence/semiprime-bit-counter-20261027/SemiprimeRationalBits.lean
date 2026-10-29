/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBitIndexTraversal
import RiemannGaussian.SemiprimeJetArrayHeight

/-!
# Exact rational arithmetic on Boolean words

The data path uses signed Boolean arithmetic, Euclidean GCD, restoring division,
and paid physical copies. Rational interpretation and reduced numerator bounds
are specifications only; no executable routine calls them.
-/
set_option autoImplicit false
set_option maxRecDepth 2000
namespace RiemannGaussian.SemiprimeRationalBits
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitGcd
open SemiprimeBitIndexClipping SemiprimeBitIndexGeometry SemiprimeBitIndexTraversal

/-- A signed numerator and an unsigned denominator, both physical Boolean words. -/
structure RationalWord where
  /-- Signed physical numerator. -/
  numerator : SignedWord
  /-- Physical nonnegative denominator. -/
  denominator : List Bool

/-- Mathematical interpretation, never called by the Boolean data path. -/
def RationalWord.value (x : RationalWord) : ℚ :=
  (x.numerator.value : ℚ) / (bitValue x.denominator : ℚ)

/-- Legal rational encodings have positive denominator. -/
def RationalWord.Valid (x : RationalWord) : Prop := 0 < bitValue x.denominator

/-- Actual arithmetic output and charged Boolean/cell/branch work. -/
structure RationalReport where
  /-- The actual computed physical output. -/
  word : RationalWord
  /-- Primitive work, including all discarded arithmetic and padding. -/
  clock : ℕ

/-- Literal zero encoding with denominator one. -/
def zeroWord : RationalWord := ⟨⟨false,[]⟩,[true]⟩

/-- Reduce by an actually computed GCD. A zero physical denominator produces
the totalized rational zero, using the actual denominator scan. -/
def reduceBits (x : RationalWord) : RationalReport :=
  let check := nonzeroBits x.denominator
  if check.nonzero = true then
    let gcd := gcdBits x.numerator.magnitude x.denominator
    let num := floorSignedBits x.numerator gcd.bits
    let den := divideBits x.denominator gcd.bits
    ⟨⟨num.word, den.quotient⟩, check.clock + gcd.clock + num.clock + den.clock + 8⟩
  else ⟨zeroWord, check.clock + 4⟩

theorem value_eq_mkRat (x : RationalWord) :
    x.value = mkRat x.numerator.value (bitValue x.denominator) := by
  rw [RationalWord.value, Rat.mkRat_eq_divInt, Rat.divInt_eq_div, Int.cast_natCast]

/-- GCD reduction produces the actual canonical integer numerator and positive
denominator of the input's rational value, including either sign of zero. -/
theorem reduceBits_components (x : RationalWord) :
    (reduceBits x).word.numerator.value = x.value.num ∧
      bitValue (reduceBits x).word.denominator = x.value.den := by
  by_cases hd : (nonzeroBits x.denominator).nonzero = true
  · have hdpos := (nonzeroBits_correct x.denominator).mp hd
    simp only [reduceBits, hd, reduceIte]
    rw [floorSignedBits_value, (divideBits_correct _ _).1, (gcdBits_correct _ _).1]
    rw [value_eq_mkRat, Rat.num_mkRat, Rat.den_mkRat, signedWord_natAbs]
    simp only [Nat.ne_of_gt hdpos, reduceIte, Nat.gcd_comm]
    trivial
  · have hz : bitValue x.denominator = 0 := by
      have h := (nonzeroBits_correct x.denominator).not.mp hd
      omega
    simp [reduceBits, hd, zeroWord, RationalWord.value, hz, SignedWord.value, bitValue, bitNat]

/-- Canonical reduction preserves the exact rational value. -/
theorem reduceBits_value (x : RationalWord) : (reduceBits x).word.value = x.value := by
  have h := reduceBits_components x
  simp only [RationalWord.value, h.1, h.2]
  exact Rat.num_div_den x.value

theorem reduceBits_valid (x : RationalWord) : (reduceBits x).word.Valid := by
  change 0 < bitValue (reduceBits x).word.denominator
  rw [(reduceBits_components x).2]
  exact x.value.den_pos

private theorem reduction_cost_envelope (W : ℕ) :
    3*W+1 + 400*(W+1)^3 + 150*(W+1)^2 + 72*(W+1)^2 + 8 ≤ 700*(W+1)^3 := by
  nlinarith

/-- Full physical reduction work is cubic in its actual input width. The
unused rounding increment of the signed divider is included. -/
theorem reduceBits_cost_width {W : ℕ} (x : RationalWord)
    (hn : x.numerator.magnitude.length ≤ W) (hd : x.denominator.length ≤ W) :
    (reduceBits x).clock ≤ 700*(W+1)^3 ∧
      (reduceBits x).word.numerator.magnitude.length ≤ W+2 ∧
      (reduceBits x).word.denominator.length ≤ W+2 := by
  have hc := nonzeroBits_cost x.denominator
  have hg := gcdBits_cost hn hd
  have hgw := gcdBits_width hn hd
  have hnum := floorSignedBits_cost_width hn hgw
  have hden := bounded_divideBits (by omega : x.denominator.length ≤ 3*W) hgw
  have hdenw := (divideBits_all_width x.denominator (gcdBits x.numerator.magnitude x.denominator).bits).1
  have hpoly := reduction_cost_envelope W
  unfold reduceBits
  dsimp only
  split
  · dsimp only
    refine ⟨?_,hnum.2,by omega⟩
    omega
  · simp only [zeroWord, List.length_nil, List.length_cons]
    refine ⟨?_,by omega,by omega⟩
    omega

/-- Reduce, then physically copy both words to the supplied public template.
The correctness theorem proves that these paid copies lose no information. -/
def fitRationalBits (x : RationalWord) (template : List Bool) : RationalReport :=
  let reduced := reduceBits x
  let num := fitSignedBits reduced.word.numerator template
  let den := fitBits reduced.word.denominator template
  ⟨⟨num.word,den.bits⟩, reduced.clock + num.clock + bitCost den + 4⟩

/-- All actual outputs occupy exactly the public width, even when their values
are zero. No uncharged canonical trimming is used. -/
theorem fitRationalBits_width (x : RationalWord) (template : List Bool) :
    (fitRationalBits x template).word.numerator.magnitude.length = template.length ∧
      (fitRationalBits x template).word.denominator.length = template.length := by
  exact ⟨(fitSignedBits_cost_width _ _).2, (fitBits_counts _ _).1⟩

theorem fitRationalBits_components (x : RationalWord) (template : List Bool)
    (hn : x.value.num.natAbs < 2^template.length) (hd : x.value.den < 2^template.length) :
    (fitRationalBits x template).word.numerator.value = x.value.num ∧
      bitValue (fitRationalBits x template).word.denominator = x.value.den := by
  have h := reduceBits_components x
  have hn' : (reduceBits x).word.numerator.value.natAbs < 2^template.length := by rw [h.1];exact hn
  have hd' : bitValue (reduceBits x).word.denominator < 2^template.length := by rw [h.2];exact hd
  exact ⟨(fitSignedBits_value hn').trans h.1, (fitBits_value hd').trans h.2⟩

/-- Derived semantic numerator/denominator heights imply correct bounded-width
execution; the data path never consults the rational specification. -/
theorem fitRationalBits_value (x : RationalWord) (template : List Bool)
    (hn : x.value.num.natAbs < 2^template.length) (hd : x.value.den < 2^template.length) :
    (fitRationalBits x template).word.value = x.value ∧
      (fitRationalBits x template).word.Valid := by
  have h := fitRationalBits_components x template hn hd
  constructor
  · simp only [RationalWord.value, h.1, h.2]
    exact Rat.num_div_den x.value
  · change 0 < bitValue (fitRationalBits x template).word.denominator
    rw [h.2]
    exact x.value.den_pos

theorem fitRationalBits_cost {W : ℕ} (x : RationalWord) (template : List Bool)
    (hn : x.numerator.magnitude.length ≤ W) (hd : x.denominator.length ≤ W) :
    (fitRationalBits x template).clock ≤ 700*(W+1)^3 + 8*template.length + 9 := by
  have hr := (reduceBits_cost_width x hn hd).1
  have hnum := (fitSignedBits_cost_width (reduceBits x).word.numerator template).1
  have hden := fitBits_cost (reduceBits x).word.denominator template
  dsimp only [fitRationalBits]
  omega

/-- Cross-multiplied signed addition, before GCD reduction. -/
def rawAddBits (x y : RationalWord) : RationalReport :=
  let left := mulSignedBits x.numerator ⟨false,y.denominator⟩
  let right := mulSignedBits y.numerator ⟨false,x.denominator⟩
  let num := addSignedBits left.word right.word
  let den := mulBits x.denominator y.denominator
  ⟨⟨num.word,den.bits⟩,left.clock+right.clock+num.clock+bitCost den+6⟩

theorem rawAddBits_value (x y : RationalWord) (hx : x.Valid) (hy : y.Valid) :
    (rawAddBits x y).word.value = x.value+y.value := by
  have hdx : (bitValue x.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hx
  have hdy : (bitValue y.denominator : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hy
  simp only [RationalWord.value, rawAddBits]
  rw [addSignedBits_value, mulSignedBits_value, mulSignedBits_value, mulBits_correct]
  change (((x.numerator.value * (bitValue y.denominator : ℤ) +
    y.numerator.value * (bitValue x.denominator : ℤ) : ℤ) : ℚ) /
    ((bitValue x.denominator * bitValue y.denominator : ℕ) : ℚ)) = _
  push_cast
  field_simp

/-- Signed product and actual unsigned denominator product, before reduction. -/
def rawMulBits (x y : RationalWord) : RationalReport :=
  let num := mulSignedBits x.numerator y.numerator
  let den := mulBits x.denominator y.denominator
  ⟨⟨num.word,den.bits⟩,num.clock+bitCost den+4⟩

theorem rawMulBits_value (x y : RationalWord) :
    (rawMulBits x y).word.value = x.value*y.value := by
  simp only [RationalWord.value, rawMulBits, mulSignedBits_value, mulBits_correct,
    Int.cast_mul, Nat.cast_mul, div_mul_div_comm]

/-- Negation changes the sign bit and pays that gate. -/
def rawNegBits (x : RationalWord) : RationalReport :=
  ⟨⟨negateWord x.numerator,x.denominator⟩,3⟩

theorem rawNegBits_value (x : RationalWord) : (rawNegBits x).word.value = -x.value := by
  simp only [rawNegBits, RationalWord.value, negateWord_value, Int.cast_neg, neg_div]

/-- Inversion swaps the actual magnitude and denominator words, retaining the
sign. The following reduction handles zero numerator by its physical scan. -/
def rawInvBits (x : RationalWord) : RationalReport :=
  ⟨⟨⟨x.numerator.negative,x.denominator⟩,x.numerator.magnitude⟩,4⟩

theorem rawInvBits_value (x : RationalWord) : (rawInvBits x).word.value = x.value⁻¹ := by
  cases h : x.numerator.negative <;>
    simp [rawInvBits, RationalWord.value, SignedWord.value, h, inv_div, neg_div]

/-- Uniform shape bound for a physical rational word. -/
def Width (x : RationalWord) (W : ℕ) : Prop :=
  x.numerator.magnitude.length ≤ W ∧ x.denominator.length ≤ W

private theorem addition_cost_envelope (W : ℕ) :
    2*(24*(W+1)^2+4) + 40*(3*W+1) + (24*(W+1)^2+1) + 6 ≤ 300*(W+1)^2 := by
  nlinarith

theorem rawAddBits_cost_width {W : ℕ} (x y : RationalWord)
    (hx : Width x W) (hy : Width y W) :
    (rawAddBits x y).clock ≤ 300*(W+1)^2 ∧ Width (rawAddBits x y).word (3*W+1) := by
  have hl := mulSignedBits_cost_width hx.1 (right := ⟨false,y.denominator⟩) hy.2
  have hr := mulSignedBits_cost_width hy.1 (right := ⟨false,x.denominator⟩) hx.2
  have hn := addSignedBits_cost_width hl.2 hr.2
  have hd := bounded_mulBits hx.2 hy.2
  have hp := addition_cost_envelope W
  dsimp only [rawAddBits, Width]
  exact ⟨by omega, hn.2, by omega⟩

theorem rawMulBits_cost_width {W : ℕ} (x y : RationalWord)
    (hx : Width x W) (hy : Width y W) :
    (rawMulBits x y).clock ≤ 300*(W+1)^2 ∧ Width (rawMulBits x y).word (3*W+1) := by
  have hn := mulSignedBits_cost_width hx.1 hy.1
  have hd := bounded_mulBits hx.2 hy.2
  dsimp only [rawMulBits, Width]
  refine ⟨?_,by omega,by omega⟩
  nlinarith [Nat.one_le_pow 2 (W+1) (by omega)]

/-- The four rational operations used by the counter and cached recurrence. -/
inductive Operation where
  | add
  | mul
  | neg
  | inv

/-- Mathematical meaning of a rational instruction. -/
def Operation.value (op : Operation) (x y : ℚ) : ℚ :=
  match op with
  | .add => x+y
  | .mul => x*y
  | .neg => -x
  | .inv => x⁻¹

/-- Actual Boolean raw instruction; unary operations do not read y's words. -/
def rawOperation (op : Operation) (x y : RationalWord) : RationalReport :=
  match op with
  | .add => rawAddBits x y
  | .mul => rawMulBits x y
  | .neg => rawNegBits x
  | .inv => rawInvBits x

theorem rawOperation_value (op : Operation) (x y : RationalWord)
    (hx : x.Valid) (hy : y.Valid) :
    (rawOperation op x y).word.value = op.value x.value y.value := by
  cases op with
  | add => exact rawAddBits_value x y hx hy
  | mul => exact rawMulBits_value x y
  | neg => exact rawNegBits_value x
  | inv => exact rawInvBits_value x

theorem rawOperation_cost_width {W : ℕ} (op : Operation) (x y : RationalWord)
    (hx : Width x W) (hy : Width y W) :
    (rawOperation op x y).clock ≤ 300*(W+1)^2 ∧
      Width (rawOperation op x y).word (3*W+1) := by
  have hp : 1 ≤ (W+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hxn := hx.1
  have hxd := hx.2
  cases op with
  | add => exact rawAddBits_cost_width x y hx hy
  | mul => exact rawMulBits_cost_width x y hx hy
  | neg =>
    dsimp only [rawOperation, rawNegBits, Width, negateWord]
    exact ⟨by omega,by omega,by omega⟩
  | inv =>
    dsimp only [rawOperation, rawInvBits, Width]
    exact ⟨by omega,by omega,by omega⟩

/-- A complete instruction: actual Boolean arithmetic, actual GCD reduction,
then paid fixed-width copying. The clock includes all three phases. -/
def executeOperation (op : Operation) (x y : RationalWord) (template : List Bool) : RationalReport :=
  let raw := rawOperation op x y
  let fitted := fitRationalBits raw.word template
  ⟨fitted.word,raw.clock+fitted.clock+3⟩

/-- Semantic coefficient heights, used only in the correctness proof. -/
def Fits (q : ℚ) (W : ℕ) : Prop := q.num.natAbs < 2^W ∧ q.den < 2^W

theorem executeOperation_correct (op : Operation) (x y : RationalWord) (template : List Bool)
    (hx : x.Valid) (hy : y.Valid) (hb : Fits (op.value x.value y.value) template.length) :
    (executeOperation op x y template).word.value = op.value x.value y.value ∧
      (executeOperation op x y template).word.Valid ∧
      Width (executeOperation op x y template).word template.length := by
  have he := rawOperation_value op x y hx hy
  have hb' : Fits (rawOperation op x y).word.value template.length := by rw [he];exact hb
  have hc := fitRationalBits_value (rawOperation op x y).word template hb'.1 hb'.2
  have hw := fitRationalBits_width (rawOperation op x y).word template
  exact ⟨hc.1.trans he,hc.2,hw.1.le,hw.2.le⟩

private theorem operation_cost_envelope (W : ℕ) :
    300*(W+1)^2 + (700*(3*W+2)^3+8*W+9) + 3 ≤ 20000*(W+1)^3 := by
  nlinarith

/-- Every rational instruction has cubic charged bit work at fixed physical
width, including reduction, full scans, padding and discarded intermediates. -/
theorem executeOperation_cost {W : ℕ} (op : Operation) (x y : RationalWord) (template : List Bool)
    (hx : Width x W) (hy : Width y W) (ht : template.length ≤ W) :
    (executeOperation op x y template).clock ≤ 20000*(W+1)^3 := by
  have hr := rawOperation_cost_width op x y hx hy
  have hf := fitRationalBits_cost (rawOperation op x y).word template hr.2.1 hr.2.2
  have hi : 3*W+1+1=3*W+2 := by omega
  rw [hi] at hf
  have hp := operation_cost_envelope W
  dsimp only [executeOperation]
  omega

/-- The constructor-derived common-denominator bounds feed the bit execution
theorem directly; no separate reduced-output height promise is required. -/
theorem fits_of_representation {q : ℚ} {d B W : ℕ} (hd : 0<d)
    (h : SemiprimeJetArrayHeight.Representation q d B) (hB : B<2^W) (hdW : d<2^W) : Fits q W := by
  have hr := SemiprimeJetArrayHeight.representation_reduced_bound hd h
  exact ⟨hr.2.trans_lt hB, hr.1.trans_lt hdW⟩

end RiemannGaussian.SemiprimeRationalBits
