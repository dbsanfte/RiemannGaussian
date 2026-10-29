/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryRowsBits
import RiemannGaussian.SemiprimeD1RecoveryCanonicalRun

/-! # Physical canonical common-denominator integer accumulator
The arithmetic path uses existing actual unsigned/signed Boolean multiplication,
addition, restoring floor division and paid fixed-width copies. Native integers
below are specifications only; no native arithmetic result is encoded.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1RecoveryIntegerBits
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitIndexClipping
open SemiprimeBitIndexTraversal SemiprimeRationalBits

/-- Actual unsigned output and its physical arithmetic/copy report. -/
structure UnsignedReport where
  /-- Actual Boolean output word. -/
  bits : List Bool
  /-- Actual gates, payload reads/writes and bounded control report. -/
  clock : ℕ

/-- Actual signed output and its physical arithmetic/copy report. -/
structure SignedReport where
  /-- Actual signed Boolean word. -/
  word : SignedWord
  /-- All executed arithmetic and copied/discarded bit payloads. -/
  clock : ℕ

/-- An unsigned word is wrapped as a positive signed word without decoding it. -/
def positive (bits : List Bool) : SignedWord := ⟨false,bits⟩

/-- Exact unsigned-to-signed payload interpretation. -/
theorem positive_value (bits : List Bool) : (positive bits).value=(bitValue bits:ℤ) := rfl

/-- Multiply actual unsigned words and copy to the public bounded store. -/
def product (template xs ys : List Bool) : UnsignedReport :=
  let raw:=mulBits xs ys
  let out:=fitBits raw.bits template
  ⟨out.bits,bitCost raw+bitCost out+3⟩

/-- Product clipping preserves the actual integer whenever original bounds fit. -/
theorem product_value (template xs ys : List Bool)
    (h : bitValue xs*bitValue ys < 2^template.length) :
    bitValue (product template xs ys).bits=bitValue xs*bitValue ys := by
  have hv:=mulBits_correct xs ys
  have hc:=fitBits_value (by rw [hv]; exact h)
  exact hc.trans hv

/-- Every unsigned product occupies exactly the public physical width. -/
theorem product_length (template xs ys : List Bool) : (product template xs ys).bits.length=template.length :=
  (fitBits_counts _ _).1

/-- Every executed unsigned multiply/copy has quadratic primitive work. -/
theorem product_clock (template xs ys : List Bool)
    (hx : xs.length ≤ template.length) (hy : ys.length ≤ template.length) :
    (product template xs ys).clock ≤ 40*(template.length+1)^2+20 := by
  have hm:=bounded_mulBits hx hy
  have hc:=fitBits_cost (mulBits xs ys).bits template
  simp only [product]
  nlinarith only [hm.1,hc]

/-- Actual signed multiplication followed by a paid bounded copy. -/
def signedProduct (template : List Bool) (x y : SignedWord) : SignedReport :=
  let raw:=mulSignedBits x y
  let out:=fitSignedBits raw.word template
  ⟨out.word,raw.clock+out.clock+3⟩

/-- No native signed multiplication executes in this data path. -/
theorem signedProduct_value (template : List Bool) (x y : SignedWord)
    (h : (x.value*y.value).natAbs < 2^template.length) :
    (signedProduct template x y).word.value=x.value*y.value := by
  have hv:=mulSignedBits_value x y
  have hc:=fitSignedBits_value (by rw [hv]; exact h)
  exact hc.trans hv

/-- Actual signed multiplication output width. -/
theorem signedProduct_length (template : List Bool) (x y : SignedWord) :
    (signedProduct template x y).word.magnitude.length=template.length :=
  (fitSignedBits_cost_width _ _).2

/-- Full signed product, normalization-by-copy and discarded payload costs. -/
theorem signedProduct_clock (template : List Bool) (x y : SignedWord)
    (hx : x.magnitude.length ≤ template.length) (hy : y.magnitude.length ≤ template.length) :
    (signedProduct template x y).clock ≤ 40*(template.length+1)^2+20 := by
  have hm:=mulSignedBits_cost_width hx hy
  have hc:=(fitSignedBits_cost_width (mulSignedBits x y).word template).1
  simp only [signedProduct]
  nlinarith only [hm.1,hc]

/-- Actual signed addition and paid clipping, with both signs represented physically. -/
def signedSum (template : List Bool) (x y : SignedWord) : SignedReport :=
  let raw:=addSignedBits x y
  let out:=fitSignedBits raw.word template
  ⟨out.word,raw.clock+out.clock+3⟩

/-- Exact signed sum from actual bit operations. -/
theorem signedSum_value (template : List Bool) (x y : SignedWord)
    (h : (x.value+y.value).natAbs < 2^template.length) :
    (signedSum template x y).word.value=x.value+y.value := by
  have hv:=addSignedBits_value x y
  have hc:=fitSignedBits_value (by rw [hv]; exact h)
  exact hc.trans hv

/-- Actual signed-sum output width. -/
theorem signedSum_length (template : List Bool) (x y : SignedWord) :
    (signedSum template x y).word.magnitude.length=template.length :=
  (fitSignedBits_cost_width _ _).2

/-- Complete signed addition/copy primitive cost. -/
theorem signedSum_clock (template : List Bool) (x y : SignedWord)
    (hx : x.magnitude.length ≤ template.length) (hy : y.magnitude.length ≤ template.length) :
    (signedSum template x y).clock ≤ 50*(template.length+1)+10 := by
  have hm:=addSignedBits_cost_width hx hy
  have hc:=(fitSignedBits_cost_width (addSignedBits x y).word template).1
  simp only [signedSum]
  omega

/-- Actual restoring signed division and bounded payload copy. -/
def quotient (template : List Bool) (x : SignedWord) (denominator : List Bool) : SignedReport :=
  let raw:=floorSignedBits x denominator
  let out:=fitSignedBits raw.word template
  ⟨out.word,raw.clock+out.clock+3⟩

/-- Floor division is the same original Euclidean integer operation. -/
theorem quotient_value (template : List Bool) (x : SignedWord) (denominator : List Bool)
    (h : (x.value/(bitValue denominator:ℤ)).natAbs < 2^template.length) :
    (quotient template x denominator).word.value=x.value/(bitValue denominator:ℤ) := by
  have hv:=floorSignedBits_value x denominator
  have hc:=fitSignedBits_value (by rw [hv]; exact h)
  exact hc.trans hv

/-- Every actual quotient output is physically bounded. -/
theorem quotient_length (template : List Bool) (x : SignedWord) (denominator : List Bool) :
    (quotient template x denominator).word.magnitude.length=template.length :=
  (fitSignedBits_cost_width _ _).2

/-- Native integer division is replaced by actual quadratic Boolean division. -/
theorem quotient_clock (template : List Bool) (x : SignedWord) (denominator : List Bool)
    (hx : x.magnitude.length ≤ template.length) (hd : denominator.length ≤ template.length) :
    (quotient template x denominator).clock ≤ 160*(template.length+1)^2+20 := by
  have hm:=floorSignedBits_cost_width hx hd
  have hc:=(fitSignedBits_cost_width (floorSignedBits x denominator).word template).1
  simp only [quotient]
  nlinarith only [hm.1,hc]

/-- Actual canonical row payloads paired with an actual child coefficient word. -/
structure Entry where
  /-- Original canonical signed numerator bits. -/
  numerator : SignedWord
  /-- Original canonical positive denominator bits. -/
  denominator : List Bool
  /-- Actual unsigned child-residue bits. -/
  child : List Bool

/-- Proof-only canonical-entry projection, never called by the bit runtime. -/
def native (es : List Entry) : List SemiprimeD1RecoveryCanonicalRun.Entry :=
  es.map fun e => ⟨e.numerator.value,bitValue e.denominator,e.child⟩

/-- Actual physical product of every canonical denominator. -/
def denominator (template : List Bool) : List Entry → UnsignedReport
  | [] => ⟨[true],3⟩
  | e::es =>
    let tail:=denominator template es
    let out:=product template e.denominator tail.bits
    ⟨out.bits,tail.clock+out.clock+3⟩

/-- The actual native canonical accumulator is followed operation for operation:
physical quotient, two signed products and one signed suffix addition. -/
def accumulate (template denominator : List Bool) : List Entry → SignedReport
  | [] => ⟨positive [],3⟩
  | e::es =>
    let tail:=accumulate template denominator es
    let cofactor:=quotient template (positive denominator) e.denominator
    let first:=signedProduct template e.numerator cofactor.word
    let second:=signedProduct template first.word (positive e.child)
    let out:=signedSum template second.word tail.word
    ⟨out.word,tail.clock+cofactor.clock+first.clock+second.clock+out.clock+8⟩

/-- The original common-denominator product is bounded from individual canonical
row heights, independently of cancellation or an advised final product. -/
theorem native_denominator_bound (es : List Entry) (A : ℕ)
    (h : ∀ e ∈ es, bitValue e.denominator ≤ 2^A) :
    (SemiprimeD1RecoveryCanonicalRun.denominator (native es)).value ≤ 2^(A*es.length) := by
  induction es with
  | nil => simp [native,SemiprimeD1RecoveryCanonicalRun.denominator]
  | cons e es ih =>
    have he:=h e (by simp)
    have ht:=ih (fun x hx => h x (by simp [hx]))
    change bitValue e.denominator *
      (SemiprimeD1RecoveryCanonicalRun.denominator (native es)).value ≤ _
    calc
      _ ≤ 2^A * 2^(A*es.length) := Nat.mul_le_mul he ht
      _ = 2^(A*(e::es).length) := by
        simp only [List.length_cons, Nat.mul_add, Nat.mul_one, pow_add]
        ac_rfl

/-- Actual denominator multiplication refines the original native traversal,
with every suffix fit derived from the individual canonical denominator caps. -/
theorem denominator_correct (template : List Bool) (es : List Entry) (A : ℕ)
    (h : ∀ e ∈ es, bitValue e.denominator ≤ 2^A)
    (hW : A*es.length+1 ≤ template.length) :
    bitValue (denominator template es).bits=
      (SemiprimeD1RecoveryCanonicalRun.denominator (native es)).value := by
  induction es with
  | nil => simp [denominator,native,SemiprimeD1RecoveryCanonicalRun.denominator,
      bitValue,bitNat]
  | cons e es ih =>
    have ht : ∀ x ∈ es, bitValue x.denominator ≤ 2^A :=
      fun x hx => h x (by simp [hx])
    have hWt : A*es.length+1 ≤ template.length := by
      simp only [List.length_cons, Nat.mul_succ] at hW
      omega
    have hv:=ih ht hWt
    have hb:=native_denominator_bound (e::es) A h
    have he : bitValue e.denominator * bitValue (denominator template es).bits <
        2^template.length := by
      rw [hv]
      change bitValue e.denominator *
        (SemiprimeD1RecoveryCanonicalRun.denominator (native es)).value ≤ _ at hb
      exact lt_of_le_of_lt hb (Nat.pow_lt_pow_right (by omega) (by omega))
    exact product_value template e.denominator (denominator template es).bits he |>.trans
      (by rw [hv]; rfl)

/-- Every native right-recursive signed suffix has a cancellation-independent
triangle bound from the actual individual input words. -/
theorem native_accumulate_bound (D A C : ℕ) (es : List Entry)
    (ha : ∀ e ∈ es, e.numerator.value.natAbs ≤ A)
    (hc : ∀ e ∈ es, bitValue e.child ≤ C) :
    (SemiprimeD1RecoveryCanonicalRun.accumulate D (native es)).value.natAbs ≤
      es.length*A*D*C := by
  induction es with
  | nil => simp [native,SemiprimeD1RecoveryCanonicalRun.accumulate]
  | cons e es ih =>
    have hA:=ha e (by simp)
    have hC:=hc e (by simp)
    have ht:=ih (fun x hx => ha x (by simp [hx])) (fun x hx => hc x (by simp [hx]))
    have hd : D / bitValue e.denominator ≤ D := Nat.div_le_self _ _
    have he : (e.numerator.value * ((D / bitValue e.denominator : ℕ):ℤ) *
        (bitValue e.child:ℤ)).natAbs ≤ A*D*C := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.mul_le_mul (Nat.mul_le_mul hA hd) hC
    have hs:=Int.natAbs_add_le (e.numerator.value * ((D / bitValue e.denominator:ℕ):ℤ) *
      (bitValue e.child:ℤ))
      (SemiprimeD1RecoveryCanonicalRun.accumulate D (native es)).value
    simp only [native,List.map_cons,SemiprimeD1RecoveryCanonicalRun.accumulate,
      SemiprimeD1IntegerRecovery.decode_eq]
    change (e.numerator.value * ((D / bitValue e.denominator:ℕ):ℤ) *
      (bitValue e.child:ℤ) +
      (SemiprimeD1RecoveryCanonicalRun.accumulate D (native es)).value).natAbs ≤ _
    calc
      _ ≤ A*D*C + es.length*A*D*C := hs.trans (Nat.add_le_add he ht)
      _ = (e::es).length*A*D*C := by simp only [List.length_cons]; ring

/-- Actual signed suffix arithmetic is exact from input-derived triangle caps.
The four guards bound cofactor/product/suffix sizes, not advised outputs. -/
theorem accumulate_correct (template denominatorBits : List Bool) (es : List Entry)
    (D A C : ℕ) (hD : bitValue denominatorBits=D)
    (ha : ∀ e ∈ es, e.numerator.value.natAbs ≤ A)
    (hc : ∀ e ∈ es, bitValue e.child ≤ C)
    (hd : D < 2^template.length) (hAD : A*D < 2^template.length)
    (hADC : A*D*C < 2^template.length)
    (hS : es.length*A*D*C < 2^template.length) :
    (accumulate template denominatorBits es).word.value=
      (SemiprimeD1RecoveryCanonicalRun.accumulate D (native es)).value := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hA:=ha e (by simp)
    have hC:=hc e (by simp)
    have hAt : ∀ x ∈ es, x.numerator.value.natAbs ≤ A :=
      fun x hx => ha x (by simp [hx])
    have hCt : ∀ x ∈ es, bitValue x.child ≤ C :=
      fun x hx => hc x (by simp [hx])
    have hSt : es.length*A*D*C < 2^template.length := by
      have hm : es.length*A*D*C ≤ (e::es).length*A*D*C :=
        Nat.mul_le_mul_right C (Nat.mul_le_mul_right D
          (Nat.mul_le_mul_right A (by simp)))
      exact lt_of_le_of_lt hm hS
    have ht:=ih hAt hCt hSt
    have hdiv : D / bitValue e.denominator ≤ D := Nat.div_le_self _ _
    have hvq : (quotient template (positive denominatorBits) e.denominator).word.value=
        ((D / bitValue e.denominator:ℕ):ℤ) := by
      have hfit : ((positive denominatorBits).value / (bitValue e.denominator:ℤ)).natAbs <
          2^template.length := by
        rw [positive_value,hD,←Int.natCast_ediv,Int.natAbs_natCast]
        exact lt_of_le_of_lt hdiv hd
      rw [quotient_value _ _ _ hfit,positive_value,hD,←Int.natCast_ediv]
    have hp1 : (e.numerator.value *
        (quotient template (positive denominatorBits) e.denominator).word.value).natAbs ≤ A*D := by
      rw [hvq,Int.natAbs_mul,Int.natAbs_natCast]
      exact Nat.mul_le_mul hA hdiv
    have hv1:=signedProduct_value template e.numerator
      (quotient template (positive denominatorBits) e.denominator).word
      (lt_of_le_of_lt hp1 hAD)
    have hp2 : ((signedProduct template e.numerator
        (quotient template (positive denominatorBits) e.denominator).word).word.value *
        (positive e.child).value).natAbs ≤ A*D*C := by
      rw [Int.natAbs_mul,positive_value,Int.natAbs_natCast]
      exact Nat.mul_le_mul (by rw [hv1]; exact hp1) hC
    have hv2:=signedProduct_value template
      (signedProduct template e.numerator
        (quotient template (positive denominatorBits) e.denominator).word).word
      (positive e.child) (lt_of_le_of_lt hp2 hADC)
    have hsBound:=native_accumulate_bound D A C (e::es) ha hc
    have hvsum : ((signedProduct template
        (signedProduct template e.numerator
          (quotient template (positive denominatorBits) e.denominator).word).word
        (positive e.child)).word.value + (accumulate template denominatorBits es).word.value).natAbs <
          2^template.length := by
      rw [hv2,hv1,hvq,positive_value,ht]
      simpa only [native,List.map_cons,SemiprimeD1RecoveryCanonicalRun.accumulate,
        SemiprimeD1IntegerRecovery.decode_eq] using lt_of_le_of_lt hsBound hS
    change (signedSum template _ _).word.value = _
    rw [signedSum_value _ _ _ hvsum,hv2,hv1,hvq,positive_value,ht]
    simp only [native,List.map_cons,SemiprimeD1RecoveryCanonicalRun.accumulate,
      SemiprimeD1IntegerRecovery.decode_eq]

/-- Every physical signed suffix occupies the public bounded store. -/
theorem accumulate_length (template denominatorBits : List Bool) (es : List Entry) :
    (accumulate template denominatorBits es).word.magnitude.length ≤ template.length := by
  cases es with
  | nil => simp [accumulate,positive]
  | cons e es => exact (signedSum_length _ _ _).le

/-- The product store has one public width, including the literal empty product. -/
theorem denominator_length (template : List Bool) (es : List Entry) (ht : 0 < template.length) :
    (denominator template es).bits.length ≤ template.length := by
  cases es with
  | nil => change 1 ≤ template.length; omega
  | cons e es => exact (product_length _ _ _).le

/-- Actual denominator scans/multiplications and fixed-store copies are paid. -/
theorem denominator_clock (template : List Bool) (es : List Entry) (ht : 0 < template.length)
    (he : ∀ e ∈ es, e.denominator.length ≤ template.length) :
    (denominator template es).clock ≤ es.length*(40*(template.length+1)^2+23)+3 := by
  induction es with
  | nil => simp [denominator]
  | cons e es ih =>
    have hc:=product_clock template e.denominator (denominator template es).bits
      (he e (by simp)) (denominator_length template es ht)
    have hi:=ih (fun x hx => he x (by simp [hx]))
    change (denominator template es).clock +
      (product template e.denominator (denominator template es).bits).clock+3 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Every actual division, signed product/addition and copied word of the
right-recursive accumulator is charged. -/
theorem accumulate_clock (template denominatorBits : List Bool) (es : List Entry)
    (hd : denominatorBits.length ≤ template.length)
    (he : ∀ e ∈ es, e.numerator.magnitude.length ≤ template.length ∧
      e.denominator.length ≤ template.length ∧ e.child.length ≤ template.length) :
    (accumulate template denominatorBits es).clock ≤
      es.length*(300*(template.length+1)^2+100)+3 := by
  induction es with
  | nil => simp [accumulate]
  | cons e es ih =>
    have hE:=he e (by simp)
    have hq:=quotient_clock template (positive denominatorBits) e.denominator hd hE.2.1
    have h1:=signedProduct_clock template e.numerator
      (quotient template (positive denominatorBits) e.denominator).word hE.1
      (quotient_length _ _ _).le
    have h2:=signedProduct_clock template
      (signedProduct template e.numerator
        (quotient template (positive denominatorBits) e.denominator).word).word
      (positive e.child) (signedProduct_length _ _ _).le hE.2.2
    have hs:=signedSum_clock template
      (signedProduct template
        (signedProduct template e.numerator
          (quotient template (positive denominatorBits) e.denominator).word).word
        (positive e.child)).word (accumulate template denominatorBits es).word
      (signedProduct_length _ _ _).le (accumulate_length _ _ _)
    have hi:=ih (fun x hx => he x (by simp [hx]))
    change (accumulate template denominatorBits es).clock + _ + _ + _ + _ + 8 ≤ _
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    nlinarith only [hq,h1,h2,hs,hi]

/-- Dyadic source-row and actual child-length bounds discharge every signed
cofactor/product/suffix guard. No intermediate or output Fits is assumed. -/
theorem accumulate_dyadic (template denominatorBits : List Bool) (es : List Entry)
    (D A K P : ℕ) (hD : bitValue denominatorBits=D)
    (ha : ∀ e ∈ es, e.numerator.value.natAbs ≤ 2^A)
    (hc : ∀ e ∈ es, e.child.length ≤ P)
    (hl : es.length ≤ K) (hd : D ≤ 2^(A*K))
    (hW : K+A+A*K+P+1 ≤ template.length) :
    (accumulate template denominatorBits es).word.value=
      (SemiprimeD1RecoveryCanonicalRun.accumulate D (native es)).value := by
  have hC : ∀ e ∈ es, bitValue e.child ≤ 2^P := by
    intro e he
    exact (bitValue_lt_width e.child).le.trans (Nat.pow_le_pow_right (by omega) (hc e he))
  have hAD : 2^A*D ≤ 2^(A+A*K) := by
    simpa only [pow_add] using Nat.mul_le_mul_left (2^A) hd
  have hADC : 2^A*D*2^P ≤ 2^(A+A*K+P) := by
    simpa only [pow_add] using Nat.mul_le_mul_right (2^P) hAD
  have hS : es.length*2^A*D*2^P ≤ 2^(K+A+A*K+P) := by
    have hlp:=hl.trans (SemiprimeD1HermiteDenominatorBits.self_le_two_power K)
    calc
      _ = es.length*(2^A*D*2^P) := by ring
      _ ≤ 2^K*2^(A+A*K+P) := Nat.mul_le_mul hlp hADC
      _ = _ := by simp only [←pow_add]; congr 1; omega
  apply accumulate_correct template denominatorBits es D (2^A) (2^P) hD ha hC
  · exact lt_of_le_of_lt hd (Nat.pow_lt_pow_right (by omega) (by omega))
  · exact lt_of_le_of_lt hAD (Nat.pow_lt_pow_right (by omega) (by omega))
  · exact lt_of_le_of_lt hADC (Nat.pow_lt_pow_right (by omega) (by omega))
  · exact lt_of_le_of_lt hS (Nat.pow_lt_pow_right (by omega) (by omega))

end RiemannGaussian.SemiprimeD1RecoveryIntegerBits
