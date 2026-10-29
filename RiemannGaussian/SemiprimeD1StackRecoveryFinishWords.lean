/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinish
import RiemannGaussian.SemiprimeSourceCompactWordIds
import RiemannGaussian.SemiprimeBitProductSort
/-! # Exact low-bit stripping and arbitrary signed floor semantics
Natural indices and signed values below are proof notation only. The source
pops actual denominator/numerator cells, records actual lost ones, and executes
the real unsigned increment for negative nonintegral quotients.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishWords
open SemiprimeBitArithmetic
open SemiprimeBitIndexClipping (SignedWord)
namespace Old
export SemiprimeD1RecoveryStripBits (acquire signed finish)
end Old
/-- Number of actually encountered leading low zeros; no such number is a runtime input or opcode. -/
def zeros:List Bool→Nat
  | false::bits=>zeros bits+1
  | _=>0
/-- Actual odd suffix after the real low-zero scan. -/
def odd (denominator:List Bool):List Bool:=denominator.drop (zeros denominator)
/-- Actual discarded low one-bit flag. -/
def lost (denominator magnitude:List Bool):Bool:=(magnitude.take (zeros denominator)).any id
/-- Actual remaining numerator cells after paired pops, defaulting to empty after numerator EOF. -/
def dropped (denominator magnitude:List Bool):List Bool:=magnitude.drop (zeros denominator)
/-- Actual raw increment is applied only for a negative numerator with at least one lost one. -/
def corrected (negative:Bool) (denominator magnitude:List Bool):List Bool:=
  if negative&&lost denominator magnitude then (addBits (dropped denominator magnitude) [true] false).bits
  else dropped denominator magnitude
/-- Actual corrected signed quotient, with arbitrary original numerator padding and both zero signs allowed. -/
def quotient (numerator:SignedWord) (denominator:List Bool):SignedWord:=
  ⟨numerator.negative,corrected numerator.negative denominator numerator.magnitude⟩
/-- Literal physically constructed shifted-one word. -/
def content (denominator:List Bool):List Bool:=List.replicate (zeros denominator) false++[true]
/-- The scan never reads more denominator cells than are physically present. -/
theorem zeros_le (bits:List Bool):zeros bits≤bits.length:=by
  induction bits with
  | nil=>rfl
  | cons b bits ih=>cases b <;> simp only [zeros,List.length_cons] <;> omega
/-- The source's actual shifted-one and odd suffix words match the old stripper byte for byte. -/
theorem acquire_words (bits:List Bool):(Old.acquire bits).content=content bits ∧ (Old.acquire bits).odd=odd bits:=by
  induction bits with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b bits ih=>
    cases b with
    | false=>
      constructor
      · simpa only [Old.acquire,content,zeros,List.replicate_succ,List.cons_append] using congrArg (false::·) ih.1
      · simpa only [Old.acquire,odd,zeros,List.drop_succ_cons] using ih.2
    | true=>
      simp only [Old.acquire,content,odd,zeros,List.replicate_zero,List.nil_append,List.drop_zero,
        SemiprimeBitProductSort.fitBits_self,and_self]
/-- The actual content word denotes the dyadic factor implied by its physical zero prefix. -/
theorem content_value (bits:List Bool):bitValue (content bits)=2^(zeros bits):=by
  unfold content
  generalize zeros bits=n
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [List.replicate_succ,List.cons_append,bitValue,bitNat,Bool.false_eq_true,ite_false,Nat.zero_add,pow_succ]
    change 2*bitValue (List.replicate n false++[true])=2^n*2
    rw [ih,Nat.mul_comm]
/-- A physical low one is present exactly when the Boolean word has positive unsigned value. -/
theorem any_positive (bits:List Bool):bits.any id=true ↔0<bitValue bits:=by
  induction bits with
  | nil=>simp [bitValue]
  | cons b bits ih=>
    cases b with
    | false=>
      simp only [List.any_cons,id_eq,Bool.false_or]
      rw [ih]
      simp [bitValue,bitNat]
    | true=>simp [List.any_cons,bitValue,bitNat]
/-- Canonical two-power split identifies the remaining physical suffix with the natural quotient. -/
theorem dropped_value (denominator magnitude:List Bool):
    bitValue (dropped denominator magnitude)=bitValue magnitude/2^(zeros denominator):=by
  have h:=SemiprimeD1JetScalarBits.bitValue_split (zeros denominator) magnitude
  have hl:=SemiprimeD1JetScalarBits.bitValue_take_lt (zeros denominator) magnitude
  unfold dropped
  rw [h,Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt hl,Nat.zero_add]
/-- The actual lost-bit flag is false exactly when division by the actual content has zero remainder. -/
theorem lost_false (denominator magnitude:List Bool):
    lost denominator magnitude=false ↔bitValue magnitude%2^(zeros denominator)=0:=by
  have hx:lost denominator magnitude=true ↔0<bitValue magnitude%2^(zeros denominator):=by
    simpa only [lost,SemiprimeD1JetScalarBits.bitValue_take] using any_positive (magnitude.take (zeros denominator))
  have hb:(lost denominator magnitude=false) ↔¬lost denominator magnitude=true:=by
    cases lost denominator magnitude <;> decide
  rw [hb,hx]
  omega
/-- The actual correction equals the old signed FLOOR quotient value, including arbitrary negative remainders. -/
theorem quotient_value (numerator:SignedWord) (denominator:List Bool):
    (quotient numerator denominator).value=numerator.value/(bitValue (content denominator):Int):=by
  rw [content_value]
  have hq:=dropped_value denominator numerator.magnitude
  have hi:=addBits_correct (dropped denominator numerator.magnitude) [true] false
  simp only [bitValue,bitNat,ite_true,Nat.mul_zero,Nat.add_zero,Bool.false_eq_true,ite_false] at hi
  cases hn:numerator.negative with
  | false=>
    simp only [quotient,corrected,hn,Bool.false_and,Bool.false_eq_true,ite_false,SemiprimeBitIndexClipping.SignedWord.value]
    rw [hq,Int.natCast_ediv]
  | true=>
    have hf:=SemiprimeBitIndexClipping.negative_nat_floor (bitValue numerator.magnitude) (2^(zeros denominator)) (by positivity)
    by_cases hm:bitValue numerator.magnitude%2^(zeros denominator)=0
    · have hl:lost denominator numerator.magnitude=false:=(lost_false denominator numerator.magnitude).mpr hm
      simp only [quotient,corrected,hn,hl,Bool.true_and,Bool.false_eq_true,ite_false,
        SemiprimeBitIndexClipping.SignedWord.value,ite_true]
      rw [hq,hf,ite_eq_left hm]
    · have hl:lost denominator numerator.magnitude=true:=by
        cases hx:lost denominator numerator.magnitude
        · exact (hm ((lost_false denominator numerator.magnitude).mp hx)).elim
        · rfl
      simp only [quotient,corrected,hn,hl,Bool.true_and,ite_true,SemiprimeBitIndexClipping.SignedWord.value]
      rw [hi,hq,hf,ite_eq_right hm]
/-- Exact old signed floor interpretation is obtained without requiring content divisibility. -/
theorem quotient_floor_original (numerator:SignedWord) (denominator:List Bool):
    (quotient numerator denominator).value=(SemiprimeBitIndexClipping.floorSignedBits numerator (Old.acquire denominator).content).word.value:=by
  rw [(acquire_words denominator).1,SemiprimeBitIndexClipping.floorSignedBits_value]
  exact quotient_value numerator denominator
end RiemannGaussian.SemiprimeD1StackRecoveryFinishWords
