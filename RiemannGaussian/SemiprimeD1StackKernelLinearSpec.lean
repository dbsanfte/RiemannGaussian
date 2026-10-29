/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1NormalizedLinearBits
import RiemannGaussian.SemiprimeD1StackAssignmentOrder
import RiemannGaussian.SemiprimeBitProductSort
import RiemannGaussian.SemiprimeEncodedRowSelection
/-! # Raw-word specification of actual cancelled-factor acquisition
These functions and equalities describe physical words only; the fixed source
has no arithmetic specification, factor or cost object in its runtime state.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackKernelLinearSpec
open SemiprimeBitArithmetic SemiprimeBitDivision SemiprimeBitIndexClipping
open SemiprimeD1RecoveryIntegerBits
/-- Actual little-endian shifted one, including its high bit. -/
def power (n:Nat):List Bool:=List.replicate n false++[true]
/-- Physical unary width template. Its bit value is never used. -/
def width (n:Nat):List Bool:=List.replicate n true
/-- Actual fit bytes, including arbitrary input padding and truncation. -/
def fit (xs:List Bool) (n:Nat):List Bool:=(fitBits xs (width n)).bits
/-- The full binary sum acquired before displacement subtraction. -/
def sum (a:Nat) (y:List Bool):List Bool:=(addBits (power a) y false).bits
/-- Actual full displacement subtraction report. -/
def displaced (a:Nat) (x y:List Bool):SubReport:=subBits (sum a y) x false
/-- Exact fitted original grid-index word. -/
def grid (a:Nat) (t:List Bool):List Bool:=fit t (a+1)
/-- Exact fitted cancelled-displacement word. -/
def cancelled (a:Nat) (x y:List Bool):List Bool:=fit (displaced a x y).result.bits (a+1)
/-- The actual first borrow determines the sign and second subtraction. -/
def negative (j d:List Bool):Bool:=(subBits j d false).borrow
/-- Actual padded absolute difference, before physical stripping. -/
def magnitude (j d:List Bool):List Bool:=
  if negative j d then (subBits d j false).result.bits else (subBits j d false).result.bits
/-- Raw canonical source-factor specification, not an executed getter. -/
def factor (k:Nat) (j d:List Bool):SemiprimeD1NormalizedLinearBits.Run:=
  SemiprimeD1NormalizedLinearBits.acquire k j d
/-- Actual alpha word is the shifted-one source with k+1 bits. -/
theorem alpha_word (k:Nat):(SemiprimeD1NormalizedLinearBits.alpha k).bits=power k:=by
  induction k with
  | zero=>rfl
  | succ k ih=>simpa only [SemiprimeD1NormalizedLinearBits.alpha,List.replicate_succ,
      SemiprimeBitFermatArithmetic.shiftTemplateBits,power,List.cons_append] using congrArg (List.cons false) ih
/-- Exact physical shifted-one value. -/
theorem power_value (n:Nat):bitValue (power n)=2^n:=by
  rw [←alpha_word]
  exact SemiprimeD1NormalizedLinearBits.alpha_value n
/-- All allocated alpha bits are counted. -/
theorem power_length (n:Nat):(power n).length=n+1:=by simp [power]
/-- The fit has exactly the requested physical width. -/
theorem fit_length (xs:List Bool) (n:Nat):(fit xs n).length=n:=by
  simpa only [fit,width,List.length_replicate] using (fitBits_counts xs (width n)).1
/-- Word fitting agrees with the original fixed-width digit constructor byte for byte. -/
theorem fit_digits (xs:List Bool) (n:Nat) (h:bitValue xs<2^n):
    fit xs n=(SemiprimeEncodedRowSelection.digits n (bitValue xs)).bits:=by
  apply SemiprimeD1StackAssignmentOrder.word_value_injective
  · rw [fit_length,SemiprimeEncodedRowSelection.digits_length]
  · rw [SemiprimeEncodedRowSelection.digits_value n (bitValue xs) h]
    exact fitBits_value (by simpa only [width,List.length_replicate] using h)
/-- The physical sum is exact on all padded original source words. -/
theorem sum_value (a:Nat) (y:List Bool):bitValue (sum a y)=2^a+bitValue y:=by
  simpa only [sum,power_value,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero]
    using addBits_correct (power a) y false
/-- Original x range makes the executed displacement borrow false. -/
theorem displaced_borrow (a:Nat) (x y:List Bool) (hx:bitValue x<2^a):
    (displaced a x y).borrow=false:=by
  cases h:(displaced a x y).borrow with
  | false=>rfl
  | true=>
    have hh:bitValue (sum a y)<bitValue x:=by
      simpa only [displaced,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero]
        using (subBits_borrow_iff (sum a y) x false).mp h
    rw [sum_value] at hh
    omega
/-- The subtraction and both fits acquire the actual original cancelled grid word. -/
theorem cancelled_digits (a:Nat) (x y:List Bool) (hx:bitValue x<2^a) (hy:bitValue y<2^a):
    cancelled a x y=(SemiprimeEncodedRowSelection.digits (a+1) (2^a+bitValue y-bitValue x)).bits:=by
  have h:=displaced_borrow a x y hx
  have hv:bitValue (displaced a x y).result.bits=2^a+bitValue y-bitValue x:=by
    rw [displaced,subBits_difference h,sum_value]
  have hb:bitValue (displaced a x y).result.bits<2^(a+1):=by rw [hv,pow_succ];omega
  exact (fit_digits _ _ hb).trans (congrArg (fun n=>(SemiprimeEncodedRowSelection.digits (a+1) n).bits) hv)
/-- Physical chosen subtraction matches the original signed-difference record RAW bytes. -/
theorem difference_word (j d:List Bool):
    (subSignedBits (positive j) (positive d)).word=⟨negative j d,magnitude j d⟩:=by
  unfold subSignedBits addSignedBits positive negateWord
  simp only [Bool.false_eq_true,Bool.not_false,Bool.false_eq_true,ite_false]
  unfold negative magnitude
  cases h:(subBits j d false).borrow <;> simp [h,negative]
/-- A copied positive suffix is byte-exact even with high zero padding. -/
theorem strip_one (xs:List Bool):
    (SemiprimeD1RecoveryStripBits.acquire (true::xs)).odd=true::xs:=by
  exact SemiprimeBitProductSort.fitBits_self _
/-- Number of physically inspected low zero bits, including all-zero padding. -/
def leading : List Bool→Nat
  | []=>0 | false::xs=>leading xs+1 | true::_=>0
/-- Exact high suffix retained after the first actual one. -/
def odd : List Bool→List Bool
  | []=>[] | false::xs=>odd xs | true::xs=>true::xs
/-- The actual low-zero scan decomposes all original physical bits. -/
theorem decompose (xs:List Bool):xs=List.replicate (leading xs) false++odd xs:=by
  induction xs with
  | nil=>rfl
  | cons b xs ih=>
    cases b
    · simpa only [leading,odd,List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih
    · rfl
/-- Every acquired odd suffix is literally empty or starts with a real one. -/
theorem odd_cases (xs:List Bool):odd xs=[] ∨ ∃tail,odd xs=true::tail:=by
  induction xs with
  | nil=>exact Or.inl rfl
  | cons b xs ih=>
    cases b with
    | false=>exact ih
    | true=>exact Or.inr ⟨xs,rfl⟩
/-- The original stripping report has exactly the same complete content/suffix bytes. -/
theorem strip_bytes (xs:List Bool):
    (SemiprimeD1RecoveryStripBits.acquire xs).content=power (leading xs) ∧
    (SemiprimeD1RecoveryStripBits.acquire xs).odd=odd xs:=by
  induction xs with
  | nil=>exact ⟨rfl,rfl⟩
  | cons b xs ih=>
    cases b
    · simpa only [SemiprimeD1RecoveryStripBits.acquire,leading,odd,power,List.replicate_succ,List.cons_append] using
        And.intro (congrArg (List.cons false) ih.1) ih.2
    · exact ⟨rfl,strip_one xs⟩
/-- Exact all-zero testing distinguishes the physical empty suffix. -/
theorem odd_empty_iff (xs:List Bool):odd xs=[] ↔ bitValue xs=0:=by
  induction xs with
  | nil=>simp [odd,bitValue]
  | cons b xs ih=>
    cases b with
    | false=>
      simpa only [odd,bitValue,bitNat,Bool.false_eq_true,ite_false,Nat.zero_add] using
        (ih.trans (by omega : bitValue xs=0 ↔ 2*bitValue xs=0))
    | true=>simp [odd,bitValue,bitNat]
/-- Every nonzero strip content is a positive actual binary divisor. -/
theorem content_positive (xs:List Bool):0<bitValue (SemiprimeD1RecoveryStripBits.acquire xs).content:=by
  rw [(strip_bytes xs).1,power_value]
  positivity
/-- Zero difference cannot carry a negative actual borrow. -/
theorem negative_zero (j d:List Bool) (hz:bitValue (magnitude j d)=0):negative j d=false:=by
  have hv:=SemiprimeD1NormalizedLinearBits.difference_value j d
  rw [difference_word] at hv
  cases hn:negative j d
  · rfl
  · have hh:=subBits_borrow_iff j d false
    have ht:bitValue j<bitValue d:=by
      simpa only [negative,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero] using hh.mp hn
    simp only [SignedWord.value,hn,ite_true,hz,Nat.cast_zero,neg_zero] at hv
    unfold SemiprimeD1WireKernelFactors.difference at hv
    omega
/-- Exact positive-divisor quotient bytes are the real divider's output interface. -/
theorem quotient_bytes (xs divisor:List Bool) (hd:0<bitValue divisor):
    (divideBits xs divisor).quotient=(divideLoop xs divisor).quotient:=by
  have hn:=(nonzeroBits_correct divisor).mpr hd
  simp only [divideBits,hn,ite_true]
end RiemannGaussian.SemiprimeD1StackKernelLinearSpec
