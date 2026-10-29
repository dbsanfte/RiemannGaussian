/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64NativeRows
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Storage
/-! # Actual radix64 alphabet/row ABI and binary powers from acquired unary width alone
This stage has its own complete physical trace/clock. It does not implement
source selection, packing replay, packets or an N-only factoring front door.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Original
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Execution SemiprimeD1StackSourceAlphabet64Bounds
open SemiprimeD1StackSourceAlphabet64NativeRows
open SemiprimeBitArithmetic (bitValue bitNat)
/-- Binary shifted ONE has its actual numerical power value; the word contains no unary value padding. -/
theorem power_value (n:Nat) :bitValue (power n)=2^n :=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    change bitValue (false::power n)=2^(n+1)
    simp only [bitValue,bitNat,Bool.false_eq_true,ite_false,Nat.zero_add,ih,pow_succ]
    omega
/-- Every cached power has a linear PHYSICAL bit width. -/
theorem power_length (n:Nat) :(power n).length=n+1 :=by
  simp only [power,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
/-- Exact source input word is retained byte for byte. -/
theorem source_preserved (a:Nat) :result a (aux .source)=List.replicate a true :=rfl
/-- Every actual raw binary counter word is retained as the source's paid enumeration witness. -/
theorem raw_enumeration (a:Nat) :result a (enumStack .output)=
    SemiprimeD1TensorTapeCodec.vectorBits (words a) :=rfl
/-- The complete literal output catalogue has EXACT frozen compact IDs and EXACT old native row bytes,
including original head-major coordinate order, every colour-zero empty field and every candidate tie position. -/
theorem output_original (a:Nat) :result a (aux .output)=
    SemiprimeD1StackOwnerLookup.records ((SemiprimeSourceCompactWordBank.acquire 64 a).ids.zip
      ((SemiprimeSourceWordBankRows.rows 64 a).value.map SemiprimeSourceHistogramRows.layout)) [] :=by
  change catalogue a=_
  unfold catalogue
  rw [entries_original]
/-- The actual square payload is BINARY L², with L=64^a; no unary exponential constructor is executed. -/
theorem square_value (a:Nat) :bitValue (result a (aux .square))=64^(2*a) :=by
  change bitValue (power (12*a))=_
  rw [power_value,show (64:Nat)=2^6 by decide,←pow_mul]
  congr 1
  omega
/-- The actual cube payload is BINARY L³. -/
theorem cube_value (a:Nat) :bitValue (result a (aux .cube))=64^(3*a) :=by
  change bitValue (power (18*a))=_
  rw [power_value,show (64:Nat)=2^6 by decide,←pow_mul]
  congr 1
  omega
/-- The actual fourth payload is BINARY L⁴. -/
theorem fourth_value (a:Nat) :bitValue (result a (aux .fourth))=64^(4*a) :=by
  change bitValue (power (24*a))=_
  rw [power_value,show (64:Nat)=2^6 by decide,←pow_mul]
  congr 1
  omega
/-- Actual saturated head power is r^(4a−1); a0 produces ONE, never a fractional exponent. -/
theorem head_value (a:Nat) :bitValue (result a (aux .head))=64^(4*a-1) :=by
  change bitValue (power (6*(4*a-1)))=_
  rw [power_value,pow_mul]
  rfl
/-- Widths of every acquired cached power are derived from the actual byte construction. -/
theorem power_widths (a:Nat) :
    (result a (aux .square)).length=12*a+1 ∧ (result a (aux .cube)).length=18*a+1 ∧
    (result a (aux .fourth)).length=24*a+1 ∧ (result a (aux .head)).length ≤ 24*a+1 :=by
  change (power (12*a)).length=_ ∧ (power (18*a)).length=_ ∧
    (power (24*a)).length=_ ∧ (power (6*(4*a-1))).length ≤ _
  simp only [power_length]
  refine ⟨True.intro,True.intro,True.intro,?_⟩
  omega
/-- The entire alphabet is nonempty even at a0: compact zero[] pairs with an empty colour row[]. -/
theorem zero_case :entries 0=[([],[])] ∧ catalogue 0=[true,false,false,false] ∧
    result 0 (aux .square)=[true] ∧ result 0 (aux .cube)=[true] ∧
    result 0 (aux .fourth)=[true] ∧ result 0 (aux .head)=[true] :=by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
/-- Every actual auxiliary work word, including unused reducer inputs, is empty after complete acquisition. -/
theorem work_clear (a:Nat) (k:Aux)
    (hk:k≠.source ∧ k≠.square ∧ k≠.cube ∧ k≠.fourth ∧ k≠.head ∧ k≠.output) :result a (aux k)=[] :=by
  cases k <;> first | rfl | exact (hk.1 rfl).elim | exact (hk.2.1 rfl).elim |
    exact (hk.2.2.1 rfl).elim | exact (hk.2.2.2.1 rfl).elim |
    exact (hk.2.2.2.2.1 rfl).elim | exact (hk.2.2.2.2.2 rfl).elim
/-- Complete SAME physical unary-input source returns exact original catalogue bytes and honest binary powers
within its own width/cardinality clock. This is not a prepared-query or N-only selector theorem. -/
theorem source_original (a:Nat) :∃q ≤ 10000*(a+1)*(64^a+1),
    SemiprimeD1StackCalls.run program q (initial (List.replicate a true))=some (done a) ∧
      (done a).data (aux .output)=SemiprimeD1StackOwnerLookup.records
        ((SemiprimeSourceCompactWordBank.acquire 64 a).ids.zip
          ((SemiprimeSourceWordBankRows.rows 64 a).value.map SemiprimeSourceHistogramRows.layout)) [] ∧
      bitValue ((done a).data (aux .square))=64^(2*a) ∧
      bitValue ((done a).data (aux .cube))=64^(3*a) ∧
      bitValue ((done a).data (aux .fourth))=64^(4*a) ∧
      bitValue ((done a).data (aux .head))=64^(4*a-1) :=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded a
  exact ⟨q,hq,hr,output_original a,square_value a,cube_value a,fourth_value a,head_value a⟩
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Original
