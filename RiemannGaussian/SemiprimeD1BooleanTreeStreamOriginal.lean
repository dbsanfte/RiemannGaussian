/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanTreeBounds

/-! # Exact old tensor construction order and individual integral entries
Predicate/producer arguments below are ONLY mathematical correctness
specifications. The fixed runtime reads an actual acquired Boolean entry
stream, never a callback/table/evaluator. Producer acquisition and its clock
remain the enclosing original-input caller's obligation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1BooleanTreeStreamOriginal
open SemiprimeD1BooleanTreeStream SemiprimeD1TensorTables

/-- Old first-port-outermost, false-then-true entry order, a proof specification. -/
def ordered : ℕ→(List Bool→Bool)→List Bool
  | 0,predicate=>[predicate []]
  | n+1,predicate=>ordered n (fun bits=>predicate (false::bits))++ordered n (fun bits=>predicate (true::bits))
/-- Every old assignment appears exactly once in its original structural order. -/
theorem ordered_length (n : ℕ) (predicate : List Bool→Bool) : (ordered n predicate).length=2^n := by
  induction n generalizing predicate with
  | zero=>rfl
  | succ n ih=>simp only [ordered,List.length_append,ih,pow_succ];omega
/-- The acquired stream frames the EXACT old eager table, not merely a
permutation. The producer's reported clock is neither read nor transported. -/
theorem table_ordered (n : ℕ) (predicate : List Bool→Bool)
    (producer : List Bool→SemiprimeD1JetRingBits.Run)
    (hp : ∀bits,bits.length=n→(producer bits).words=words (predicate bits)) (tail : List Bool) :
    table n (ordered n predicate++tail)=(build n producer).table := by
  induction n generalizing predicate producer tail with
  | zero=>simpa only [table,ordered,List.singleton_append,List.head?_cons,Option.getD_some,build] using
      congrArg Table.leaf (hp [] rfl).symm
  | succ n ih=>
    let low:=fun bits=>predicate (false::bits)
    let high:=fun bits=>predicate (true::bits)
    have hlow:=ih low (fun bits=>producer (false::bits))
      (fun bits hb=>hp (false::bits) (by simp only [List.length_cons,hb])) (ordered n high++tail)
    have hhigh:=ih high (fun bits=>producer (true::bits))
      (fun bits hb=>hp (true::bits) (by simp only [List.length_cons,hb])) tail
    have hd : ((ordered n low++ordered n high)++tail).drop (2^n)=ordered n high++tail := by
      rw [List.append_assoc,←ordered_length n low,List.drop_left]
    change Table.fork (table n ((ordered n low++ordered n high)++tail))
      (table n (((ordered n low++ordered n high)++tail).drop (2^n)))=
        Table.fork (build n (fun bits=>producer (false::bits))).table (build n (fun bits=>producer (true::bits))).table
    rw [hd,List.append_assoc,hlow,hhigh]
/-- Actual source output is the EXACT old root-table tape once entry acquisition
has supplied that exact stream; no old constructor clock is substituted. -/
theorem bytes_ordered (n : ℕ) (predicate : List Bool→Bool)
    (producer : List Bool→SemiprimeD1JetRingBits.Run)
    (hp : ∀bits,bits.length=n→(producer bits).words=words (predicate bits)) (tail : List Bool) :
    bytes n (ordered n predicate++tail)=SemiprimeD1TensorTapeCodec.tape (build n producer).table :=
  congrArg SemiprimeD1TensorTapeCodec.tape (table_ordered n predicate producer hp tail)
/-- Complete original entry stream is consumed, while every later byte survives. -/
theorem ordered_suffix (n : ℕ) (predicate : List Bool→Bool) (tail : List Bool) :
    (ordered n predicate++tail).drop (2^n)=tail := by
  rw [←ordered_length n predicate,List.drop_left]
/-- Each actually stored local scalar is one canonical individual0/1 entry. -/
theorem entry_words (n : ℕ) (raw : List Bool) (input : Fin n→Bool) :
    ∃b:Bool,valueAt (table n raw) input=words b := by
  induction n generalizing raw with
  | zero=>exact ⟨raw.head?.getD false,rfl⟩
  | succ n ih=>
    cases h:input 0
    · simpa only [table,valueAt,h,Bool.false_eq_true,ite_false] using ih raw (fun j=>input j.succ)
    · simpa only [table,valueAt,h,ite_true] using ih (raw.drop (2^n)) (fun j=>input j.succ)
/-- Every ACTUAL integral scalar coefficient is individually0/1 BEFORE any
network product; no already-reduced aggregate is treated as an integer lift. -/
theorem literal_entry_coefficient (n : ℕ) (raw : List Bool) (input : Fin n→Bool) :
    ∃b:Bool,SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal [] (valueAt (table n raw) input))=(if b then 1 else 0) := by
  obtain ⟨b,hb⟩:=entry_words n raw input
  refine ⟨b,?_⟩
  rw [SemiprimeD1JetLiteralLift.literal_coefficient [] _ (by simp) 0 (by decide),hb]
  cases b <;> simp [words,SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat]
/-- Individual entry reduction is the valid integral map at arbitrary precision. -/
theorem entry_reduce (n : ℕ) (raw : List Bool) (input : Fin n→Bool) (p : ℕ) :
    SemiprimeD1JetScalarMap.scalarMap (SemiprimeD1JetBoxIndex.dims []) (SemiprimeD1DyadicInteger.reduction p)
      (SemiprimeD1JetLiteralLift.literal [] (valueAt (table n raw) input))=
      SemiprimeD1JetInterpretation.interpret ⟨[],p⟩ (valueAt (table n raw) input) :=
  SemiprimeD1JetLiteralLift.literal_reduce [] p _
end RiemannGaussian.SemiprimeD1BooleanTreeStreamOriginal
