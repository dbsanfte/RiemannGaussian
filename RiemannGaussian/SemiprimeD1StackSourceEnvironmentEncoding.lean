/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironment
import RiemannGaussian.SemiprimeSourceHistogramPrefix
import RiemannGaussian.SemiprimeSourceWordIdEnvironment
/-! # Exact compact prefix-key and marked candidate-ID semantics
All functions in this module specify actual source-produced words. They are not
runtime opcodes, source operands, environment getters or transported clocks.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentEncoding
open SemiprimeD1StackSourceEnvironment
open SemiprimeBitArithmetic (bitValue bitNat)
open SemiprimeSourceCompactBits (Compact)
open SemiprimeD1StackReduceExecution (trimReverse)
/-- Literal output of the actual reverse/high-zero-trim sequence. -/
def normalize (word:List Bool) :List Bool :=trimReverse word.reverse
/-- Actual normalization retains the exact candidate number, including padded zero. -/
theorem normalize_value (word:List Bool) :bitValue (normalize word)=bitValue word :=by
  rw [normalize,SemiprimeD1StackReduceExecution.trimReverse_value,List.reverse_reverse]
/-- Actual normalized candidate IDs are compact. -/
theorem normalize_compact (word:List Bool) :Compact (normalize word) :=
  SemiprimeD1StackReduceExecution.trimReverse_compact _
/-- High-zero stripping never allocates more cells than the supplied reversed word. -/
theorem trimReverse_length (word:List Bool) :(trimReverse word).length≤word.length :=by
  induction word with
  | nil=>rfl
  | cons b word ih=>cases b <;> simp only [trimReverse,List.length_cons,List.length_reverse] <;> omega
/-- Padded input bytes are fully charged and their normalized output cannot grow. -/
theorem normalize_length (word:List Bool) :(normalize word).length≤word.length :=by
  simpa only [normalize,List.length_reverse] using trimReverse_length word.reverse
/-- Actual normalization agrees with the frozen original compact-prefix codec. -/
theorem normalize_trim (word:List Bool) :normalize word=(SemiprimeSourceCompactBits.trim word).bits :=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ (normalize_compact word)
    (SemiprimeSourceCompactBits.trim_compact word)
  rw [normalize_value,SemiprimeSourceCompactBits.trim_value]
/-- Actual acquired compact IDs retain their exact selected bytes. -/
theorem normalize_of_compact (word:List Bool) (hc:Compact word) :normalize word=word :=
  SemiprimeSourceCompactWordIds.compact_value_injective _ _ (normalize_compact word) hc (normalize_value word)
/-- Reversed wrapped bits receive one literal high carry bit only after the actual overflow pop. -/
def successorScratch (word:List Bool) :List Bool :=
  if SemiprimeD1StackIncrement.overflow word then true::(SemiprimeD1StackIncrement.wrapped word).reverse
  else (SemiprimeD1StackIncrement.wrapped word).reverse
/-- Actual output of overflow/reverse/carry/trim, not an arithmetic instruction. -/
def successor (word:List Bool) :List Bool :=trimReverse (successorScratch word)
/-- The physically appended high true bit has its exact binary positional value. -/
theorem append_true_value (word:List Bool) :bitValue (word++[true])=bitValue word+2^word.length :=by
  induction word with
  | nil=>simp [bitValue,bitNat]
  | cons b word ih=>cases b <;> simp only [List.cons_append,bitValue,bitNat,ite_true,Bool.false_eq_true,ite_false,
      ih,List.length_cons,pow_succ] <;> omega
/-- Full actual compact successor has no numeric overflow, including the empty initial key. -/
theorem successor_value (word:List Bool) :bitValue (successor word)=bitValue word+1 :=by
  have h:=SemiprimeD1StackIncrement.value_balance word
  rw [successor,SemiprimeD1StackReduceExecution.trimReverse_value]
  unfold successorScratch
  cases ho:SemiprimeD1StackIncrement.overflow word with
  | false=>simpa only [ho,Bool.false_eq_true,ite_false,List.reverse_reverse,bitNat,ite_false,Nat.mul_zero,Nat.add_zero] using h
  | true=>
    simp only [ite_true,List.reverse_cons,List.reverse_reverse,append_true_value,
      SemiprimeD1StackIncrement.wrapped_length]
    simpa only [ho,bitNat,ite_true,Nat.mul_one] using h
/-- Every actual next key is compact, even after an all-true carry. -/
theorem successor_compact (word:List Bool) :Compact (successor word) :=
  SemiprimeD1StackReduceExecution.trimReverse_compact _
/-- Actual next-key storage grows by at most one physical bit. -/
theorem successor_length (word:List Bool) :(successor word).length≤word.length+1 :=by
  have h:=trimReverse_length (successorScratch word)
  unfold successor successorScratch
  unfold successorScratch at h
  cases ho:SemiprimeD1StackIncrement.overflow word <;>
    simp only [ho,Bool.false_eq_true,ite_false,ite_true,List.length_cons,List.length_reverse,
      SemiprimeD1StackIncrement.wrapped_length] at h ⊢ <;> omega
/-- Actual prefix counter word after k paid compact increment rounds, used only in specifications. -/
def variableKey (k:Nat) :List Bool :=(successor^[k]) []
/-- No key is supplied at initialization. -/
theorem variableKey_zero :variableKey 0=[] :=rfl
/-- Every successive variable key comes from the same actual paid compact successor fragment. -/
theorem variableKey_succ (k:Nat) :variableKey (k+1)=successor (variableKey k) :=
  Function.iterate_succ_apply' _ _ _
/-- Actual generated key denotes its original prefix position. -/
theorem variableKey_value (k:Nat) :bitValue (variableKey k)=k :=by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [variableKey_succ,successor_value,ih]
/-- All generated original-variable keys are compact. -/
theorem variableKey_compact (k:Nat) :Compact (variableKey k) :=by
  cases k with
  | zero=>trivial
  | succ k=>rw [variableKey_succ];exact successor_compact _
/-- A coarse physical-width bound is paid by the number of actual parsed prefix fields. -/
theorem variableKey_length (k:Nat) :(variableKey k).length≤k :=by
  induction k with
  | zero=>rfl
  | succ k ih=>rw [variableKey_succ];exact (successor_length _).trans (by omega)
/-- Compact binary variable keys cannot alias distinct original positions. -/
theorem variableKey_injective :Function.Injective variableKey :=by
  intro a b h
  have hv:=congrArg bitValue h
  simpa only [variableKey_value] using hv
/-- Physical true marker distinguishes a selected zero ID from a missing key. -/
def marked (id:List Bool) :List Bool :=true::normalize id
/-- Newest-first selected prefix has newest-first physical dictionary rows with oldest key zero. -/
def prefixRows :List (List Bool)→List (List Bool×List Bool)
  | []=>[]
  | id::ids=>(variableKey ids.length,marked id)::prefixRows ids
/-- The exact actual whole dictionary uses the existing first-match record codec. -/
def dictionary (ids:List (List Bool)) :List Bool :=L.records (prefixRows ids) []
/-- A parsed chosen ID prepends one real row at the current physically acquired next key. -/
theorem dictionary_cons (id:List Bool) (ids:List (List Bool)) :
    dictionary (id::ids)=true::SemiprimeSourceHistogramKeyBits.frame (variableKey ids.length)
      (SemiprimeSourceHistogramKeyBits.frame (marked id) (dictionary ids)) :=rfl
/-- Original reverse-prefix positions have the same compact next-key word as the actual source. -/
theorem original_nextKey (ids:List (List Bool)) :
    variableKey ids.length=(SemiprimeSourceHistogramPrefix.acquire ids).nextKey :=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ (variableKey_compact _)
    (SemiprimeSourceHistogramPrefix.next_compact ids)
  rw [variableKey_value,SemiprimeSourceHistogramPrefix.next_value]
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentEncoding
