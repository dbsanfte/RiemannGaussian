/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrences
import RiemannGaussian.SemiprimeSourceHistogramHeadRefinement
/-! # Original ordered compact owner/factor keys and actual counter invariants
All lists, natural counts and routing expressions are mathematical specifications
for actual byte traces. None is a source program/control operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesEncoding
open SemiprimeBitArithmetic (bitValue)
namespace Keys
export SemiprimeSourceHistogramHeadRefinement (numberKey numberKey_value numberKey_compact numberKey_injective)
end Keys
namespace Owner
export SemiprimeD1StackNetworkOwnerIndexEncoding (ownerWord ownerWord_length ownerWord_value ownerWord_zero ownerWord_no_overflow ownerWord_succ)
end Owner
/-- The actual reversed-bit reducer result, specified without executing a native trim operation. -/
def normal (word:List Bool) :List Bool :=SemiprimeD1StackReduceExecution.trimReverse word.reverse
/-- Actual canonical trim preserves every original binary value, including arbitrary padding and zero. -/
theorem normal_value (word:List Bool) :bitValue (normal word)=bitValue word :=by
  rw [normal,SemiprimeD1StackReduceExecution.trimReverse_value,List.reverse_reverse]
/-- Actual canonical trim has no extra high-zero aliases. -/
theorem normal_compact (word:List Bool) :SemiprimeSourceCompactBits.Compact (normal word) :=
  SemiprimeD1StackReduceExecution.trimReverse_compact _
/-- Actual normalizer never expands the physically parsed input width. -/
theorem trimReverse_length (word:List Bool) :(SemiprimeD1StackReduceExecution.trimReverse word).length≤word.length :=by
  induction word with
  | nil=>rfl
  | cons bit word ih=>
    cases bit
    · change (SemiprimeD1StackReduceExecution.trimReverse word).length≤word.length+1
      omega
    · simp only [SemiprimeD1StackReduceExecution.trimReverse,List.length_reverse]
      exact le_rfl
/-- Every emitted compact key width is paid by its actual input bytes. -/
theorem normal_length (word:List Bool) :(normal word).length≤word.length :=by
  simpa only [normal,List.length_reverse] using trimReverse_length word.reverse
/-- Literal normalizer bytes equal the original canonical numeric namespace key. -/
theorem normal_key (word:List Bool) :normal word=Keys.numberKey (bitValue word) :=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ (normal_compact word) (Keys.numberKey_compact _)
  rw [normal_value,Keys.numberKey_value]
/-- Fixed-width actual counter includes its final value n+F and is allocated by real n/F scans. -/
def counterWord (n F v:Nat) :List Bool :=Owner.ownerWord (n+F) v
/-- All counter words retain precisely the physically allocated n+F+1 bits. -/
theorem counter_length (n F v:Nat) (hv:v≤n+F) :(counterWord n F v).length=n+F+1 :=Owner.ownerWord_length _ _ hv
/-- Every actual initialized/factor/final counter represents the exact binary ordinal. -/
theorem counter_value (n F v:Nat) (hv:v≤n+F) :bitValue (counterWord n F v)=v :=Owner.ownerWord_value _ _ hv
/-- The actual source allocation is all-zero bits, without a binary numeral supplier. -/
theorem counter_zero (n F:Nat) :counterWord n F 0=List.replicate (n+F+1) false :=Owner.ownerWord_zero _
/-- The actual increment's carry is always false throughout the paid n initialization and F factor steps. -/
theorem counter_no_overflow (n F v:Nat) (hv:v≤n+F) :SemiprimeD1StackIncrement.overflow (counterWord n F v)=false :=
  Owner.ownerWord_no_overflow _ _ hv
/-- Every real factor/initialization increment produces exactly the next physical word. -/
theorem counter_succ (n F v:Nat) (hv:v<n+F) :
    SemiprimeD1StackIncrement.wrapped (counterWord n F v)=counterWord n F (v+1) :=Owner.ownerWord_succ _ _ hv
/-- Every factor key is the compact binary ordinal n+f of the actual scanned factor. -/
theorem counter_key (n F f:Nat) (hf:f≤F) :normal (counterWord n F (n+f))=Keys.numberKey (n+f) :=by
  rw [normal_key,counter_value n F (n+f) (by omega)]
/-- Exact original factor-major/local-slot ordered pair stream; empty factors advance the factor key. -/
def pairsFrom (n:Nat) :Nat→List (List (List Bool))→List (List Bool×List Bool)
  | _,[]=>[]
  | f,row::rows=>row.map (fun word=>(normal word,Keys.numberKey (n+f)))++pairsFrom n (f+1) rows
/-- Complete zero-based original factor traversal. -/
def pairs (n:Nat) (rows:List (List (List Bool))) :List (List Bool×List Bool) :=pairsFrom n 0 rows
/-- Exactly one pair per physically scanned original occurrence; repeated owner keys remain repeated. -/
theorem pairsFrom_length (n f:Nat) (rows:List (List (List Bool))) :
    (pairsFrom n f rows).length=(rows.map List.length).sum :=by
  induction rows generalizing f with
  | nil=>rfl
  | cons row rows ih=>simp only [pairsFrom,List.length_append,List.length_map,List.map_cons,List.sum_cons,ih]
/-- Complete descriptor count is the actual local occurrence count. -/
theorem pairs_length (n:Nat) (rows:List (List (List Bool))) :
    (pairs n rows).length=(rows.map List.length).sum :=pairsFrom_length _ _ _
/-- Literal desired downstream dictionary/stream bytes: one pair per actual occurrence, one final false. -/
def tape (n:Nat) (rows:List (List (List Bool))) :List Bool :=SemiprimeD1StackOwnerLookup.records (pairs n rows) []
/-- Original nested acquired-owner row input bytes. -/
def inputTape (rows:List (List (List Bool))) :List Bool :=SemiprimeD1StackNetworkRowsEncoding.rowsTape rows
/-- Actual original per-row owner codec, including every repeated value and zero-port factor. -/
def originalRows (net:SemiprimeD1TensorNetwork.Network) :List (List (List Bool)) :=
  net.rows.map (fun row=>row.map (fun v=>Owner.ownerWord net.leftCount v.val))
/-- Original acquisition's literal row output is exactly the two-input source ABI. -/
theorem original_input (net:SemiprimeD1TensorNetwork.Network) :
    inputTape (originalRows net)=SemiprimeD1StackNetworkRowsEncoding.originalTape net :=rfl
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesEncoding
