/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeCodec
import RiemannGaussian.SemiprimeD1BooleanRootTables

/-! # Exact first-port/false-branch-first Boolean root table stream
These are mathematical specifications of the actual tree writer. The entry
stream must be acquired by the enclosing checker caller; no producer function
or tensor table is a runtime input to the writer's fixed instruction table.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
namespace RiemannGaussian.SemiprimeD1BooleanTreeStream
open SemiprimeD1TensorTables

/-- Canonical individual0/1 integer entry, before any product or reduction. -/
def words (bit : Bool) : List (List Bool) := [if bit then [true] else []]
/-- Actual complete scalar root leaf, including all vector/field/end tags. -/
def leafBytes (bit : Bool) : List Bool := if bit then [false,true,true,true,false,false] else [false,true,false,false]
/-- Literal root leaf serialization is exactly the old codec. -/
theorem leafBytes_original (bit : Bool) : leafBytes bit=SemiprimeD1TensorTapeCodec.tape (.leaf (words bit)) := by
  cases bit <;> rfl
/-- Sequential preorder entries determine the original port-outermost table.
Missing entries are physical EOF/default-false, never an evaluator callback. -/
def table : (n : ℕ)→List Bool→Table n
  | 0,raw=>.leaf (words (raw.head?.getD false))
  | n+1,raw=>.fork (table n raw) (table n (raw.drop (2^n)))
/-- Complete actual output bytes, specified through the old table codec. -/
def bytes (n : ℕ) (raw : List Bool) : List Bool := SemiprimeD1TensorTapeCodec.tape (table n raw)
/-- A zero-depth source emits exactly one actual scalar leaf. -/
theorem bytes_zero (raw : List Bool) : bytes 0 raw=leafBytes (raw.head?.getD false) :=
  (leafBytes_original _).symm
/-- Original false-first, first-port-outermost serialized branch order. -/
theorem bytes_succ (n : ℕ) (raw : List Bool) :
    bytes (n+1) raw=true::(bytes n raw++bytes n (raw.drop (2^n))) := rfl
/-- The old codec output is uniformly between constant multiples of its actual
number of scalar leaves; every branch/leaf/word frame is counted. -/
theorem bytes_length (n : ℕ) (raw : List Bool) :
    4*2^n≤(bytes n raw).length ∧ (bytes n raw).length+1≤7*2^n := by
  induction n generalizing raw with
  | zero=>
    rw [bytes_zero]
    cases h:raw.head?.getD false <;> simp [leafBytes]
  | succ n ih=>
    obtain ⟨hl0,hl1⟩:=ih raw
    obtain ⟨hr0,hr1⟩:=ih (raw.drop (2^n))
    rw [bytes_succ]
    simp only [List.length_cons,List.length_append,pow_succ]
    constructor <;> omega
/-- Every stream entry yields the original canonical root context, including
zero values and the final EOF/default entry. -/
theorem good (n : ℕ) (raw : List Bool) : Good SemiprimeD1RootOwnerTables.rootContext (table n raw) := by
  induction n generalizing raw with
  | zero=>
    cases h:raw.head?.getD false <;>
      simp [table,words,h,Good,GoodWords,SemiprimeD1RootOwnerTables.rootContext,
        SemiprimeD1JetAxes.Context.rank,SemiprimeSourceCompactBits.Compact]
  | succ n ih=>exact ⟨ih raw,ih (raw.drop (2^n))⟩
end RiemannGaussian.SemiprimeD1BooleanTreeStream
