/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64
import RiemannGaussian.SemiprimeD1StackOwnerLookup
/-! # Exact compact-ID, high-base64-digit-first colour and binary-power byte specification -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64
open SemiprimeBitArithmetic (bitValue)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeSourceCompactBits (Compact trim)
/-- Literal compact normalization of an ACTUAL little-endian word; mathematical specification only. -/
def compact (bits:List Bool) :List Bool :=(trim bits).bits
/-- Actual reducer.trim output on the reversed word is the identical compact encoding. -/
theorem trim_reverse (bits:List Bool) :
    SemiprimeD1StackReduceExecution.trimReverse bits.reverse=compact bits :=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _
    (SemiprimeD1StackReduceExecution.trimReverse_compact _) (SemiprimeSourceCompactBits.trim_compact _)
  rw [SemiprimeD1StackReduceExecution.trimReverse_value,List.reverse_reverse,SemiprimeSourceCompactBits.trim_value]
/-- A word with six physical bits per coordinate, in old head-major coordinate order. -/
def colours :Nat→List Bool→List (List Bool)
  | 0,_=>[]
  | a+1,reverseBits=>compact ((reverseBits.take 6).reverse)::colours a (reverseBits.drop 6)
/-- Complete original-order row colour fields; there are NO vector tags between its fields. -/
def fields (colours:List (List Bool)) :List Bool :=colours.foldr frame []
/-- One physical fixed-width word's exact complete colour row. -/
def row (a:Nat) (word:List Bool) :List Bool :=fields (colours a word.reverse)
/-- Original actual6a-bit false-first increment enumeration, specified without a runtime cardinality operand. -/
def words (a:Nat) :List (List Bool) :=
  SemiprimeD1StackAssignmentOrder.assignments (2^(6*a)) (List.replicate (6*a) false)
/-- One canonical candidate and its complete compact colour row, in original ascending candidate order. -/
def entries (a:Nat) :List (List Bool×List Bool) :=(words a).map (fun word=>(compact word,row a word))
/-- Exact old generic physical dictionary grammar used by the real lookup consumer. -/
def catalogue (a:Nat) :List Bool :=SemiprimeD1StackOwnerLookup.records (entries a) []
/-- Binary ONE shifted by actual physical zero pushes, never unary numeric power padding. -/
def power (zeros:Nat) :List Bool :=List.replicate zeros false++[true]
/-- Abstract complete30-role result keeps the actual raw enumerator vector and retained source width. -/
def result (a:Nat) :Stack→List Bool :=Sum.elim
  (SemiprimeD1StackAssignmentLoop.data [] [] [] [] (SemiprimeD1TensorTapeCodec.vectorBits (words a)))
  (fun k=>match k with
    | .source=>List.replicate a true | .square=>power (12*a) | .cube=>power (18*a)
    | .fourth=>power (24*a) | .head=>power (6*(4*a-1)) | .output=>catalogue a | _=>[])
/-- Actual stopped configuration has clear flags and no pending real return cells. -/
def done (a:Nat) :C.State Stack Label :=⟨none,none,none,result a,[]⟩
/-- Each actual normalized ID retains its numeric value and has canonical bytes. -/
theorem compact_spec (bits:List Bool) :bitValue (compact bits)=bitValue bits ∧ Compact (compact bits) :=
  ⟨SemiprimeSourceCompactBits.trim_value _,SemiprimeSourceCompactBits.trim_compact _⟩
/-- Compact colours have at most their actual six input bits. -/
theorem colour_width (bits:List Bool) :(compact ((bits.take 6).reverse)).length ≤ 6 :=
  (SemiprimeSourceCompactBits.trim_length _).trans (by rw [List.length_reverse];exact List.length_take_le _ _)
/-- Coordinate extraction retains EXACTLY the prescribed original row length. -/
theorem colours_length (a:Nat) (bits:List Bool) :(colours a bits).length=a :=by
  induction a generalizing bits with
  | zero=>rfl
  | succ a ih=>simp only [colours,List.length_cons,ih]
/-- Every framed compact colour costs at most thirteen actual bytes. -/
theorem fields_length (cs:List (List Bool)) (h:∀c∈cs,c.length ≤ 6) :(fields cs).length ≤ 13*cs.length :=by
  induction cs with
  | nil=>rfl
  | cons c cs ih=>
    have hc:=h c List.mem_cons_self
    have ht:=ih (fun x hx=>h x (List.mem_cons_of_mem _ hx))
    change (frame c (fields cs)).length ≤ _
    rw [SemiprimeSourceHistogramKeyBits.frame_length,List.length_cons]
    omega
/-- Original row colour payload width is derived from real block widths, not an output-size supplier. -/
theorem row_length (a:Nat) (word:List Bool) :(row a word).length ≤ 13*a :=by
  have hw:∀a:Nat,∀bits:List Bool,∀c∈colours a bits,c.length ≤ 6:=by
    intro a
    induction a with
    | zero=>intro bits c hc;cases hc
    | succ a ih=>
      intro bits c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact colour_width bits
      · exact ih _ c hc
  exact (fields_length _ (hw a word.reverse)).trans (by rw [colours_length])
/-- Acquired raw assignment list contains exactly64^a candidates. -/
theorem words_length (a:Nat) :(words a).length=64^a :=by
  rw [words,SemiprimeD1StackAssignmentOrder.assignments_length]
  calc
    2^(6*a)=(2^6)^a:=by rw [pow_mul]
    _=64^a:=by norm_num
/-- Every emitted actual assignment has exactly6a physical bits. -/
theorem word_width (a:Nat) (w:List Bool) (hw:w∈words a) :w.length=6*a :=
  (SemiprimeD1StackAssignmentOrder.assignments_width _ _ w hw).trans List.length_replicate
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Encoding
