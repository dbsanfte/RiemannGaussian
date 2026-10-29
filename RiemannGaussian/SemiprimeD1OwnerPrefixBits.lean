/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RootOwnerTables
import RiemannGaussian.SemiprimeD1TensorTapeCodec

/-! # Physical owner-prefix records and exact duplicate/conflict semantics
Keys are binary original WIRE values, not factor-major occurrence ordinals.
These definitions specify a literal parser/equality source; they are never an
instruction evaluating a list, prefix compatibility or an allowed-value answer.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1OwnerPrefixBits
open SemiprimeSourceHistogramKeyBits (frame frame_length)
open SemiprimeBitArithmetic

/-- A framed binary wire key followed by ONE actual value bit per record.
The final false tag is consumed; bytes beyond it are retained exactly. -/
def records : List (List Bool×Bool)→List Bool→List Bool
  | [],tail=>false::tail
  | (key,value)::rest,tail=>true::frame key (value::records rest tail)
/-- Actual initialized compatibility flags, updated by every original record. -/
def scan (query : List Bool) : List (List Bool×Bool)→Bool→Bool→Bool×Bool
  | [],low,high=>(low,high)
  | (key,value)::rest,low,high=>
      let same:=decide (bitValue key=bitValue query)
      scan query rest (low && !(same && value)) (high && !(same && !value))
/-- All physical framing, including every value and record/end tag, is retained. -/
theorem records_length (rows : List (List Bool×Bool)) (tail : List Bool) :
    (records rows tail).length=3*rows.length+2*(rows.map (fun x=>x.1.length)).sum+1+tail.length := by
  induction rows with
  | nil=>simp [records,Nat.add_comm]
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    simp only [records,List.length_cons,frame_length,List.map_cons,List.sum_cons,ih]
    omega
/-- Every row rules out exactly its opposite value when its original key matches. -/
theorem scan_all (query : List Bool) (rows : List (List Bool×Bool)) (low high : Bool) :
    scan query rows low high=
      (low && rows.all (fun x=>decide (bitValue x.1≠bitValue query ∨ x.2=false)),
       high && rows.all (fun x=>decide (bitValue x.1≠bitValue query ∨ x.2=true))) := by
  induction rows generalizing low high with
  | nil=>simp only [scan,List.all_nil,Bool.and_true]
  | cons row rows ih=>
    rcases row with ⟨key,value⟩
    rw [scan,ih]
    by_cases h:bitValue key=bitValue query <;> cases value <;>
      simp [h,List.all_cons]
/-- Original finite-wire keys and ALL original prefix records are the only
semantic premise; duplicates and inconsistent repeated assignments remain. -/
theorem scan_original {n : ℕ} (wire : Fin n) (fixed : List (Fin n×Bool))
    (encode : Fin n→List Bool) (he : ∀i,bitValue (encode i)=i.val) :
    scan (encode wire) (fixed.map (fun x=>(encode x.1,x.2))) true true=
      (SemiprimeD1RootOwnerTables.allowed fixed wire false,
       SemiprimeD1RootOwnerTables.allowed fixed wire true) := by
  rw [scan_all]
  simp only [Bool.true_and,List.all_map,Function.comp_def,SemiprimeD1RootOwnerTables.allowed]
  congr 2 <;> funext x <;> by_cases hx:x.1=wire
  · simp [he,hx]
  · have hv:x.1.val≠wire.val:=fun h=>hx (Fin.ext h)
    simp [he,hx,hv]
  · simp [he,hx]
  · have hv:x.1.val≠wire.val:=fun h=>hx (Fin.ext h)
    simp [he,hx,hv]
end RiemannGaussian.SemiprimeD1OwnerPrefixBits
