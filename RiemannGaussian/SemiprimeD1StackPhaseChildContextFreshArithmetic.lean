/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextFresh
/-! # Exact fresh dense-index words and literal framed coefficient bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshArithmetic
open SemiprimeD1StackPhaseChildContextFresh
/-- A reduced scalar unit is empty at precision zero and the literal bit one otherwise. -/
def unit (positive : Bool) : List Bool :=if positive then [true] else []
/-- Dense-index allocator interpretation; these natural indices never occur in runtime control. -/
def words : Nat→Nat→Bool→List (List Bool)
  | 0,_,_=>[]
  | n+1,0,b=>unit b::List.replicate n []
  | n+1,r+1,b=>[]::words n r b
/-- Every physically allocated coefficient gets exactly one original vector constructor/field. -/
def chunk (w : List Bool) : List Bool :=true::SemiprimeSourceHistogramKeyBits.frame w []
/-- All coefficient bytes except the final vector terminator. -/
def bytes (ws : List (List Bool)) : List Bool :=(ws.map chunk).flatten
/-- Empty coefficient allocation emits exactly two literal codec bits. -/
theorem chunk_zero : chunk []=[true,false] :=rfl
/-- Nonzero reduced unit emits exactly four literal codec bits. -/
theorem chunk_one : chunk [true]=[true,true,true,false] :=rfl
/-- Flattened coefficient chunks are in the EXACT existing vector order. -/
theorem bytes_vector (ws : List (List Bool)) : bytes ws++[false]=SemiprimeD1TensorTapeCodec.vectorBits ws :=by
  induction ws with
  | nil=>rfl
  | cons w ws ih=>
    change (chunk w++bytes ws)++[false]=_
    rw [List.append_assoc,ih]
    change (true::SemiprimeSourceHistogramKeyBits.frame w [])++SemiprimeD1TensorTapeCodec.vectorBits ws=_
    simp only [List.cons_append,SemiprimeD1TensorTapeCodec.frame_append,List.nil_append]
    rfl
/-- The allocation shape is the actual new-rank counter length, including the q=1 all-zero case. -/
theorem words_length (n r : Nat) (b : Bool) : (words n r b).length=n :=by
  induction n generalizing r with
  | zero=>rfl
  | succ n ih=>cases r <;> simp only [words,List.length_cons,List.length_replicate,ih]
/-- Original dense index is exactly oldrank; the one-cell-axis edge case needs no exception. -/
theorem words_range (n r : Nat) (b : Bool) :
    words n r b=(List.range n).map (fun i=>if i=r then unit b else []) :=by
  induction n generalizing r with
  | zero=>rfl
  | succ n ih=>
    cases r with
    | zero=>
      rw [List.range_succ_eq_map,List.map_cons,List.map_map]
      simp only [words,ite_false,Nat.reduceEqDiff,ite_true,Function.comp_def]
      rw [List.map_const',List.length_range]
    | succ r=>
      rw [List.range_succ_eq_map,List.map_cons,List.map_map]
      have hz : ¬0=r+1:=by omega
      simp only [words,hz,ite_false,Nat.succ.injEq,Function.comp_def,ih]
/-- At most one four-byte unit occurs; every other allocated coefficient has two bytes. -/
theorem bytes_length (n r : Nat) (b : Bool) : (bytes (words n r b)).length≤2*n+2 :=by
  have hz:∀n,(bytes (List.replicate n [])).length=2*n:=by
    intro n
    induction n with
    | zero=>rfl
    | succ n ih=>simp only [List.replicate_succ,bytes,List.map_cons,List.flatten_cons,List.length_append,chunk_zero,List.length_cons,List.length_nil] at *;omega
  induction n generalizing r with
  | zero=>simp only [words,bytes,List.map_nil,List.flatten_nil,List.length_nil];omega
  | succ n ih=>
    cases r with
    | zero=>
      have hu:(chunk (unit b)).length≤4:=by cases b <;> decide
      change (chunk (unit b)++bytes (List.replicate n [])).length≤_
      rw [List.length_append,hz]
      omega
    | succ r=>
      change (chunk []++bytes (words n r b)).length≤_
      rw [List.length_append,chunk_zero]
      have h:=ih r
      change 2+(bytes (words n r b)).length≤_
      omega
/-- Source reduction of the literal scalar unit agrees with the actual width-empty peek. -/
theorem unit_reduce (p : Nat) :
    (SemiprimeD1JetScalarBits.reduce p [true]).bits=unit (decide (0<p)) :=by
  cases p with
  | zero=>rfl
  | succ p=>
    change (SemiprimeSourceCompactBits.trim (SemiprimeD1JetScalarBits.takeBits (p+1) [true]).bits).bits=_
    rw [SemiprimeD1JetScalarBits.takeBits_bits]
    simp [unit,SemiprimeSourceCompactBits.trim]
/-- Exact original FreshJetBits.acquireFresh coefficient list, before its literal vector codec. -/
theorem words_original (old : SemiprimeD1JetAxes.Context) (q p : Nat) :
    words (q*old.rank) old.rank (decide (0<p))=(SemiprimeD1FreshJetBits.acquireFresh old q p).words :=by
  rw [words_range]
  simp only [SemiprimeD1FreshJetBits.acquireFresh,unit_reduce]
end RiemannGaussian.SemiprimeD1StackPhaseChildContextFreshArithmetic
