/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecordsSort
import RiemannGaussian.SemiprimeD1BoundaryRecordsBounds

/-! # Near-linear executed report of the actual boundary-record merge sort
Each pass pays the full stored record size and visits only linearly many
records. The exact length-derived pass budget adds a logarithmic factor;
there is no quadratic intermediate-table scan hidden in this bound.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsSortBounds
open SemiprimeD1BoundaryRecords (Entry)
open SemiprimeD1BoundaryRecordsSort

/-- A real merge pass cannot increase the number of runs. -/
theorem mergePass_length_le (runs : List (List Entry)) :
    (SemiprimeD1BoundaryRecords.mergePass runs).value.length ≤ runs.length := by
  rw [mergePass_length]
  omega

/-- The same physical maximum-record-byte bound survives every real pass. -/
theorem mergePass_bounded (runs : List (List Entry)) (B : Nat)
    (h : ∀e∈runs.flatten,SemiprimeD1BoundaryRecords.size e≤B) :
    ∀e∈(SemiprimeD1BoundaryRecords.mergePass runs).value.flatten,
      SemiprimeD1BoundaryRecords.size e≤B := by
  intro e he
  exact h e ((mergePass_perm runs).mem_iff.mp he)

/-- One actual sequential pass has linear full-record work, including all
comparisons, copies and run-list bookkeeping. -/
theorem mergePass_clock : ∀(runs : List (List Entry)) (B : Nat),
    (∀e∈runs.flatten,SemiprimeD1BoundaryRecords.size e≤B) →
    (SemiprimeD1BoundaryRecords.mergePass runs).clock ≤
      30*(B+1)*(runs.flatten.length+runs.length+1)
  | [],B,h => by simp only [SemiprimeD1BoundaryRecords.mergePass,List.flatten_nil,List.length_nil]; omega
  | [xs],B,h => by simp only [SemiprimeD1BoundaryRecords.mergePass]; nlinarith
  | xs::ys::rest,B,h => by
    have hm := SemiprimeD1BoundaryRecordsBounds.merge_clock xs ys B (by
      intro e he
      exact h e (by simp only [List.flatten_cons,List.mem_append] at he ⊢; tauto))
    have ht := mergePass_clock rest B (by
      intro e he
      exact h e (by simp only [List.flatten_cons,List.mem_append]; tauto))
    simp only [SemiprimeD1BoundaryRecords.mergePass,List.flatten_cons,List.length_append,List.length_cons]
    nlinarith

/-- All executed passes and the actual fuel-zero fallback retain linear work
per pass. This bound holds even for an insufficient caller budget. -/
theorem sortPasses_clock (fuel : Nat) (runs : List (List Entry)) (B : Nat)
    (hb : ∀e∈runs.flatten,SemiprimeD1BoundaryRecords.size e≤B) :
    (SemiprimeD1BoundaryRecords.sortPasses fuel runs).clock ≤
      60*(B+1)*(runs.flatten.length+runs.length+1)*(fuel+1) := by
  induction fuel generalizing runs with
  | zero =>
    cases runs with
    | nil => simp only [SemiprimeD1BoundaryRecords.sortPasses,List.flatten_nil,List.length_nil]; omega
    | cons xs rest =>
      cases rest with
      | nil =>
        simp only [SemiprimeD1BoundaryRecords.sortPasses]
        exact Nat.one_le_of_lt (by positivity)
      | cons ys rest =>
        have hc := SemiprimeD1BoundaryRecordsBounds.copyEntries_clock (xs::ys::rest).flatten B hb
        simp only [SemiprimeD1BoundaryRecords.sortPasses]
        nlinarith
  | succ fuel ih =>
    cases runs with
    | nil => simp only [SemiprimeD1BoundaryRecords.sortPasses,List.flatten_nil,List.length_nil]; nlinarith
    | cons xs rest =>
      cases rest with
      | nil =>
        simp only [SemiprimeD1BoundaryRecords.sortPasses]
        exact Nat.one_le_of_lt (by positivity)
      | cons ys rest =>
        have hp := mergePass_clock (xs::ys::rest) B hb
        have ht := ih (SemiprimeD1BoundaryRecords.mergePass (xs::ys::rest)).value
          (mergePass_bounded _ B hb)
        rw [mergePass_flatten_length] at ht
        have hn := mergePass_length_le (xs::ys::rest)
        have ht' :
            (SemiprimeD1BoundaryRecords.sortPasses fuel
              (SemiprimeD1BoundaryRecords.mergePass (xs::ys::rest)).value).clock ≤
            60*(B+1)*((xs::ys::rest).flatten.length+(xs::ys::rest).length+1)*(fuel+1) := by
          apply ht.trans
          gcongr
        simp only [SemiprimeD1BoundaryRecords.sortPasses]
        nlinarith

/-- The actual closed sort has O(N*(B+1)*log(N+2)) executed record work.
B bounds each complete key-plus-jet record, not merely a single coefficient. -/
theorem sort_clock (es : List Entry) (B : Nat)
    (hb : ∀e∈es,SemiprimeD1BoundaryRecords.size e≤B) :
    (SemiprimeD1BoundaryRecords.sort es).clock ≤
      200*(B+1)*(es.length+1)*(Nat.size es.length+2) := by
  have hs := sortPasses_clock (Nat.size es.length+1) (es.map (fun e => [e])) B (by
    simpa only [←List.flatMap_def,List.flatMap_singleton'] using hb)
  simp only [←List.flatMap_def,List.flatMap_singleton',List.length_map] at hs
  have hs' :
      (SemiprimeD1BoundaryRecords.sortPasses (Nat.size es.length+1)
        (es.map (fun e => [e]))).clock ≤
        120*(B+1)*(es.length+1)*(Nat.size es.length+2) := by
    apply hs.trans
    have h : es.length+es.length+1 ≤ 2*(es.length+1) := by omega
    have hm := Nat.mul_le_mul_right (Nat.size es.length+1+1)
      (Nat.mul_le_mul_left (60*(B+1)) h)
    convert hm using 1; ring
  have hpad : 3*es.length+1 ≤ 80*(B+1)*(es.length+1)*(Nat.size es.length+2) := by
    have h1 : 1 ≤ B+1 := by omega
    have h2 : 1 ≤ Nat.size es.length+2 := by omega
    have h := Nat.mul_le_mul (Nat.mul_le_mul_right (es.length+1)
      (Nat.mul_le_mul_left 80 h1)) h2
    simp only [Nat.mul_one] at h
    omega
  simp only [SemiprimeD1BoundaryRecords.sort]
  nlinarith only [hs',hpad]

/-- For at most 2^W records, sorting costs one such exponential times a
polynomial byte/width factor, rather than its square. -/
theorem sort_clock_pow (es : List Entry) (B W : Nat)
    (hb : ∀e∈es,SemiprimeD1BoundaryRecords.size e≤B) (hn : es.length ≤ 2^W) :
    (SemiprimeD1BoundaryRecords.sort es).clock ≤ 200*(B+1)*(2^W+1)*(W+3) := by
  have hp : (2:Nat)^W < 2^(W+1) := by
    rw [pow_succ]
    have h : 0<(2:Nat)^W := by positivity
    omega
  have hs : Nat.size es.length ≤ W+1 := Nat.size_le.mpr (hn.trans_lt hp)
  apply (sort_clock es B hb).trans
  have hsize : Nat.size es.length+2 ≤ W+3 := by omega
  exact Nat.mul_le_mul
    (Nat.mul_le_mul_left (200*(B+1)) (Nat.add_le_add_right hn 1)) hsize

end RiemannGaussian.SemiprimeD1BoundaryRecordsSortBounds
