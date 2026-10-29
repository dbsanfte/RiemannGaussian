/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RecoveryRowsRun

/-! # Actual canonical-row integer recovery from original parameters
The runtime consumes the newly acquired canonical integer rows directly, rather
than recomputing rational weights or accepting an advised scalar-row answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryCanonicalRun
open SemiprimeD1RecoveryScalarRun SemiprimeD1RecoveryRowsRun
open SemiprimeD1IntegerRecovery SemiprimeD1WireKernelOriginal
open SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid

/-- Actual cached canonical integer row and an actual copied child word. -/
structure Entry where
  /-- Canonical signed weight numerator. -/
  numerator : ℤ
  /-- Canonical positive weight denominator. -/
  denominator : ℕ
  /-- Actual retained child digits. -/
  child : List Bool

/-- Read and copy each actual retained child word once beside its cached row. -/
def entries (children : ℕ → Array (List Bool)) : List Row → Run (List Entry)
  | [] => ⟨[],1⟩
  | r::rs =>
    let tail:=entries children rs
    let child:=((children r.node)[r.index]?).getD []
    ⟨⟨r.numerator,r.denominator,child.map id⟩::tail.value,tail.work+2*child.length+6⟩

/-- Proof-only canonical projection of the original rational terms. -/
def canonical (ts : List Term) : List Entry :=
  ts.map fun t => ⟨t.weight.num,t.weight.den,t.child⟩

/-- Actual copied child digits and canonical rows are preserved exactly. -/
theorem entries_value (children : ℕ → Array (List Bool)) (rs : List Row) :
    (entries children rs).value=rs.map fun r =>
      Entry.mk r.numerator r.denominator (((children r.node)[r.index]?).getD []) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [entries,ih]

/-- Filtering then flattening is the literal conditional traversal. -/
theorem filter_flatMap {α β : Type} (xs : List α) (P : α → Bool) (f : α → List β) :
    (xs.filter P).flatMap f=xs.flatMap (fun x => if P x then f x else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp:P x <;> simp [hp,ih]

/-- Original row acquisition and child copying have exactly the original term data. -/
theorem acquired_entries (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    (entries children (SemiprimeD1RecoveryRowsRun.acquire a M u).rows).value=
      canonical (SemiprimeD1IntegerRecovery.terms a M u children) := by
  rw [entries_value,SemiprimeD1RecoveryRowsRun.acquire_rows]
  simp only [originalRows,canonical,SemiprimeD1IntegerRecovery.terms,filter_flatMap,
    List.map_flatMap]
  apply List.flatMap_congr
  intro t ht
  let w:=SemiprimeD1JetRecoveryWeights.acquire a (height M u) u t
  have hw : w.weights.size=w.retained := by
    simp [w,SemiprimeD1JetRecoveryWeights.acquire]
  change (if t=center a ∨ w.retained=0 then [] else _).map _ = _
  by_cases hs : t=center a ∨ w.retained=0
  · rcases hs with h|h
    · simp [h]
    · have hz : nodeMultiplicity a (height M u) u t=0 := h
      simp [h,hz]
  · have htne : t≠center a := fun h => hs (Or.inl h)
    have hq : 0<nodeMultiplicity a (height M u) u t := by
      have hn : w.retained≠0 := fun h => hs (Or.inr h)
      change nodeMultiplicity a (height M u) u t≠0 at hn
      omega
    have hn : w.retained≠0 := fun h => hs (Or.inr h)
    dsimp only [w] at hn hw ⊢
    simp [htne,hn,hq,List.map_map,hw]


/-- Actual common-denominator traversal of the cached integer rows. -/
def denominator : List Entry → Run ℕ
  | [] => ⟨1,1⟩
  | r::rs => let tail:=denominator rs; ⟨r.denominator*tail.value,tail.work+3⟩

/-- Actual signed integer numerator traversal, including every decoded child digit. -/
def accumulate (D : ℕ) : List Entry → Run ℤ
  | [] => ⟨0,1⟩
  | r::rs =>
    let tail:=accumulate D rs
    let child:=SemiprimeD1IntegerRecovery.decode r.child
    let cofactor:=D/r.denominator
    let term:=r.numerator*(cofactor:ℤ)*(child:ℤ)
    ⟨term+tail.value,tail.work+2*r.child.length+8⟩

/-- Cached integer denominators equal the original acquired common denominator. -/
theorem denominator_value (ts : List Term) :
    (denominator (canonical ts)).value=SemiprimeD1IntegerRecovery.denominator ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [canonical,SemiprimeD1IntegerRecovery.denominator] at ih
    simp [canonical,denominator,SemiprimeD1IntegerRecovery.denominator,ih]

/-- Cached signed integer products equal the original exact recovery numerator. -/
theorem accumulate_value (D : ℕ) (ts : List Term) :
    (accumulate D (canonical ts)).value=SemiprimeD1IntegerRecovery.accumulate D ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [canonical] at ih
    simp [canonical,accumulate,SemiprimeD1IntegerRecovery.accumulate,
      SemiprimeD1IntegerRecovery.scaled,ih]

/-- Actual cached recovery and its retained original producer report. -/
structure Report where
  /-- The actual integer common denominator. -/
  denominator : ℕ
  /-- The actual signed integer numerator. -/
  numerator : ℤ
  /-- Original scalar/array/canonical acquisition stages, retained once. -/
  producerWork : ℕ
  /-- Copy, decoder and native integer execution stages, retained once. -/
  integerWork : ℕ

/-- Full original-parameter producer, canonical-row cache and integer accumulator. -/
def run (a M u : ℕ) (children : ℕ → Array (List Bool)) : Report :=
  let rows:=SemiprimeD1RecoveryRowsRun.acquire a M u
  let terms:=entries children rows.rows
  let D:=denominator terms.value
  let N:=accumulate D.value terms.value
  ⟨D.value,N.value,rows.work,terms.work+D.work+N.work+4⟩

/-- The ACTUAL new canonical-cache path returns the established common denominator. -/
theorem run_denominator (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    (run a M u children).denominator=(SemiprimeD1IntegerRecovery.run a M u children).denominator := by
  simp only [run,acquired_entries,denominator_value,SemiprimeD1IntegerRecovery.run,
    denominatorRun_value]

/-- The ACTUAL new canonical-cache path returns the established signed integer numerator. -/
theorem run_numerator (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    (run a M u children).numerator=(SemiprimeD1IntegerRecovery.run a M u children).numerator := by
  simp only [run,acquired_entries,denominator_value,accumulate_value,SemiprimeD1IntegerRecovery.run,
    denominatorRun_value,accumulateRun_value]

/-- Complete new actual producer refines the original D.5 rational functional. -/
theorem run_recover (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    ((run a M u children).numerator:ℚ)/(run a M u children).denominator=
      SemiprimeD1JetRecoveryPrecision.recover a M u (decodedPackets children) := by
  rw [run_numerator,run_denominator]
  exact SemiprimeD1IntegerRecovery.run_recover a M u children

/-- Every executed child copy is retained in the native report. -/
theorem entries_work (children : ℕ → Array (List Bool)) (rs : List Row) :
    (entries children rs).work=
      2*((entries children rs).value.map (fun e => e.child.length)).sum+6*rs.length+1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [entries,List.map_id,List.map_cons,List.sum_cons,List.length_cons] at *; omega

/-- Canonical row acquisition does not change the number of retained child terms. -/
theorem entries_length (children : ℕ → Array (List Bool)) (rs : List Row) :
    (entries children rs).value.length=rs.length := by rw [entries_value]; simp

/-- One actual denominator multiplication and associated native control per row. -/
theorem denominator_work (es : List Entry) : (denominator es).work=3*es.length+1 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [denominator,List.length_cons,ih]; omega

/-- Every actual native integer arithmetic and child-decoding stage is retained. -/
theorem accumulate_work (D : ℕ) (es : List Entry) :
    (accumulate D es).work=2*(es.map (fun e => e.child.length)).sum+8*es.length+1 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [accumulate,List.map_cons,List.sum_cons,List.length_cons,ih]; omega

/-- Exact new canonical-cache integer-stage report, without a scalar row answer. -/
theorem run_integer_work (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    (run a M u children).integerWork=
      4*((SemiprimeD1IntegerRecovery.terms a M u children).map (fun t => t.child.length)).sum+
        17*(SemiprimeD1IntegerRecovery.terms a M u children).length+7 := by
  have he:=entries_work children (SemiprimeD1RecoveryRowsRun.acquire a M u).rows
  have hl:=entries_length children (SemiprimeD1RecoveryRowsRun.acquire a M u).rows
  rw [acquired_entries] at he hl
  simp only [canonical,List.length_map,List.map_map,Function.comp_def] at he hl
  simp only [run,denominator_work,accumulate_work,acquired_entries,canonical,
    List.length_map,List.map_map,Function.comp_def]
  omega

/-- The complete original scalar acquisition report is retained unchanged. -/
theorem run_producer_work (a M u : ℕ) (children : ℕ → Array (List Bool)) :
    (run a M u children).producerWork ≤ SemiprimeD1RecoveryRowsRun.budget a M u :=
  SemiprimeD1RecoveryRowsRun.acquire_work a M u

/-- Original dimensions and actual child lengths close the native integer-stage bound. -/
theorem run_integer_work_bound (a M u P : ℕ) (hM : u ≤ M)
    (children : ℕ → Array (List Bool))
    (hc : ∀(t j : ℕ), (((children t)[j]?).getD []).length ≤ P) :
    (run a M u children).integerWork ≤ (4*P+17)*(size a*(4*M))+7 := by
  rw [run_integer_work]
  have hl:=SemiprimeD1IntegerRecoveryHeight.terms_length a M u hM children
  have hs : ((SemiprimeD1IntegerRecovery.terms a M u children).map (fun t => t.child.length)).sum ≤
      (SemiprimeD1IntegerRecovery.terms a M u children).length*P := by
    have he : ((SemiprimeD1IntegerRecovery.terms a M u children).map (fun t => t.child.length)).length • P=
        (SemiprimeD1IntegerRecovery.terms a M u children).length*P := by simp
    rw [← he]
    apply List.sum_le_length_nsmul
    intro z hz
    obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hz
    obtain ⟨t,ht,hq,j,hj,rfl⟩:=SemiprimeD1IntegerRecovery.terms_mem a M u children t ht
    exact hc t j
  nlinarith only [hs,hl]

/-- Suffixes of actual cached rows preserve canonical term data. -/
theorem canonical_drop (ts : List Term) (k : ℕ) :
    (canonical ts).drop k=canonical (ts.drop k) := by simp [canonical,List.map_drop]

/-- Every ACTUAL right-recursive cached-integer accumulator frame has an
original-derived dyadic height; no intermediate numerator bound is assumed. -/
theorem cached_suffix_bits (a M u P : ℕ) (hM : u ≤ M)
    (children : ℕ → Array (List Bool))
    (hc : ∀(t j : ℕ), (((children t)[j]?).getD []).length ≤ P) (k : ℕ) :
    let es:=(entries children (SemiprimeD1RecoveryRowsRun.acquire a M u).rows).value
    (accumulate (denominator es).value (es.drop k)).value.natAbs ≤
      2^SemiprimeD1IntegerRecoveryHeight.recoveryExponent a M P := by
  dsimp only
  rw [acquired_entries,denominator_value,canonical_drop,accumulate_value]
  exact SemiprimeD1IntegerRecoveryHeight.original_suffix_bits a M u P hM children hc k

end RiemannGaussian.SemiprimeD1RecoveryCanonicalRun
