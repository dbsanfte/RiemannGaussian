/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidRawAcquisition
import RiemannGaussian.SemiprimePaidRuntimeDesign
import RiemannGaussian.SemiprimePaidMeasurementBound
import RiemannGaussian.SemiprimeCachedSourceCounter
import RiemannGaussian.SemiprimePaidFiniteEnumerations

/-! # Original input to acquired source, physical designs and scalar count
The runtime calls the paid finite enumerator, actual coefficient and integer
family producers, and the encoded physical selector. Every returned lower
report is retained before the materialized native count is returned.
This joins component ledgers; a whole primitive-bit/address clock is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace RiemannGaussian.SemiprimeFullSetupCounter
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SemiprimeLocalArrayFrontend SemiprimeRuntimeDesignAcquisition
variable {n F r Q : ℕ} [NeZero r]

/-- All input-only setup and all physical node designs execute before counting. -/
def count (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport) :
    SemiprimeAcquiredHermite.ScalarRun :=
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeMaterializedOriginalSource.acquire owner Sigma.fst en.value eps R
  let raw := SemiprimePaidRawAcquisition.acquire arity coordinate en.value eps R B
  let bits := SemiprimePaidMeasurementBound.bits B Q R
  let designs := Array.ofFn (fun t : Fin Q => SemiprimePaidRuntimeDesign.build
    (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F) raw.value t)
    (SemiprimePaidRawAcquisition.reader (n:=n) raw.value t) bits)
  let out := SemiprimeMaterializedFibreNative.count Q J R
    (fun t => (designs[t.val]'(by simp [designs])).value)
    (fun e i v => SemiprimeSourceArrayAcquisition.read en.value.incidences source.value ⟨e,i⟩ v) T
  ⟨out.value,en.work+source.work+raw.work+(designs.toList.map (fun x => x.work)).sum+out.work+10*Q+20⟩

/-- Actual cached original row bounds suffice for the executed physical builder. -/
theorem physical_design (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q) (t : Fin Q) :
    (SemiprimePaidRuntimeDesign.build
      (SemiprimePaidRawAcquisition.raw (SemiprimePaidRawAcquisition.acquire arity coordinate
        (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B).value t)
      (SemiprimePaidRawAcquisition.reader (SemiprimePaidRawAcquisition.acquire arity coordinate
        (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B).value t)
      (SemiprimePaidMeasurementBound.bits B Q R)).value=
      build (SemiprimeAcquiredSourceCounter.raw (r:=r) arity coordinate eps R B t) := by
  let snapshot := (SemiprimePaidRawAcquisition.acquire arity coordinate
    (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B).value
  have hb : ∀ g j v, |(SemiprimePaidRawAcquisition.raw (n:=n) (F:=F) snapshot t).rows g j v|≤
      (2^(SemiprimePaidMeasurementBound.bits B Q R) : ℕ) := by
    rw [SemiprimePaidRawAcquisition.acquire_raw]
    intro g j v
    exact (SemiprimeAcquiredSourceCounter.raw_bounded arity coordinate eps R B howner hQ hAQ t g j v).trans
      (by exact_mod_cast SemiprimePaidMeasurementBound.bound_le B Q R)
  rw [SemiprimePaidRuntimeDesign.build_eq _ _ _
    (fun g j v => SemiprimePaidRawAcquisition.reader_value snapshot t g j v) hb]
  rw [SemiprimePaidRawAcquisition.acquire_raw]

/-- Setup replacement preserves the actual old count value under its original guards. -/
theorem count_value_eq_cached (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q) :
    (count (r:=r) (Q:=Q) arity coordinate eps R B J T).value=
      (SemiprimeCachedSourceCounter.count (r:=r) (Q:=Q) arity coordinate eps R B J T).value := by
  simp only [count,Array.getElem_ofFn,SemiprimeCachedSourceCounter.count]
  simp only [SemiprimePaidFiniteEnumerations.indexed_value]
  congr 2
  funext t
  change (SemiprimePaidRuntimeDesign.build
    (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F)
      (SemiprimePaidRawAcquisition.acquire arity coordinate
        (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value eps R B).value t)
    (SemiprimePaidRawAcquisition.reader (n:=n)
      (SemiprimePaidRawAcquisition.acquire arity coordinate
        (SemiprimePaidFiniteEnumerations.indexed n F r Q arity).value eps R B).value t)
    (SemiprimePaidMeasurementBound.bits B Q R)).value=
    build (SemiprimeAcquiredSourceCounter.raw (r:=r) arity coordinate eps R B t)
  rw [SemiprimePaidFiniteEnumerations.indexed_value]
  exact physical_design arity coordinate eps R B howner hQ hAQ t

/-- Original-network contraction, with the actual physical selector in the runtime path. -/
theorem count_correct (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q)
    (hJ : 0<J) (hprecision : (∑ e, arity e)*R<Q*J) :
    (count (r:=r) (Q:=Q) arity coordinate eps R B J T).value=
      SemiprimeCounterNative.originalContraction arity (fun e eta => ((T e eta).value : ℚ)) coordinate :=
  (count_value_eq_cached arity coordinate eps R B J T howner hQ hAQ).trans
    (SemiprimeCachedSourceCounter.count_correct arity coordinate eps R B J T howner hQ hAQ hJ hprecision)

end RiemannGaussian.SemiprimeFullSetupCounter
