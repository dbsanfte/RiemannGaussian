/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedFibreNative
import RiemannGaussian.SemiprimeAcquiredSourceCounter

/-!
# Actual source acquisition feeds the materialized-head counter

The coefficient arrays and runtime designs are computed from the original
network. They are not supplied answers. The selected interpreter ledger and
source-preprocessing bit clock remain distinct interfaces.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedAcquiredCounter
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SemiprimeLocalArrayFrontend SemiprimeRuntimeDesignAcquisition SemiprimeJetArray
open SemiprimeAcquiredSourceCounter (raw layout sourceDesign sourceDesign_runtime)
variable {n F r Q : ℕ} [NeZero r]

/-- Compute the original source arrays and integer designs, then execute the NEW
complete cached-head counter, including actual native factors and Hermite recovery. -/
def count (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport) :
    SemiprimeAcquiredHermite.ScalarRun :=
  let en := SemiprimeFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeSourceArrayAcquisition.acquire owner Sigma.fst en eps R
  let designs := Array.ofFn (fun t : Fin Q => build (raw (r := r) arity coordinate eps R B t))
  SemiprimeMaterializedFibreNative.count Q J R
    (fun t => designs[t.val]'(by simp [designs]))
    (fun e i v => SemiprimeSourceArrayAcquisition.read en.incidences source ⟨e,i⟩ v) T

/-- The materialized source-to-scalar count is the original network contraction.
No coefficient, integer row, native locality, fibre, group, or count oracle occurs. -/
theorem count_correct (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card ≤ B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hJ : 0<J) (hprecision : (∑ e, arity e)*R<Q*J) :
    (count (r := r) (Q := Q) arity coordinate eps R B J T).value =
      SemiprimeCounterNative.originalContraction arity
        (fun e eta => ((T e eta).value : ℚ)) coordinate := by
  let en := SemiprimeFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeSourceArrayAcquisition.acquire owner Sigma.fst en eps R
  let readSource := fun (e : Fin F) (i : Fin (arity e)) (v : Fin n) =>
    SemiprimeSourceArrayAcquisition.read en.incidences source ⟨e,i⟩ v
  have hs (e : Fin F) (i : Fin (arity e)) (v : Fin n) (k : ℕ) (hk : k≤R) :
      coefficient (readSource e i v) k=((layout (r := r) (Q := Q) arity coordinate eps R).row ⟨e,i⟩ v).coeff k :=
    SemiprimeSourceArrayAcquisition.acquire_coefficient owner Sigma.fst en eps R ⟨e,i⟩ v k hk
  have h := SemiprimeMaterializedFibreNative.count_correct Q J R hJ
    (fun t => sourceDesign (r := r) (Q := Q) arity coordinate eps R B howner hQ hAQ t) readSource T
    (fun e i v => (layout (r := r) (Q := Q) arity coordinate eps R).row_degree ⟨e,i⟩ v)
    hs hprecision coordinate
    (fun e i v => (layout (r := r) (Q := Q) arity coordinate eps R).row_origin ⟨e,i⟩ v)
  simp only [sourceDesign_runtime] at h
  simpa only [count,Array.getElem_ofFn] using h

/-- The NEW actual traversal has the same scalar value as the previous executed
source counter; their work reports and execution paths need not agree. -/
theorem count_value_eq_old (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card ≤ B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hJ : 0<J) (hprecision : (∑ e, arity e)*R<Q*J) :
    (count (r := r) (Q := Q) arity coordinate eps R B J T).value =
      (SemiprimeAcquiredSourceCounter.count (r := r) (Q := Q) arity coordinate eps R B J T).value :=
  (count_correct arity coordinate eps R B J T howner hQ hAQ hJ hprecision).trans
    (SemiprimeAcquiredSourceCounter.count_correct arity coordinate eps R B J T
      howner hQ hAQ hJ hprecision).symm

end RiemannGaussian.SemiprimeMaterializedAcquiredCounter
