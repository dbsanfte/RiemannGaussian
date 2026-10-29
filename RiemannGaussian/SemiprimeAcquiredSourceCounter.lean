/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceArrayAcquisition
import RiemannGaussian.SemiprimeSourceConstraintAcquisition
import RiemannGaussian.SemiprimeSourceRuntimeDesignBridge

/-!
# Source-to-scalar counter on an original indexed network

Source coefficients and padded integer measurement rows are acquired from the
original finite network and public parameters. The runtime path has no
polynomial layout or supplied coefficient/constraint answer. The operation
reports have their stated array-interpreter scope, not a complete bit runtime.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeAcquiredSourceCounter
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SemiprimeLocalArrayFrontend SemiprimeRuntimeDesignAcquisition SemiprimeJetArray
variable {n F r Q : ℕ} [NeZero r]

/-- Public native integer-constraint height, computed directly from source parameters. -/
def measurementBound (B Q R : ℕ) : ℕ := B*2*(8*Q)^(2*R)

/-- Raw integer rows and groups acquired from the original finite network. -/
def raw (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) (t : Fin Q) : RawDesign n F :=
  let en := SemiprimeFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  { r := r
    head := SemiprimeSourceConstraintAcquisition.head owner Sigma.fst en eps t
    assigned := fun e => SemiprimeFiniteEnumerations.searchWords owner Sigma.fst en eps (.inr e) t
    count := fun _ => (SemiprimeSourceConstraintAcquisition.rowIndices owner Sigma.fst en eps).values.length
    rows := SemiprimeSourceConstraintAcquisition.matrix owner Sigma.fst en eps R t
    W := fun _ => measurementBound B Q R }

/-- Execute the source-array, selected-design and scalar counter chain.
The node designs and original coefficient family are materialized before use. -/
def count (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → EntryReport) :
    SemiprimeAcquiredHermite.ScalarRun :=
  let en := SemiprimeFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeSourceArrayAcquisition.acquire owner Sigma.fst en eps R
  let designs := Array.ofFn (fun t : Fin Q => build (raw (r := r) arity coordinate eps R B t))
  SemiprimeNodeArrayExecution.count Q J R
    (fun t => designs[t.val]'(by simp [designs]))
    (fun e i v => SemiprimeSourceArrayAcquisition.read en.incidences source ⟨e,i⟩ v) T

/-- Mathematical original-network source, used only by correctness proofs. -/
noncomputable def layout (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R : ℕ) :=
  SemiprimeSourceLayout.builtLayout
    (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
    (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R

/-- Old source constraints are covered by actually acquired padded integer rows. -/
theorem raw_covers (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (t : Fin Q) (g : Fin r) (j : Fin ((layout (r := r) (Q := Q) arity coordinate eps R).rowCount t g)) :
    ∃ k : Fin ((raw (r := r) arity coordinate eps R B t).count g),
      ∀ v : {v : Fin n // (layout (r := r) (Q := Q) arity coordinate eps R).head t v=g},
        (raw (r := r) arity coordinate eps R B t).rows g k v.val=
          (layout (r := r) (Q := Q) arity coordinate eps R).constraints t g j v := by
  obtain ⟨k,hk⟩ := SemiprimeSourceConstraintAcquisition.source_rows_in_matrix
    (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
    (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R t g j
  exact ⟨k,fun v => (hk v).symm⟩

/-- Actual acquired rows are old constraints or zero, on their named source head. -/
theorem raw_from_source (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (t : Fin Q) (g : Fin r) (k : Fin ((raw (r := r) arity coordinate eps R B t).count g)) :
    (∀ v : {v : Fin n // (layout (r := r) (Q := Q) arity coordinate eps R).head t v=g},
      (raw (r := r) arity coordinate eps R B t).rows g k v.val=0) ∨
    ∃ j : Fin ((layout (r := r) (Q := Q) arity coordinate eps R).rowCount t g),
      ∀ v : {v : Fin n // (layout (r := r) (Q := Q) arity coordinate eps R).head t v=g},
        (raw (r := r) arity coordinate eps R B t).rows g k v.val=
          (layout (r := r) (Q := Q) arity coordinate eps R).constraints t g j v :=
  SemiprimeSourceConstraintAcquisition.matrix_rows_from_source
    (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
    (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R t g k

/-- The padded acquired constraints have the constructor's actual integer height. -/
theorem raw_bounded (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card ≤ B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (t : Fin Q) (g : Fin r) (j : Fin ((raw (r := r) arity coordinate eps R B t).count g)) (v : Fin n) :
    |(raw (r := r) arity coordinate eps R B t).rows g j v| ≤
      ((raw (r := r) arity coordinate eps R B t).W g : ℤ) := by
  classical
  let d := raw (r := r) arity coordinate eps R B t
  have hhead : ∀ v, d.head v=(layout (r := r) (Q := Q) arity coordinate eps R).head t v := fun _ => rfl
  by_cases hv : d.head v=g
  · let vv : {v : Fin n // (layout (r := r) (Q := Q) arity coordinate eps R).head t v=g} :=
      ⟨v,by rw [← hhead]; exact hv⟩
    rcases raw_from_source (r := r) (Q := Q) arity coordinate eps R B t g j with hz|⟨k,hk⟩
    · rw [hz vv]
      exact Int.natCast_nonneg _
    · rw [hk vv]
      exact SemiprimeSourceLayoutHeight.builtLayout_constraints_abs_le
        (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
        (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B howner hQ hAQ t g k vv
  · have hz := SemiprimeSourceConstraintAcquisition.matrix_not_head
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
      (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R t g j v hv
    exact (congrArg (fun z : ℤ => |z|) hz).trans_le (Int.natCast_nonneg _)

/-- Proof-only native source certificate for the computed runtime integer design. -/
noncomputable def sourceDesign (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card ≤ B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q) (t : Fin Q) :
    SemiprimeIndexedNodeCertificate.Data arity (fun e i v =>
      ((layout (r := r) (Q := Q) arity coordinate eps R).row ⟨e,i⟩ v).eval ((t.val : ℚ)+1)) :=
  SemiprimeSourceRuntimeDesignBridge.sourceCertificate
    (raw (r := r) arity coordinate eps R B t) (layout (r := r) (Q := Q) arity coordinate eps R) t
    (fun _ => rfl) (fun _ => rfl) arity (fun e i => ⟨e,i⟩) (fun _ _ => rfl)
    (raw_bounded (r := r) (Q := Q) arity coordinate eps R B howner hQ hAQ t)
    (raw_covers (r := r) (Q := Q) arity coordinate eps R B t)

/-- Erase the mathematical source proof before executing the runtime counter. -/
theorem sourceDesign_runtime (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card ≤ B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R ≤ Q) (t : Fin Q) :
    SemiprimeNodeArrayExecution.runtimeDesign
      (sourceDesign (r := r) (Q := Q) arity coordinate eps R B howner hQ hAQ t) =
      build (raw (r := r) arity coordinate eps R B t) := rfl

/-- The actual acquired design has precisely the original source rank. -/
theorem selected_count_source (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (t : Fin Q) (g : Fin r) :
    (build (raw (r := r) arity coordinate eps R B t)).m g =
      SqrtLog.LayoutRank.rowRank ((layout (r := r) (Q := Q) arity coordinate eps R).constraints t g) :=
  SemiprimeSourceRuntimeDesignBridge.selected_count_source
    (raw (r := r) arity coordinate eps R B t) (layout (r := r) (Q := Q) arity coordinate eps R) t
    (fun _ => rfl) (raw_from_source (r := r) (Q := Q) arity coordinate eps R B t)
    (raw_covers (r := r) (Q := Q) arity coordinate eps R B t) g

/-- Source-to-scalar correctness on original input tables. Coefficients, integer
constraints, row locality, selected rank and Taylor packets are not supplied answers. -/
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
  let readSource := fun (e : Fin F) (i : Fin (arity e)) (v : Fin n) => SemiprimeSourceArrayAcquisition.read en.incidences source ⟨e,i⟩ v
  have hs (e : Fin F) (i : Fin (arity e)) (v : Fin n) (k : ℕ) (hk : k≤R) :
      coefficient (readSource e i v) k=((layout (r := r) (Q := Q) arity coordinate eps R).row ⟨e,i⟩ v).coeff k :=
    SemiprimeSourceArrayAcquisition.acquire_coefficient owner Sigma.fst en eps R ⟨e,i⟩ v k hk
  have h := SemiprimeNodeArrayExecution.count_correct Q J R hJ
    (fun t => sourceDesign (r := r) (Q := Q) arity coordinate eps R B howner hQ hAQ t) readSource T
    (fun e i v => (layout (r := r) (Q := Q) arity coordinate eps R).row_degree ⟨e,i⟩ v)
    hs hprecision coordinate
    (fun e i v => (layout (r := r) (Q := Q) arity coordinate eps R).row_origin ⟨e,i⟩ v)
  simp only [sourceDesign_runtime] at h
  simpa only [count, Array.getElem_ofFn] using h

end RiemannGaussian.SemiprimeAcquiredSourceCounter
