/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidFiniteEnumerations
import RiemannGaussian.SemiprimeMaterializedOriginalSource

/-! # Original source acquisition including actual enumeration generation
Only original indexed network metadata and numerical parameters are inputs.
All enumerations are acquired by the NEW paid constructor before word search.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimePaidEnumeratedSource
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SemiprimeMaterializedSourceUniversal SemiprimeJetArray
variable {n F r Q : ℕ} [NeZero r]

/-- Execute finite data acquisition and source acquisition with BOTH reports retained. -/
def acquire (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R : ℕ) : Run (Array (Array (Array ℚ))) :=
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeMaterializedOriginalSource.acquire owner Sigma.fst en.value eps R
  ⟨source.value,en.work+source.work+1⟩

/-- Exact original immutable arrays, not just matching membership or size. -/
theorem acquire_value (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R : ℕ) :
    (acquire (r:=r) (Q:=Q) arity coordinate eps R).value=
      (SemiprimeMaterializedOriginalSource.acquire
        (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2) Sigma.fst
        (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R).value := by
  simp only [acquire,SemiprimePaidFiniteEnumerations.indexed_value]

/-- Existing source accessors read the exact original built-layout coefficient. -/
theorem acquire_coefficient (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R : ℕ)
    (e : Fin F) (i : Fin (arity e)) (v : Fin n) (k : ℕ) (hk : k≤R) :
    coefficient (SemiprimeSourceArrayAcquisition.read
      (SemiprimeFiniteEnumerations.indexed n F r Q arity).incidences
      (acquire (r:=r) (Q:=Q) arity coordinate eps R).value ⟨e,i⟩ v) k=
      ((SemiprimeSourceLayout.builtLayout
        (fun j : (f : Fin F) × Fin (arity f) => coordinate j.1 j.2) Sigma.fst
        (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R).row ⟨e,i⟩ v).coeff k := by
  rw [acquire_value]
  exact SemiprimeMaterializedOriginalSource.acquire_coefficient (n:=n) (r:=r) (Q:=Q)
    (fun j : (f : Fin F) × Fin (arity f) => coordinate j.1 j.2)
    (fun j : (f : Fin F) × Fin (arity f) => j.1)
    (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R ⟨e,i⟩ v k hk

/-- Enlarging the explicitly acquired word menu can only enlarge the source work envelope. -/
theorem sourceBudget_mono_words (M n a A D T N Q R start : ℕ) (ha : a≤A) :
    SemiprimeMaterializedOriginalSource.budget M n a D T N Q R start ≤
      SemiprimeMaterializedOriginalSource.budget M n A D T N Q R start := by
  unfold SemiprimeMaterializedOriginalSource.budget
    SemiprimeMaterializedSourceWords.producerBudget
    SemiprimeMaterializedScoreSearch.evaluatorBudget
  gcongr

/-- The actual complete finite-data and source producer envelope. -/
def budget (n F r Q R M : ℕ) : ℕ :=
  SemiprimePaidFiniteEnumerations.budget n F r Q M+
    SemiprimeMaterializedOriginalSource.budget M n (r^Q) (r^(2*Q)) (M^2+Q*n^2) (n+F) Q R
      (SemiprimeMaterializedSourcePullback.centered r Q R)+1

/-- Initial finite list generation is no longer omitted from this executed source clock. -/
theorem acquire_work (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R : ℕ) :
    (acquire (r:=r) (Q:=Q) arity coordinate eps R).work ≤ budget n F r Q R (∑ e,arity e) := by
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  have he : en.work ≤ SemiprimePaidFiniteEnumerations.budget n F r Q (∑ e,arity e) := by
    exact SemiprimePaidFiniteEnumerations.indexed_work n F r Q arity
  have hs := SemiprimeMaterializedOriginalSource.acquire_work owner Sigma.fst en.value eps R
  have ht : en.value.wordTail.length≤r^Q := by
    rw [SemiprimePaidFiniteEnumerations.indexed_value]
    exact (List.length_filter_le _ _).trans_eq (SemiprimeFiniteEnumerations.words_length r Q)
  rw [SemiprimePaidFiniteEnumerations.indexed_incidence_length,
    SemiprimePaidFiniteEnumerations.indexed_universal_length,
    SemiprimePaidFiniteEnumerations.indexed_score_length,
    SemiprimePaidFiniteEnumerations.indexed_indices_length] at hs
  have hm := sourceBudget_mono_words (∑ e,arity e) n en.value.wordTail.length (r^Q)
    (r^(2*Q)) ((∑ e,arity e)^2+Q*n^2) (n+F) Q R
    (SemiprimeMaterializedSourcePullback.centered r Q R) ht
  unfold acquire budget
  dsimp only
  change en.work+_+1≤_
  exact Nat.add_le_add_right (Nat.add_le_add he (hs.trans hm)) 1

end RiemannGaussian.SemiprimePaidEnumeratedSource
