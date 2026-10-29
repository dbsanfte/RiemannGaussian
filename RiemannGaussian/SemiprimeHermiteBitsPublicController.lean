/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePaidFactorDecoder
import RiemannGaussian.SemiprimeCachedSourcePublicExecution
import RiemannGaussian.SemiprimeHermiteBitsSetupCounter
import RiemannGaussian.SemiprimePrefixEntryWords

/-!
# Word-valued native packet reports survive prefix recovery and decoding

Every query executes HermiteBitsSetupCounter ONCE and retains its full source/native
report. No count or corrected-port answer is a public runtime input. The budget theorem takes a
bound on this ACTUAL counter report; setup reports are retained from the new full-setup counter. Literal machine
addressing and a complete primitive bit clock remain distinct obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeHermiteBitsPublicController
open scoped BigOperators
open SemiprimePaidPrefixController SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open SemiprimeLocalArrayFrontend

/-- Actual public restricted scalar counter, never a supplied count answer. -/
def counter (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (fixed : List (Fin (wireCount N) × Bool)) : SemiprimeAcquiredHermite.ScalarRun :=
  SemiprimeHermiteBitsSetupCounter.count (r := r) (Q := Q)
    (indexedArity N) (indexedCoordinate N hN) eps R 2 J
    (SemiprimePrefixEntryWords.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed)

/-- One cached scalar report, an actual rational floor, and retained prefixRun metadata work. -/
def prefixRun (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (fixed : List (Fin (wireCount N) × Bool)) : Run ℕ :=
  let result := counter N hN r Q eps R J fixed
  ⟨Nat.floor result.value,result.work+fixed.length+3⟩

/-- Numerical guards identify the newly acquired scalar with the previous exact public count. -/
theorem prefix_value (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤ Q)
    (hJ : 0< J) (hprecision : (∑ e, indexedArity N e)*R< Q*J)
    (fixed : List (Fin (wireCount N) × Bool)) :
    (prefixRun N hN r Q eps R J fixed).value=
      SemiprimeCachedSourcePublicExecution.prefixCount N hN r Q eps R J fixed := by
  apply congrArg Nat.floor
  have hnew := SemiprimeHermiteBitsSetupCounter.count_correct (r:=r) (Q:=Q)
    (indexedArity N) (indexedCoordinate N hN) eps R 2 J
    (SemiprimePrefixEntryWords.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed)
    (hT:=fun e eta => SemiprimePrefixEntryWords.entry_abs
      (indexedArity N) (indexedCoordinate N hN) (indexedEntry N hN) fixed e eta)
    (indexed_occurrences N hN) hQ hAQ hJ hprecision
  simp only [SemiprimePrefixEntryWords.entry_value] at hnew
  exact hnew.trans (SemiprimeCachedSourceCounter.count_correct (r:=r) (Q:=Q)
    (indexedArity N) (indexedCoordinate N hN) eps R 2 J
    (SemiprimeAcquiredPrefixSearch.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed) (indexed_occurrences N hN) hQ hAQ hJ hprecision).symm

/-- Every restricted query counts exactly the original accepting assignments. -/
theorem prefix_correct (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤ Q)
    (hJ : 0< J) (hprecision : (∑ e, indexedArity N e)*R< Q*J)
    (fixed : List (Fin (wireCount N) × Bool)) :
    (prefixRun N hN r Q eps R J fixed).value =
      SemiprimeCountRecovery.acceptedCount
        (SemiprimeCountRecovery.restricted SemiprimeCounterSearch.assignmentBit (indexedPredicate N hN) fixed) := by
  rw [prefix_value N hN r Q eps R J hQ hAQ hJ hprecision]
  exact SemiprimeCachedSourcePublicExecution.prefixCount_correct N hN r Q eps R J hQ hAQ hJ hprecision fixed

/-- No source/native work is discarded by floor or prefixRun recovery. -/
theorem prefix_work (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (fixed : List (Fin (wireCount N) × Bool)) :
    (prefixRun N hN r Q eps R J fixed).work=
      (counter N hN r Q eps R J fixed).work+fixed.length+3 := rfl

/-- Actual paid original local checker plus a uniform all-reachable-prefixRun gate budget. -/
def entryBudget (N : ℕ) : ℕ :=
  1048576*(64*bitLength N+2)^10+wireCount N*(3*scopeBound (bitLength N)+2)+4

/-- The actual literal-word terminal callback has a derived uniform clock. -/
theorem entry_work_le (N : ℕ) (hN : 0< N) (fixed : List (Fin (wireCount N) × Bool))
    (hf : fixed.length≤ wireCount N) (e : Fin (factorCount N))
    (input : Fin (indexedArity N e) → Bool) :
    (SemiprimePrefixEntryWords.entry (indexedArity N) (indexedCoordinate N hN)
      (indexedEntry N hN) fixed e input).clock≤ entryBudget N := by
  have hc := indexedEntry_clock N hN e input
  have he := indexedArity_le N e
  have hm := Nat.mul_le_mul hf (show 3*indexedArity N e+2≤3*scopeBound (bitLength N)+2 by omega)
  change (indexedEntry N hN e input).clock+fixed.length*(3*indexedArity N e+2)+4≤ entryBudget N
  unfold entryBudget
  omega

/-- Report-bearing search invokes the actual acquired counter at every query. -/
def search (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) :
    SearchResult (Fin (wireCount N)) :=
  let indices := finIndices (wireCount N)
  let result := SemiprimePaidPrefixController.search (prefixRun N hN r Q eps R J) indices.value
  ⟨result.values,result.queries,result.work+indices.work+1⟩

/-- Exact selected list and query count are preserved under the numerical guards. -/
theorem search_result (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤ Q)
    (hJ : 0< J) (hprecision : (∑ e, indexedArity N e)*R< Q*J)
    :
    (search N hN r Q eps R J).values=(SemiprimeCachedSourcePublicExecution.search N hN r Q eps R J).values ∧
      (search N hN r Q eps R J).queries=(SemiprimeCachedSourcePublicExecution.search N hN r Q eps R J).queries := by
  have hp : (fun fixed => (prefixRun N hN r Q eps R J fixed).value) =
      SemiprimeCachedSourcePublicExecution.prefixCount N hN r Q eps R J := by
    funext fixed
    exact prefix_value N hN r Q eps R J hQ hAQ hJ hprecision fixed
  simpa only [search,finIndices_value,hp,SemiprimeCachedSourcePublicExecution.search] using
    SemiprimePaidPrefixController.search_result (prefixRun N hN r Q eps R J) (List.finRange (wireCount N))

/-- Complete aggregate count-work bound at every reachable prefixRun length. -/
theorem search_work (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J B : ℕ)
    (hb : ∀ fixed, fixed.length≤ wireCount N → (counter N hN r Q eps R J fixed).work≤ B) :
    (search N hN r Q eps R J).work≤(wireCount N+1)*(B+wireCount N+11)+1+3*(wireCount N+1)^2+1 := by
  have h := SemiprimePaidPrefixController.search_work (prefixRun N hN r Q eps R J)
    (B+wireCount N+3) (List.finRange (wireCount N)) (by
      intro fixed hf
      simp only [List.length_finRange] at hf
      have hc := hb fixed hf
      rw [prefix_work]
      omega)
  simp only [List.length_finRange] at h
  have he : B+wireCount N+3+8=B+wireCount N+11 := by omega
  rw [he] at h
  have ha := finIndices_work (wireCount N)
  simp only [search,finIndices_value]
  omega

/-- Actual factor output with both all counter work and the physical decoder work. -/
structure FactorRun where
  /-- Actual decoded integer, or no original accepted factor assignment. -/
  value : Option ℕ
  /-- Number of actual acquired counter calls. -/
  queries : ℕ
  /-- Complete retained lower reports and selected controller work. -/
  work : ℕ

/-- Search once, then decode once on its actual positive branch. -/
def factor (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) : FactorRun :=
  let selected := search N hN r Q eps R J
  match selected.values with
  | none => ⟨none,selected.queries,selected.work+2⟩
  | some values =>
    let decoded := SemiprimePaidFactorDecoder.decode N values 0
    ⟨some decoded.value,selected.queries,selected.work+decoded.work+2⟩

/-- Under the numerical guards, every public output agrees exactly with the actual prior source-counter factorer. -/
theorem factor_value (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤ Q)
    (hJ : 0< J) (hprecision : (∑ e, indexedArity N e)*R< Q*J) :
    (factor N hN r Q eps R J).value=SemiprimeCachedSourcePublicExecution.factor N hN r Q eps R J := by
  have hs := (search_result N hN r Q eps R J hQ hAQ hJ hprecision).1
  unfold SemiprimeCachedSourcePublicExecution.factor
  rw [← hs]
  unfold factor
  cases he : (search N hN r Q eps R J).values <;>
    simp only [he,SemiprimePaidFactorDecoder.decode_value,Option.map_none,Option.map_some]

/-- Correct guarded public outputs are actual nontrivial integer divisors. -/
theorem factor_sound (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤ Q)
    (hJ : 0< J) (hprecision : (∑ e, indexedArity N e)*R< Q*J)
    (p : ℕ) (hp : (factor N hN r Q eps R J).value=some p) : 2≤ p ∧ p< N ∧ p∣N :=
  SemiprimeCachedSourcePublicExecution.factor_sound N hN r Q eps R J hQ hAQ hJ hprecision p
    ((factor_value N hN r Q eps R J hQ hAQ hJ hprecision).symm.trans hp)

/-- Under the numerical guards, failure means there is no ordinary factor pair. -/
theorem factor_none_iff (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ)
    (hQ : 1≤ Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R≤ Q)
    (hJ : 0< J) (hprecision : (∑ e, indexedArity N e)*R< Q*J)
    : (factor N hN r Q eps R J).value=none ↔
      ¬Nonempty (SemiprimePublicFactorCount.OrdinaryFactors N) := by
  rw [factor_value N hN r Q eps R J hQ hAQ hJ hprecision]
  exact SemiprimeCachedSourcePublicExecution.factor_none_iff N hN r Q eps R J hQ hAQ hJ hprecision

/-- At most one initial plus one acquired counter call per actual public wire. -/
theorem factor_queries (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J : ℕ) :
    (factor N hN r Q eps R J).queries≤ wireCount N+1 := by
  have hs := SemiprimePaidPrefixController.search_queries (prefixRun N hN r Q eps R J)
    (List.finRange (wireCount N))
  simp only [List.length_finRange] at hs
  unfold factor
  cases he : (search N hN r Q eps R J).values <;> simp only [he] <;> simpa only [search,finIndices_value] using hs

/-- Complete uniform factor-controller envelope, with explicit physical decoder dimensions. -/
theorem factor_work (N : ℕ) (hN : 0< N) (r Q : ℕ) [NeZero r] (eps : ℚ) (R J B : ℕ)
    (hb : ∀ fixed, fixed.length≤ wireCount N → (counter N hN r Q eps R J fixed).work≤ B) :
    (factor N hN r Q eps R J).work≤
      (wireCount N+1)*(B+wireCount N+3*(wireCount N+1)^2+SemiprimePaidFactorDecoder.budget N (wireCount N)+16) := by
  have hs := search_work N hN r Q eps R J B hb
  have hlarge : (wireCount N+1)*(B+wireCount N+11)+1+3*(wireCount N+1)^2+1+
      SemiprimePaidFactorDecoder.budget N (wireCount N)+2≤
        (wireCount N+1)*(B+wireCount N+3*(wireCount N+1)^2+SemiprimePaidFactorDecoder.budget N (wireCount N)+16) := by
    nlinarith [Nat.zero_le (wireCount N*SemiprimePaidFactorDecoder.budget N (wireCount N))]
  unfold factor
  cases he : (search N hN r Q eps R J).values with
  | none =>
    simp only [he]
    calc
      _ ≤ (wireCount N+1)*(B+wireCount N+11)+1+3*(wireCount N+1)^2+1+2 := Nat.add_le_add_right hs 2
      _ ≤ (wireCount N+1)*(B+wireCount N+11)+1+3*(wireCount N+1)^2+1+SemiprimePaidFactorDecoder.budget N (wireCount N)+2 := by omega
      _ ≤ _ := hlarge
  | some values =>
    have hl := SemiprimePaidPrefixController.search_length (prefixRun N hN r Q eps R J)
      (List.finRange (wireCount N)) values (by simpa only [search,finIndices_value] using he)
    simp only [List.length_finRange] at hl
    have hd := SemiprimePaidFactorDecoder.decode_work N values 0
    rw [hl] at hd
    simp only [he]
    exact (Nat.add_le_add_right (Nat.add_le_add hs hd) 2).trans hlarge

end RiemannGaussian.SemiprimeHermiteBitsPublicController
