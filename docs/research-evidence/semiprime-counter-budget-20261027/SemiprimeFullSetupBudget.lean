/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFullSetupCounter
import RiemannGaussian.SemiprimePaidEnumeratedSource

/-! # Numeric bounds for the actual full-setup counter's setup ledger
Only the setup part is bounded here. Native counting and primitive bit/address
composition are separate. Large measurement magnitudes are not input dimensions.
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
namespace RiemannGaussian.SemiprimeFullSetupBudget
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open SemiprimeRuntimeDesignAcquisition
variable {n F r Q : ℕ} [NeZero r]

/-- The literal setup sum occurring in the actual full counter. -/
def setupWork (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B : ℕ) : ℕ :=
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeMaterializedOriginalSource.acquire owner Sigma.fst en.value eps R
  let raw := SemiprimePaidRawAcquisition.acquire arity coordinate en.value eps R B
  let bits := SemiprimePaidMeasurementBound.bits B Q R
  let designs := Array.ofFn (fun t : Fin Q => SemiprimePaidRuntimeDesign.build
    (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F) raw.value t)
    (SemiprimePaidRawAcquisition.reader (n:=n) raw.value t) bits)
  en.work+source.work+raw.work+(designs.toList.map (fun x => x.work)).sum+10*Q+20

/-- Selector group budgets are monotone in the actual matrix dimensions. -/
theorem groupBudget_mono {m h p n bits a b : ℕ} (hm : m≤p) (hh : h≤n) (hab : a≤b) :
    SemiprimePaidRuntimeDesign.groupBudget m h bits a ≤
      SemiprimePaidRuntimeDesign.groupBudget p n bits b := by
  unfold SemiprimePaidRuntimeDesign.groupBudget SemiprimeEncodedRowSelection.budget
    SemiprimeRowSelectionBits.runBudget SemiprimeRowSelectionBits.insertBudget
    SemiprimeRowSelectionBits.residualRowBudget SemiprimeRowSelectionBits.normalizeRowBudget
    SemiprimeRowSelectionBits.updateRowBudget SemiprimeRowSelectionBitArithmetic.residualBudget
    SemiprimeMaterializedSelectionTemporaries.selectorWidth
    SemiprimeMaterializedSelectionTemporaries.leafBits
    SemiprimeMaterializedSelectionTemporaries.residualBits
    SemiprimeMaterializedSelectionTemporaries.normalizeBits
    SemiprimeMaterializedSelectionTemporaries.updateBits
  all_goals simp only [SemiprimeMaterializedSelectionTemporaries.normalizeBits,
    SemiprimeMaterializedSelectionTemporaries.residualBits,
    SemiprimeMaterializedSelectionTemporaries.leafBits]; gcongr

/-- Setup-only design envelope uses the safe polynomial column bound n. -/
def designBudget (n F r p bits readBudget : ℕ) : ℕ :=
  3*(n+1)^2+r*(5*n+1)+r*SemiprimePaidRuntimeDesign.groupBudget p n bits readBudget+
    100*(n+F+r+1)^4*(1+r*p)

/-- The actual build budget is bounded without using selected rank as an exponent. -/
theorem buildBudget_le (d : RawDesign n F) (p bits readBudget : ℕ)
    (hc : ∀ g,d.count g≤p) :
    SemiprimePaidRuntimeDesign.buildBudget d bits readBudget ≤
      designBudget n F d.r p bits readBudget := by
  have hh (g : Fin d.r) : headSize d g≤n := by
    exact (List.length_filter_le _ _).trans_eq (by simp [SemiprimeFiniteEnumerations.fin])
  have hs := Finset.sum_le_sum (fun g (_ : g∈(Finset.univ : Finset (Fin d.r))) =>
    groupBudget_mono (bits:=bits) (hc g) (hh g) (le_refl readBudget))
  have ht := Finset.sum_le_sum (fun g (_ : g∈(Finset.univ : Finset (Fin d.r))) => hc g)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs ht
  unfold SemiprimePaidRuntimeDesign.buildBudget designBudget
  gcongr

/-- A polynomial source envelope replacing the subset expansion by paid alphabet D. -/
def sourceBudget (M n A D T N Q R : ℕ) : ℕ :=
  SemiprimeMaterializedSourceWords.producerBudget A T N Q+
  SemiprimeMaterializedSourceAcquisition.packingBudget M D Q (4*N+6*(N+1)^2+7)+
  (D*(D*(D*SemiprimeMaterializedSourceRows.rowPolynomial Q R+2)+3)+1+
    (Q*(R+1)+Q+R+R^2)+(2*Q*(R+1)+R^2)+1)+
  M*(n*(R+2+M*(2*(3*M+1)+2*(D*(7*Q+4)+1)+R+7+4*(R+1)+1)+2)+3)+2+
  M+M*n+1+M+D+9

/-- Actual source costs have a fixed polynomial bound at the native alphabet. -/
theorem sourceBudget_le (M n A D T N Q R start : ℕ)
    (hD : 2^(2*Q)≤D) (hstart : start≤Q) :
    SemiprimeMaterializedOriginalSource.budget M n A D T N Q R start ≤
      sourceBudget M n A D T N Q R := by
  have hr := SemiprimeMaterializedSourceRows.rowBudget_polynomial Q R D hD
  unfold SemiprimeMaterializedOriginalSource.budget SemiprimeMaterializedSourceAcquisition.budget
    SemiprimeMaterializedSourcePullback.acquireBudget SemiprimeMaterializedSourceRows.acquireBudget
    sourceBudget
  simp only [Nat.add_assoc]
  gcongr

/-- Raw setup envelope with interval start replaced by its public upper bound Q. -/
def rawBudget (n F M r Q R D A : ℕ) : ℕ :=
  SemiprimePaidSourceMetadata.budget n F M D A (M^2+Q*n^2) (n+F) Q+
  SemiprimePaidOriginalConstraints.polynomial M n A D (M^2+Q*n^2) (n+F) Q R Q r+
  4*R+1+M*D+M+12

/-- Both the word-menu and interval substitutions preserve the raw setup envelope. -/
theorem rawBudget_le (n F M r Q R D a A : ℕ) (ha : a≤A)
    (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q) :
    SemiprimePaidRawAcquisition.budget n F r Q R M D a (M^2+Q*n^2) (n+F) ≤
      rawBudget n F M r Q R D A := by
  unfold SemiprimePaidRawAcquisition.budget rawBudget
    SemiprimePaidSourceMetadata.budget SemiprimePaidOriginalConstraints.polynomial
    SemiprimePaidConstraintAcquisition.polynomial SemiprimePaidConstraintAcquisition.universalPolynomial
    SemiprimeMaterializedSourceWords.producerBudget SemiprimeMaterializedScoreSearch.evaluatorBudget
  gcongr

/-- Literal fixed polynomial in original dimensions and the two alphabet sizes. -/
def setupBudget (n F M r Q R B D A : ℕ) : ℕ :=
  SemiprimePaidFiniteEnumerations.polynomial n F M Q A A+
  sourceBudget M n A D (M^2+Q*n^2) (n+F) Q R+
  rawBudget n F M r Q R D A+
  Q*designBudget n F r (M*D+M) (SemiprimePaidMeasurementBound.bits B Q R)
    (2*(Q+r+(M*D+M)+n)+14)+10*Q+20

/-- One actual physical design has a uniform polynomial setup bound. -/
theorem physical_work_bound (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q) (t : Fin Q) :
    (SemiprimePaidRuntimeDesign.build
      (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F)
        (SemiprimePaidRawAcquisition.acquire arity coordinate
          (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B).value t)
      (SemiprimePaidRawAcquisition.reader (n:=n)
        (SemiprimePaidRawAcquisition.acquire arity coordinate
          (SemiprimeFiniteEnumerations.indexed n F r Q arity) eps R B).value t)
      (SemiprimePaidMeasurementBound.bits B Q R)).work ≤
    designBudget n F r ((∑ e,arity e)*r^(2*Q)+(∑ e,arity e))
      (SemiprimePaidMeasurementBound.bits B Q R)
      (2*(Q+r+((∑ e,arity e)*r^(2*Q)+(∑ e,arity e))+n)+14) := by
  let en := SemiprimeFiniteEnumerations.indexed n F r Q arity
  let snapshot := (SemiprimePaidRawAcquisition.acquire arity coordinate en eps R B).value
  let d : RawDesign n F := SemiprimePaidRawAcquisition.raw snapshot t
  let p := (∑ e,arity e)*r^(2*Q)+(∑ e,arity e)
  let bits := SemiprimePaidMeasurementBound.bits B Q R
  let rb := 2*(Q+r+p+n)+14
  have hc : snapshot.count≤p := by
    have h := SemiprimeCachedRawConstraints.acquired_count_le arity coordinate en eps R
    have hM : en.incidences.values.length=∑ e,arity e :=
      SemiprimeFiniteEnumerations.indexedIncidences_length F arity
    have hD : en.types.values.length=r^(2*Q) := SemiprimeFiniteEnumerations.universal_length r Q
    rw [hM,hD] at h
    exact h
  have hb : ∀ g j v, |d.rows g j v|≤(2^bits : ℕ) := by
    dsimp only [d,snapshot,en]
    rw [SemiprimePaidRawAcquisition.acquire_raw]
    intro g j v
    exact (SemiprimeAcquiredSourceCounter.raw_bounded arity coordinate eps R B howner hQ hAQ t g j v).trans
      (by exact_mod_cast SemiprimePaidMeasurementBound.bound_le B Q R)
  have hr : ∀ g j v,(SemiprimePaidRawAcquisition.reader (n:=n) snapshot t g j v).work≤rb := by
    intro g j v
    have h := SemiprimePaidRawAcquisition.acquire_reader_work arity coordinate en eps R B t g j v
    apply h.trans
    dsimp only [rb]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2
      (Nat.add_le_add_right (Nat.add_le_add_left hc (Q+r)) n)) 14
  have hw := SemiprimePaidRuntimeDesign.build_work d
    (SemiprimePaidRawAcquisition.reader (n:=n) snapshot t) bits rb
    (fun g j v => SemiprimePaidRawAcquisition.reader_value snapshot t g j v) hb hr
  exact hw.trans (buildBudget_le d p bits rb (fun _ => hc))

/-- Every setup report in the actual full counter is bounded from original parameters. -/
theorem setup_work_bound (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B : ℕ)
    (hr : 2≤r)
    (howner : ∀ v, (Finset.univ.filter
      (fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2=v)).card≤B)
    (hQ : 1≤Q) (hAQ : Subexp.TailInterval.intervalStart r Q R≤Q) :
    setupWork (r:=r) (Q:=Q) arity coordinate eps R B ≤
      setupBudget n F (∑ e,arity e) r Q R B (r^(2*Q)) (r^Q) := by
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  have he := SemiprimePaidFiniteEnumerations.indexed_work_polynomial n F r Q arity hQ
  have hs := SemiprimeMaterializedOriginalSource.acquire_work (n:=n) (r:=r) (Q:=Q) owner Sigma.fst en.value eps R
  have hx := SemiprimePaidRawAcquisition.acquire_work_native (n:=n) (r:=r) (Q:=Q) arity coordinate en.value hr eps R B
  have ht : en.value.wordTail.length≤r^Q := by
    rw [SemiprimePaidFiniteEnumerations.indexed_value]
    exact (List.length_filter_le _ _).trans_eq (SemiprimeFiniteEnumerations.words_length r Q)
  rw [SemiprimePaidFiniteEnumerations.indexed_incidence_length,
    SemiprimePaidFiniteEnumerations.indexed_universal_length,
    SemiprimePaidFiniteEnumerations.indexed_score_length,
    SemiprimePaidFiniteEnumerations.indexed_indices_length] at hs hx
  have hsource := hs.trans ((SemiprimePaidEnumeratedSource.sourceBudget_mono_words
    (∑ e,arity e) n en.value.wordTail.length (r^Q) (r^(2*Q)) ((∑ e,arity e)^2+Q*n^2)
    (n+F) Q R (SemiprimeMaterializedSourcePullback.centered r Q R) ht).trans
    (sourceBudget_le (∑ e,arity e) n (r^Q) (r^(2*Q)) ((∑ e,arity e)^2+Q*n^2)
      (n+F) Q R (SemiprimeMaterializedSourcePullback.centered r Q R)
      (Nat.pow_le_pow_left hr _) hAQ))
  have hraw := hx.trans (rawBudget_le n F (∑ e,arity e) r Q R (r^(2*Q)) en.value.wordTail.length (r^Q) ht hAQ)
  have hd := Finset.sum_le_sum (fun t (_ : t∈(Finset.univ : Finset (Fin Q))) =>
    physical_work_bound arity coordinate eps R B howner hQ hAQ t)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hd
  unfold setupWork setupBudget
  dsimp only
  simp only [Array.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  dsimp only [en,owner] at hsource hraw
  simp only [SemiprimePaidFiniteEnumerations.indexed_value] at hsource hraw ⊢
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · exact Nat.add_le_add (Nat.add_le_add he hsource) hraw
  · let f := fun en : SemiprimeSourceLayout.Enumerations
        ((e : Fin F) × Fin (arity e)) (Fin n) (Fin F) r Q =>
      ∑ t : Fin Q, (SemiprimePaidRuntimeDesign.build
        (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F)
          (SemiprimePaidRawAcquisition.acquire arity coordinate en eps R B).value t)
        (SemiprimePaidRawAcquisition.reader (n:=n)
          (SemiprimePaidRawAcquisition.acquire arity coordinate en eps R B).value t)
        (SemiprimePaidMeasurementBound.bits B Q R)).work
    have hEq := congrArg f (SemiprimePaidFiniteEnumerations.indexed_value n F r Q arity)
    exact hEq.le.trans hd

/-- The native report uses the actual physical designs and source arrays. -/
def nativeWork (arity : Fin F → ℕ) (coordinate : (e : Fin F) → Fin (arity e) → Fin n)
    (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → SemiprimeLocalArrayFrontend.EntryReport) : ℕ :=
  let en := SemiprimePaidFiniteEnumerations.indexed n F r Q arity
  let owner := fun i : (e : Fin F) × Fin (arity e) => coordinate i.1 i.2
  let source := SemiprimeMaterializedOriginalSource.acquire owner Sigma.fst en.value eps R
  let raw := SemiprimePaidRawAcquisition.acquire arity coordinate en.value eps R B
  let bits := SemiprimePaidMeasurementBound.bits B Q R
  let designs := Array.ofFn (fun t : Fin Q => SemiprimePaidRuntimeDesign.build
    (SemiprimePaidRawAcquisition.raw (n:=n) (F:=F) raw.value t)
    (SemiprimePaidRawAcquisition.reader (n:=n) raw.value t) bits)
  (SemiprimeMaterializedFibreNative.count Q J R
    (fun t => (designs[t.val]'(by simp [designs])).value)
    (fun e i v => SemiprimeSourceArrayAcquisition.read en.value.incidences source.value ⟨e,i⟩ v) T).work

/-- Exact additive separation of ACTUAL setup from ACTUAL native execution. -/
theorem count_work_eq_setup_add_native (arity : Fin F → ℕ)
    (coordinate : (e : Fin F) → Fin (arity e) → Fin n) (eps : ℚ) (R B J : ℕ)
    (T : (e : Fin F) → (Fin (arity e) → Bool) → SemiprimeLocalArrayFrontend.EntryReport) :
    (SemiprimeFullSetupCounter.count (r:=r) (Q:=Q) arity coordinate eps R B J T).work=
      setupWork (r:=r) (Q:=Q) arity coordinate eps R B+
      nativeWork (r:=r) (Q:=Q) arity coordinate eps R B J T := by
  unfold SemiprimeFullSetupCounter.count setupWork nativeWork
  dsimp only
  omega

end RiemannGaussian.SemiprimeFullSetupBudget
