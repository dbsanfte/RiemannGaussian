/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceWordIdCaller
import RiemannGaussian.SemiprimeSourceWordIdCountsClock
import RiemannGaussian.SemiprimeSourceSearchState

/-! # Original-resource report of acquired Boolean-ID source selection
All bank/ID acquisition, prefix copies, concrete predicate/count/weight work and
actual controller reports are retained. Native arity/owner/index/descriptor and
finite natural-control stages still require the full primitive-machine join.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceWordIdSearchBudget
open scoped BigOperators
open SemiprimeRationalBits SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceWordBank SemiprimeSourceWordIdControl

/-- Derived physical cached-weight width from original input magnitudes. -/
def weightCap (M n lam U : ℕ) : ℕ :=
  SemiprimeSourceScoreWeightBits.weightWidth (SemiprimeSourceScoreWeightAcquisition.inputWidth M n lam U)
/-- Actual physical score width from acquired count and weight array sizes. -/
def wordCap (L T M n lam U : ℕ) : ℕ :=
  3*SemiprimeSourceWordIdCountsBounds.operandWidth L T (weightCap M n lam U)+1
/-- Every scan, comparison, selected-ID copy and complete prefix copy in the controller. -/
def controlBudget (L T N M n r Q lam U : ℕ) : ℕ :=
  2*N+3+N*((L-1)*(2*SemiprimeSourceWordIdCountsClock.scoreBudget r Q N L T (weightCap M n lam U)+
    200*(wordCap L T M n lam U+1)^2+4*(2*L)+5)+4*(2*L)+2+N*(4*(2*L)+4)+4)+N*(4*(2*L)+4)+1
/-- Original bank/weights setup and actual finite physical-ID controller. -/
def runBudget (M n r Q lam L U T N : ℕ) : ℕ :=
  SemiprimeSourceWordBankAcquisitionBudget.budget r Q L+
    SemiprimeSourceScoreWeightAcquisition.acquisitionBudget M n r Q lam U+
      controlBudget L T N M n r Q lam U+L+5

/-- Actual acquired input and reachable-menu invariants close the complete search report. -/
theorem run_work (M n r Q lam : ℕ) [NeZero r]
    (programs : List (ScoreProgram Q)) (N : ℕ)
    (hp : ∀ p∈programs,∀ i∈support p,i ≤ N) :
    (SemiprimeSourceWordIdSearch.run M n r Q lam programs N).work ≤
      runBudget M n r Q lam (r^Q) (r^(2*Q)) programs.length N := by
  let bank := acquire r Q
  let weights := SemiprimeSourceScoreWeightAcquisition.acquire M n r Q lam
  have hi : bank.ids.length=r^Q := (acquire_ids_length r Q).trans
    (SemiprimeSourceWordBankIndexed.acquire_length r Q)
  have hw := SemiprimeSourceScoreWeightAcquisition.acquire_length M n r Q lam
  have hc := SemiprimeSourceWordIdMenu.candidates_valid r Q
  rw [SemiprimeSourceWordIdMenu.first_eq_default] at hc
  have hd := SemiprimeSourceWordBankIndexed.default_mem r Q
  have callback (tokens : List Bool) (fixed : List (List Bool))
      (hlen : tokens.length+fixed.length ≤ N) (hf : InMenu bank.ids fixed) :
      (SemiprimeSourceWordIdCounts.score bank weights defaultID programs tokens.length fixed).clock ≤
          SemiprimeSourceWordIdCountsClock.scoreBudget r Q N (r^Q) programs.length
            (weightCap M n lam (r^(2*Q))) ∧
        Width (SemiprimeSourceWordIdCounts.score bank weights defaultID programs tokens.length fixed).word
          (wordCap (r^Q) programs.length M n lam (r^(2*Q))) := by
    have hv := SemiprimeSourceWordIdCountsBounds.score_width bank weights defaultID programs tokens.length fixed
      (weightCap M n lam (r^(2*Q))) (SemiprimeSourceWordIdCountsBounds.acquired_ids_pos r Q) hw.1 hw.2
    rw [hi] at hv
    exact ⟨SemiprimeSourceWordIdCountsClock.score_clock r Q weights defaultID programs tokens.length fixed
      N _ hd hf (by omega) hp hw.1 hw.2,hv⟩
  have hcontrol := SemiprimeSourceWordIdControl.run_work bank.ids defaultID
    (SemiprimeSourceWordIdMenu.tail bank)
    (fun ts fixed => SemiprimeSourceWordIdCounts.score bank weights defaultID programs ts.length fixed)
    N [] (SemiprimeSourceWordIdCountsClock.scoreBudget r Q N (r^Q) programs.length
      (weightCap M n lam (r^(2*Q))))
    (wordCap (r^Q) programs.length M n lam (r^(2*Q))) (2*r^Q) N
    (SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q) hc
    (by simp [InMenu]) callback (by simp)
  have htail : (SemiprimeSourceWordIdMenu.tail bank).length=r^Q-1 := by
    simp only [SemiprimeSourceWordIdMenu.tail,List.length_tail,hi]
  rw [htail] at hcontrol
  have hb := SemiprimeSourceWordBankAcquisitionBudget.acquire_clock r Q (NeZero.pos r)
  have hwc := SemiprimeSourceScoreWeightAcquisition.acquire_clock M n r Q lam (NeZero.pos r)
  change _ ≤ runBudget M n r Q lam (r^Q) (r^(2*Q)) programs.length N
  unfold SemiprimeSourceWordIdSearch.run runBudget controlBudget
  dsimp only
  rw [show (acquire r Q).ids.length=r^Q from hi]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add hb hwc) hcontrol) (r^Q)) 5

/-- All original metadata/descriptor acquisition plus concrete ID selection. -/
def indexedBudget (n F r Q lam M L U T N : ℕ) : ℕ :=
  SemiprimeSourceWordIdMetadata.budget n F Q M+T*(8*N+15)+1+
    runBudget M n r Q lam L U T N+3

/-- Actual original metadata completeness supplies the descriptor bounds; no program advice. -/
theorem indexed_work (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    (SemiprimeSourceWordIdCaller.indexed n F r Q lam arity owner).work ≤
      indexedBudget n F r Q lam (∑ e,arity e) (r^Q) (r^(2*Q)) ((∑ e,arity e)^2+Q*n^2) (n+F) := by
  let metadata := SemiprimeSourceWordIdMetadata.acquire n F Q arity
  have cert := SemiprimeSourceWordIdMetadata.indices_certificate n F Q arity
  let indices : OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.FiniteEnumeration (Fin n ⊕ Fin F) :=
    ⟨metadata.indices,cert.1,cert.2⟩
  have hp : ∀ p∈(SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst metadata.indices metadata.terms).value,
      ∀ i∈support p,i ≤ metadata.indices.length := by
    intro p hpm i hi
    exact (SemiprimeSourceSearchState.compileAll_support_lt owner Sigma.fst indices metadata.terms p hpm i hi).le
  have hs := run_work metadata.incidences.length n r Q lam
    (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst metadata.indices metadata.terms).value
    metadata.indices.length hp
  rw [SemiprimeSourceSearchState.compileAll_length] at hs
  have hc := SemiprimeMaterializedSourceWords.compileAll_work owner Sigma.fst metadata.indices metadata.terms
  have hm := SemiprimeSourceWordIdMetadata.acquire_clock n F Q arity
  have sizes := SemiprimeSourceWordIdMetadata.sizes n F Q arity
  change metadata.incidences.length=_ ∧ metadata.terms.length=_ ∧ metadata.indices.length=_ at sizes
  rw [sizes.1] at hs
  rw [sizes.2.1,sizes.2.2] at hs hc
  have total := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hm hc) hs) 3
  unfold SemiprimeSourceWordIdCaller.indexed indexedBudget
  dsimp only
  change metadata.clock+(SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst metadata.indices metadata.terms).work+
    (SemiprimeSourceWordIdSearch.run metadata.incidences.length n r Q lam
      (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst metadata.indices metadata.terms).value metadata.indices.length).work+3 ≤ _
  rw [sizes.1,sizes.2.2]
  simpa only [Nat.add_assoc] using total

end RiemannGaussian.SemiprimeSourceWordIdSearchBudget
