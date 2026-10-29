/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceClassifiedCaller
import RiemannGaussian.SemiprimeSourceClassifiedCountsClock
import RiemannGaussian.SemiprimeSourceSearchState

/-! # Actual original-resource report of classified source selection
All bank/power/weight setup, concrete classified callbacks, comparisons and
copies remain. No local completion tree, unary padding, or unary universal
cardinality initializer occurs. Native original metadata/control is explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceClassifiedSearchBudget
open scoped BigOperators
open SemiprimeRationalBits SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceWordBank SemiprimeSourceWordIdControl

/-- Actual cached coefficient width from original dimensions and power growth. -/
def weightCap (M n lam r Q : ℕ) : ℕ :=
  SemiprimeSourceScoreWeightBits.weightWidth (SemiprimeSourceClassifiedWeights.inputWidth M n lam r Q)
/-- Actual score width uses physical local payload size and the number of lane additions. -/
def wordCap (r Q T M n lam : ℕ) : ℕ :=
  3*SemiprimeSourceClassifiedCountsClock.operandWidth r Q T (weightCap M n lam r Q)+1
/-- Complete existing controller report with concrete classified score budgets. -/
def controlBudget (L T N M n r Q lam : ℕ) : ℕ :=
  2*N+3+N*((L-1)*(2*SemiprimeSourceClassifiedCountsClock.scoreBudget r Q N L T (weightCap M n lam r Q)+
    200*(wordCap r Q T M n lam+1)^2+4*(2*L)+5)+4*(2*L)+2+N*(4*(2*L)+4)+4)+N*(4*(2*L)+4)+1
/-- The actual bank/powers/weights setup and every executed source-selection step. -/
def runBudget (M n r Q lam L T N : ℕ) : ℕ :=
  SemiprimeSourceWordBankAcquisitionBudget.budget r Q L+
    SemiprimeSourceCountPowers.budget r Q+SemiprimeSourceClassifiedWeights.budget M n lam r Q+
      controlBudget L T N M n r Q lam+L+7

/-- Actual acquired bank/cache and reachable-menu invariants close the search report. -/
theorem run_work (M n r Q lam : ℕ) [NeZero r] (programs : List (ScoreProgram Q)) (N : ℕ)
    (hp : ∀ p∈programs,∀ i∈support p,i ≤ N) :
    (SemiprimeSourceClassifiedSearch.run M n r Q lam programs N).work ≤
      runBudget M n r Q lam (r^Q) programs.length N := by
  let bank := acquire r Q
  let powers := SemiprimeSourceCountPowers.acquire r Q
  let weights := SemiprimeSourceClassifiedWeights.acquire M n lam powers
  have hi : bank.ids.length=r^Q := (acquire_ids_length r Q).trans
    (SemiprimeSourceWordBankIndexed.acquire_length r Q)
  have hw := SemiprimeSourceClassifiedWeights.acquire_length M n r Q lam
  have hc := SemiprimeSourceWordIdMenu.candidates_valid r Q
  rw [SemiprimeSourceWordIdMenu.first_eq_default] at hc
  have hd := SemiprimeSourceWordBankIndexed.default_mem r Q
  have callback (tokens : List Bool) (fixed : List (List Bool))
      (hlen : tokens.length+fixed.length ≤ N) (hf : InMenu bank.ids fixed) :
      (SemiprimeSourceClassifiedCounts.score bank powers weights defaultID programs tokens.length fixed).clock ≤
          SemiprimeSourceClassifiedCountsClock.scoreBudget r Q N (r^Q) programs.length (weightCap M n lam r Q) ∧
        Width (SemiprimeSourceClassifiedCounts.score bank powers weights defaultID programs tokens.length fixed).word
          (wordCap r Q programs.length M n lam) := by
    exact ⟨SemiprimeSourceClassifiedCountsClock.score_clock r Q weights defaultID programs tokens.length fixed
      N _ hd hf (by omega) hp hw.1 hw.2,
      SemiprimeSourceClassifiedCountsClock.score_width r Q weights defaultID programs tokens.length fixed
        _ hw.1 hw.2⟩
  have hcontrol := SemiprimeSourceWordIdControl.run_work bank.ids defaultID
    (SemiprimeSourceWordIdMenu.tail bank)
    (fun ts fixed => SemiprimeSourceClassifiedCounts.score bank powers weights defaultID programs ts.length fixed)
    N [] (SemiprimeSourceClassifiedCountsClock.scoreBudget r Q N (r^Q) programs.length (weightCap M n lam r Q))
    (wordCap r Q programs.length M n lam) (2*r^Q) N
    (SemiprimeSourceWordBankAcquisitionBudget.acquire_ids_bounded r Q) hc
    (by simp [InMenu]) callback (by simp)
  have htail : (SemiprimeSourceWordIdMenu.tail bank).length=r^Q-1 := by
    simp only [SemiprimeSourceWordIdMenu.tail,List.length_tail,hi]
  rw [htail] at hcontrol
  have hb := SemiprimeSourceWordBankAcquisitionBudget.acquire_clock r Q (NeZero.pos r)
  have hpw := SemiprimeSourceCountPowers.acquire_clock r Q
  have hwc := SemiprimeSourceClassifiedWeights.acquire_clock M n r Q lam
  unfold SemiprimeSourceClassifiedSearch.run runBudget controlBudget
  dsimp only
  rw [show (acquire r Q).ids.length=r^Q from hi]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hb hpw) hwc) hcontrol) (r^Q)) 7

/-- Original metadata/descriptors and the concrete optimized source search. -/
def indexedBudget (n F r Q lam M L T N : ℕ) : ℕ :=
  SemiprimeSourceWordIdMetadata.budget n F Q M+T*(8*N+15)+1+
    runBudget M n r Q lam L T N+3

/-- Original acquired metadata itself supplies every support and dimension bound. -/
theorem indexed_work (n F r Q lam : ℕ) [NeZero r] (arity : Fin F → ℕ)
    (owner : ((e : Fin F) × Fin (arity e)) → Fin n) :
    (SemiprimeSourceClassifiedCaller.indexed n F r Q lam arity owner).work ≤
      indexedBudget n F r Q lam (∑ e,arity e) (r^Q) ((∑ e,arity e)^2+Q*n^2) (n+F) := by
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
  unfold SemiprimeSourceClassifiedCaller.indexed indexedBudget
  dsimp only
  change metadata.clock+(SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst metadata.indices metadata.terms).work+
    (SemiprimeSourceClassifiedSearch.run metadata.incidences.length n r Q lam
      (SemiprimeMaterializedSourceWords.compileAll owner Sigma.fst metadata.indices metadata.terms).value metadata.indices.length).work+3 ≤ _
  rw [sizes.1,sizes.2.2]
  simpa only [Nat.add_assoc] using total

end RiemannGaussian.SemiprimeSourceClassifiedSearchBudget
