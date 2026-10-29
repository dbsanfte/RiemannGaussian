import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SqrtLog.PackingSelection
import OpenAISemiprime.Algorithms.SubexponentialSAT.LocalExpectation

namespace OAI.Algorithms

/-! A deterministic conditional-expectation algorithm with at most four word reads per term. -/
namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation

section Algorithm
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

abbrev ScoreTerm (I V : Type*) (Q : ℕ) := (I × I) ⊕ (Fin Q × V × V)

def scoreSupport : ScoreTerm I V Q → Finset (V ⊕ E)
  | .inl (i,j) => [Sum.inl (ivar i), Sum.inr (factor i),
      Sum.inl (ivar j), Sum.inr (factor j)].toFinset
  | .inr (_,v,w) => [Sum.inl v, Sum.inl w].toFinset

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem scoreSupport_card_le (z : ScoreTerm I V Q) :
    (scoreSupport ivar factor z).card ≤ 4 := by
  cases z with
  | inl p => exact (List.toFinset_card_le _).trans (by simp)
  | inr p => exact (List.toFinset_card_le _).trans (by simp)

def scoreTerm (x y : ℚ) : ScoreTerm I V Q → WordAssignment V E r Q → ℚ
  | .inl (i,j), ω => y^2 *
      (if incidenceType ivar factor ω i = incidenceType ivar factor ω j then 1 else 0)
  | .inr (t,v,w), ω => x^2 * (if ω (.inl v) t = ω (.inl w) t then 1 else 0)

def scoreOffset (x y : ℚ) : ℚ :=
  y^2 * (Fintype.card I : ℚ)^2 / (Fintype.card (UniversalType r Q 1) : ℚ) +
    x^2 * (Q : ℚ) * (Fintype.card V : ℚ)^2 / (r : ℚ)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem scoreTerm_dependsOn (x y : ℚ) (z : ScoreTerm I V Q) :
    DependsOn (scoreSupport ivar factor z) (scoreTerm (r := r) ivar factor x y z) := by
  intro ω ω' h
  cases z with
  | inl p =>
    rcases p with ⟨i,j⟩
    have hi : incidenceType ivar factor ω i = incidenceType ivar factor ω' i := by
      apply UniversalType.ext
      · exact h _ (by simp [scoreSupport])
      · funext s
        exact h _ (by simp [scoreSupport])
    have hj : incidenceType ivar factor ω j = incidenceType ivar factor ω' j := by
      apply UniversalType.ext
      · exact h _ (by simp [scoreSupport])
      · funext s
        exact h _ (by simp [scoreSupport])
    simp only [scoreTerm, hi, hj]
  | inr p =>
    rcases p with ⟨t,v,w⟩
    have hv := h (Sum.inl v) (by simp [scoreSupport])
    have hw := h (Sum.inl w) (by simp [scoreSupport])
    simp only [scoreTerm, hv, hw]

variable [NeZero r]

private theorem sum_list_eq {T : Type*} [Fintype T] [DecidableEq T]
    (xs : List T) (hn : xs.Nodup) (hc : ∀ t, t ∈ xs) (f : T → ℚ) :
    (xs.map f).sum = ∑ t, f t := by
  rw [← List.sum_toFinset f hn]
  have hs : xs.toFinset = Finset.univ := by ext t; simp [hc t]
  rw [hs]

omit [Fintype E] [DecidableEq E] in
theorem objective_score_eq (terms : List (ScoreTerm I V Q))
    (hn : terms.Nodup) (hc : ∀ z, z ∈ terms) (x y : ℚ)
    (ω : WordAssignment V E r Q) :
    objective terms (scoreTerm ivar factor x y) (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) ω =
      jointScore (fun η => energy (incidenceType ivar factor η)) headEnergy x y ω := by
  unfold objective
  rw [sum_list_eq terms hn hc, Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, scoreTerm]
  unfold jointScore headEnergy scoreOffset
  dsimp only
  rw [energy_eq_collisions]
  simp_rw [energy_eq_collisions]
  simp only [Fintype.card_fin, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum]
  ring

def numberedScoreSupport (indices : List (V ⊕ E)) (z : ScoreTerm I V Q) : Finset ℕ :=
  (scoreSupport ivar factor z).image (indexCode indices)

def numberedScoreTerm (indices : List (V ⊕ E)) (x y : ℚ) (z : ScoreTerm I V Q) :
    (ℕ → Word r Q) → ℚ :=
  reindexTerm (indexCode indices) (scoreTerm ivar factor x y z)

omit [NeZero r] in
omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numberedScoreTerm_dependsOn (indices : List (V ⊕ E)) (x y : ℚ)
    (z : ScoreTerm I V Q) :
    DependsOn (numberedScoreSupport ivar factor indices z)
      (numberedScoreTerm (r := r) ivar factor indices x y z) :=
  reindexTerm_dependsOn _ _ _ (scoreTerm_dependsOn ivar factor x y z)

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numberedScoreSupport_card_le (indices : List (V ⊕ E)) (z : ScoreTerm I V Q) :
    (numberedScoreSupport ivar factor indices z).card ≤ 4 :=
  Finset.card_image_le.trans (scoreSupport_card_le ivar factor z)

/-- Actual finite word search. It evaluates only local completions at each choice. -/
def computedWords (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) :
    WordAssignment V E r Q :=
  let values := localAssign a tail terms (numberedScoreSupport ivar factor indices)
    (numberedScoreTerm ivar factor indices x y)
    (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) a indices.length
  fun i => decode a values (indexCode indices i)

theorem computedWords_score_le_mean (a : Word r Q) (tail : List (Word r Q))
    (haN : (a::tail).Nodup) (haC : ∀ w, w ∈ a::tail)
    (terms : List (ScoreTerm I V Q)) (htN : terms.Nodup) (htC : ∀ z, z ∈ terms)
    (indices : List (V ⊕ E)) (hiN : indices.Nodup) (hiC : ∀ i, i ∈ indices)
    (x y : ℚ) :
    jointScore (fun η => energy (incidenceType ivar factor η)) headEnergy x y
      (computedWords ivar factor a tail terms indices x y) ≤
    SubexponentialSAT.Variance.mean SubexponentialSAT.Variance.uniformWeight
      (jointScore (fun η : WordAssignment V E r Q => energy (incidenceType ivar factor η))
        headEnergy x y) := by
  have h := localAssign_le_initial a tail terms (numberedScoreSupport ivar factor indices)
    (numberedScoreTerm ivar factor indices x y)
    (numberedScoreTerm_dependsOn ivar factor indices x y)
    (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) a indices.length
  have heq := initialEvaluator_reindex_uniform (a::tail) (List.cons_ne_nil _ _) haN haC
    terms (scoreSupport ivar factor) (scoreTerm ivar factor x y)
    (scoreTerm_dependsOn ivar factor x y)
    (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) a indices hiN hiC
  have ho : objective terms (scoreTerm (r := r) ivar factor x y)
      (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) =
      jointScore (fun η => energy (incidenceType ivar factor η)) headEnergy x y := by
    funext ω
    exact objective_score_eq ivar factor terms htN htC x y ω
  rw [ho] at heq
  rw [← heq]
  convert h using 1
  exact (objective_score_eq ivar factor terms htN htC x y _).symm
  rfl

/-- Same search instrumented by the number of local term evaluations. -/
def computedWordsCounted (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) :
    WordAssignment V E r Q × ℕ :=
  let result := assignWithCost a tail
    (sequentialEvaluatorCounted (a::tail) terms (numberedScoreSupport ivar factor indices)
      (numberedScoreTerm ivar factor indices x y)
      (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) a) indices.length []
  (fun i => decode a result.1 (indexCode indices i), result.2)

omit [Fintype E] [DecidableEq I] [NeZero r] in
theorem computedWordsCounted_value (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) :
    (computedWordsCounted ivar factor a tail terms indices x y).1 =
      computedWords ivar factor a tail terms indices x y := by
  simp only [computedWordsCounted, computedWords, localAssign, assignWithCost_value,
    sequentialEvaluatorCounted_value]

omit [NeZero r] in
omit [Fintype E] [DecidableEq I] in
theorem computedWordsCounted_calls_le (a : Word r Q) (tail : List (Word r Q))
    (terms : List (ScoreTerm I V Q)) (indices : List (V ⊕ E)) (x y : ℚ) :
    (computedWordsCounted ivar factor a tail terms indices x y).2 ≤
      indices.length * (2*tail.length*(terms.length*(a::tail).length^4)) := by
  apply assignWithCost_calls_le
  intro n fixed
  exact sequentialEvaluatorCounted_calls_le (a::tail) (List.cons_ne_nil _ _)
    terms (numberedScoreSupport ivar factor indices)
    (numberedScoreTerm ivar factor indices x y)
    (scoreOffset (I := I) (V := V) (r := r) (Q := Q) x y) a n fixed 4
    (numberedScoreSupport_card_le ivar factor indices)

end Algorithm
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
