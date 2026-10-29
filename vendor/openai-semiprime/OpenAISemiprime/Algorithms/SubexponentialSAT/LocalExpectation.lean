import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.ConditionalExpectation
import OpenAISemiprime.Algorithms.SubexponentialSAT.TypeDistribution

namespace OAI.Algorithms

/-!
# Conditional expectations of local objectives

A local term is evaluated only on the still-unassigned coordinates in its
support. The resulting evaluator is proved equal to exhaustive conditional
expectation. Instrumentation counts calls to local terms, separately from
arithmetic and data-structure costs.
-/

namespace SubexponentialSAT.LocalExpectation

open SubexponentialSAT.ConditionalExpectation
open scoped BigOperators

variable {I W J : Type*} [DecidableEq I]

/-- A term reads only the coordinates in `support`. -/
def DependsOn (support : Finset I) (f : (I → W) → ℚ) : Prop :=
  ∀ ω ω', (∀ i ∈ support, ω i = ω' i) → f ω = f ω'

/-- Exhaustive conditional average on an explicit list of remaining indices. -/
def wordExpectation (alphabet : List W) (f : (I → W) → ℚ) :
    List I → (I → W) → ℚ
  | [], ω => f ω
  | i :: remaining, ω => mean alphabet
      (fun w => wordExpectation alphabet f remaining (Function.update ω i w))

theorem mean_const (alphabet : List W) (hne : alphabet ≠ []) (r : ℚ) :
    mean alphabet (fun _ => r) = r := by
  have hlen : (alphabet.length : ℚ) ≠ 0 := by
    exact_mod_cast (List.length_pos_iff.mpr hne).ne'
  simp only [mean, List.map_const', List.sum_replicate, nsmul_eq_mul]
  apply (div_eq_iff hlen).2
  ring

theorem mean_add (alphabet : List W) (f g : W → ℚ) :
    mean alphabet (fun w => f w + g w) = mean alphabet f + mean alphabet g := by
  simp [mean, List.sum_map_add, add_div]

theorem mean_sub (alphabet : List W) (f g : W → ℚ) :
    mean alphabet (fun w => f w - g w) = mean alphabet f - mean alphabet g := by
  have h : (alphabet.map (fun w => f w - g w)).sum =
      (alphabet.map f).sum - (alphabet.map g).sum := by
    induction alphabet with
    | nil => simp
    | cons a as ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring
  simp only [mean, h, sub_div]

theorem wordExpectation_dependsOn (alphabet : List W) (support : Finset I)
    (f : (I → W) → ℚ) (hf : DependsOn support f) (remaining : List I) :
    DependsOn support (wordExpectation alphabet f remaining) := by
  induction remaining with
  | nil => exact hf
  | cons i remaining ih =>
      intro ω ω' h
      simp only [wordExpectation]
      apply congrArg (mean alphabet)
      funext w
      apply ih
      intro j hj
      by_cases hji : j = i
      · subst j; simp
      · simp [Function.update_of_ne hji, h j hj]

/-- Indices still free and actually read by a local term. -/
def active (support : Finset I) (remaining : List I) : List I :=
  remaining.filter (fun i => decide (i ∈ support))

/-- Removing unread free indices leaves the exact conditional average. -/
theorem wordExpectation_filter (alphabet : List W) (hne : alphabet ≠ [])
    (support : Finset I) (f : (I → W) → ℚ) (hf : DependsOn support f)
    (remaining : List I) (ω : I → W) :
    wordExpectation alphabet f remaining ω =
      wordExpectation alphabet f (active support remaining) ω := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      by_cases hi : i ∈ support
      · simp only [active, List.filter_cons, hi, decide_true,
          ite_true, wordExpectation]
        apply congrArg (mean alphabet)
        funext w
        exact ih _
      · have hignore (w : W) :
            wordExpectation alphabet f remaining (Function.update ω i w) =
              wordExpectation alphabet f remaining ω := by
          apply wordExpectation_dependsOn alphabet support f hf remaining
          intro j hj
          have hji : j ≠ i := by intro h; subst j; exact hi hj
          simp [Function.update_of_ne hji]
        simp only [wordExpectation, active, List.filter_cons, hi, decide_false,
          Bool.false_eq_true, ite_false]
        simp_rw [hignore]
        rw [mean_const alphabet hne]
        exact ih ω

theorem wordExpectation_add (alphabet : List W) (f g : (I → W) → ℚ)
    (remaining : List I) (ω : I → W) :
    wordExpectation alphabet (fun η => f η + g η) remaining ω =
      wordExpectation alphabet f remaining ω + wordExpectation alphabet g remaining ω := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      simp only [wordExpectation]
      simp_rw [ih]
      exact mean_add alphabet _ _

theorem wordExpectation_sub (alphabet : List W) (f g : (I → W) → ℚ)
    (remaining : List I) (ω : I → W) :
    wordExpectation alphabet (fun η => f η - g η) remaining ω =
      wordExpectation alphabet f remaining ω - wordExpectation alphabet g remaining ω := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      simp only [wordExpectation]
      simp_rw [ih]
      exact mean_sub alphabet _ _

theorem wordExpectation_const (alphabet : List W) (hne : alphabet ≠ [])
    (r : ℚ) (remaining : List I) (ω : I → W) :
    wordExpectation alphabet (fun _ => r) remaining ω = r := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      simp only [wordExpectation]
      simp_rw [ih]
      exact mean_const alphabet hne r

theorem wordExpectation_sum (alphabet : List W) (terms : List J)
    (f : J → (I → W) → ℚ) (remaining : List I) (ω : I → W) :
    wordExpectation alphabet (fun η => (terms.map (fun j => f j η)).sum) remaining ω =
      (terms.map (fun j => wordExpectation alphabet (f j) remaining ω)).sum := by
  induction terms with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      induction remaining generalizing ω with
      | nil => rfl
      | cons i remaining ih => simp only [wordExpectation]; simp_rw [ih]; simp [mean]
  | cons j terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [wordExpectation_add, ih]

/-- A sum of local terms with a constant offset, including the collision form
of the sum of squared type-count deviations. -/
def objective (terms : List J) (f : J → (I → W) → ℚ) (offset : ℚ)
    (ω : I → W) : ℚ := (terms.map (fun j => f j ω)).sum - offset

/-- Efficient local conditional evaluation: a separate small enumeration for
each local term, with unrelated random words omitted. -/
def localEvaluator (alphabet : List W) (terms : List J)
    (support : J → Finset I) (f : J → (I → W) → ℚ) (offset : ℚ)
    (remaining : List I) (ω : I → W) : ℚ :=
  (terms.map (fun j => wordExpectation alphabet (f j) (active (support j) remaining) ω)).sum
    - offset

theorem localEvaluator_eq (alphabet : List W) (hne : alphabet ≠ [])
    (terms : List J) (support : J → Finset I) (f : J → (I → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ)
    (remaining : List I) (ω : I → W) :
    localEvaluator alphabet terms support f offset remaining ω =
      wordExpectation alphabet (objective terms f offset) remaining ω := by
  unfold localEvaluator objective
  rw [wordExpectation_sub, wordExpectation_sum,
    wordExpectation_const alphabet hne]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  exact (wordExpectation_filter alphabet hne (support j) (f j) (hf j) remaining ω).symm

/-- A repetition-free remaining-index list has at most `support.card` active
indices. No bound on the total number of remaining indices is needed. -/
theorem active_length_le (support : Finset I) (remaining : List I)
    (hremaining : remaining.Nodup) :
    (active support remaining).length ≤ support.card := by
  have hn : (active support remaining).Nodup := hremaining.filter _
  rw [← List.toFinset_card_of_nodup hn]
  apply Finset.card_le_card
  intro i hi
  have hi' : i ∈ active support remaining := by simpa using hi
  exact of_decide_eq_true (List.mem_filter.mp hi').2

/-- Exact instrumentation of exhaustive averaging over its supplied indices.
One count unit is one invocation of the local terminal function `f`. -/
def wordExpectationCounted (alphabet : List W) (f : (I → W) → ℚ) :
    List I → (I → W) → ℚ × ℕ
  | [], ω => (f ω, 1)
  | i :: remaining, ω =>
      let children := alphabet.map (fun w =>
        wordExpectationCounted alphabet f remaining (Function.update ω i w))
      ((children.map Prod.fst).sum / (alphabet.length : ℚ),
        (children.map Prod.snd).sum)

theorem wordExpectationCounted_value (alphabet : List W) (f : (I → W) → ℚ)
    (remaining : List I) (ω : I → W) :
    (wordExpectationCounted alphabet f remaining ω).1 =
      wordExpectation alphabet f remaining ω := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      simp [wordExpectationCounted, wordExpectation, mean, List.map_map, ih,
        Function.comp_def]

theorem wordExpectationCounted_calls (alphabet : List W) (f : (I → W) → ℚ)
    (remaining : List I) (ω : I → W) :
    (wordExpectationCounted alphabet f remaining ω).2 = alphabet.length ^ remaining.length := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons i remaining ih =>
      simp [wordExpectationCounted, List.map_map, ih, Function.comp_def,
        pow_succ, Nat.mul_comm]

/-- The implementation computes each local result once and sums its value
and terminal-call count. -/
def localEvaluatorCounted (alphabet : List W) (terms : List J)
    (support : J → Finset I) (f : J → (I → W) → ℚ) (offset : ℚ)
    (remaining : List I) (ω : I → W) : ℚ × ℕ :=
  let results := terms.map (fun j =>
    wordExpectationCounted alphabet (f j) (active (support j) remaining) ω)
  ((results.map Prod.fst).sum - offset, (results.map Prod.snd).sum)

theorem localEvaluatorCounted_value (alphabet : List W) (terms : List J)
    (support : J → Finset I) (f : J → (I → W) → ℚ) (offset : ℚ)
    (remaining : List I) (ω : I → W) :
    (localEvaluatorCounted alphabet terms support f offset remaining ω).1 =
      localEvaluator alphabet terms support f offset remaining ω := by
  simp [localEvaluatorCounted, localEvaluator, List.map_map,
    wordExpectationCounted_value, Function.comp_def]

theorem localEvaluatorCounted_calls (alphabet : List W) (terms : List J)
    (support : J → Finset I) (f : J → (I → W) → ℚ) (offset : ℚ)
    (remaining : List I) (ω : I → W) :
    (localEvaluatorCounted alphabet terms support f offset remaining ω).2 =
      (terms.map (fun j => alphabet.length ^ (active (support j) remaining).length)).sum := by
  simp [localEvaluatorCounted, List.map_map, wordExpectationCounted_calls,
    Function.comp_def]

/-- With fixed alphabet and fixed support bound, this is linear in the number
of local terms, regardless of the number of globally unassigned variables. -/
theorem localEvaluatorCounted_calls_le (alphabet : List W) (hne : alphabet ≠ [])
    (terms : List J) (support : J → Finset I) (f : J → (I → W) → ℚ) (offset : ℚ)
    (remaining : List I) (hremaining : remaining.Nodup) (ω : I → W)
    (s : ℕ) (hs : ∀ j, (support j).card ≤ s) :
    (localEvaluatorCounted alphabet terms support f offset remaining ω).2 ≤
      terms.length * alphabet.length ^ s := by
  rw [localEvaluatorCounted_calls]
  have hterm (j : J) : alphabet.length ^ (active (support j) remaining).length ≤
      alphabet.length ^ s :=
    Nat.pow_le_pow_right (List.length_pos_iff.mpr hne)
      ((active_length_le (support j) remaining hremaining).trans (hs j))
  induction terms with
  | nil => simp
  | cons j terms ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        _ ≤ alphabet.length ^ s + terms.length * alphabet.length ^ s :=
          Nat.add_le_add (hterm j) ih
        _ = _ := by ring

section Sequential

/-- Decode the reverse list of chosen values into numbered word variables. -/
def decode (default : W) : List W → ℕ → W
  | [] => fun _ => default
  | w :: fixed => Function.update (decode default fixed) fixed.length w

/-- Polynomially many local evaluations per sequential candidate when term
supports are bounded. Numbered coordinates start at `fixed.length`. -/
def sequentialEvaluator (alphabet : List W) (terms : List J)
    (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ) (offset : ℚ)
    (default : W) (n : ℕ) (fixed : List W) : ℚ :=
  localEvaluator alphabet terms support f offset
    (List.range' fixed.length n) (decode default fixed)

theorem sequentialEvaluator_zero (alphabet : List W) (hne : alphabet ≠ [])
    (terms : List J) (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W)
    (fixed : List W) :
    sequentialEvaluator alphabet terms support f offset default 0 fixed =
      objective terms f offset (decode default fixed) := by
  rw [sequentialEvaluator, localEvaluator_eq alphabet hne terms support f hf]
  rfl

theorem sequentialEvaluator_step (alphabet : List W) (hne : alphabet ≠ [])
    (terms : List J) (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W)
    (n : ℕ) (fixed : List W) :
    sequentialEvaluator alphabet terms support f offset default (n + 1) fixed =
      mean alphabet (fun w =>
        sequentialEvaluator alphabet terms support f offset default n (w :: fixed)) := by
  simp only [sequentialEvaluator]
  simp_rw [localEvaluator_eq alphabet hne terms support f hf]
  simp only [List.range'_succ, wordExpectation, decode, List.length_cons]

/-- Exact equality of the fast local evaluator and the original conditional
mean on lists of word choices. -/
theorem sequentialEvaluator_eq (alphabet : List W) (hne : alphabet ≠ [])
    (terms : List J) (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W)
    (n : ℕ) (fixed : List W) :
    sequentialEvaluator alphabet terms support f offset default n fixed =
      conditionalMean alphabet (fun xs => objective terms f offset (decode default xs)) n fixed := by
  apply evaluator_eq_conditionalMean
  · exact sequentialEvaluator_zero alphabet hne terms support f hf offset default
  · exact sequentialEvaluator_step alphabet hne terms support f hf offset default

/-- Actual sequential search using only the local evaluator. -/
def localAssign (a : W) (tail : List W) (terms : List J)
    (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ) (offset : ℚ)
    (default : W) (n : ℕ) : List W :=
  assignWithEvaluator a tail
    (sequentialEvaluator (a :: tail) terms support f offset default) n []

theorem localAssign_le_initial (a : W) (tail : List W) (terms : List J)
    (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W) (n : ℕ) :
    objective terms f offset (decode default (localAssign a tail terms support f offset default n)) ≤
      sequentialEvaluator (a :: tail) terms support f offset default n [] := by
  exact assignWithEvaluator_le a tail
    (fun xs => objective terms f offset (decode default xs))
    (sequentialEvaluator (a :: tail) terms support f offset default)
    (sequentialEvaluator_zero _ (List.cons_ne_nil _ _) terms support f hf offset default)
    (sequentialEvaluator_step _ (List.cons_ne_nil _ _) terms support f hf offset default) n []

end Sequential

section Reindex

/-- Numbering through an explicit enumeration, using the supplied decidable
equality uniformly across generic and concrete index types. -/
def indexCode (indices : List I) (i : I) : ℕ := indices.idxOf i

/-- Pull a local term back to numbered coordinates. -/
def reindexTerm (code : I → ℕ) (f : (I → W) → ℚ) (ξ : ℕ → W) : ℚ :=
  f (fun i => ξ (code i))

omit [DecidableEq I] in
theorem reindexTerm_dependsOn (code : I → ℕ) (support : Finset I)
    (f : (I → W) → ℚ) (hf : DependsOn support f) :
    DependsOn (support.image code) (reindexTerm code f) := by
  intro ξ ξ' h
  apply hf
  intro i hi
  exact h _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

theorem wordExpectation_reindex (alphabet : List W) (code : I → ℕ)
    (hcode : Function.Injective code) (f : (I → W) → ℚ)
    (remaining : List I) (ξ : ℕ → W) :
    wordExpectation alphabet (reindexTerm code f) (remaining.map code) ξ =
      wordExpectation alphabet f remaining (fun i => ξ (code i)) := by
  induction remaining generalizing ξ with
  | nil => rfl
  | cons i remaining ih =>
      simp only [List.map_cons, wordExpectation]
      apply congrArg (mean alphabet)
      funext w
      rw [ih]
      congr 1
      funext j
      by_cases hji : j = i
      · subst j; simp
      · have hc : code j ≠ code i := fun h => hji (hcode h)
        simp [Function.update_of_ne hji, Function.update_of_ne hc]

theorem idxOf_injective (indices : List I) (hcomplete : ∀ i, i ∈ indices) :
    Function.Injective (fun i => indexCode indices i) := by
  intro i j h
  exact (List.idxOf_inj (hcomplete i)).mp h

theorem map_idxOf_eq_range (indices : List I) (hn : indices.Nodup) :
    indices.map (fun i => indexCode indices i) = List.range indices.length := by
  apply List.ext_getElem
  · simp
  · intro n hn₁ hn₂
    simp only [List.getElem_map, List.getElem_range]
    exact hn.idxOf_getElem n (by simpa using hn₁)

/-- Explicit `idxOf` numbering preserves the initial conditional mean. -/
theorem initialEvaluator_reindex_eq (alphabet : List W) (ha : alphabet ≠ [])
    (terms : List J) (support : J → Finset I) (f : J → (I → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W)
    (indices : List I) (hn : indices.Nodup) (hc : ∀ i, i ∈ indices) :
    sequentialEvaluator alphabet terms
      (fun j => (support j).image (fun i => indexCode indices i))
      (fun j => reindexTerm (fun i => indexCode indices i) (f j)) offset default
      indices.length [] =
    wordExpectation alphabet (objective terms f offset) indices (fun _ => default) := by
  unfold sequentialEvaluator
  rw [localEvaluator_eq alphabet ha _ _ _
    (fun j => reindexTerm_dependsOn _ _ _ (hf j))]
  change wordExpectation alphabet
    (reindexTerm (fun i => indexCode indices i) (objective terms f offset))
      (List.range' 0 indices.length) (fun _ => default) = _
  rw [← List.range_eq_range', ← map_idxOf_eq_range indices hn,
    wordExpectation_reindex alphabet _ (idxOf_injective indices hc)]

/-- Full explicit enumerations turn the initial local evaluator into the
ordinary uniform mean on all independent word assignments. -/
theorem initialEvaluator_reindex_uniform [Fintype I] [Fintype W]
    [DecidableEq W] [Nonempty W]
    (alphabet : List W) (ha : alphabet ≠ []) (haNodup : alphabet.Nodup)
    (haFull : ∀ w, w ∈ alphabet)
    (terms : List J) (support : J → Finset I) (f : J → (I → W) → ℚ)
    (hf : ∀ j, DependsOn (support j) (f j)) (offset : ℚ) (default : W)
    (indices : List I) (hn : indices.Nodup) (hc : ∀ i, i ∈ indices) :
    sequentialEvaluator alphabet terms
      (fun j => (support j).image (fun i => indexCode indices i))
      (fun j => reindexTerm (fun i => indexCode indices i) (f j)) offset default
      indices.length [] =
    SubexponentialSAT.Variance.mean SubexponentialSAT.Variance.uniformWeight (objective terms f offset) := by
  rw [initialEvaluator_reindex_eq alphabet ha terms support f hf offset default indices hn hc]
  exact SubexponentialSAT.TypeDistribution.recursive_word_mean_eq_uniform alphabet haNodup haFull
    (objective terms f offset) (wordExpectation alphabet (objective terms f offset))
    (fun _ => rfl) (fun _ _ _ => rfl) indices hc _

end Reindex

section SearchCost

/-- Instrumented finite search with a cost returned by each score evaluation.
Each comparison evaluates the two compared scores exactly once. -/
def chooseWithCost (score : W → ℚ × ℕ) (a : W) : List W → W × ℕ
  | [] => (a, 0)
  | b :: bs =>
      let c := chooseWithCost score b bs
      let left := score a
      let right := score c.1
      (if left.1 ≤ right.1 then a else c.1, c.2 + left.2 + right.2)

theorem chooseWithCost_value (score : W → ℚ × ℕ) (a : W) (tail : List W) :
    (chooseWithCost score a tail).1 = chooseMin (fun w => (score w).1) a tail := by
  induction tail generalizing a with
  | nil => rfl
  | cons b bs ih => simp [chooseWithCost, chooseMin, ih]

theorem chooseWithCost_calls_le (score : W → ℚ × ℕ) (a : W) (tail : List W)
    (B : ℕ) (hB : ∀ w, (score w).2 ≤ B) :
    (chooseWithCost score a tail).2 ≤ 2 * tail.length * B := by
  induction tail generalizing a with
  | nil => simp [chooseWithCost]
  | cons b bs ih =>
      change (chooseWithCost score b bs).2 + (score a).2 +
        (score (chooseWithCost score b bs).1).2 ≤ 2 * (bs.length + 1) * B
      calc
        _ ≤ 2 * bs.length * B + B + B :=
          Nat.add_le_add (Nat.add_le_add (ih b) (hB a)) (hB _)
        _ = _ := by ring

/-- Sequential assignment with the evaluator's terminal-call counts composed. -/
def assignWithCost (a : W) (tail : List W)
    (evaluate : ℕ → List W → ℚ × ℕ) : ℕ → List W → List W × ℕ
  | 0, fixed => (fixed, 0)
  | n + 1, fixed =>
      let next := chooseWithCost (fun w => evaluate n (w :: fixed)) a tail
      let result := assignWithCost a tail evaluate n (next.1 :: fixed)
      (result.1, next.2 + result.2)

theorem assignWithCost_value (a : W) (tail : List W)
    (evaluate : ℕ → List W → ℚ × ℕ) (n : ℕ) (fixed : List W) :
    (assignWithCost a tail evaluate n fixed).1 =
      assignWithEvaluator a tail (fun n xs => (evaluate n xs).1) n fixed := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih => simp [assignWithCost, assignWithEvaluator, ih, chooseWithCost_value]

theorem assignWithCost_calls_le (a : W) (tail : List W)
    (evaluate : ℕ → List W → ℚ × ℕ) (B : ℕ)
    (hB : ∀ n fixed, (evaluate n fixed).2 ≤ B) (n : ℕ) (fixed : List W) :
    (assignWithCost a tail evaluate n fixed).2 ≤ n * (2 * tail.length * B) := by
  induction n generalizing fixed with
  | zero => simp [assignWithCost]
  | succ n ih =>
      change (chooseWithCost (fun w => evaluate n (w :: fixed)) a tail).2 +
        (assignWithCost a tail evaluate n
          ((chooseWithCost (fun w => evaluate n (w :: fixed)) a tail).1 :: fixed)).2 ≤
        (n + 1) * (2 * tail.length * B)
      calc
        _ ≤ 2 * tail.length * B + n * (2 * tail.length * B) :=
          Nat.add_le_add (chooseWithCost_calls_le _ a tail B (fun w => hB n (w :: fixed))) (ih _)
        _ = _ := by ring

def sequentialEvaluatorCounted (alphabet : List W) (terms : List J)
    (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ) (offset : ℚ)
    (default : W) (n : ℕ) (fixed : List W) : ℚ × ℕ :=
  localEvaluatorCounted alphabet terms support f offset
    (List.range' fixed.length n) (decode default fixed)

theorem sequentialEvaluatorCounted_value (alphabet : List W) (terms : List J)
    (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ) (offset : ℚ)
    (default : W) (n : ℕ) (fixed : List W) :
    (sequentialEvaluatorCounted alphabet terms support f offset default n fixed).1 =
      sequentialEvaluator alphabet terms support f offset default n fixed :=
  localEvaluatorCounted_value _ _ _ _ _ _ _

theorem sequentialEvaluatorCounted_calls_le (alphabet : List W) (ha : alphabet ≠ [])
    (terms : List J) (support : J → Finset ℕ) (f : J → (ℕ → W) → ℚ) (offset : ℚ)
    (default : W) (n : ℕ) (fixed : List W) (s : ℕ) (hs : ∀ j, (support j).card ≤ s) :
    (sequentialEvaluatorCounted alphabet terms support f offset default n fixed).2 ≤
      terms.length * alphabet.length ^ s :=
  localEvaluatorCounted_calls_le alphabet ha terms support f offset _
    (List.nodup_range') _ s hs

end SearchCost

section PairObjective

open SubexponentialSAT.Types SubexponentialSAT.TypeDistribution SubexponentialSAT.SlotAssignment

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {Q Δ : ℕ} (slots : SlotMap P Δ)

private theorem sum_enumeration {K : Type*} [DecidableEq K] [Fintype K]
    (xs : List K) (hn : xs.Nodup) (hc : ∀ x, x ∈ xs) (f : K → ℚ) :
    (xs.map f).sum = ∑ x, f x := by
  rw [← List.sum_toFinset f hn]
  have h : xs.toFinset = Finset.univ := by ext x; simp [hc x]
  rw [h]

private theorem sum_product {A B : Type*} (xs : List A) (ys : List B)
    (f : A × B → ℚ) :
    ((xs.product ys).map f).sum =
      (xs.map (fun x => (ys.map (fun y => f (x, y))).sum)).sum := by
  induction xs with
  | nil => simp [List.product]
  | cons x xs ih =>
      change (List.map f ((ys.map (fun y => (x, y))) ++ xs.product ys)).sum = _
      simp [List.map_map, Function.comp_def, ih]

private theorem list_product_length {A B : Type*} (xs : List A) (ys : List B) :
    (xs.product ys).length = xs.length * ys.length := List.length_product xs ys

/-- The squared type-count potential from Section 5.4. -/
def pairObjective (ω : Assignment V E Q Δ) : ℚ :=
  ∑ u : UniversalType Q Δ,
    ((SubexponentialSAT.Variance.typeCount (assignmentType P slots) u ω : ℚ) -
      (Fintype.card V : ℚ) / (Fintype.card (UniversalType Q Δ) : ℚ)) ^ 2

def pairTerm (pair : V × V) (ω : Assignment V E Q Δ) : ℚ :=
  pairCollision P slots ω pair.1 pair.2

def pairOffset : ℚ :=
  (Fintype.card V : ℚ) ^ 2 / (Fintype.card (UniversalType Q Δ) : ℚ)

omit [Fintype V] in
theorem pairTerm_dependsOn (pair : V × V) :
    DependsOn (pairSupport P slots pair.1 pair.2) (pairTerm (Q := Q) P slots pair) := by
  intro ω ω' h
  exact pairCollision_congr P slots ω ω' pair.1 pair.2 h

omit [DecidableEq E] in
theorem objective_pair_eq (vertices : List V) (hn : vertices.Nodup)
    (hc : ∀ v, v ∈ vertices) (ω : Assignment V E Q Δ) :
    objective (vertices.product vertices) (pairTerm P slots) (pairOffset (V := V) (Q := Q) (Δ := Δ)) ω =
      pairObjective P slots ω := by
  unfold objective pairObjective
  rw [assignment_deviation_eq_collisions]
  unfold pairOffset
  congr 1
  rw [sum_product, sum_enumeration vertices hn hc]
  apply Finset.sum_congr rfl
  intro v _
  exact sum_enumeration vertices hn hc (fun w => pairCollision P slots ω v w)

/-- The actual local-pair evaluator on the manuscript's factor/head/padding
word variables. Only the union of the two read supports is enumerated. -/
def pairEvaluator (alphabet : List (Word Q)) (vertices : List V)
    (remaining : List (SeedIndex V E Δ)) (ω : Assignment V E Q Δ) : ℚ :=
  localEvaluator alphabet (vertices.product vertices)
    (fun pair => pairSupport P slots pair.1 pair.2) (pairTerm P slots)
    (pairOffset (V := V) (Q := Q) (Δ := Δ)) remaining ω

theorem pairEvaluator_eq (alphabet : List (Word Q)) (ha : alphabet ≠ [])
    (vertices : List V) (hn : vertices.Nodup) (hc : ∀ v, v ∈ vertices)
    (remaining : List (SeedIndex V E Δ)) (ω : Assignment V E Q Δ) :
    pairEvaluator P slots alphabet vertices remaining ω =
      wordExpectation alphabet (pairObjective P slots) remaining ω := by
  unfold pairEvaluator
  rw [localEvaluator_eq alphabet ha _ _ _ (pairTerm_dependsOn P slots)]
  have h : objective (vertices.product vertices) (pairTerm (Q := Q) P slots)
      (pairOffset (V := V) (Q := Q) (Δ := Δ)) = pairObjective (Q := Q) P slots := by
    funext η
    exact objective_pair_eq P slots vertices hn hc η
  rw [h]

/-- The evaluator makes at most `D² q^(2(Δ+1))` local collision calls for a
vertex enumeration of length `D`. This bound is uniform over partial assignments. -/
theorem pairEvaluator_calls_le (alphabet : List (Word Q)) (ha : alphabet ≠ [])
    (vertices : List V) (remaining : List (SeedIndex V E Δ)) (hr : remaining.Nodup)
    (ω : Assignment V E Q Δ) :
    (localEvaluatorCounted alphabet (vertices.product vertices)
      (fun pair => pairSupport P slots pair.1 pair.2) (pairTerm P slots)
      (pairOffset (V := V) (Q := Q) (Δ := Δ)) remaining ω).2 ≤
      vertices.length ^ 2 * alphabet.length ^ (2 * (Δ + 1)) := by
  simpa only [list_product_length, pow_two] using
    localEvaluatorCounted_calls_le alphabet ha (vertices.product vertices)
      (fun pair => pairSupport P slots pair.1 pair.2) (pairTerm P slots)
      (pairOffset (V := V) (Q := Q) (Δ := Δ)) remaining hr ω (2 * (Δ + 1))
      (fun pair => pairSupport_card_le P slots pair.1 pair.2)

/-- Numbered local support from an explicit list of independent word indices. -/
def numberedPairSupport (indices : List (SeedIndex V E Δ)) (pair : V × V) : Finset ℕ :=
  (pairSupport P slots pair.1 pair.2).image (fun i => indexCode indices i)

def numberedPairTerm (indices : List (SeedIndex V E Δ)) (pair : V × V) :
    (ℕ → Word Q) → ℚ :=
  reindexTerm (fun i => indexCode indices i) (pairTerm P slots pair)

omit [Fintype V] in
theorem numberedPairTerm_dependsOn (indices : List (SeedIndex V E Δ)) (pair : V × V) :
    DependsOn (numberedPairSupport P slots indices pair)
      (numberedPairTerm (Q := Q) P slots indices pair) :=
  reindexTerm_dependsOn _ _ _ (pairTerm_dependsOn P slots pair)

omit [Fintype V] in
theorem numberedPairSupport_card_le (indices : List (SeedIndex V E Δ)) (pair : V × V) :
    (numberedPairSupport P slots indices pair).card ≤ 2 * (Δ + 1) :=
  (Finset.card_image_le).trans (pairSupport_card_le P slots pair.1 pair.2)

/-- A concrete, terminating deterministic word assignment using the efficient
local-pair conditional evaluator at every choice. -/
def computedAssignment (a : Word Q) (tail : List (Word Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) : Assignment V E Q Δ :=
  let values := localAssign a tail (vertices.product vertices)
    (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
    (pairOffset (V := V) (Q := Q) (Δ := Δ)) a indices.length
  fun i => decode a values (indexCode indices i)

theorem computedAssignment_le_initial (a : Word Q) (tail : List (Word Q))
    (vertices : List V) (hn : vertices.Nodup) (hc : ∀ v, v ∈ vertices)
    (indices : List (SeedIndex V E Δ)) :
    pairObjective P slots (computedAssignment P slots a tail vertices indices) ≤
      sequentialEvaluator (a :: tail) (vertices.product vertices)
        (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
        (pairOffset (V := V) (Q := Q) (Δ := Δ)) a indices.length [] := by
  have h := localAssign_le_initial a tail (vertices.product vertices)
    (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
    (numberedPairTerm_dependsOn P slots indices) (pairOffset (V := V) (Q := Q) (Δ := Δ)) a indices.length
  convert h using 1
  symm
  exact objective_pair_eq P slots vertices hn hc _

/-- The executable local-pair construction satisfies the manuscript's
deviation bound. All enumerations are explicit algorithm inputs. -/
theorem computedAssignment_deviation_le (a : Word Q) (tail : List (Word Q))
    (haNodup : (a :: tail).Nodup) (haFull : ∀ w, w ∈ a :: tail)
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (SeedIndex V E Δ)) (hiNodup : indices.Nodup)
    (hiFull : ∀ i, i ∈ indices) {k : ℕ} (hP : P.Bounded k Δ) :
    pairObjective P slots (computedAssignment P slots a tail vertices indices) ≤
      (Fintype.card (UniversalType Q Δ) : ℚ) *
        (1 + (Δ * k : ℕ)) * (Fintype.card V : ℚ) := by
  calc
    _ ≤ sequentialEvaluator (a :: tail) (vertices.product vertices)
        (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
        (pairOffset (V := V) (Q := Q) (Δ := Δ)) a indices.length [] :=
      computedAssignment_le_initial P slots a tail vertices hvNodup hvFull indices
    _ = SubexponentialSAT.Variance.mean SubexponentialSAT.Variance.uniformWeight
        (objective (vertices.product vertices) (pairTerm (Q := Q) P slots)
          (pairOffset (V := V) (Q := Q) (Δ := Δ))) := by
      exact initialEvaluator_reindex_uniform (a :: tail) (List.cons_ne_nil _ _) haNodup haFull
        (vertices.product vertices) (fun pair => pairSupport P slots pair.1 pair.2)
        (pairTerm (Q := Q) P slots) (pairTerm_dependsOn P slots)
        (pairOffset (V := V) (Q := Q) (Δ := Δ)) a indices hiNodup hiFull
    _ = SubexponentialSAT.Variance.mean SubexponentialSAT.Variance.uniformWeight (pairObjective (Q := Q) P slots) := by
      apply congrArg (SubexponentialSAT.Variance.mean SubexponentialSAT.Variance.uniformWeight)
      funext ω
      exact objective_pair_eq P slots vertices hvNodup hvFull ω
    _ ≤ _ := mean_squared_deviation_le P slots hP

/-- A shared factor receives one word at all of its incidences in the computed
assignment, so the derandomization preserves the required slot consistency. -/
theorem computedAssignment_consistent (a : Word Q) (tail : List (Word Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ))
    (v : V) (e : Incident P v) :
    (assignmentType P slots (computedAssignment P slots a tail vertices indices) v).slot
        (slots v e) =
      computedAssignment P slots a tail vertices indices (.inl e.val) := by
  rw [assignmentType_eq_typeFromWords, typeFromWords_incidence]

/-- The same concrete assignment, instrumented to count local collision calls. -/
def computedAssignmentCounted (a : Word Q) (tail : List (Word Q)) (vertices : List V)
    (indices : List (SeedIndex V E Δ)) : Assignment V E Q Δ × ℕ :=
  let result := assignWithCost a tail
    (sequentialEvaluatorCounted (a :: tail) (vertices.product vertices)
      (numberedPairSupport P slots indices) (numberedPairTerm P slots indices)
      (pairOffset (V := V) (Q := Q) (Δ := Δ)) a) indices.length []
  (fun i => decode a result.1 (indexCode indices i), result.2)

theorem computedAssignmentCounted_value (a : Word Q) (tail : List (Word Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) :
    (computedAssignmentCounted P slots a tail vertices indices).1 =
      computedAssignment P slots a tail vertices indices := by
  simp only [computedAssignmentCounted, computedAssignment, localAssign,
    assignWithCost_value, sequentialEvaluatorCounted_value]

/-- Whole-search bound: the actual instrumented program makes at most
`M * 2(q-1) * D² * q^(2(Δ+1))` local collision evaluations. -/
theorem computedAssignmentCounted_calls_le (a : Word Q) (tail : List (Word Q))
    (vertices : List V) (indices : List (SeedIndex V E Δ)) :
    (computedAssignmentCounted P slots a tail vertices indices).2 ≤
      indices.length * (2 * tail.length *
        (vertices.length ^ 2 * (a :: tail).length ^ (2 * (Δ + 1)))) := by
  apply assignWithCost_calls_le
  intro n fixed
  simpa only [list_product_length, pow_two] using
    sequentialEvaluatorCounted_calls_le (a :: tail) (List.cons_ne_nil _ _)
      (vertices.product vertices) (numberedPairSupport P slots indices)
      (numberedPairTerm P slots indices) (pairOffset (V := V) (Q := Q) (Δ := Δ))
      a n fixed (2 * (Δ + 1)) (numberedPairSupport_card_le P slots indices)

private theorem enumeration_length {K : Type*} [DecidableEq K] [Fintype K]
    (xs : List K) (hn : xs.Nodup) (hc : ∀ x, x ∈ xs) : xs.length = Fintype.card K := by
  rw [← List.toFinset_card_of_nodup hn]
  have h : xs.toFinset = Finset.univ := by ext x; simp [hc x]
  rw [h, Finset.card_univ]

/-- The explicit seed representation includes factor words, heads, and all
padding slots. Its length is still linear in the number of chunks. -/
theorem indices_length_le (indices : List (SeedIndex V E Δ))
    (hn : indices.Nodup) (hc : ∀ i, i ∈ indices) {k : ℕ} (hP : P.Bounded k Δ) :
    indices.length ≤ (2 * Δ + 1) * Fintype.card V := by
  rw [enumeration_length indices hn hc]
  simp only [SeedIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h := SubexponentialSAT.Incidence.bounded_card_factors_le P k Δ hP
  nlinarith

/-- A polynomial bound in the input chunk count for the fully instrumented
local-pair search. The leading factor depends only on the fixed alphabet and Δ.
Arithmetic bit costs and list-processing costs are not asserted to be unit cost. -/
theorem computedAssignmentCounted_calls_polynomial (a : Word Q) (tail : List (Word Q))
    (vertices : List V) (hvNodup : vertices.Nodup) (hvFull : ∀ v, v ∈ vertices)
    (indices : List (SeedIndex V E Δ)) (hiNodup : indices.Nodup)
    (hiFull : ∀ i, i ∈ indices) {k : ℕ} (hP : P.Bounded k Δ) :
    (computedAssignmentCounted P slots a tail vertices indices).2 ≤
      ((2 * Δ + 1) * (2 * tail.length) * (a :: tail).length ^ (2 * (Δ + 1))) *
        (Fintype.card V) ^ 3 := by
  calc
    _ ≤ indices.length * (2 * tail.length *
        (vertices.length ^ 2 * (a :: tail).length ^ (2 * (Δ + 1)))) :=
      computedAssignmentCounted_calls_le P slots a tail vertices indices
    _ = indices.length * (2 * tail.length *
        ((Fintype.card V) ^ 2 * (a :: tail).length ^ (2 * (Δ + 1)))) := by
      rw [enumeration_length vertices hvNodup hvFull]
    _ ≤ ((2 * Δ + 1) * Fintype.card V) * (2 * tail.length *
        ((Fintype.card V) ^ 2 * (a :: tail).length ^ (2 * (Δ + 1)))) :=
      Nat.mul_le_mul_right _ (indices_length_le P indices hiNodup hiFull hP)
    _ = _ := by ring

end PairObjective

end SubexponentialSAT.LocalExpectation

end OAI.Algorithms
