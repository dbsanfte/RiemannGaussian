import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Finite conditional expectation by executable sequential search

An alphabet is given as an explicit nonempty list. With a duplicate-free list,
the averages below are uniform averages on words over that alphabet. No choice
oracle is used: `chooseMin` and `assign` are recursive finite algorithms.
-/

namespace SubexponentialSAT.ConditionalExpectation

open scoped BigOperators

variable {α : Type*}

/-- The arithmetic mean of a score on an explicitly enumerated alphabet. -/
def mean (alphabet : List α) (score : α → ℚ) : ℚ :=
  (alphabet.map score).sum / (alphabet.length : ℚ)

/-- Deterministic finite search; ties favor the first candidate. -/
def chooseMin (score : α → ℚ) (a : α) : List α → α
  | [] => a
  | b :: bs =>
      let c := chooseMin score b bs
      if score a ≤ score c then a else c

theorem chooseMin_mem (score : α → ℚ) (a : α) (tail : List α) :
    chooseMin score a tail ∈ a :: tail := by
  induction tail generalizing a with
  | nil => simp [chooseMin]
  | cons b bs ih =>
      simp only [chooseMin]
      split_ifs with h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih b)

theorem chooseMin_le (score : α → ℚ) (a : α) (tail : List α) :
    ∀ x ∈ a :: tail, score (chooseMin score a tail) ≤ score x := by
  induction tail generalizing a with
  | nil => simp [chooseMin]
  | cons b bs ih =>
      intro x hx
      simp only [chooseMin]
      split_ifs with h
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact h.trans (ih b x hx)
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact le_of_lt (lt_of_not_ge h)
        · exact ih b x hx

theorem le_mean (alphabet : List α) (score : α → ℚ)
    (hne : alphabet ≠ []) (r : ℚ) (h : ∀ x ∈ alphabet, r ≤ score x) :
    r ≤ mean alphabet score := by
  have hsum : (alphabet.length : ℚ) * r ≤ (alphabet.map score).sum := by
    clear hne
    revert h
    induction alphabet with
    | nil => intro h; simp
    | cons a as ih =>
        intro h
        have ha : r ≤ score a := h a List.mem_cons_self
        have ht : ∀ x ∈ as, r ≤ score x := fun x hx => h x (List.mem_cons_of_mem a hx)
        have hi := ih ht
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons,
          List.sum_cons]
        nlinarith
  have hpos : (0 : ℚ) < alphabet.length := by
    exact_mod_cast List.length_pos_iff.mpr hne
  exact (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hsum)

theorem chooseMin_le_mean (score : α → ℚ) (a : α) (tail : List α) :
    score (chooseMin score a tail) ≤ mean (a :: tail) score :=
  le_mean (a :: tail) score (List.cons_ne_nil _ _)
    (score (chooseMin score a tail)) (chooseMin_le score a tail)

/-- The abstract finite-uniform interface. The proof applies the same finite
search to an enumeration; executable users can supply that enumeration directly
to `chooseMin`. -/
theorem exists_le_uniform_mean [Fintype α] [Nonempty α] (score : α → ℚ) :
    ∃ x, score x ≤ (∑ y, score y) / (Fintype.card α : ℚ) := by
  classical
  obtain ⟨a, tail, h⟩ := List.exists_cons_of_ne_nil
    ((Finset.univ_nonempty : (Finset.univ : Finset α).Nonempty).toList_ne_nil)
  have hmean : mean (a :: tail) score =
      (∑ y, score y) / (Fintype.card α : ℚ) := by
    rw [← h]
    simp [mean]
  exact ⟨chooseMin score a tail, hmean ▸ chooseMin_le_mean score a tail⟩

theorem exists_le_of_uniform_mean_le [Fintype α] [Nonempty α]
    (score : α → ℚ) (bound : ℚ)
    (h : (∑ y, score y) / (Fintype.card α : ℚ) ≤ bound) :
    ∃ x, score x ≤ bound := by
  obtain ⟨x, hx⟩ := exists_le_uniform_mean score
  exact ⟨x, hx.trans h⟩

/-- Conditional uniform mean over all assignments of the remaining variables.
The list `fixed` records coordinates already fixed, in reverse order. -/
def conditionalMean (alphabet : List α) (objective : List α → ℚ) :
    ℕ → List α → ℚ
  | 0, fixed => objective fixed
  | n + 1, fixed =>
      mean alphabet (fun a => conditionalMean alphabet objective n (a :: fixed))

/-- Fix one coordinate at a time by minimizing its exact conditional mean. -/
def assign (a : α) (tail : List α) (objective : List α → ℚ) :
    ℕ → List α → List α
  | 0, fixed => fixed
  | n + 1, fixed =>
      let next := chooseMin
        (fun x => conditionalMean (a :: tail) objective n (x :: fixed)) a tail
      assign a tail objective n (next :: fixed)

/-- The same executable search accepts a separately implemented conditional
mean evaluator. Its computation cost is not hidden in the correctness theorem. -/
def assignWithEvaluator (a : α) (tail : List α)
    (evaluate : ℕ → List α → ℚ) : ℕ → List α → List α
  | 0, fixed => fixed
  | n + 1, fixed =>
      let next := chooseMin (fun x => evaluate n (x :: fixed)) a tail
      assignWithEvaluator a tail evaluate n (next :: fixed)

/-- Terminal evaluation and the finite averaging identity independently
characterize the required conditional means. -/
theorem evaluator_eq_conditionalMean (alphabet : List α)
    (objective : List α → ℚ) (evaluate : ℕ → List α → ℚ)
    (hzero : ∀ fixed, evaluate 0 fixed = objective fixed)
    (hstep : ∀ n fixed, evaluate (n + 1) fixed =
      mean alphabet (fun x => evaluate n (x :: fixed)))
    (n : ℕ) (fixed : List α) :
    evaluate n fixed = conditionalMean alphabet objective n fixed := by
  induction n generalizing fixed with
  | zero => exact hzero fixed
  | succ n ih =>
      rw [hstep, conditionalMean]
      congr 1
      funext x
      exact ih (x :: fixed)

/-- Correctness of the search with a supplied exact evaluator. An efficient
local-probability evaluator may replace exhaustive enumeration once its two
identities below and its separate runtime bounds have been established. -/
theorem assignWithEvaluator_le (a : α) (tail : List α)
    (objective : List α → ℚ) (evaluate : ℕ → List α → ℚ)
    (hzero : ∀ fixed, evaluate 0 fixed = objective fixed)
    (hstep : ∀ n fixed, evaluate (n + 1) fixed =
      mean (a :: tail) (fun x => evaluate n (x :: fixed)))
    (n : ℕ) (fixed : List α) :
    objective (assignWithEvaluator a tail evaluate n fixed) ≤ evaluate n fixed := by
  induction n generalizing fixed with
  | zero => simp [assignWithEvaluator, hzero]
  | succ n ih =>
      rw [assignWithEvaluator, hstep]
      exact (ih _).trans (chooseMin_le_mean _ a tail)

theorem assignWithEvaluator_exhaustive (a : α) (tail : List α)
    (objective : List α → ℚ) (n : ℕ) (fixed : List α) :
    assignWithEvaluator a tail (conditionalMean (a :: tail) objective) n fixed =
      assign a tail objective n fixed := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih => simp only [assignWithEvaluator, assign, ih]

/-- Every step preserves the conditional-expectation upper bound. -/
theorem assign_le_conditionalMean (a : α) (tail : List α)
    (objective : List α → ℚ) (n : ℕ) (fixed : List α) :
    objective (assign a tail objective n fixed) ≤
      conditionalMean (a :: tail) objective n fixed := by
  induction n generalizing fixed with
  | zero => exact le_rfl
  | succ n ih =>
      simp only [assign, conditionalMean]
      exact (ih _).trans (chooseMin_le_mean _ a tail)

theorem assign_length (a : α) (tail : List α) (objective : List α → ℚ)
    (n : ℕ) (fixed : List α) :
    (assign a tail objective n fixed).length = n + fixed.length := by
  induction n generalizing fixed with
  | zero => simp [assign]
  | succ n ih => simp only [assign, ih, List.length_cons]; omega

/-- All newly selected coordinates belong to the supplied alphabet. -/
theorem assign_mem (a : α) (tail : List α) (objective : List α → ℚ)
    (n : ℕ) (fixed : List α) (hprefix : ∀ x ∈ fixed, x ∈ a :: tail) :
    ∀ x ∈ assign a tail objective n fixed, x ∈ a :: tail := by
  induction n generalizing fixed with
  | zero => exact hprefix
  | succ n ih =>
      simp only [assign]
      apply ih
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact chooseMin_mem _ a tail
      · exact hprefix x hx

/-- Explicit exhaustive enumeration of completions. Prefixes are stored in
reverse coordinate order, consistently with `assign`. -/
def completions (alphabet : List α) : ℕ → List α → List (List α)
  | 0, fixed => [fixed]
  | n + 1, fixed => alphabet.flatMap (fun a => completions alphabet n (a :: fixed))

/-- The returned assignment extends precisely the coordinates already fixed. -/
theorem assign_mem_completions (a : α) (tail : List α)
    (objective : List α → ℚ) (n : ℕ) (fixed : List α) :
    assign a tail objective n fixed ∈ completions (a :: tail) n fixed := by
  induction n generalizing fixed with
  | zero => simp [assign, completions]
  | succ n ih =>
      simp only [assign, completions, List.mem_flatMap]
      exact ⟨_, chooseMin_mem _ a tail, ih _⟩

private theorem length_flatMap_const {β : Type*} (xs : List β)
    (f : β → List α) (m : ℕ) (h : ∀ x, (f x).length = m) :
    (xs.flatMap f).length = xs.length * m := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, h, ih, Nat.add_mul, Nat.add_comm]

theorem completions_length (alphabet : List α) (n : ℕ) (fixed : List α) :
    (completions alphabet n fixed).length = alphabet.length ^ n := by
  induction n generalizing fixed with
  | zero => simp [completions]
  | succ n ih =>
      rw [completions, length_flatMap_const _ _ _ (fun x => ih (x :: fixed))]
      simp [pow_succ, Nat.mul_comm]

private theorem sum_map_flatMap {β : Type*} (xs : List β)
    (f : β → List α) (g : α → ℚ) :
    ((xs.flatMap f).map g).sum = (xs.map (fun x => ((f x).map g).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, ih]

private theorem sum_map_div {β : Type*} (xs : List β) (f : β → ℚ) (d : ℚ) :
    (xs.map (fun x => f x / d)).sum = (xs.map f).sum / d := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, add_div]

/-- The recursive conditional mean is the ordinary finite average over all
complete assignments extending the fixed coordinates. -/
theorem conditionalMean_eq_mean_completions (alphabet : List α)
    (objective : List α → ℚ) (n : ℕ) (fixed : List α) :
    conditionalMean alphabet objective n fixed =
      mean (completions alphabet n fixed) objective := by
  induction n generalizing fixed with
  | zero => simp [conditionalMean, completions, mean]
  | succ n ih =>
      simp only [conditionalMean]
      simp_rw [ih]
      simp only [mean, completions_length, Nat.cast_pow]
      rw [sum_map_div]
      rw [completions, sum_map_flatMap]
      simp [pow_succ, div_div, mul_comm]

/-- An instrumented evaluator recording calls to the complete-assignment
objective. This deliberately exposes the cost of exhaustive evaluation. -/
def conditionalMeanCounted (alphabet : List α) (objective : List α → ℚ) :
    ℕ → List α → ℚ × ℕ
  | 0, fixed => (objective fixed, 1)
  | n + 1, fixed =>
      let children := alphabet.map
        (fun a => conditionalMeanCounted alphabet objective n (a :: fixed))
      ((children.map Prod.fst).sum / (alphabet.length : ℚ),
        (children.map Prod.snd).sum)

theorem conditionalMeanCounted_value (alphabet : List α)
    (objective : List α → ℚ) (n : ℕ) (fixed : List α) :
    (conditionalMeanCounted alphabet objective n fixed).1 =
      conditionalMean alphabet objective n fixed := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih =>
      simp [conditionalMeanCounted, conditionalMean, mean, List.map_map, ih,
        Function.comp_def]

/-- Exactly `q^n` complete-assignment evaluations for `n` remaining variables
over an alphabet of size `q`. This is not a polynomial-time evaluator. -/
theorem conditionalMeanCounted_evaluations (alphabet : List α)
    (objective : List α → ℚ) (n : ℕ) (fixed : List α) :
    (conditionalMeanCounted alphabet objective n fixed).2 = alphabet.length ^ n := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih =>
      simp [conditionalMeanCounted, List.map_map, ih, Function.comp_def,
        pow_succ, Nat.mul_comm]

/-- Deterministic derandomization from any established bound on the initial
uniform average. This supplies both an explicit witness and its guarantee. -/
theorem assign_le_initial_mean (a : α) (tail : List α)
    (objective : List α → ℚ) (n : ℕ) :
    objective (assign a tail objective n []) ≤
      mean (completions (a :: tail) n []) objective := by
  rw [← conditionalMean_eq_mean_completions]
  exact assign_le_conditionalMean a tail objective n []

theorem assign_le_of_initial_mean_le (a : α) (tail : List α)
    (objective : List α → ℚ) (n : ℕ) (bound : ℚ)
    (h : mean (completions (a :: tail) n []) objective ≤ bound) :
    objective (assign a tail objective n []) ≤ bound :=
  (assign_le_initial_mean a tail objective n).trans h

/-- Instrumented minimum search. Its second component counts exactly one for
each rational comparison; evaluating a score is a separate cost. -/
def chooseMinCounted (score : α → ℚ) (a : α) : List α → α × ℕ
  | [] => (a, 0)
  | b :: bs =>
      let c := chooseMinCounted score b bs
      (if score a ≤ score c.1 then a else c.1, c.2 + 1)

theorem chooseMinCounted_value (score : α → ℚ) (a : α) (tail : List α) :
    (chooseMinCounted score a tail).1 = chooseMin score a tail := by
  induction tail generalizing a with
  | nil => rfl
  | cons b bs ih => simp [chooseMinCounted, chooseMin, ih]

theorem chooseMinCounted_comparisons (score : α → ℚ) (a : α) (tail : List α) :
    (chooseMinCounted score a tail).2 = tail.length := by
  induction tail generalizing a with
  | nil => rfl
  | cons b bs ih => simp [chooseMinCounted, ih]

/-- Instrumented sequential assignment. This measures rational comparisons,
not the bit cost of computing the conditional means supplied to the search. -/
def assignCounted (a : α) (tail : List α) (objective : List α → ℚ) :
    ℕ → List α → List α × ℕ
  | 0, fixed => (fixed, 0)
  | n + 1, fixed =>
      let next := chooseMinCounted
        (fun x => conditionalMean (a :: tail) objective n (x :: fixed)) a tail
      let result := assignCounted a tail objective n (next.1 :: fixed)
      (result.1, next.2 + result.2)

theorem assignCounted_value (a : α) (tail : List α) (objective : List α → ℚ)
    (n : ℕ) (fixed : List α) :
    (assignCounted a tail objective n fixed).1 = assign a tail objective n fixed := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih => simp [assignCounted, assign, ih, chooseMinCounted_value]

theorem assignCounted_comparisons (a : α) (tail : List α) (objective : List α → ℚ)
    (n : ℕ) (fixed : List α) :
    (assignCounted a tail objective n fixed).2 = n * tail.length := by
  induction n generalizing fixed with
  | zero => simp [assignCounted]
  | succ n ih =>
      simp [assignCounted, ih, chooseMinCounted_comparisons, Nat.add_mul, Nat.add_comm]

end SubexponentialSAT.ConditionalExpectation

end OAI.Algorithms
