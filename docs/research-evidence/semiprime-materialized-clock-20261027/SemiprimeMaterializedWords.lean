/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFiniteEnumerations

/-! # Explicit local-expectation search with its scalar and list-control trace
This executes every local completion, scalar sum/division, candidate comparison
and sequential assignment. Terminal computations return their own work; this
module does not turn an arbitrary terminal function into a constant-cost oracle.
The trace is a scalar/control trace, with bit refinement stated separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedWords
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation ConditionalExpectation

/-- A produced value and the work of its executed producer. -/
structure Run (A : Type*) where
  /-- Actual output. -/
  value : A
  /-- Executed scalar and finite-list control events. -/
  work : ℕ

/-- Sum actual child results, retaining every callback's work. -/
def sumRun {A : Type*} (f : A → Run ℚ) : List A → Run ℚ
  | [] => ⟨0,1⟩
  | a::as =>
      let x := f a
      let y := sumRun f as
      ⟨x.value+y.value,x.work+y.work+3⟩

theorem sumRun_value {A : Type*} (f : A → Run ℚ) (xs : List A) :
    (sumRun f xs).value=(xs.map (fun a => (f a).value)).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [sumRun,List.map_cons,List.sum_cons,ih]

theorem sumRun_work {A : Type*} (f : A → Run ℚ) (xs : List A) (B : ℕ)
    (hf : ∀ a ∈ xs, (f a).work≤B) :
    (sumRun f xs).work≤xs.length*(B+3)+1 := by
  induction xs with
  | nil => simp [sumRun]
  | cons a as ih =>
      have hx := hf a (by simp)
      have hy := ih (fun b hb => hf b (by simp [hb]))
      simp only [sumRun,List.length_cons]
      nlinarith

/-- Finite averaging over the explicitly named, small support only. -/
def expectation {W : Type*} (alphabet : List W) (f : (ℕ → W) → Run ℚ) :
    List ℕ → (ℕ → W) → Run ℚ
  | [], omega =>
      let x := f omega
      ⟨x.value,x.work+1⟩
  | i::remaining, omega =>
      let x := sumRun (fun a => expectation alphabet f remaining (Function.update omega i a)) alphabet
      ⟨x.value/(alphabet.length : ℚ),x.work+alphabet.length+3⟩

theorem expectation_value {W : Type*} (alphabet : List W) (f : (ℕ → W) → Run ℚ)
    (remaining : List ℕ) (omega : ℕ → W) :
    (expectation alphabet f remaining omega).value=
      wordExpectation alphabet (fun x => (f x).value) remaining omega := by
  induction remaining generalizing omega with
  | nil => rfl
  | cons i remaining ih =>
      simp only [expectation,wordExpectation,mean,sumRun_value]
      congr 2
      apply List.map_congr_left
      intro a _
      exact ih _

/-- A fixed support gives a fixed polynomial in the actual alphabet size.
All internal averages and list traversals are included, not only leaf calls. -/
theorem expectation_work {W : Type*} (alphabet : List W) (f : (ℕ → W) → Run ℚ)
    (B : ℕ) (hf : ∀ omega, (f omega).work≤B) (remaining : List ℕ) (omega : ℕ → W) :
    (expectation alphabet f remaining omega).work≤
      (alphabet.length+1)^(remaining.length+1)*(B+10) := by
  induction remaining generalizing omega with
  | nil =>
      have h := hf omega
      simp only [expectation,List.length_nil,Nat.zero_add,pow_one]
      nlinarith
  | cons i remaining ih =>
      let A := alphabet.length
      let D := (A+1)^(remaining.length+1)*(B+10)
      have hs := sumRun_work
        (fun a => expectation alphabet f remaining (Function.update omega i a)) alphabet D
        (fun a _ => ih _)
      have hp : A+1≤(A+1)^(remaining.length+1) := by
        simpa using Nat.pow_le_pow_right (by omega : 0<A+1) (by omega : 1≤remaining.length+1)
      have hd : 4*A+4≤D := by dsimp [D]; nlinarith
      change (sumRun _ alphabet).work+A+3≤_
      simp only [List.length_cons,pow_succ]
      change (sumRun _ alphabet).work+A+3≤(A+1)^(remaining.length+1)*(A+1)*(B+10)
      dsimp [D] at hs hd
      dsimp [A] at *
      nlinarith

/-- Actual finite index-membership scan. -/
def memberRun (i : ℕ) : List ℕ → Run Bool
  | [] => ⟨false,1⟩
  | j::js =>
      if i=j then ⟨true,2⟩ else
      let rest := memberRun i js
      ⟨rest.value,rest.work+2⟩

theorem memberRun_value (i : ℕ) (xs : List ℕ) : (memberRun i xs).value=decide (i∈xs) := by
  induction xs with
  | nil => simp [memberRun]
  | cons j js ih => by_cases h : i=j <;> simp [memberRun,h,ih]

theorem memberRun_work (i : ℕ) (xs : List ℕ) : (memberRun i xs).work≤2*xs.length+1 := by
  induction xs with
  | nil => simp [memberRun]
  | cons j js ih => by_cases h : i=j <;> simp only [memberRun,h,ite_true,ite_false,List.length_cons] <;> omega

/-- Filter remaining indices using the actual cached support-list scan. -/
def activeRun (support : List ℕ) : List ℕ → Run (List ℕ)
  | [] => ⟨[],1⟩
  | i::remaining =>
      let test := memberRun i support
      let rest := activeRun support remaining
      ⟨if test.value then i::rest.value else rest.value,test.work+rest.work+3⟩

theorem activeRun_value (support remaining : List ℕ) :
    (activeRun support remaining).value=active support.toFinset remaining := by
  induction remaining with
  | nil => rfl
  | cons i remaining ih => simp [activeRun,active,List.filter_cons,memberRun_value,ih]

theorem activeRun_work (support remaining : List ℕ) :
    (activeRun support remaining).work≤remaining.length*(2*support.length+4)+1 := by
  induction remaining with
  | nil => simp [activeRun]
  | cons i remaining ih =>
      have hm := memberRun_work i support
      simp only [activeRun,List.length_cons]
      nlinarith

/-- One actual local expectation, including acquisition of its active support. -/
def localTerm {W : Type*} (alphabet : List W) (support : List ℕ)
    (f : (ℕ → W) → Run ℚ) (remaining : List ℕ) (omega : ℕ → W) : Run ℚ :=
  let selected := activeRun support remaining
  let result := expectation alphabet f selected.value omega
  ⟨result.value,selected.work+result.work+1⟩

theorem localTerm_value {W : Type*} (alphabet : List W) (support : List ℕ)
    (f : (ℕ → W) → Run ℚ) (remaining : List ℕ) (omega : ℕ → W) :
    (localTerm alphabet support f remaining omega).value=
      wordExpectation alphabet (fun x => (f x).value) (active support.toFinset remaining) omega := by
  simp only [localTerm,expectation_value,activeRun_value]

theorem localTerm_work {W : Type*} (alphabet : List W) (support : List ℕ)
    (f : (ℕ → W) → Run ℚ) (B s : ℕ) (hf : ∀ omega, (f omega).work≤B)
    (hs : support.length≤ s) (remaining : List ℕ) (hr : remaining.Nodup) (omega : ℕ → W) :
    (localTerm alphabet support f remaining omega).work≤
      remaining.length*(2*s+4)+(alphabet.length+1)^(s+1)*(B+10)+2 := by
  have ha := activeRun_work support remaining
  have hb := expectation_work alphabet f B hf (activeRun support remaining).value omega
  have hl : (activeRun support remaining).value.length≤ s := by
    rw [activeRun_value]
    exact (active_length_le support.toFinset remaining hr).trans ((List.toFinset_card_le _).trans hs)
  have hp := Nat.pow_le_pow_right (by omega : 0<alphabet.length+1) (Nat.add_le_add_right hl 1)
  have hm := Nat.mul_le_mul_right (B+10) hp
  have hc := Nat.mul_le_mul_left remaining.length (show 2*support.length+4≤2*s+4 by omega)
  change (activeRun support remaining).work+(expectation alphabet f (activeRun support remaining).value omega).work+1≤_
  omega

/-- Actual scalar objective evaluation with all local completion work retained. -/
def evaluate {W J : Type*} (alphabet : List W) (terms : List J)
    (support : J → List ℕ) (f : J → (ℕ → W) → Run ℚ) (offset : ℚ)
    (remaining : List ℕ) (omega : ℕ → W) : Run ℚ :=
  let result := sumRun (fun j => localTerm alphabet (support j) (f j) remaining omega) terms
  ⟨result.value-offset,result.work+2⟩

theorem evaluate_value {W J : Type*} (alphabet : List W) (terms : List J)
    (support : J → List ℕ) (f : J → (ℕ → W) → Run ℚ) (offset : ℚ)
    (remaining : List ℕ) (omega : ℕ → W) :
    (evaluate alphabet terms support f offset remaining omega).value=
      localEvaluator alphabet terms (fun j => (support j).toFinset)
        (fun j x => (f j x).value) offset remaining omega := by
  simp only [evaluate,localEvaluator,sumRun_value,localTerm_value]

theorem evaluate_work {W J : Type*} (alphabet : List W) (terms : List J)
    (support : J → List ℕ) (f : J → (ℕ → W) → Run ℚ) (offset : ℚ)
    (B s : ℕ) (hf : ∀ j omega, (f j omega).work≤B) (hs : ∀ j, (support j).length≤ s)
    (remaining : List ℕ) (hr : remaining.Nodup) (omega : ℕ → W) :
    (evaluate alphabet terms support f offset remaining omega).work≤
      terms.length*(remaining.length*(2*s+4)+(alphabet.length+1)^(s+1)*(B+10)+5)+3 := by
  have h := sumRun_work (fun j => localTerm alphabet (support j) (f j) remaining omega) terms
    (remaining.length*(2*s+4)+(alphabet.length+1)^(s+1)*(B+10)+2)
    (fun j _ => localTerm_work alphabet (support j) (f j) B s (hf j) (hs j) remaining hr omega)
  change (sumRun _ terms).work+2≤_
  nlinarith

/-- Candidate comparison executes both score producers, including comparison control. -/
def choose {W : Type*} (score : W → Run ℚ) (a : W) : List W → Run W
  | [] => ⟨a,1⟩
  | b::bs =>
      let next := choose score b bs
      let left := score a
      let right := score next.value
      ⟨if left.value≤right.value then a else next.value,next.work+left.work+right.work+3⟩

theorem choose_value {W : Type*} (score : W → Run ℚ) (a : W) (tail : List W) :
    (choose score a tail).value=chooseMin (fun w => (score w).value) a tail := by
  induction tail generalizing a with
  | nil => rfl
  | cons b bs ih => simp only [choose,chooseMin,ih]

theorem choose_work {W : Type*} (score : W → Run ℚ) (a : W) (tail : List W)
    (B : ℕ) (hf : ∀ w, (score w).work≤B) :
    (choose score a tail).work≤tail.length*(2*B+3)+1 := by
  induction tail generalizing a with
  | nil => simp [choose]
  | cons b bs ih =>
      have ht := ih b
      have hl := hf a
      have hr := hf (choose score b bs).value
      simp only [choose,List.length_cons]
      nlinarith

/-- All candidate evaluations and actual sequential updates are performed. -/
def assign {W : Type*} (a : W) (tail : List W)
    (evaluator : ℕ → List W → Run ℚ) : ℕ → List W → Run (List W)
  | 0, fixed => ⟨fixed,1⟩
  | n+1, fixed =>
      let next := choose (fun w => evaluator n (w::fixed)) a tail
      let rest := assign a tail evaluator n (next.value::fixed)
      ⟨rest.value,next.work+rest.work+3⟩

theorem assign_value {W : Type*} (a : W) (tail : List W)
    (evaluator : ℕ → List W → Run ℚ) (n : ℕ) (fixed : List W) :
    (assign a tail evaluator n fixed).value=
      assignWithEvaluator a tail (fun n xs => (evaluator n xs).value) n fixed := by
  induction n generalizing fixed with
  | zero => rfl
  | succ n ih => simp only [assign,assignWithEvaluator,ih,choose_value]

/-- The evaluator bound is needed only on physically reachable list lengths. -/
theorem assign_work {W : Type*} (a : W) (tail : List W)
    (evaluator : ℕ → List W → Run ℚ) (B N : ℕ)
    (he : ∀ n fixed, n+fixed.length≤N → (evaluator n fixed).work≤B)
    (n : ℕ) (fixed : List W) (hlen : n+fixed.length≤N) :
    (assign a tail evaluator n fixed).work≤n*(tail.length*(2*B+3)+4)+1 := by
  induction n generalizing fixed with
  | zero => simp [assign]
  | succ n ih =>
      have hn : ∀ w, (evaluator n (w::fixed)).work≤B := by
        intro w
        apply he
        simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hlen
      have hc := choose_work (fun w => evaluator n (w::fixed)) a tail B hn
      have ht := ih ((choose (fun w => evaluator n (w::fixed)) a tail).value::fixed) (by simp only [List.length_cons]; omega)
      change (choose _ a tail).work+(assign a tail evaluator n _).work+3≤_
      nlinarith

/-- Actual numbered local evaluator, with range/list-length construction included. -/
def sequential {W J : Type*} (alphabet : List W) (terms : List J)
    (support : J → List ℕ) (f : J → (ℕ → W) → Run ℚ) (offset : ℚ)
    (default : W) (n : ℕ) (fixed : List W) : Run ℚ :=
  let result := evaluate alphabet terms support f offset
    (List.range' fixed.length n) (decode default fixed)
  ⟨result.value,result.work+fixed.length+n+2⟩

theorem sequential_value {W J : Type*} (alphabet : List W) (terms : List J)
    (support : J → List ℕ) (f : J → (ℕ → W) → Run ℚ) (offset : ℚ)
    (default : W) (n : ℕ) (fixed : List W) :
    (sequential alphabet terms support f offset default n fixed).value=
      sequentialEvaluator alphabet terms (fun j => (support j).toFinset)
        (fun j x => (f j x).value) offset default n fixed := by
  exact evaluate_value alphabet terms support f offset _ _

/-- Public uniform evaluator envelope on all reachable input-list lengths. -/
def evaluatorBudget (A T N B s : ℕ) : ℕ :=
  T*(N*(2*s+4)+(A+1)^(s+1)*(B+10)+5)+N+5

theorem sequential_work {W J : Type*} (alphabet : List W) (terms : List J)
    (support : J → List ℕ) (f : J → (ℕ → W) → Run ℚ) (offset : ℚ)
    (B s N : ℕ) (hf : ∀ j omega, (f j omega).work≤B) (hs : ∀ j, (support j).length≤ s)
    (default : W) (n : ℕ) (fixed : List W) (hlen : n+fixed.length≤N) :
    (sequential alphabet terms support f offset default n fixed).work≤
      evaluatorBudget alphabet.length terms.length N B s := by
  have h := evaluate_work alphabet terms support f offset B s hf hs
    (List.range' fixed.length n) (List.nodup_range') (decode default fixed)
  simp only [List.length_range'] at h
  have hn : n≤N := by omega
  have hc := Nat.mul_le_mul_left terms.length
    (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.mul_le_mul_right (2*s+4) hn) ((alphabet.length+1)^(s+1)*(B+10))) 5)
  change (evaluate _ _ _ _ _ _ _).work+fixed.length+n+2≤_
  unfold evaluatorBudget
  omega

/-- Complete actual search from the empty prefix. All terminal computations
and internal averages/comparisons are executed; no optimum is supplied. -/
def search {W J : Type*} (a : W) (tail : List W) (terms : List J)
    (support : J → List ℕ) (f : J → (ℕ → W) → Run ℚ) (offset : ℚ) (N : ℕ) :
    Run (List W) := assign a tail (sequential (a::tail) terms support f offset a) N []

theorem search_value {W J : Type*} (a : W) (tail : List W) (terms : List J)
    (support : J → List ℕ) (f : J → (ℕ → W) → Run ℚ) (offset : ℚ) (N : ℕ) :
    (search a tail terms support f offset N).value=
      localAssign a tail terms (fun j => (support j).toFinset)
        (fun j x => (f j x).value) offset a N := by
  simp only [search,assign_value,localAssign,sequential_value]

/-- Whole executed search, not only its number of terminal calls. The supplied
B is the actual terminal producer budget; it is not silently set to one. -/
theorem search_work {W J : Type*} (a : W) (tail : List W) (terms : List J)
    (support : J → List ℕ) (f : J → (ℕ → W) → Run ℚ) (offset : ℚ)
    (B s N : ℕ) (hf : ∀ j omega, (f j omega).work≤B) (hs : ∀ j, (support j).length≤ s) :
    (search a tail terms support f offset N).work≤
      N*(tail.length*(2*evaluatorBudget (a::tail).length terms.length N B s+3)+4)+1 :=
  assign_work a tail (sequential (a::tail) terms support f offset a)
    (evaluatorBudget (a::tail).length terms.length N B s) N
    (fun n fixed hn => sequential_work (a::tail) terms support f offset B s N hf hs a n fixed hn)
    N [] (by simp)

end RiemannGaussian.SemiprimeMaterializedWords
