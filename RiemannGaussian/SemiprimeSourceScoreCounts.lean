/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedScoreSearch

/-! # Actual integer counts of original source collision terminals
No rational score, count answer or assignment-function oracle is a runtime input.
The integer/control ledger is native; a physical digit interpreter is separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeSourceScoreCounts
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment

/-- Actual original Boolean terminal, with all cached environment reads retained. -/
def hit {r Q : ℕ} (p : ScoreProgram Q) (env : Environment r Q) : Run Bool :=
  match p with
  | .incidence a b c d =>
    let wa := readEnv env a
    let wb := readEnv env b
    let wc := readEnv env c
    let wd := readEnv env d
    let heads := equalCoordinates Q (wordAt wa.value) (wordAt wc.value)
    let slots := equalCoordinates Q (wordAt wb.value) (wordAt wd.value)
    ⟨heads.value && slots.value,wa.work+wb.work+wc.work+wd.work+heads.work+slots.work+4⟩
  | .head t a b =>
    let wa := readEnv env a
    let wb := readEnv env b
    ⟨decide (wordAt wa.value t=wordAt wb.value t),wa.work+wb.work+5⟩

/-- Which of the two original squared scale factors multiplies this instruction. -/
def weight {Q : ℕ} (x y : ℚ) : ScoreProgram Q → ℚ
  | .incidence _ _ _ _ => y*y
  | .head _ _ _ => x*x

/-- Exact native terminal relation, including its actual tests. -/
theorem terminal_count {r Q : ℕ} (x y : ℚ) (p : ScoreProgram Q) (env : Environment r Q) :
    (terminal x y p env).value=weight x y p*(if (hit p env).value then 1 else 0) ∧
    (terminal x y p env).work=(hit p env).work := by
  cases p with
  | incidence a b c d => exact ⟨rfl,rfl⟩
  | head t a b =>
    constructor
    · simp [terminal,hit,weight]
    · rfl

/-- Actual finite integer sum, retaining every producer report. -/
def sumCount {α : Type*} (f : α→Run ℕ) : List α→Run ℕ
  | [] => ⟨0,1⟩
  | a::as => let first:=f a
            let rest:=sumCount f as
            ⟨first.value+rest.value,first.work+rest.work+3⟩

/-- Exact original list order and multiplicity in integer summation. -/
theorem sumCount_value {α : Type*} (f : α→Run ℕ) (xs : List α) :
    (sumCount f xs).value=(xs.map (fun a => (f a).value)).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [sumCount,List.map_cons,List.sum_cons,ih]

/-- Casting this actual finite sum introduces no averaging or missing branch. -/
theorem sumCount_cast {α : Type*} (f : α→Run ℕ) (xs : List α) :
    ((sumCount f xs).value:ℚ)=(xs.map (fun a => ((f a).value:ℚ))).sum := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [sumCount,Nat.cast_add,List.map_cons,List.sum_cons,ih]

/-- Per-leaf bounds accumulate for every actual list prefix. -/
theorem sumCount_le {α : Type*} (f : α→Run ℕ) (xs : List α) (B : ℕ)
    (h : ∀ a∈xs,(f a).value≤ B) : (sumCount f xs).value≤ xs.length*B := by
  induction xs with
  | nil => simp [sumCount]
  | cons a as ih =>
    have ha:=h a List.mem_cons_self
    have ht:=ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [sumCount,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Count TRUE leaves using the SAME ordered local completions and override pushes. -/
def count {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q) :
    List ℕ→Environment r Q→Run ℕ
  | [],env => let out:=hit p env
              ⟨if out.value then 1 else 0,out.work+1⟩
  | i::remaining,env =>
    let out:=sumCount (fun w =>
      let child:=count alphabet p remaining (extend env i w)
      ⟨child.value,child.work+Q+2⟩) alphabet
    ⟨out.value,out.work+alphabet.length+3⟩

/-- Counts never exceed the number of actual leaves, even with repeated words,
repeated overridden IDs, or an empty alphabet. -/
theorem count_le {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) :
    (count alphabet p remaining env).value≤ alphabet.length^remaining.length := by
  induction remaining generalizing env with
  | nil => simp only [count,List.length_nil,pow_zero];split <;> omega
  | cons i remaining ih =>
    have h:=sumCount_le (fun w =>
      let child:=count alphabet p remaining (extend env i w)
      (⟨child.value,child.work+Q+2⟩:Run ℕ)) alphabet (alphabet.length^remaining.length)
      (fun w _ => ih (extend env i w))
    simpa only [count,List.length_cons,pow_succ,Nat.mul_comm] using h

/-- A finite scalar-linear sum identity, valid also at a zero divisor argument. -/
theorem linear_sum {α : Type*} (xs : List α) (f : α→ℚ) (a b : ℚ) :
    (xs.map (fun x => a*f x/b)).sum=a*(xs.map f).sum/b := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih];ring

/-- Exact finite averaging identity for the actual original evaluator.
Zero-length alphabets are covered by the original rational zero-division convention. -/
theorem expectation_count {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q) :
    (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining env).value=
      weight x y p*((count alphabet p remaining env).value:ℚ)/
        (alphabet.length:ℚ)^remaining.length := by
  induction remaining generalizing env with
  | nil =>
    simp only [SemiprimeMaterializedScoreSearch.expectation,count,List.length_nil,pow_zero,div_one]
    rw [(terminal_count x y p env).1]
    split <;> simp
  | cons i remaining ih =>
    have hcast:=sumCount_cast (fun w =>
      let child:=count alphabet p remaining (extend env i w)
      (⟨child.value,child.work+Q+2⟩:Run ℕ)) alphabet
    simp only [SemiprimeMaterializedScoreSearch.expectation,count,sumRun_value,List.length_cons]
    rw [hcast]
    have hm : (alphabet.map (fun w =>
        (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining (extend env i w)).value)).sum=
        weight x y p*((alphabet.map (fun w => ((count alphabet p remaining (extend env i w)).value:ℚ))).sum)/
          (alphabet.length:ℚ)^remaining.length := by
      calc
        _=(alphabet.map (fun w => weight x y p*((count alphabet p remaining (extend env i w)).value:ℚ)/
          (alphabet.length:ℚ)^remaining.length)).sum := by
            congr 1
            exact List.map_congr_left (fun w _ => ih (extend env i w))
        _=_ := linear_sum _ _ _ _
    rw [hm,pow_succ]
    ring

/-- Equal callback work yields equal executed integer and rational sum ledgers. -/
theorem sumCount_work_eq {α : Type*} (f : α→Run ℕ) (g : α→Run ℚ) (xs : List α)
    (h : ∀ a∈xs,(f a).work=(g a).work) : (sumCount f xs).work=(sumRun g xs).work := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [sumCount,sumRun,h a List.mem_cons_self,
      ih (fun a ha => h a (List.mem_cons_of_mem _ ha))]

/-- The actual integer traversal retains the original terminal and branch ledger. -/
theorem count_work_eq {r Q : ℕ} (alphabet : List (Word r Q)) (x y : ℚ)
    (p : ScoreProgram Q) (remaining : List ℕ) (env : Environment r Q) :
    (count alphabet p remaining env).work=
      (SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining env).work := by
  induction remaining generalizing env with
  | nil => simp only [count,SemiprimeMaterializedScoreSearch.expectation,(terminal_count x y p env).2]
  | cons i remaining ih =>
    have hh:=sumCount_work_eq
      (fun w => let child:=count alphabet p remaining (extend env i w)
                (⟨child.value,child.work+Q+2⟩:Run ℕ))
      (fun w => let child:=SemiprimeMaterializedScoreSearch.expectation alphabet x y p remaining (extend env i w)
                (⟨child.value,child.work+Q+2⟩:Run ℚ)) alphabet (fun w _ => by
        change (count alphabet p remaining (extend env i w)).work+Q+2=_
        rw [ih])
    simpa only [count,SemiprimeMaterializedScoreSearch.expectation] using congrArg (fun n => n+alphabet.length+3) hh

/-- Original dimension bounds give a complete native scalar/list traversal budget. -/
theorem count_work {r Q : ℕ} (alphabet : List (Word r Q)) (p : ScoreProgram Q)
    (remaining : List ℕ) (env : Environment r Q) (N s : ℕ)
    (hn : env.fixed.length≤ N) (hs : env.overrides.length+remaining.length≤ s) :
    (count alphabet p remaining env).work≤
      (alphabet.length+1)^(remaining.length+1)*(terminalBudget N s Q+Q+20) := by
  rw [count_work_eq alphabet 0 0 p remaining env]
  exact SemiprimeMaterializedScoreSearch.expectation_work alphabet 0 0 p remaining env N s hn hs

end RiemannGaussian.SemiprimeSourceScoreCounts
