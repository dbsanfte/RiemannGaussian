/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedWordSearch

/-!
# Cached-word environment and executed original collision scores

No arbitrary assignment function is a runtime terminal input. A reverse-prefix
list and a short override list supply words through actual paid list scans;
word coordinates are then stored/read as arrays. This is a scalar/list-control
ledger; primitive bit/physical address simulation is a distinct refinement.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedScoreEnvironment
open OAI.Algorithms.SubexponentialSAT
open LocalExpectation MulticolorTypes SqrtLog
open SemiprimeMaterializedWords
open SemiprimeMaterializedWordSearch (readRun readRun_value readRun_work)

/-- Word coordinates are concrete cached array entries. -/
structure CachedWord (r Q : ℕ) where
  /-- Actual colour coordinates. -/
  data : Array (Fin r)
  /-- The array's public word dimension. -/
  size_eq : data.size=Q

/-- Materialize all Q coordinates of a supplied actual finite source word. -/
def cacheWord {r Q : ℕ} (w : Word r Q) : CachedWord r Q :=
  ⟨Array.ofFn w,by simp⟩

/-- Literal array-coordinate read, not a functional assignment lookup. -/
def wordAt {r Q : ℕ} (w : CachedWord r Q) (t : Fin Q) : Fin r :=
  w.data[t.val]'(by rw [w.size_eq]; exact t.isLt)

/-- Cached coordinates recover the input word exactly. -/
theorem wordAt_cacheWord {r Q : ℕ} (w : Word r Q) : wordAt (cacheWord w)=w := by
  funext t
  simp [wordAt,cacheWord]

/-- The runtime base prefix and at most a small local override list. -/
structure Environment (r Q : ℕ) where
  /-- Cached fallback source word. -/
  default : CachedWord r Q
  /-- Cached words in the published reverse-prefix order. -/
  fixed : List (CachedWord r Q)
  /-- Newest local override first; collisions correctly replace old values. -/
  overrides : List (ℕ × CachedWord r Q)

/-- Execute a newest-first override scan, then the actual reverse-prefix scan. -/
def readOverrides {r Q : ℕ} (default : CachedWord r Q) (fixed : List (CachedWord r Q))
    (i : ℕ) : List (ℕ × CachedWord r Q) → Run (CachedWord r Q)
  | [] => readRun default fixed i
  | p::ps => if p.1=i then ⟨p.2,2⟩ else
      let rest := readOverrides default fixed i ps
      ⟨rest.value,rest.work+2⟩

/-- Actual environment read including both possible scans. -/
def readEnv {r Q : ℕ} (env : Environment r Q) (i : ℕ) : Run (CachedWord r Q) :=
  readOverrides env.default env.fixed i env.overrides

/-- Semantic interpretation used only by specifications. -/
def denote {r Q : ℕ} (env : Environment r Q) : ℕ → Word r Q :=
  fun i => wordAt (readEnv env i).value

/-- Push a local override, with no functional-update closure. -/
def extend {r Q : ℕ} (env : Environment r Q) (i : ℕ) (w : Word r Q) : Environment r Q :=
  ⟨env.default,env.fixed,(i,cacheWord w)::env.overrides⟩

/-- The actual override scan realizes exactly the source functional update. -/
theorem denote_extend {r Q : ℕ} (env : Environment r Q) (i : ℕ) (w : Word r Q) :
    denote (extend env i w)=Function.update (denote env) i w := by
  funext j
  by_cases h : i=j
  · subst j
    simp [denote,readEnv,readOverrides,extend,wordAt_cacheWord]
  · simp [denote,readEnv,readOverrides,extend,h,Ne.symm h]

/-- Materialize the actual current prefix once before its objective is evaluated. -/
def baseEnvironment {r Q : ℕ} (a : Word r Q) (fixed : List (Word r Q)) : Environment r Q :=
  ⟨cacheWord a,fixed.map cacheWord,[]⟩

/-- Prefix list scans, rather than free functional reads, implement the old decoder. -/
theorem denote_baseEnvironment {r Q : ℕ} (a : Word r Q) (fixed : List (Word r Q)) :
    denote (baseEnvironment a fixed)=decode a fixed := by
  funext i
  simp only [denote,readEnv,baseEnvironment,readOverrides,readRun_value]
  induction fixed with
  | nil => exact wordAt_cacheWord a
  | cons b bs ih =>
    simp only [List.map_cons,decode,List.length_map]
    by_cases h : i=bs.length
    · simp [h,wordAt_cacheWord]
    · simpa only [Function.update_of_ne h,Function.update_of_ne h] using ih

/-- Every reverse-prefix and override scan is paid, without cached-length assumptions. -/
theorem readOverrides_work {r Q : ℕ} (default : CachedWord r Q)
    (fixed : List (CachedWord r Q)) (i : ℕ) (overrides : List (ℕ × CachedWord r Q)) :
    (readOverrides default fixed i overrides).work ≤ 2*overrides.length+3*(fixed.length+1)^2 := by
  induction overrides with
  | nil => simpa only [readOverrides,List.length_nil,Nat.mul_zero,Nat.zero_add] using
      readRun_work default fixed i
  | cons p ps ih =>
    by_cases h : p.1=i <;> simp only [readOverrides,h,ite_true,ite_false,List.length_cons] <;> nlinarith

/-- Exact uniform read budget at a bounded current prefix and local support. -/
theorem readEnv_work {r Q : ℕ} (env : Environment r Q) (N s : ℕ)
    (hn : env.fixed.length≤N) (hs : env.overrides.length≤ s) (i : ℕ) :
    (readEnv env i).work ≤ 2*s+3*(N+1)^2 :=
  (readOverrides_work env.default env.fixed i env.overrides).trans (by gcongr)

/-- Concrete original score instruction, containing only acquired numeric codes. -/
inductive ScoreProgram (Q : ℕ) where
  /-- Collision of the head AND the factor word of two incidences. -/
  | incidence (owner1 factor1 owner2 factor2 : ℕ)
  /-- Collision of two head colours at one actual interpolation coordinate. -/
  | head (t : Fin Q) (owner1 owner2 : ℕ)

/-- The instruction's acquired support, with harmless repeated coordinates retained. -/
def support {Q : ℕ} : ScoreProgram Q → List ℕ
  | .incidence a b c d => [a,b,c,d]
  | .head _ a b => [a,b]

/-- Every original terminal reads at most four assignment words. -/
theorem support_length {Q : ℕ} (p : ScoreProgram Q) : (support p).length≤4 := by
  cases p <;> simp [support]

/-- Compare Q concrete cached colour coordinates through an actual recursive loop. -/
def equalCoordinates {r : ℕ} : (Q : ℕ) → (Fin Q → Fin r) → (Fin Q → Fin r) → Run Bool
  | 0, _, _ => ⟨true,1⟩
  | Q+1, a, b =>
    let rest := equalCoordinates Q (fun t => a t.succ) (fun t => b t.succ)
    ⟨decide (a 0=b 0) && rest.value,rest.work+4⟩

/-- This loop compares every actual coordinate, including the zero-length case. -/
theorem equalCoordinates_value {r : ℕ} (Q : ℕ) (a b : Fin Q → Fin r) :
    (equalCoordinates Q a b).value=decide (a=b) := by
  induction Q with
  | zero => simp [equalCoordinates,Subsingleton.elim a b]
  | succ Q ih =>
    apply Bool.eq_iff_iff.mpr
    simp only [equalCoordinates,Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro ⟨h0,hs⟩
      funext i
      exact Fin.cases h0 (fun t => congrFun hs t) i
    · intro h
      subst b
      exact ⟨rfl,rfl⟩

/-- Every stored colour read and comparison contributes to the actual loop charge. -/
theorem equalCoordinates_work {r : ℕ} (Q : ℕ) (a b : Fin Q → Fin r) :
    (equalCoordinates Q a b).work=4*Q+1 := by
  induction Q with
  | zero => rfl
  | succ Q ih => simp only [equalCoordinates,ih]; omega

/-- Original terminal score, computed from cached labels and actual list reads. -/
def terminal {r Q : ℕ} (x y : ℚ) (p : ScoreProgram Q) (env : Environment r Q) : Run ℚ :=
  match p with
  | .incidence a b c d =>
    let wa := readEnv env a
    let wb := readEnv env b
    let wc := readEnv env c
    let wd := readEnv env d
    let heads := equalCoordinates Q (wordAt wa.value) (wordAt wc.value)
    let slots := equalCoordinates Q (wordAt wb.value) (wordAt wd.value)
    ⟨y*y*(if heads.value && slots.value then 1 else 0),
      wa.work+wb.work+wc.work+wd.work+heads.work+slots.work+4⟩
  | .head t a b =>
    let wa := readEnv env a
    let wb := readEnv env b
    ⟨x*x*(if wordAt wa.value t=wordAt wb.value t then 1 else 0),wa.work+wb.work+5⟩

/-- Source score semantics on a numbered word assignment. -/
def programValue {r Q : ℕ} (x y : ℚ) (p : ScoreProgram Q) (omega : ℕ → Word r Q) : ℚ :=
  match p with
  | .incidence a b c d => y^2*(if omega a=omega c ∧ omega b=omega d then 1 else 0)
  | .head t a b => x^2*(if omega a t=omega b t then 1 else 0)

/-- There is no terminal-score-answer premise: the executed score is the source expression. -/
theorem terminal_value {r Q : ℕ} (x y : ℚ) (p : ScoreProgram Q) (env : Environment r Q) :
    (terminal x y p env).value=programValue x y p (denote env) := by
  cases p <;> simp only [terminal,programValue,equalCoordinates_value,Bool.and_eq_true,
    decide_eq_true_eq,denote,pow_two] <;> rfl

/-- Uniform polynomial terminal envelope, including functional decoder replacement. -/
def terminalBudget (N s Q : ℕ) : ℕ := 4*(2*s+3*(N+1)^2)+8*Q+10

/-- The source terminal producer is paid, rather than supplied with cost one. -/
theorem terminal_work {r Q : ℕ} (x y : ℚ) (p : ScoreProgram Q) (env : Environment r Q)
    (N s : ℕ) (hn : env.fixed.length≤N) (hs : env.overrides.length≤ s) :
    (terminal x y p env).work≤terminalBudget N s Q := by
  have hr := readEnv_work env N s hn hs
  cases p with
  | incidence a b c d =>
    simp only [terminal,equalCoordinates_work,terminalBudget]
    have ha := hr a
    have hb := hr b
    have hc := hr c
    have hd := hr d
    omega
  | head t a b =>
    simp only [terminal,terminalBudget]
    have ha := hr a
    have hb := hr b
    omega

end RiemannGaussian.SemiprimeMaterializedScoreEnvironment
