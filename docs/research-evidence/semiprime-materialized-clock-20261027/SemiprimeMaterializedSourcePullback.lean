/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourceCache

/-! # Paid original-coordinate assembly from actual packing addresses
Address acquisition is an explicit upstream seam. This run consumes finite
materialized addresses and actual universal source arrays; no row answer occurs.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedSourcePullback
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes Subexp.ConstructivePacking SqrtLog
open SemiprimeMaterializedSourceUniversal SemiprimeJetArray SemiprimeArrayOps
variable {I : Type} [DecidableEq I] {r Q : ℕ}

/-- Materialized original incidence addresses, with literal block IDs and universal words. -/
abbrev Addresses (I : Type*) (r Q : ℕ) := List (I × Option (ℕ × UniversalType r Q 1))

/-- Finite incidence-address scan with no inverse-index or function-table oracle. -/
def address (i : I) : Addresses I r Q → Run (Option (ℕ × UniversalType r Q 1))
  | [] => ⟨none,1⟩
  | (j,a)::as =>
      if i=j then ⟨a,3⟩
      else let tail := address i as; ⟨tail.value,tail.work+3⟩

theorem address_map (i : I) (is : List I) (f : I → Option (ℕ × UniversalType r Q 1))
    (hi : i∈is) : (address i (is.map (fun j => (j,f j)))).value=f i := by
  induction is with
  | nil => simp at hi
  | cons j js ih =>
    simp only [List.map_cons,address]
    by_cases h : i=j
    · subst j
      rw [ite_eq_left rfl]
    · rw [ite_eq_right h]
      exact ih ((List.mem_cons.mp hi).resolve_left h)

theorem address_work (i : I) (as : Addresses I r Q) :
    (address i as).work≤3*as.length+1 := by
  induction as with
  | nil => simp [address]
  | cons a as ih =>
    rcases a with ⟨j,a⟩
    simp only [address,List.length_cons]
    split_ifs <;> dsimp only <;> omega

/-- Actual literal zero/one arrays with their allocated-cell clock. -/
def literal (J : ℕ) (one : Bool) : Run (Array ℚ) :=
  ⟨Array.ofFn (fun k : Fin J => if one && decide (k.val=0) then 1 else 0),J+1⟩

/-- Assemble one complete-block or leftover entry from actual materialized addresses. -/
def assembled (R : ℕ) (as : Addresses I r Q) (keys : List (UniversalType r Q 1))
    (cache : List (List (Array ℚ))) (i j : I) : Run (Array ℚ) :=
  let ai := address i as
  match ai.value with
  | none =>
      let out := literal (R+1) (decide (i=j))
      ⟨out.value,ai.work+out.work+2⟩
  | some a =>
      let bj := address j as
      match bj.value with
      | none => let out := literal (R+1) false; ⟨out.value,ai.work+bj.work+out.work+2⟩
      | some b =>
          if a.1=b.1 then
            let out := SemiprimeMaterializedSourceCache.read R keys cache a.2 b.2
            ⟨out.value,ai.work+bj.work+out.work+3⟩
          else
            let out := literal (R+1) false
            ⟨out.value,ai.work+bj.work+out.work+3⟩

/-- No address branch omits an actual scan or array allocation/cache read. -/
theorem assembled_work (R : ℕ) (as : Addresses I r Q) (keys : List (UniversalType r Q 1))
    (cache : List (List (Array ℚ))) (i j : I) :
    (assembled R as keys cache i j).work≤
      2*(3*as.length+1)+2*(keys.length*(7*Q+4)+1)+R+5 := by
  have hi := address_work i as
  have hj := address_work j as
  cases ha : (address i as).value with
  | none =>
    simp only [assembled,ha,literal]
    omega
  | some a =>
    cases hb : (address j as).value with
    | none =>
      simp only [assembled,ha,hb,literal]
      omega
    | some b =>
      unfold assembled
      dsimp only
      rw [ha,hb]
      dsimp only
      split_ifs <;> dsimp only
      · have ho := SemiprimeMaterializedSourceCache.read_work R keys cache a.2 b.2
        omega
      · simp only [literal]
        omega

/-- Add actual cached arrays and retain the callback and array interpreter costs. -/
def add (J : ℕ) (a b : Run (Array ℚ)) : Run (Array ℚ) :=
  let out := addJet a.value b.value J
  ⟨out.coefficients,a.work+b.work+out.arithmetic+out.reads+J+1⟩

theorem add_work (J : ℕ) (a b : Run (Array ℚ)) :
    (add J a b).work=a.work+b.work+4*J+1 := by
  have hw := addJet_work a.value b.value J
  simp only [add]
  rw [hw.1,hw.2]
  omega

/-- Sum original incidence contributions with every callback executed once. -/
def sumArrays (J : ℕ) (f : I → Run (Array ℚ)) : List I → Run (Array ℚ)
  | [] => literal J false
  | i::is => let a := f i; let b := sumArrays J f is; add J a b

omit [DecidableEq I] in
theorem sumArrays_work (J : ℕ) (f : I → Run (Array ℚ)) (is : List I) (B : ℕ)
    (h : ∀ i∈is, (f i).work≤B) :
    (sumArrays J f is).work≤J+1+is.length*(B+4*J+1) := by
  induction is with
  | nil => simp [sumArrays,literal]
  | cons i is ih =>
    have ha := h i (by simp)
    have hb := ih (fun j hj => h j (by simp [hj]))
    simp only [sumArrays,add_work,List.length_cons]
    nlinarith

/-- Pull back all actual original incidences owned by a particular variable. -/
def sourceRow {n : ℕ} (R : ℕ) (is : List I) (owner : I → Fin n)
    (as : Addresses I r Q) (keys : List (UniversalType r Q 1))
    (cache : List (List (Array ℚ))) (i : I) (v : Fin n) : Run (Array ℚ) :=
  sumArrays (R+1) (fun j =>
    if owner j=v then
      let out := assembled R as keys cache i j
      ⟨out.value,out.work+2⟩
    else let out := literal (R+1) false; ⟨out.value,out.work+2⟩) is

/-- Actual finite original-variable pullback clock. -/
theorem sourceRow_work {n : ℕ} (R : ℕ) (is : List I) (owner : I → Fin n)
    (as : Addresses I r Q) (keys : List (UniversalType r Q 1))
    (cache : List (List (Array ℚ))) (i : I) (v : Fin n) :
    (sourceRow R is owner as keys cache i v).work≤
      R+2+is.length*(2*(3*as.length+1)+2*(keys.length*(7*Q+4)+1)+R+7+4*(R+1)+1) := by
  apply sumArrays_work
  intro j _
  split_ifs <;> dsimp only
  · have h := assembled_work R as keys cache i j
    omega
  · simp only [literal]
    omega

/-- Low coefficient of a literal array, including both Boolean choices. -/
theorem literal_coefficient (J : ℕ) (one : Bool) (k : ℕ) (hk : k<J) :
    coefficient (literal J one).value k=if one && decide (k=0) then 1 else 0 := by
  exact ofFn_coefficient _ k hk

omit [DecidableEq I] in
/-- The actual array sum has the exact finite-sum coefficient semantics. -/
theorem sumArrays_coefficient (J : ℕ) (f : I → Run (Array ℚ)) (is : List I)
    (k : ℕ) (hk : k<J) :
    coefficient (sumArrays J f is).value k=(is.map (fun i => coefficient (f i).value k)).sum := by
  induction is with
  | nil => simp only [sumArrays,literal_coefficient J false k hk,Bool.false_and,Bool.false_eq_true,ite_false,List.map_nil,List.sum_nil]
  | cons i is ih =>
    simp only [sumArrays,add,List.map_cons,List.sum_cons]
    rw [addJet_coefficient _ _ J k hk,ih]

/-- One immutable actual address table, used only to state source agreement. -/
def packingAddresses (P : PackingData I (UniversalType r Q 1)) : Addresses I r Q :=
  P.vertices.values.map (fun i => (i,(P.lookup i).map (fun a => (a.1.val,a.2))))

theorem address_packing (P : PackingData I (UniversalType r Q 1)) (i : I) :
    (address i (packingAddresses P)).value=(P.lookup i).map (fun a => (a.1.val,a.2)) :=
  address_map i P.vertices.values _ (P.vertices.complete i)

/-- The original numerator centering used by the mathematical source constructor. -/
def centered (r Q R : ℕ) : ℕ := Subexp.TailInterval.intervalStart r Q R

/-- All cached complete-block and leftover coefficients equal the existing source assembly. -/
theorem assembled_coefficient (P : PackingData I (UniversalType r Q 1)) (R : ℕ)
    (keys : List (UniversalType r Q 1)) (complete : ∀ u, u∈keys) (i j : I)
    (k : ℕ) (hk : k<R+1) :
    coefficient (assembled R (packingAddresses P) keys
      (SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys).value i j).value k=
    coefficient (SemiprimeBlockArrayExecution.assembled P (R+1)
      (SemiprimeSourceArrayAcquisition.universal R) i j).jet.coefficients k := by
  have hi := address_packing P i
  have hj := address_packing P j
  unfold assembled SemiprimeBlockArrayExecution.assembled
  dsimp only
  rw [hi]
  cases hp : P.lookup i with
  | none =>
    simp only [Option.map_none]
    split_ifs with he
    · simp only [literal_coefficient _ _ k hk,SemiprimeFibreArrayExecution.oneRun,
        SemiprimeArrayOps.oneJet]
      rw [ofFn_coefficient _ k hk]
      simp [he]
    · simp only [literal_coefficient _ _ k hk,SemiprimeFibreArrayExecution.zeroRun]
      simp only [Ne.symm he,decide_false,Bool.false_and,Bool.false_eq_true,ite_false]
      exact (zeroJet_coefficient (R+1) k).symm
  | some a =>
    simp only [Option.map_some]
    rw [hj]
    cases hq : P.lookup j with
    | none =>
      simp only [Option.map_none,literal_coefficient _ _ k hk,Bool.false_and,
        SemiprimeFibreArrayExecution.zeroRun]
      exact (zeroJet_coefficient (R+1) k).symm
    | some b =>
      simp only [Option.map_some]
      by_cases hb : b.1=a.1
      · have hv : a.1.val=b.1.val := congrArg Fin.val hb.symm
        rw [ite_eq_left hv,ite_eq_left hb]
        rw [SemiprimeMaterializedSourceCache.read_acquire _ _ _ complete]
        rfl
      · have hv : a.1.val≠b.1.val := by
          intro he
          exact hb (Fin.ext he.symm)
        rw [ite_eq_right hv,ite_eq_right hb]
        simp only [literal_coefficient _ _ k hk,Bool.false_and,SemiprimeFibreArrayExecution.zeroRun]
        exact (zeroJet_coefficient (R+1) k).symm

/-- Original-coordinate coefficients are the SAME actual built source coefficients. -/
theorem sourceRow_coefficient [Fintype I] (P : PackingData I (UniversalType r Q 1))
    {n : ℕ} (owner : I → Fin n) (R : ℕ) (keys : List (UniversalType r Q 1))
    (complete : ∀ u, u∈keys) (i : I) (v : Fin n) (k : ℕ) (hk : k<R+1) :
    coefficient (sourceRow R P.vertices.values owner (packingAddresses P) keys
      (SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys).value i v).value k=
      (LayoutPullback.row owner (LayoutBlocks.assembledRow P.completeBlocks
        (SemiprimeSourceLayout.universalLayout r Q R).row i) v).coeff k := by
  unfold sourceRow
  rw [sumArrays_coefficient _ _ _ k hk,← List.sum_toFinset _ P.vertices.nodup]
  have hu : P.vertices.values.toFinset=Finset.univ := by
    ext j
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact P.vertices.complete j
  rw [hu]
  unfold LayoutPullback.row
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  by_cases ho : owner j=v
  · simp only [ite_eq_left ho]
    rw [assembled_coefficient P R keys complete i j k hk]
    exact SemiprimeBlockArrayExecution.assembled_spec P (R+1)
      (SemiprimeSourceArrayAcquisition.universal R)
      (SemiprimeSourceLayout.universalLayout r Q R).row
      (SemiprimeSourceArrayAcquisition.universal_spec R) i j k hk
  · simp only [ite_eq_right ho,literal_coefficient _ false k hk,Bool.false_and,
      Bool.false_eq_true,ite_false,Polynomial.coeff_zero]

/-- Acquire every original incidence-by-variable array from immutable labels and universal cache. -/
def acquire {n : ℕ} (R : ℕ) (is : List I) (owner : I → Fin n)
    (as : Addresses I r Q) (keys : List (UniversalType r Q 1)) :
    Run (List (List (Array ℚ))) :=
  let universal := SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys
  let out := collect (fun i => collect (sourceRow R is owner as keys universal.value i)
    (List.finRange n)) is
  ⟨out.value,universal.work+out.work+1⟩

/-- Every source-array callback and the one universal-cache acquisition is paid. -/
def acquireBudget (R Q m n D a A : ℕ) : ℕ :=
  SemiprimeMaterializedSourceRows.acquireBudget A R Q D+
    m*(n*(R+2+m*(2*(3*a+1)+2*(D*(7*Q+4)+1)+R+7+4*(R+1)+1)+2)+3)+2

theorem acquire_work {n : ℕ} (R : ℕ) (is : List I) (owner : I → Fin n)
    (as : Addresses I r Q) (keys : List (UniversalType r Q 1)) :
    (acquire R is owner as keys).work≤
      acquireBudget R Q is.length n keys.length as.length (centered r Q R) := by
  let universal := SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys
  let B := R+2+is.length*(2*(3*as.length+1)+2*(keys.length*(7*Q+4)+1)+R+7+4*(R+1)+1)
  have inner (i : I) :
      (collect (sourceRow R is owner as keys universal.value i) (List.finRange n)).work≤n*(B+2)+1 := by
    have h := collect_work (sourceRow R is owner as keys universal.value i) (List.finRange n)
      B (fun v _ => sourceRow_work R is owner as keys universal.value i v)
    simpa only [List.length_finRange] using h
  have outer := collect_work
    (fun i => collect (sourceRow R is owner as keys universal.value i) (List.finRange n)) is
    (n*(B+2)+1) (fun i _ => inner i)
  have hu := SemiprimeMaterializedSourceRows.acquire_work (centered r Q R) R keys
  unfold acquire
  dsimp only
  unfold acquireBudget
  dsimp only [universal,B] at outer
  nlinarith

/-- Cached original-source outputs are actual nested maps of the acquired row arrays. -/
theorem acquire_value {n : ℕ} (R : ℕ) (is : List I) (owner : I → Fin n)
    (as : Addresses I r Q) (keys : List (UniversalType r Q 1)) :
    (acquire R is owner as keys).value=is.map (fun i => (List.finRange n).map (fun v =>
      (sourceRow R is owner as keys
        (SemiprimeMaterializedSourceRows.acquire (centered r Q R) R keys).value i v).value)) := by
  simp only [acquire,collect_value]

end RiemannGaussian.SemiprimeMaterializedSourcePullback
