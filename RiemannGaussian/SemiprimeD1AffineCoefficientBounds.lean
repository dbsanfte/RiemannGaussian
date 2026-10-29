/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1AffineCoefficient

/-! # Original-data work bound for requested affine-product coefficients
Generic ring operations and native tuple/list work are counted separately by
the producer; their sum is bounded without an advised coefficient/clock oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1AffineCoefficientBounds
open SemiprimeD1AffineCoefficient

/-- Every cached scalar read scans at most the original list once. -/
theorem read_work {R : Type*} (default : R) (vs : List R) (i : ℕ) :
    (read default vs i).2 ≤ 3*vs.length+1 := by
  induction vs generalizing i with
  | nil => simp [SemiprimeD1AffineCoefficient.read]
  | cons v vs ih =>
    cases i with
    | zero => simp only [SemiprimeD1AffineCoefficient.read,List.length_cons];omega
    | succ i => have h:=ih i;simp only [SemiprimeD1AffineCoefficient.read,List.length_cons];omega

/-- Full acquired tuple copies have literal linear work. -/
theorem copyTuple_work (beta : List ℕ) : (copyTuple beta).2=3*beta.length+1 := by
  induction beta with
  | nil => rfl
  | cons b bs ih => simp only [copyTuple,List.length_cons,ih];omega

/-- Every actual tuple-decrement path and copied suffix is paid. -/
theorem decrement_work (beta : List ℕ) (i : ℕ) : (decrement beta i).2 ≤ 3*beta.length+2 := by
  induction beta generalizing i with
  | nil => simp [decrement]
  | cons b bs ih =>
    cases i with
    | zero => simp only [decrement,copyTuple_work,List.length_cons];omega
    | succ i => have h:=ih i;simp only [decrement,List.length_cons];omega

/-- Terminal all-zero check pays each original tuple cell exactly once. -/
theorem zeroTest_work (beta : List ℕ) : (zeroTest beta).2=3*beta.length+1 := by
  induction beta with
  | nil => rfl
  | cons b bs ih => simp only [zeroTest,List.length_cons,ih];omega

/-- Actual branch accumulation retains each acquired report and one ring addition. -/
theorem sumRuns_work {R : Type*} [AddMonoid R] (rs : List (Run R)) :
    (sumRuns rs).work=(rs.map Run.work).sum+4*rs.length+1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change r.ringOps+(sumRuns rs).ringOps+1+(r.control+(sumRuns rs).control+3)=_
    have he : r.ringOps+(sumRuns rs).ringOps+1+(r.control+(sumRuns rs).control+3)=
        r.work+(sumRuns rs).work+4 := by unfold Run.work;ring
    rw [he,ih]
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- Literal bounded sum of cached branch reports. -/
theorem map_work_le {R : Type*} (indices : List ℕ) (f : ℕ→Run R) (B : ℕ)
    (h : ∀i∈indices,(f i).work ≤ B) :
    (indices.map (fun i => (f i).work)).sum ≤ indices.length*B := by
  induction indices with
  | nil => simp
  | cons i indices ih =>
    have hh:=h i List.mem_cons_self
    have ht:=ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- Fixed polynomial overhead before branching, from actual source dimensions. -/
def stageConstant (K tupleLength rowWidth : ℕ) : ℕ :=
  (K+1)*(6*tupleLength+3*rowWidth+24)+11

/-- One actual row's recursive branches cost at mostK+1 acquired subcalls plus
a fixed original-dimension overhead. The final theorem discharges all subcalls. -/
theorem evaluate_step_le {R : Type*} [CommRing R] (K : ℕ) (row : Row R)
    (rows : List (Row R)) (beta : List ℕ) (A B : ℕ)
    (hrow : row.coefficients.length ≤ A)
    (hchild : ∀target : List ℕ,target.length=beta.length→(evaluate K rows target).work ≤ B) :
    (evaluate K (row::rows) beta).work ≤ (K+1)*B+stageConstant K beta.length A := by
  let branch (i : ℕ) : Run R :=
    let exponent:=read 0 beta i
    if exponent.1=0 then ⟨0,0,exponent.2+3⟩
    else
      let target:=decrement beta i
      let child:=evaluate K rows target.1
      let coeff:=read 0 row.coefficients i
      ⟨coeff.1*child.value,child.ringOps+1,
        exponent.2+target.2+child.control+coeff.2+5⟩
  have hbranch (i : ℕ) : (branch i).work ≤ B+6*beta.length+3*A+10 := by
    have he:=read_work 0 beta i
    have ht:=decrement_work beta i
    have hc:=read_work (0:R) row.coefficients i
    have hh:=hchild (decrement beta i).1 (decrement_length beta i)
    unfold Run.work at hh
    unfold branch Run.work
    dsimp only
    split_ifs <;> dsimp only <;> omega
  have hs:=map_work_le (List.range K) branch (B+6*beta.length+3*A+10) (fun i _=>hbranch i)
  simp only [List.length_range] at hs
  have hsum := sumRuns_work ((List.range K).map branch)
  simp only [List.map_map,Function.comp_def,List.length_map,List.length_range] at hsum
  have hbase:=hchild beta rfl
  have heq : (evaluate K (row::rows) beta).work=
      (evaluate K rows beta).work+(sumRuns ((List.range K).map branch)).work+10*K+10 := by
    change ((evaluate K rows beta).ringOps+(sumRuns ((List.range K).map branch)).ringOps+2)+
      ((evaluate K rows beta).control+(sumRuns ((List.range K).map branch)).control+10*K+8)=_
    unfold Run.work
    ring
  rw [heq]
  unfold stageConstant
  rw [hsum]
  nlinarith

/-- Exact closed original-data upper bound, with no output/fit/work advice. -/
def budget (K L tupleLength rowWidth : ℕ) : ℕ :=
  (L+1)*stageConstant K tupleLength rowWidth*(K+1)^L

/-- Pure scalar recursion balance, independent of all executable projections. -/
theorem recursion_budget (K L C : ℕ) :
    (K+1)*((L+1)*C*(K+1)^L)+C ≤ (L+2)*C*(K+1)^(L+1) := by
  have hp : 1 ≤ (K+1)^(L+1) := Nat.one_le_pow _ _ (by omega)
  have hc:=Nat.mul_le_mul_left C hp
  calc
    _ ≤ (K+1)*((L+1)*C*(K+1)^L)+C*(K+1)^(L+1) := by omega
    _ = _ := by rw [pow_succ];ring

/-- Actual requested-coefficient acquisition is bounded bypoly(K,L)*(K+1)^L.
All recursive tuple shapes and every branch callback are discharged internally. -/
theorem evaluate_work {R : Type*} [CommRing R] (K : ℕ) (rows : List (Row R))
    (beta : List ℕ) (A : ℕ) (hrows : ∀row∈rows,row.coefficients.length ≤ A) :
    (evaluate K rows beta).work ≤ budget K rows.length beta.length A := by
  induction rows generalizing beta with
  | nil =>
    have hz:=zeroTest_work beta
    change 0+((zeroTest beta).2+2) ≤ _
    simp only [Nat.zero_add]
    unfold budget stageConstant
    simp only [List.length_nil,Nat.zero_add,pow_zero,Nat.mul_one,Nat.one_mul]
    have hm : 6*beta.length+3*A+24 ≤ (K+1)*(6*beta.length+3*A+24) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos K)
    omega
  | cons row rows ih =>
    have hrow:=hrows row List.mem_cons_self
    have htail : ∀r∈rows,r.coefficients.length ≤ A := fun r hr=>hrows r (List.mem_cons_of_mem row hr)
    have hstep:=evaluate_step_le K row rows beta A (budget K rows.length beta.length A) hrow (by
      intro target hlen
      have h:=ih target htail
      simpa only [hlen] using h)
    have hrec:=recursion_budget K rows.length (stageConstant K beta.length A)
    unfold budget at hstep ⊢
    simp only [List.length_cons]
    exact hstep.trans hrec

/-- Original finite-mode data and acquired tuple shape specialize the bound to
poly(K,L)*(K+1)^L, with no coefficient value or subcall-work premise. -/
theorem evaluate_work_modes {R : Type*} [CommRing R] (K : ℕ) (rows : List (Row R))
    (beta : List ℕ) (hbeta : beta.length=K)
    (hrows : ∀row∈rows,row.coefficients.length ≤ K) :
    (evaluate K rows beta).work ≤
      (rows.length+1)*stageConstant K K K*(K+1)^rows.length := by
  simpa only [budget,hbeta] using evaluate_work K rows beta K hrows

end RiemannGaussian.SemiprimeD1AffineCoefficientBounds
