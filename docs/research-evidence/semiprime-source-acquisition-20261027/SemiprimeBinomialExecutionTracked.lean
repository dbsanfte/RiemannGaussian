/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBinomialExecution

/-! # Fully acquired integer Pascal, target and parity arrays -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeBinomialExecutionTracked
open scoped BigOperators
open SemiprimeBinomialExecution

/-- Actual Pascal row and its scalar/read ledger. -/
structure PascalRun where
  /-- Materialized natural coefficient row. -/
  coefficients : Array ℕ
  /-- Scalar integer additions in the coordinate callbacks. -/
  additions : ℕ
  /-- Conservative actual old-row reads, including the zero boundary slot. -/
  reads : ℕ

/-- Acquire Pascal coefficients without native choose or matrix advice. -/
def acquireChoose (R : ℕ) : ℕ → PascalRun
  | 0 => ⟨Array.ofFn (fun k : Fin (R+1) => if k.val=0 then 1 else 0),0,0⟩
  | A+1 =>
      let old := acquireChoose R A
      let next := Array.ofFn (fun k : Fin (R+1) => natCoeff old.coefficients k.val+
        if k.val=0 then 0 else natCoeff old.coefficients (k.val-1))
      ⟨next,old.additions+(R+1),old.reads+2*(R+1)⟩

/-- The instrumented supplier returns exactly the proved Pascal row. -/
theorem acquireChoose_value (R A : ℕ) : (acquireChoose R A).coefficients=chooseRow R A := by
  induction A with
  | zero => rfl
  | succ A ih => simp only [acquireChoose,chooseRow,ih]

/-- Every Pascal coordinate addition/read is paid in the actual finite loops. -/
theorem acquireChoose_work (R A : ℕ) :
    (acquireChoose R A).additions=A*(R+1) ∧ (acquireChoose R A).reads=2*A*(R+1) := by
  induction A with
  | zero => simp [acquireChoose]
  | succ A ih => simp only [acquireChoose]; constructor <;> nlinarith

/-- Compute the parity sign by actual integer negations. -/
def sign : ℕ → ℤ × ℕ
  | 0 => (1,0)
  | A+1 => let old := sign A; (-old.1,old.2+1)

theorem sign_value (A : ℕ) : (sign A).1=(-1 : ℤ)^A := by
  induction A with
  | zero => rfl
  | succ A ih => simp only [sign,ih,pow_succ]; ring

theorem sign_work (A : ℕ) : (sign A).2=A := by
  induction A with
  | zero => rfl
  | succ A ih => simp only [sign,ih]

/-- Cached powers for the explicit lower Pascal solution. -/
structure LowerRun where
  /-- Already computed lower coefficients. -/
  coefficients : Array ℤ
  /-- Next cached scalar power, never recomputed recursively from its exponent. -/
  next : ℤ
  /-- Actual integer products. -/
  arithmetic : ℕ

/-- Acquire a geometric target array by one multiplication per next entry. -/
def acquireLower (base : ℤ) : ℕ → LowerRun
  | 0 => ⟨#[],base,0⟩
  | len+1 =>
      let old := acquireLower base len
      ⟨old.coefficients.push old.next,old.next*(-2),old.arithmetic+1⟩

theorem acquireLower_size (base : ℤ) (len : ℕ) : (acquireLower base len).coefficients.size=len := by
  induction len with
  | zero => rfl
  | succ len ih => simp only [acquireLower,Array.size_push,ih]

theorem acquireLower_next (base : ℤ) (len : ℕ) : (acquireLower base len).next=base*(-2 : ℤ)^len := by
  induction len with
  | zero => simp [acquireLower]
  | succ len ih => simp only [acquireLower,ih,pow_succ]; ring

theorem acquireLower_work (base : ℤ) (len : ℕ) : (acquireLower base len).arithmetic=len := by
  induction len with
  | zero => rfl
  | succ len ih => simp only [acquireLower,ih]

/-- Each retained target entry is the actual explicitly computed geometric coefficient. -/
theorem acquireLower_value (base : ℤ) (len k : ℕ) (hk : k<len) :
    coeff (acquireLower base len).coefficients k=base*(-2 : ℤ)^k := by
  induction len with
  | zero => omega
  | succ len ih =>
    by_cases he : k=len
    · subst k
      simp only [acquireLower,coeff,Array.getElem?_push,acquireLower_size,ite_true,
        Option.getD_some,acquireLower_next]
    · have hkl : k<len := by omega
      simp only [acquireLower,coeff,Array.getElem?_push,acquireLower_size,ite_eq_right he]
      exact ih hkl

/-- A cached solve depends only on target coordinates that its loop actually reads. -/
theorem solve_target_ext (kernel : Array ℕ) (f g : ℕ → ℤ) (len : ℕ)
    (h : ∀ k<len,f k=g k) : solve kernel f len=solve kernel g len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have ho := ih (fun k hk => h k (by omega))
    simp only [solve,ho,h len (by omega)]

/-- All integer coefficient arrays and complete scalar/read costs of the acquisition. -/
structure ParityRun where
  /-- Reversed upper-solve output coefficients. -/
  coefficients : Array ℤ
  /-- Pascal additions, sign negations, target products and solve arithmetic. -/
  arithmetic : ℕ
  /-- Pascal/solve cached-array reads. -/
  reads : ℕ

/-- Full integer acquisition: Pascal kernel, geometric target and cached solve. -/
def acquireParity (A R : ℕ) : ParityRun :=
  let kernel := acquireChoose R A
  let phase := sign A
  let targets := acquireLower phase.1 R
  let out := solve kernel.coefficients (fun k => coeff targets.coefficients (R-(k+1))) R
  ⟨out.coefficients,kernel.additions+phase.2+targets.arithmetic+out.arithmetic,
    kernel.reads+out.reads⟩

/-- Every acquired coefficient is the original exact parity coefficient, not advice. -/
theorem acquireParity_value (A R : ℕ) :
    (acquireParity A R).coefficients=(parityArray A R).coefficients := by
  simp only [acquireParity,acquireChoose_value,sign_value,parityArray]
  apply congrArg SolveRun.coefficients
  apply solve_target_ext
  intro k hk
  rw [acquireLower_value _ _ _ (by omega)]
  rfl

/-- The complete scalar/read work includes the two coefficient suppliers. -/
theorem acquireParity_work (A R : ℕ) :
    (acquireParity A R).arithmetic=A*(R+1)+A+R+R^2 ∧
      (acquireParity A R).reads=2*A*(R+1)+R^2 := by
  have hp := acquireChoose_work R A
  have hl := acquireLower_work (sign A).1 R
  have hs := solve_work (acquireChoose R A).coefficients
    (fun k => coeff (acquireLower (sign A).1 R).coefficients (R-(k+1))) R
  simp only [acquireParity,sign_work]
  constructor <;> omega

/-- Original-order executable coefficient function with ALL sources acquired internally. -/
def acquiredParity (A R : ℕ) : Fin R → ℤ :=
  let out := acquireParity A R
  fun j => coeff out.coefficients j.rev.val

/-- No runtime coefficient-vector supplier appears in this exact source equality. -/
theorem acquiredParity_eq (A R : ℕ) :
    acquiredParity A R=OAI.Algorithms.SubexponentialSAT.BinomialInterpolation.parityCoefficients (K:=ℤ) A R := by
  rw [← parity_eq]
  funext j
  simp only [acquiredParity,parity,acquireParity_value]

end RiemannGaussian.SemiprimeBinomialExecutionTracked
