/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeBinomialExecutionTracked

/-! # Integer coefficient and scratch bounds for executed parity interpolation -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeBinomialExecutionBounds
open scoped BigOperators
open SemiprimeBinomialExecution

/-- Every actual scalar dot prefix has an absolute bound before cancellations. -/
theorem dot_bound (kernel : Array ℕ) (a : Array ℤ) (row len M B : ℕ)
    (hk : ∀ i<len,natCoeff kernel (row-i)≤ M)
    (ha : ∀ i<len,|coeff a i|≤(B : ℤ)) :
    |(dot kernel a row len).value|≤(len*M*B : ℕ) := by
  rw [dot_value]
  calc
    _ ≤ ∑ i∈Finset.range len,|(natCoeff kernel (row-i) : ℤ)*coeff a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i∈Finset.range len,(M : ℤ)*(B : ℤ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hindex := Finset.mem_range.mp hi
      rw [abs_mul,Int.abs_natCast]
      exact mul_le_mul (by exact_mod_cast hk i hindex) (ha i hindex) (abs_nonneg _) (by positivity)
    _ = _ := by simp [Nat.mul_assoc]

/-- A simple positive majorant of every stage of the unitriangular solve. -/
def solveBase (total M : ℕ) : ℕ := total*M+1

/-- All cached solve coefficients have a uniform integer bound, including every prefix. -/
theorem solve_bound (kernel : Array ℕ) (target : ℕ → ℤ) (total M Z : ℕ)
    (hk : ∀ i≤ total,natCoeff kernel i≤ M)
    (ht : ∀ i<total,|target i|≤(Z : ℤ)) (len : ℕ) (hlen : len≤ total) :
    ∀ i<len,|coeff (solve kernel target len).coefficients i|≤(Z*solveBase total M^len : ℕ) := by
  induction len with
  | zero => intro i hi; omega
  | succ len ih =>
    have hprev := ih (by omega : len≤ total)
    intro i hi
    by_cases he : i=len
    · subst i
      rw [solve_new,← dot_value]
      have hd := dot_bound kernel (solve kernel target len).coefficients len len M
        (Z*solveBase total M^len) (fun j _ => hk _ (by omega)) hprev
      have hab := abs_sub (target len) (dot kernel (solve kernel target len).coefficients len len).value
      have hz := ht len (by omega)
      have hpower : 1≤ solveBase total M^len := by
        simpa only [one_pow] using Nat.pow_le_pow_left
          (show 1≤ solveBase total M by unfold solveBase; omega) len
      have hNat : Z+len*M*(Z*solveBase total M^len)≤ Z*solveBase total M^(len+1) := by
        calc
          _ ≤ Z*solveBase total M^len+total*M*(Z*solveBase total M^len) :=
            Nat.add_le_add (by simpa using Nat.mul_le_mul_left Z hpower)
              (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right M (by omega : len≤ total)))
          _ = _ := by rw [pow_succ]; unfold solveBase; ring
      have hsum : |target len-(dot kernel (solve kernel target len).coefficients len len).value|≤
          (Z+len*M*(Z*solveBase total M^len) : ℕ) := by
        exact hab.trans (by exact_mod_cast add_le_add hz hd)
      exact hsum.trans (by exact_mod_cast hNat)
    · rw [solve_old _ _ _ _ (by omega : i<len)]
      have hp := Nat.pow_le_pow_right (show 1≤ solveBase total M by unfold solveBase; omega)
        (Nat.le_succ len)
      exact (hprev i (by omega)).trans (by exact_mod_cast Nat.mul_le_mul_left Z hp)

/-- The explicit Pascal supplier never exceeds the native binomial height. -/
theorem chooseRow_bound (R A k : ℕ) (hk : k≤ R) : natCoeff (chooseRow R A) k≤ 2^A := by
  rw [chooseRow_correct R A k hk]
  exact Nat.choose_le_two_pow _ _

/-- The lower solution's magnitude is just a small integer power of two. -/
theorem lower_abs (A s : ℕ) : |lower A s|=(2 : ℤ)^s := by
  simp [lower,abs_mul,abs_pow]

/-- Every runtime reversed target is bounded, including natural zero extension. -/
theorem target_bound (A R k : ℕ) : |lower A (R-(k+1))|≤(2^R : ℕ) := by
  rw [lower_abs]
  exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤ 2) (Nat.sub_le R (k+1))

/-- Uniform height of every acquired original-order parity coefficient. -/
theorem parity_bound (A R : ℕ) (j : Fin R) :
    |parity A R j|≤(2^R*(R*2^A+1)^R : ℕ) := by
  have h := solve_bound (chooseRow R A) (fun k => lower A (R-(k+1))) R (2^A) (2^R)
    (fun k hk => chooseRow_bound R A k hk) (fun k _ => target_bound A R k) R le_rfl j.rev.val j.rev.isLt
  exact h

/-- All completed integer coefficients fit an explicit polynomial exponent envelope. -/
theorem parity_bound_power (A R : ℕ) (j : Fin R) :
    |parity A R j|≤(2^(R*(A+Nat.clog 2 (R+1)+1)) : ℕ) := by
  have hbase : R*2^A+1≤ 2^(A+Nat.clog 2 (R+1)) := by
    calc
      R*2^A+1 ≤ (R+1)*2^A := by have hp : 1≤ 2^A := Nat.one_le_pow _ _ (by decide); nlinarith
      _ ≤ (2^Nat.clog 2 (R+1))*2^A := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) _)
      _ = _ := by rw [pow_add]; ring
  have hp := Nat.mul_le_mul_left (2^R) (Nat.pow_le_pow_left hbase R)
  have he : 2^R*(2^(A+Nat.clog 2 (R+1)))^R=2^(R*(A+Nat.clog 2 (R+1)+1)) := by
    rw [← pow_mul,← pow_add]
    congr 1
    ring
  exact (parity_bound A R j).trans (by exact_mod_cast hp.trans_eq he)

/-- The fully tracked acquired vector retains the same explicit integer bit envelope. -/
theorem acquiredParity_bound_power (A R : ℕ) (j : Fin R) :
    |SemiprimeBinomialExecutionTracked.acquiredParity A R j|≤
      (2^(R*(A+Nat.clog 2 (R+1)+1)) : ℕ) := by
  have h : SemiprimeBinomialExecutionTracked.acquiredParity A R=parity A R :=
    (SemiprimeBinomialExecutionTracked.acquiredParity_eq A R).trans (parity_eq A R).symm
  rw [h]
  exact parity_bound_power A R j

/-- Even the retained next target power has only R+1 binary digits. -/
theorem acquiredLower_next_bound (A R : ℕ) :
    |(SemiprimeBinomialExecutionTracked.acquireLower
      (SemiprimeBinomialExecutionTracked.sign A).1 R).next|=(2 : ℤ)^R := by
  rw [SemiprimeBinomialExecutionTracked.acquireLower_next,
    SemiprimeBinomialExecutionTracked.sign_value]
  exact lower_abs A R

end RiemannGaussian.SemiprimeBinomialExecutionBounds
