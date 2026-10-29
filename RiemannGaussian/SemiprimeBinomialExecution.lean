/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import OpenAISemiprime.Algorithms.SubexponentialSAT.BinomialInterpolation
import Mathlib.Data.Vector.Basic

/-! # Cached integer binomial/parity coefficient acquisition -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeBinomialExecution
open scoped BigOperators
open Matrix
open OAI.Algorithms.SubexponentialSAT

/-- Read an integer coefficient with literal zero beyond its retained array. -/
def coeff (a : Array ℤ) (i : ℕ) : ℤ := a[i]?.getD 0

/-- Read a natural Pascal coefficient with zero beyond its retained array. -/
def natCoeff (a : Array ℕ) (i : ℕ) : ℕ := a[i]?.getD 0

/-- Cached truncated Pascal row; each new row reads only the computed previous one. -/
def chooseRow (R : ℕ) : ℕ → Array ℕ
  | 0 => Array.ofFn (fun k : Fin (R+1) => if k.val=0 then 1 else 0)
  | A+1 =>
      let old := chooseRow R A
      Array.ofFn (fun k : Fin (R+1) => natCoeff old k.val+
        if k.val=0 then 0 else natCoeff old (k.val-1))

/-- Every retained Pascal row has exactly the requested finite width. -/
theorem chooseRow_size (R A : ℕ) : (chooseRow R A).size=R+1 := by
  cases A <;> simp [chooseRow]

/-- Each computed Pascal entry equals its literal integer binomial coefficient. -/
theorem chooseRow_correct (R A k : ℕ) (hk : k≤ R) : natCoeff (chooseRow R A) k=A.choose k := by
  induction A generalizing k with
  | zero =>
    simp only [chooseRow,natCoeff,Array.getElem?_ofFn,dite_eq_left (by omega : k<R+1),Option.getD_some]
    cases k <;> simp
  | succ A ih =>
    simp only [chooseRow,natCoeff,Array.getElem?_ofFn,dite_eq_left (by omega : k<R+1),Option.getD_some]
    change natCoeff (chooseRow R A) k+(if k=0 then 0 else natCoeff (chooseRow R A) (k-1))=_
    rw [ih k hk]
    cases k with
    | zero => simp
    | succ k =>
      simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.add_sub_cancel]
      rw [ih k (by omega),Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one,Nat.add_comm]

/-- Tracked scalar dot output of a unitriangular convolution row. -/
structure DotRun where
  /-- Actual integer value. -/
  value : ℤ
  /-- Integer additions/multiplications executed. -/
  arithmetic : ℕ
  /-- Coefficient-array reads executed. -/
  reads : ℕ

/-- Finite dot product reads already cached coefficient prefixes only. -/
def dot (kernel : Array ℕ) (a : Array ℤ) (row : ℕ) : ℕ → DotRun
  | 0 => ⟨0,0,0⟩
  | len+1 =>
      let old := dot kernel a row len
      ⟨old.value+(natCoeff kernel (row-len) : ℤ)*coeff a len,old.arithmetic+2,old.reads+2⟩

theorem dot_value (kernel : Array ℕ) (a : Array ℤ) (row len : ℕ) :
    (dot kernel a row len).value=∑ i∈Finset.range len,(natCoeff kernel (row-i) : ℤ)*coeff a i := by
  induction len with
  | zero => simp [dot]
  | succ len ih => simp only [dot,ih,Finset.sum_range_succ]

theorem dot_work (kernel : Array ℕ) (a : Array ℤ) (row len : ℕ) :
    (dot kernel a row len).arithmetic=2*len ∧ (dot kernel a row len).reads=2*len := by
  induction len with
  | zero => exact ⟨rfl,rfl⟩
  | succ len ih => simp only [dot]; omega

/-- The entire computed integer prefix with actual arithmetic/read counters. -/
structure SolveRun where
  /-- Coefficients in reversed upper-triangular order. -/
  coefficients : Array ℤ
  /-- Integer arithmetic calls in the actual recurrence. -/
  arithmetic : ℕ
  /-- Actual cached-coefficient reads. -/
  reads : ℕ

/-- Cached unitriangular recurrence; there is no division or matrix inverse. -/
def solve (kernel : Array ℕ) (target : ℕ → ℤ) : ℕ → SolveRun
  | 0 => ⟨#[],0,0⟩
  | len+1 =>
      let old := solve kernel target len
      let sum := dot kernel old.coefficients len len
      ⟨old.coefficients.push (target len-sum.value),old.arithmetic+sum.arithmetic+1,old.reads+sum.reads+1⟩

theorem solve_size (kernel : Array ℕ) (target : ℕ → ℤ) (len : ℕ) :
    (solve kernel target len).coefficients.size=len := by
  induction len with
  | zero => rfl
  | succ len ih => simp only [solve,Array.size_push,ih]

/-- Every previously acquired integer coefficient survives the next cached push. -/
theorem solve_old (kernel : Array ℕ) (target : ℕ → ℤ) (len i : ℕ) (hi : i<len) :
    coeff (solve kernel target (len+1)).coefficients i=coeff (solve kernel target len).coefficients i := by
  simp only [solve,coeff,Array.getElem?_push,solve_size,ite_eq_right (by omega : i≠len)]

/-- The new coordinate is the actual computed unitriangular recurrence. -/
theorem solve_new (kernel : Array ℕ) (target : ℕ → ℤ) (len : ℕ) :
    coeff (solve kernel target (len+1)).coefficients len=
      target len-∑ i∈Finset.range len,(natCoeff kernel (len-i) : ℤ)*coeff (solve kernel target len).coefficients i := by
  simp only [solve,coeff,Array.getElem?_push,solve_size,ite_true,Option.getD_some]
  exact congrArg (target len-·) (dot_value _ _ _ _)

/-- Every final coefficient satisfies its exact lower unitriangular equation. -/
theorem solve_equation (kernel : Array ℕ) (target : ℕ → ℤ) (h0 : natCoeff kernel 0=1)
    (len k : ℕ) (hk : k<len) :
    (∑ i∈Finset.range (k+1),(natCoeff kernel (k-i) : ℤ)*coeff (solve kernel target len).coefficients i)=target k := by
  induction len with
  | zero => omega
  | succ len ih =>
    by_cases he : k=len
    · subst k
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self,h0,Nat.cast_one,one_mul,solve_new]
      have hs : (∑ i∈Finset.range len,(natCoeff kernel (len-i) : ℤ)*coeff (solve kernel target (len+1)).coefficients i)=
          ∑ i∈Finset.range len,(natCoeff kernel (len-i) : ℤ)*coeff (solve kernel target len).coefficients i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [solve_old _ _ _ _ (Finset.mem_range.mp hi)]
      rw [hs]
      ring
    · have hkl : k<len := by omega
      rw [← ih hkl]
      apply Finset.sum_congr rfl
      intro i hi
      rw [solve_old _ _ _ _ (by have := Finset.mem_range.mp hi; omega)]

/-- The actual recurrence has exactly len squared arithmetic calls and reads. -/
theorem solve_work (kernel : Array ℕ) (target : ℕ → ℤ) (len : ℕ) :
    (solve kernel target len).arithmetic=len^2 ∧ (solve kernel target len).reads=len^2 := by
  induction len with
  | zero => exact ⟨rfl,rfl⟩
  | succ len ih =>
    have hd := dot_work kernel (solve kernel target len).coefficients len len
    simp only [solve]
    constructor <;> nlinarith


/-- Explicit solution of the lower Pascal system for alternating targets. -/
def lower (A s : ℕ) : ℤ := (-1 : ℤ)^A*(-2 : ℤ)^s

/-- Extending a lower finite sum to a longer finite dimension adds only zero terms. -/
theorem sum_fin_cutoff (R k : ℕ) (hk : k<R) (f : ℕ → ℤ) :
    (∑ i : Fin R,if i.val≤ k then f i.val else 0)=∑ i∈Finset.range (k+1),f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i≤ k then f i else 0) R]
  have he : (∑ i∈Finset.range (k+1),if i≤ k then f i else 0)=∑ i∈Finset.range R,if i≤ k then f i else 0 := by
    apply Finset.sum_subset (Finset.range_mono (by omega : k+1≤ R))
    intro i hi hin
    have hki : ¬i≤ k := by have hh := Finset.mem_range.not.mp hin; omega
    simp only [ite_eq_right hki]
  rw [← he]
  apply Finset.sum_congr rfl
  intro i hi
  exact ite_eq_left (by have := Finset.mem_range.mp hi; omega)

/-- The explicit lower vector solves the actual Pascal matrix over the integers. -/
theorem lower_spec (A R : ℕ) :
    BinomialMatrix.L ℤ R *ᵥ (fun s : Fin R => lower A s.val)=
      fun d => (-1 : ℤ)^(A+d.val) := by
  funext d
  change (∑ s : Fin R,(d.val.choose s.val : ℤ)*lower A s.val)=_
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => (d.val.choose s : ℤ)*lower A s) R]
  have hs : (∑ s∈Finset.range (d.val+1),(d.val.choose s : ℤ)*lower A s)=
      ∑ s∈Finset.range R,(d.val.choose s : ℤ)*lower A s := by
    apply Finset.sum_subset (Finset.range_mono (by omega : d.val+1≤ R))
    intro s hs hsmall
    have hds : d.val<s := by have := Finset.mem_range.not.mp hsmall; omega
    simp only [Nat.choose_eq_zero_of_lt hds,Nat.cast_zero,zero_mul]
  have hb := add_pow (-2 : ℤ) 1 d.val
  simp only [show (-2 : ℤ)+1=(-1) by norm_num,one_pow,mul_one] at hb
  calc
    _ = (-1 : ℤ)^A*∑ s∈Finset.range (d.val+1),(-2 : ℤ)^s*(d.val.choose s : ℤ) := by
      rw [← hs,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      unfold lower
      ring
    _ = (-1 : ℤ)^A*(-1 : ℤ)^d.val := by rw [← hb]
    _ = _ := (pow_add _ _ _).symm

/-- Actual cached integer solve in reversed upper-triangular index order. -/
def parityArray (A R : ℕ) : SolveRun :=
  let kernel := chooseRow R A
  solve kernel (fun k => lower A (R-(k+1))) R

/-- Executable original-order coefficients; no matrix or polynomial input occurs. -/
def parity (A R : ℕ) : Fin R → ℤ :=
  let computed := parityArray A R
  fun j => coeff computed.coefficients j.rev.val

/-- The cached recurrence solves the actual upper translation matrix. -/
theorem upper_spec (A R : ℕ) :
    BinomialMatrix.U ℤ A R *ᵥ parity A R=fun s : Fin R => lower A s.val := by
  funext s
  let k := s.rev.val
  have hk : k<R := s.rev.isLt
  have he := solve_equation (chooseRow R A) (fun k => lower A (R-(k+1)))
    (by simpa only [Nat.choose_zero_right] using chooseRow_correct R A 0 (Nat.zero_le _)) R k hk
  have hs : R-(k+1)=s.val := by
    have hh := congrArg Fin.val (Fin.rev_rev s)
    simpa only [Fin.val_rev,k] using hh
  change (∑ j : Fin R,(if s.val≤ j.val then (A.choose (j.val-s.val) : ℤ) else 0)*
    coeff (parityArray A R).coefficients j.rev.val)=lower A s.val
  calc
    _ = ∑ i : Fin R,(if i.val≤ k then (A.choose (k-i.val) : ℤ)*coeff (parityArray A R).coefficients i.val else 0) := by
      rw [← Equiv.sum_comp Fin.revPerm (fun j : Fin R =>
        (if s.val≤ j.val then (A.choose (j.val-s.val) : ℤ) else 0)*
          coeff (parityArray A R).coefficients j.rev.val)]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Fin.revPerm_apply,Fin.rev_rev]
      have hi : i.val<R := i.isLt
      have hski : (s.val≤ i.rev.val) ↔ i.val≤ k := by simp only [Fin.val_rev,k]; omega
      by_cases h : i.val≤ k
      · rw [ite_eq_left (hski.mpr h),ite_eq_left h]
        have hd : i.rev.val-s.val=k-i.val := by simp only [Fin.val_rev,k]; omega
        rw [hd]
      · rw [ite_eq_right (fun hh => h (hski.mp hh)),ite_eq_right h,zero_mul]
    _ = ∑ i∈Finset.range (k+1),(A.choose (k-i) : ℤ)*coeff (parityArray A R).coefficients i :=
      sum_fin_cutoff R k hk (fun i : ℕ => (A.choose (k-i) : ℤ)*coeff (parityArray A R).coefficients i)
    _ = lower A s.val := by
      rw [← hs]
      convert he using 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [chooseRow_correct R A (k-i) (by omega)]
      rfl

/-- The acquired integer vector equals the source's previously implicit inverse solution. -/
theorem parity_eq (A R : ℕ) :
    parity A R=BinomialInterpolation.parityCoefficients (K:=ℤ) A R := by
  apply BinomialInterpolation.coefficients_unique (BinomialMatrix.B ℤ A R)
    (BinomialInterpolation.isUnit_det_binomial A R) (fun d => (-1 : ℤ)^(A+d.val))
  rw [BinomialMatrix.factorization,← Matrix.mulVec_mulVec,upper_spec,lower_spec]

end RiemannGaussian.SemiprimeBinomialExecution
