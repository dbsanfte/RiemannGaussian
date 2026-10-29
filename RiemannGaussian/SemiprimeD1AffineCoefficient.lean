/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-! # Acquired single coefficient of an actual affine-row product
Only rows, literal coefficient lists and the acquired exponent tuple are runtime
inputs. No polynomial, coefficient table or desired coefficient answer executes.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1AffineCoefficient

/-- Actual affine row base and finite mode-coefficient list. -/
structure Row (R : Type*) where
  /-- Coefficient of the constant monomial. -/
  base : R
  /-- Mode coefficients in literal0-based order. -/
  coefficients : List R

/-- Cached generic-ring result with separate ring-operation and native control work. -/
structure Run (R : Type*) where
  /-- Actual acquired scalar. -/
  value : R
  /-- All generic-ring additions and multiplications. -/
  ringOps : ℕ
  /-- Actual tuple/list reads, copies and finite native control. -/
  control : ℕ

/-- Combined scoped report, not a full physical-ring-word clock. -/
def Run.work {R : Type*} (out : Run R) : ℕ := out.ringOps+out.control

/-- Actual cached-list read and its finite traversal report. -/
def read {R : Type*} (default : R) : List R→ℕ→R×ℕ
  | [],_ => (default,1)
  | v::_,0 => (v,3)
  | _::vs,i+1 => let tail:=read default vs i;(tail.1,tail.2+3)

/-- Actual list lookup has the literal original value. -/
theorem read_value {R : Type*} (default : R) (vs : List R) (i : ℕ) :
    (read default vs i).1=vs.getD i default := by
  induction vs generalizing i with
  | nil => simp [read]
  | cons v vs ih => cases i <;> simp [read,ih]

/-- Actual full tuple copy, used at the decreased coordinate's suffix. -/
def copyTuple : List ℕ→List ℕ×ℕ
  | [] => ([],1)
  | b::bs => let tail:=copyTuple bs;(b::tail.1,tail.2+3)

/-- Acquired tuple copies preserve every original exponent. -/
theorem copyTuple_value (beta : List ℕ) : (copyTuple beta).1=beta := by
  induction beta with
  | nil => rfl
  | cons b bs ih => simp [copyTuple,ih]

/-- Decrement one actual mode exponent; NativeNat subtraction is explicit metadata. -/
def decrement : List ℕ→ℕ→List ℕ×ℕ
  | [],_ => ([],1)
  | b::bs,0 => let tail:=copyTuple bs;((b-1)::tail.1,tail.2+4)
  | b::bs,i+1 => let tail:=decrement bs i;(b::tail.1,tail.2+3)

/-- No branch alters the acquired tuple shape. -/
theorem decrement_length (beta : List ℕ) (i : ℕ) : (decrement beta i).1.length=beta.length := by
  induction beta generalizing i with
  | nil => rfl
  | cons b bs ih => cases i <;> simp [decrement,copyTuple_value,ih]

/-- Exact original exponent at EVERY coordinate after the literal decrement. -/
theorem decrement_getD (beta : List ℕ) (i j : ℕ) :
    (decrement beta i).1.getD j 0=if j=i then beta.getD j 0-1 else beta.getD j 0 := by
  induction beta generalizing i j with
  | nil => simp [decrement]
  | cons b bs ih =>
    cases i with
    | zero => cases j <;> simp [decrement,copyTuple_value]
    | succ i =>
      cases j with
      | zero => simp [decrement]
      | succ j =>
        simpa only [decrement,List.getD_cons_succ,Nat.succ.injEq] using ih i j

/-- The copied tuple denotes precisely exponent subtraction, not an advised target. -/
theorem decrement_finsupp (beta : List ℕ) (i : ℕ) :
    (decrement beta i).1.toFinsupp=beta.toFinsupp-Finsupp.single i 1 := by
  ext j
  simp only [List.toFinsupp_apply,decrement_getD,Finsupp.tsub_apply,Finsupp.single_apply]
  by_cases h : j=i
  · subst j;simp
  · simp [h,Ne.symm h]

/-- Actual all-zero scan used at the row recursion's terminal leaf. -/
def zeroTest : List ℕ→Bool×ℕ
  | [] => (true,1)
  | b::bs => let tail:=zeroTest bs;(decide (b=0)&&tail.1,tail.2+3)

/-- A literal tuple head is zero separately from its entire tail. -/
theorem cons_finsupp_zero (b : ℕ) (bs : List ℕ) :
    (b::bs).toFinsupp=0 ↔ b=0 ∧ bs.toFinsupp=0 := by
  constructor
  · intro h
    constructor
    · have hz:=congrArg (fun f : ℕ→₀ℕ => f 0) h
      simpa only [List.toFinsupp_apply,List.getD_cons_zero,Finsupp.zero_apply] using hz
    · ext i
      have hz:=congrArg (fun f : ℕ→₀ℕ => f (i+1)) h
      simpa only [List.toFinsupp_apply,List.getD_cons_succ,Finsupp.zero_apply] using hz
  · rintro ⟨hb,ht⟩
    ext i
    cases i with
    | zero => simpa only [List.toFinsupp_apply,List.getD_cons_zero,Finsupp.zero_apply] using hb
    | succ i =>
      have hz:=congrArg (fun f : ℕ→₀ℕ => f i) ht
      simpa only [List.toFinsupp_apply,List.getD_cons_succ,Finsupp.zero_apply] using hz

/-- Terminal leaf scan is exactly the zero exponent test. -/
theorem zeroTest_value (beta : List ℕ) : (zeroTest beta).1=true ↔ beta.toFinsupp=0 := by
  induction beta with
  | nil => simp [zeroTest]
  | cons b bs ih => simp [zeroTest,ih,cons_finsupp_zero]

/-- Cache all branch reports, summing actual scalars and retaining every clock. -/
def sumRuns {R : Type*} [AddMonoid R] : List (Run R)→Run R
  | [] => ⟨0,0,1⟩
  | r::rs =>
    let tail:=sumRuns rs
    ⟨r.value+tail.value,r.ringOps+tail.ringOps+1,r.control+tail.control+3⟩

/-- Actual branch accumulation is the sum of its acquired branch values. -/
theorem sumRuns_value {R : Type*} [AddMonoid R] (rs : List (Run R)) :
    (sumRuns rs).value=(rs.map Run.value).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [sumRuns,List.map_cons,List.sum_cons,ih]

/-- Recursion visits only the requested coefficient's actual predecessor tuples.
Each branch is acquired ONCE into the finite branch-report list. -/
def evaluate {R : Type*} [CommRing R] (K : ℕ) : List (Row R)→List ℕ→Run R
  | [],beta =>
    let test:=zeroTest beta
    ⟨if test.1 then 1 else 0,0,test.2+2⟩
  | row::rows,beta =>
    let base:=evaluate K rows beta
    let branches:=(List.range K).map (fun i =>
      let exponent:=read 0 beta i
      if exponent.1=0 then (⟨0,0,exponent.2+3⟩ : Run R)
      else
        let target:=decrement beta i
        let child:=evaluate K rows target.1
        let coeff:=read 0 row.coefficients i
        ⟨coeff.1*child.value,child.ringOps+1,
          exponent.2+target.2+child.control+coeff.2+5⟩)
    let total:=sumRuns branches
    ⟨row.base*base.value+total.value,base.ringOps+total.ringOps+2,
      base.control+total.control+10*K+8⟩

/-- Actual affine row's mathematical polynomial; never executed by evaluate. -/
noncomputable def rowPolynomial {R : Type*} [CommRing R] (K : ℕ) (row : Row R) : MvPolynomial ℕ R :=
  MvPolynomial.C row.base+
    ((List.range K).map (fun i => MvPolynomial.C (row.coefficients.getD i 0)*MvPolynomial.X i)).sum

/-- Literal product of the original finite affine rows. -/
noncomputable def polynomial {R : Type*} [CommRing R] (K : ℕ) (rows : List (Row R)) : MvPolynomial ℕ R :=
  (rows.map (rowPolynomial K)).prod

/-- The additive coefficient identity, avoiding deprecated polynomial aliases. -/
theorem coefficient_add {R : Type*} [CommRing R] (p q : MvPolynomial ℕ R) (e : ℕ→₀ℕ) :
    (p+q).coeff e=p.coeff e+q.coeff e := (MvPolynomial.lcoeff R e).map_add p q

/-- One selected linear mode contributes exactly the decremented requested exponent. -/
theorem mode_coefficient {R : Type*} [CommRing R] (c : R) (i : ℕ)
    (p : MvPolynomial ℕ R) (beta : List ℕ) :
    (MvPolynomial.C c*MvPolynomial.X i*p).coeff beta.toFinsupp=
      if beta.getD i 0=0 then 0 else c*p.coeff (decrement beta i).1.toFinsupp := by
  rw [mul_assoc,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_X_mul']
  simp [decrement_finsupp]

/-- Finite row-mode sum has the exact coefficient recurrence. -/
theorem modes_coefficient {R : Type*} [CommRing R] (indices : List ℕ) (row : Row R)
    (p : MvPolynomial ℕ R) (beta : List ℕ) :
    (((indices.map (fun i => MvPolynomial.C (row.coefficients.getD i 0)*MvPolynomial.X i)).sum)*p).coeff
      beta.toFinsupp=
      (indices.map (fun i => if beta.getD i 0=0 then 0 else
        row.coefficients.getD i 0*p.coeff (decrement beta i).1.toFinsupp)).sum := by
  induction indices with
  | nil => simp
  | cons i indices ih =>
    simp only [List.map_cons,List.sum_cons,add_mul,coefficient_add,mode_coefficient,ih]

/-- The acquired single coefficient is EXACT for every original tuple/row list.
No dense polynomial or target coefficient answer is a runtime input. -/
theorem evaluate_value {R : Type*} [CommRing R] (K : ℕ) (rows : List (Row R)) (beta : List ℕ) :
    (evaluate K rows beta).value=(polynomial K rows).coeff beta.toFinsupp := by
  induction rows generalizing beta with
  | nil =>
    simp only [evaluate,polynomial,List.map_nil,List.prod_nil,MvPolynomial.coeff_one]
    by_cases h : beta.toFinsupp=0
    · simp [h,(zeroTest_value beta).mpr h]
    · have hn : (zeroTest beta).1≠true := fun hz => h ((zeroTest_value beta).mp hz)
      simp [Ne.symm h,hn]
  | cons row rows ih =>
    simp only [evaluate,polynomial,List.map_cons,List.prod_cons,rowPolynomial,add_mul,
      coefficient_add,MvPolynomial.coeff_C_mul,modes_coefficient,read_value,sumRuns_value,
      List.map_map,Function.comp_def]
    rw [ih beta]
    congr 1
    congr 1
    apply List.map_congr_left
    intro i _
    by_cases h : beta.getD i 0=0
    · simp only [h,ite_true]
    · simp only [h,ite_false]
      exact congrArg (fun x => row.coefficients.getD i 0*x) (ih (decrement beta i).1)

/-- Finite acquired mode-tuple interpretation for the actual weighted menu. -/
noncomputable def betaF (K : ℕ) (beta : List ℕ) : Fin K→₀ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => beta.getD i.val 0)

/-- Finite exponent interpretation reads the original acquired list entry. -/
theorem betaF_apply (K : ℕ) (beta : List ℕ) (i : Fin K) : betaF K beta i=beta.getD i.val 0 := rfl

/-- Actual menu shape gives exact list recovery, with no exponent-value advice. -/
theorem betaF_inverse (K : ℕ) (beta : List ℕ) (h : beta.length=K) :
    List.ofFn (fun i : Fin K => betaF K beta i)=beta := by
  subst K
  have hf : (fun i : Fin beta.length => betaF beta.length beta i)=
      (fun i : Fin beta.length => beta[i.val]) := by
    funext i
    rw [betaF_apply]
    exact List.getD_eq_getElem beta 0 i.isLt
  rw [hf]
  exact List.ofFn_getElem

/-- Nat-mode polynomial exponents are the literal embedding of the acquiredFinK tuple. -/
theorem betaF_embDomain (K : ℕ) (beta : List ℕ) (h : beta.length=K) :
    Finsupp.embDomain (Fin.valEmbedding : Fin K↪ℕ) (betaF K beta)=beta.toFinsupp := by
  ext j
  by_cases hj : j<K
  · let i : Fin K:=⟨j,hj⟩
    change (Finsupp.embDomain (Fin.valEmbedding : Fin K↪ℕ) (betaF K beta)) ((Fin.valEmbedding : Fin K↪ℕ) i)=_
    rw [Finsupp.embDomain_apply_self,betaF_apply,List.toFinsupp_apply]
  · have hn : j∉Set.range (Fin.valEmbedding : Fin K↪ℕ) := by
      rintro ⟨i,hi⟩
      exact hj (hi ▸ i.isLt)
    rw [Finsupp.embDomain_of_notMem_range _ _ _ hn]
    symm
    exact List.toFinsupp_apply_le beta j (by omega)

end RiemannGaussian.SemiprimeD1AffineCoefficient
