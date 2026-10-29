/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeFibreArrayExecution
import RiemannGaussian.SemiprimeHermiteArrayHeight

/-!
# Hermite reconstruction with acquired node arrays

Each node callback executes once and its entire work is retained. The finite
packet copy prevents any dependence on unspecified coefficients past J.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeAcquiredHermite
open scoped BigOperators
open Polynomial SemiprimeJetArray SemiprimeArrayOps SemiprimeFibreArrayExecution
open SemiprimeHermiteArrayHeight

/-- One retained scalar and its combined arithmetic/read/control ledger. -/
structure ScalarRun where
  /-- Actual output. -/
  value : ℚ
  /-- Callback work plus reconstruction and finite traversal work. -/
  work : ℕ

/-- Materialize exactly the requested coefficient prefix from the acquired array. -/
def packet (J : ℕ) (r : Run) : Array ℚ :=
  Array.ofFn (fun k : Fin J => coefficient r.jet.coefficients k)

theorem packet_correct (J : ℕ) (r : Run) (P : Polynomial ℚ) (h : Spec J r P) :
    asPolynomial (packet J r) = P %ₘ X^J := by
  ext k
  rw [asPolynomial_coeff, SemiprimeJetRecurrence.coeff_mod_X_pow]
  by_cases hk : k < J
  · rw [ite_eq_left hk]
    exact (ofFn_coefficient _ k hk).trans (h k hk)
  · rw [ite_eq_right hk]
    exact coefficient_zero (by simpa only [packet, Array.size_ofFn] using Nat.le_of_not_gt hk)

/-- Acquire once, copy the retained packet, then execute the intrinsic Hermite node. -/
def node {Q : ℕ} (J : ℕ) (acquire : Fin Q → Run) (t : Fin Q) : ScalarRun :=
  let acquired := acquire t
  let H := packet J acquired
  let out := hermiteNode H Q J t
  ⟨out.value, acquired.work + 2*J+1 + out.arithmetic + out.reads + 1⟩

theorem node_work {Q : ℕ} (J : ℕ) (acquire : Fin Q → Run) (t : Fin Q) :
    (node J acquire t).work ≤ (acquire t).work+2*J+2+2*nodeWork Q J := by
  have hs := hermiteNode_work (packet J (acquire t)) Q J t
  simp only [node]
  omega

/-- The callback is invoked once per loop step, with its work and output cached. -/
def sumFrom (f : ℕ → ScalarRun) : ℕ → ℕ → ScalarRun → ScalarRun
  | 0, _, acc => acc
  | fuel+1, start, acc =>
      let next := f start
      sumFrom f fuel (start+1) ⟨acc.value+next.value,acc.work+next.work+2⟩

theorem sumFrom_value (f : ℕ → ScalarRun) (fuel start : ℕ) (acc : ScalarRun) :
    (sumFrom f fuel start acc).value = acc.value+∑ i ∈ Finset.range fuel, (f (start+i)).value := by
  induction fuel generalizing start acc with
  | zero => simp [sumFrom]
  | succ fuel ih =>
    rw [sumFrom,ih,Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have he : (∑ i ∈ Finset.range fuel, (f (start+1+i)).value) =
        ∑ i ∈ Finset.range fuel, (f (start+(i+1))).value := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2; omega
    rw [he]
    ring

theorem sumFrom_work (f : ℕ → ScalarRun) (fuel start : ℕ) (acc : ScalarRun) :
    (sumFrom f fuel start acc).work = acc.work+∑ i ∈ Finset.range fuel, (f (start+i)).work+2*fuel := by
  induction fuel generalizing start acc with
  | zero => simp [sumFrom]
  | succ fuel ih =>
    rw [sumFrom,ih,Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have he : (∑ i ∈ Finset.range fuel, (f (start+1+i)).work) =
        ∑ i ∈ Finset.range fuel, (f (start+(i+1))).work := by
      apply Finset.sum_congr rfl
      intro i _
      congr 2; omega
    rw [he]
    omega

/-- All nodes are streamed; the callback computes each H internally. -/
def reconstruct (Q J : ℕ) (acquire : Fin Q → Run) : ScalarRun :=
  sumFrom (fun i => if hi : i<Q then node J acquire ⟨i,hi⟩ else ⟨0,0⟩) Q 0 ⟨0,0⟩

theorem reconstruct_value (Q J : ℕ) (acquire : Fin Q → Run) :
    (reconstruct Q J acquire).value = (hermite Q J (fun t => packet J (acquire t))).value := by
  rw [hermite_value_sum,reconstruct,sumFrom_value]
  simp only [zero_add,Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [dite_eq_left (Finset.mem_range.mp hi),node]

/-- Exact recovery with independently executed acquisition at every node. -/
theorem reconstruct_correct (Q J : ℕ) (hJ : 0<J) (P : Polynomial ℚ)
    (hP : P.natDegree<Q*J) (acquire : Fin Q → Run)
    (ha : ∀ t, Spec J (acquire t) (taylor ((t.val : ℚ)+1) P)) :
    (reconstruct Q J acquire).value = P.eval 0 := by
  rw [reconstruct_value]
  exact hermite_correct Q J hJ P hP _ (fun t => packet_correct J (acquire t) _ (ha t))

theorem reconstruct_work (Q J : ℕ) (acquire : Fin Q → Run) :
    (reconstruct Q J acquire).work ≤
      (∑ t, (acquire t).work)+Q*(2*J+4+2*nodeWork Q J) := by
  rw [reconstruct,sumFrom_work]
  simp only [Nat.zero_add]
  have he : (∑ i ∈ Finset.range Q,
      (if hi : i<Q then node J acquire ⟨i,hi⟩ else ⟨0,0⟩).work) =
      ∑ t : Fin Q, (node J acquire t).work := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [dite_eq_left (Finset.mem_range.mp hi)]
  rw [he]
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun t _ => node_work J acquire t)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul] at hs
  nlinarith

end RiemannGaussian.SemiprimeAcquiredHermite
