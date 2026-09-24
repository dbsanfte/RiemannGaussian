/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszZeroParityOrders

/-!
# Summed exceptional factorial allocations

The exact multinomial weights, rather than individual low-order atoms,
have a uniform exponential lower tail. Every selected prime has a fixed
positive log share. No prime-phase theorem is used in this estimate.
-/

namespace RiemannGaussian.ZetaRieszParityOrderTail
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszSkewAllocation ZetaRieszParityPacket
open ZetaRieszPrimeEndpoint ZetaRieszWideOwnerAudit ZetaRieszAnnulusJoint

/-- Every base factorial order is at least N/200. The least-prime
derivative has one additional order, so also meets this lower cut. -/
def GoodAllocation {ι : Type*} (S : Finset ι) (N : ℕ) (d : ι → ℕ) : Prop :=
  ∀ p ∈ S, N ≤ 200*d p

/-- The exact complementary multinomial mass before any rectangle
restriction; imposing that restriction can only reduce this mass. -/
def badAllocationMass {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ) (N : ℕ) : ℝ :=
  ∑ d ∈ (Finset.piAntidiag S (N+1)).filter (fun d => ¬GoodAllocation S N d),
    allocationWeight S x d

theorem allocationWeight_nonneg {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ p ∈ S, 0 ≤ x p) (d : ι → ℕ) : 0 ≤ allocationWeight S x d :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun p hp => pow_nonneg (hx p hp) _))

/-- The one-coordinate tilt is an exact finite multinomial identity. -/
theorem allocation_tilt {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ) {p : ι}
    (hp : p ∈ S) (M : ℕ) (q : ℝ) :
    (∑ d ∈ Finset.piAntidiag S M, q^(d p)*allocationWeight S x d) =
      (q*x p+∑ i ∈ S.erase p, x i)^M := by
  let y : ι → ℝ := fun i => (if i = p then q else 1)*x i
  have hw (d : ι → ℕ) : q^(d p)*allocationWeight S x d = allocationWeight S y d := by
    unfold allocationWeight
    simp only [y, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow,
      Finset.prod_ite_eq', if_pos hp]
    ring
  simp_rw [hw]
  rw [show (∑ d ∈ Finset.piAntidiag S M, allocationWeight S y d) =
      (∑ i ∈ S, y i)^M from (Finset.sum_pow_eq_sum_piAntidiag S y M).symm]
  congr 1
  rw [← Finset.sum_erase_add S y hp]
  have he : (∑ i ∈ S.erase p, y i) = ∑ i ∈ S.erase p, x i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [y, (Finset.mem_erase.mp hi).1]
  rw [he]
  simp [y, add_comm]

/-- A literal lower tail at N/200, uniformly for every prime share at
least 3/250. The exponent 1/400 exceeds the source growth budget. -/
theorem single_bad_mass_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ p ∈ S, 0 ≤ x p) (hsum : ∑ p ∈ S, x p = 1)
    {p : ι} (hp : p ∈ S) (hpx : (3/250 : ℝ) ≤ x p) (N : ℕ) :
    (∑ d ∈ (Finset.piAntidiag S (N+1)).filter (fun d => 200*d p < N),
      allocationWeight S x d) ≤ Real.exp (-(N : ℝ)/400) := by
  have hxp1 : x p ≤ 1 := by rw [← hsum]; exact Finset.single_le_sum hx hp
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hhalf : (1/2 : ℝ) = Real.exp (-Real.log 2) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  let B : ℝ := Real.exp ((N : ℝ)/200*Real.log 2)
  have htilt (d : ι → ℕ) (hd : 200*d p < N) : 1 ≤ B*(1/2 : ℝ)^(d p) := by
    have hdc : 200*(d p : ℝ) < N := by exact_mod_cast hd
    dsimp only [B]
    rw [hhalf, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith
  have hw := allocationWeight_nonneg S x hx
  have he : (1/2 : ℝ)*x p+∑ i ∈ S.erase p, x i = 1-x p/2 := by
    have h := Finset.sum_erase_add S x hp
    rw [hsum] at h
    linarith
  have hbase0 : 0 ≤ 1-x p/2 := by linarith
  have hbase : 1-x p/2 ≤ Real.exp (-(3/500 : ℝ)) := by
    linarith [Real.add_one_le_exp (-(3/500 : ℝ))]
  calc
    _ ≤ ∑ d ∈ (Finset.piAntidiag S (N+1)).filter (fun d => 200*d p < N),
        B*((1/2 : ℝ)^(d p)*allocationWeight S x d) := by
      apply Finset.sum_le_sum
      intro d hd
      nlinarith [mul_le_mul_of_nonneg_right (htilt d (Finset.mem_filter.mp hd).2) (hw d)]
    _ ≤ ∑ d ∈ Finset.piAntidiag S (N+1),
        B*((1/2 : ℝ)^(d p)*allocationWeight S x d) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => mul_nonneg (Real.exp_pos _).le (mul_nonneg (by positivity) (hw d)))
    _ = B*(1-x p/2)^(N+1) := by rw [← Finset.mul_sum, allocation_tilt S x hp, he]
    _ ≤ B*Real.exp (-(3/500 : ℝ))^(N+1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase0 hbase _) (Real.exp_pos _).le
    _ ≤ _ := by
      dsimp only [B]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlo : Real.log 2 ≤ (7/10 : ℝ) := by linarith [Real.log_two_lt_d9]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (α := ℝ) N)]

/-- The finite union bound retains the complete multinomial weights. -/
theorem badAllocationMass_le {ι : Type*} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ p ∈ S, (3/250 : ℝ) ≤ x p) (hsum : ∑ p ∈ S, x p = 1) (N : ℕ) :
    badAllocationMass S x N ≤ (S.card : ℝ)*Real.exp (-(N : ℝ)/400) := by
  have hx0 (p : ι) (hp : p ∈ S) : 0 ≤ x p := by linarith [hx p hp]
  have hw := allocationWeight_nonneg S x hx0
  have hsingle := fun p hp => single_bad_mass_le S x hx0 hsum hp (hx p hp) N
  calc
    _ ≤ ∑ p ∈ S, ∑ d ∈ (Finset.piAntidiag S (N+1)).filter (fun d => 200*d p < N),
        allocationWeight S x d := by
      simp only [badAllocationMass, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro d _
      by_cases hg : GoodAllocation S N d
      · rw [if_neg (not_not.mpr hg)]
        exact Finset.sum_nonneg (fun p _ => by split_ifs <;> first | exact hw d | exact le_rfl)
      · rw [if_pos hg]
        simp only [GoodAllocation, not_forall] at hg
        obtain ⟨p, hp, hbad⟩ := hg
        have hh : 200*d p < N := Nat.lt_of_not_ge hbad
        exact (show allocationWeight S x d =
          (if 200*d p < N then allocationWeight S x d else 0) from (if_pos hh).symm).trans_le
            (Finset.single_le_sum (f := fun i =>
              if 200*d i < N then allocationWeight S x d else 0)
              (fun i _ => by split_ifs <;> first | exact hw d | exact le_rfl) hp)
    _ ≤ ∑ _p ∈ S, Real.exp (-(N : ℝ)/400) := Finset.sum_le_sum hsingle
    _ = _ := by simp

/-- Each prime in the literal box has the stated log share; their
normalized shares sum exactly to one by squarefreeness. -/
theorem fullParityBox_shares {n : ℕ} (h : FullParityBox n) :
    (∀ p ∈ n.primeFactors, (3/250 : ℝ) ≤ Real.log p/Real.log n) ∧
      (∑ p ∈ n.primeFactors, Real.log p/Real.log n) = 1 := by
  have hn : 0 < Real.log n := Real.log_pos (by exact_mod_cast h.nontrivial)
  constructor
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hr := Nat.minFac_prime h.nontrivial.ne'
    apply (le_div_iff₀ hn).mpr
    exact h.least_lower.trans (Real.log_le_log (by exact_mod_cast hr.pos)
      (by exact_mod_cast Nat.minFac_le_of_dvd hpp.two_le (Nat.dvd_of_mem_primeFactors hp)))
  · rw [← Finset.sum_div, ← CoprimeEulerPhase.squarefree_log_eq_prime_sum h.squarefree,
      div_self hn.ne']

/-- All individual low orders together have exponentially small
factorial mass on every literal packet label, independently of phase. -/
theorem fullParityBox_bad_mass {n : ℕ} (h : FullParityBox n) (N : ℕ) :
    badAllocationMass n.primeFactors (fun p => Real.log p/Real.log n) N ≤
      39*Real.exp (-(N : ℝ)/400) := by
  obtain ⟨hx, hs⟩ := fullParityBox_shares h
  exact (badAllocationMass_le _ _ hx hs N).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast fullParityBox_count_le h) (Real.exp_pos _).le)

end
end RiemannGaussian.ZetaRieszParityOrderTail
