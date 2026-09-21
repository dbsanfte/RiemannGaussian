/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.PrimeNewtonMoments
import RiemannGaussian.PrimeCountEulerMoments
import RiemannGaussian.ZetaRieszSymmetricOperators
import RiemannGaussian.ZetaRieszBalancedCompanion

/-!
# Complete signed differential operators, with their cutoff scope explicit

The complete polynomial extensions have actual convergent Dirichlet sums.
These identities do not complete an arithmetic mask: the linear polynomial
agrees with the original coefficient only on LinearClass, whereas the
balanced three-prime boxes use the other adjacent-moment combination.
-/

namespace RiemannGaussian.ZetaRieszCompleteOperators
noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
open PrimeNewtonThree PrimeCountEuler ZetaRieszSymmetricOperators
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency
open ZetaRieszDominantAllocation
open Filter Topology

/-- The proposed complete reflected-linear three-prime operator. -/
theorem hasSum_linear_three {L : ℝ} (hL : L ≠ 0) (N : ℕ) {s : ℂ} (hs : 1<s.re) :
    HasSum (fun v => tripleWeight v*
      (((Real.log (tripleLabel v)/L)*(2*L-Real.log (tripleLabel v)) : ℝ) : ℂ)*
        zetaPrimeLogKernel N s (tripleLabel v))
      (2*((N+1 : ℕ) : ℂ)*threeMoment (N+1) s -
        (((N+1 : ℕ) : ℂ)*((N+2 : ℕ) : ℂ)/(L : ℂ))*threeMoment (N+2) s) := by
  have h := ((hasSum_threeMoment (N+1) hs).mul_left (2*((N+1 : ℕ) : ℂ))).sub
    ((hasSum_threeMoment (N+2) hs).mul_left
      (((N+1 : ℕ) : ℂ)*((N+2 : ℕ) : ℂ)/(L : ℂ)))
  apply h.congr_fun
  intro v
  have he := linear_three_kernel_operator hL N (tripleLabel v) s
  linear_combination (tripleWeight v)*he

/-- The complete extension of the actual pair-saturated polynomial. -/
theorem hasSum_balanced_three {L : ℝ} (hL : L ≠ 0) (N : ℕ) {s : ℂ} (hs : 1<s.re) :
    HasSum (fun v => tripleWeight v*
      (((Real.log (tripleLabel v)/L)*(Real.log (tripleLabel v)-L) : ℝ) : ℂ)*
        zetaPrimeLogKernel N s (tripleLabel v))
      ((((N+1 : ℕ) : ℂ)*((N+2 : ℕ) : ℂ)/(L : ℂ))*threeMoment (N+2) s -
        ((N+1 : ℕ) : ℂ)*threeMoment (N+1) s) := by
  have h := ((hasSum_threeMoment (N+2) hs).mul_left
    (((N+1 : ℕ) : ℂ)*((N+2 : ℕ) : ℂ)/(L : ℂ))).sub
    ((hasSum_threeMoment (N+1) hs).mul_left ((N+1 : ℕ) : ℂ))
  apply h.congr_fun
  intro v
  have he := balanced_three_kernel_operator hL N (tripleLabel v) s
  linear_combination (tripleWeight v)*he

/-- K at z=1, applied after the factorially normalized D moment. -/
def countMoment (N : ℕ) (s : ℂ) : ℂ :=
  deriv (fun z => factorialMoment z N s) 1

theorem hasSum_signedMoment (N : ℕ) {s : ℂ} (hs : 1<s.re) :
    HasSum (fun n => (μ n : ℂ)*zetaPrimeLogKernel N s n) (factorialMoment 1 N s) := by
  have h := (DirichletFamilyMoments.summable_moment (coefficient 1) id
    (fun _ hσ => summable_coefficient_feature (by norm_num) hσ) N hs).hasSum
  simpa only [factorialMoment, DirichletFamilyMoments.moment, coefficient,
    one_pow, mul_one, id_eq] using h

/-- The exact single-label D,K polynomial, retaining the Mobius sign. -/
theorem linear_kernel_operator {L : ℝ} (hL : L ≠ 0) (N n : ℕ) (s : ℂ) :
    (ZetaRieszReflectedLinear.linearCoefficient L n : ℂ)*zetaPrimeLogKernel N s n =
      -((N+1 : ℕ) : ℂ)*(((count n : ℂ)-1)*(μ n : ℂ)*zetaPrimeLogKernel (N+1) s n) +
        (((N+1 : ℕ) : ℂ)*((N+2 : ℕ) : ℂ)/(L : ℂ))*
          (((count n : ℂ)-2)*(μ n : ℂ)*zetaPrimeLogKernel (N+2) s n) := by
  have h1 := ZetaRieszHeadOrders.log_mul_kernel N n s
  have h2 := ZetaRieszHeadOrders.log_mul_kernel (N+1) n s
  rw [show N+1+1 = N+2 by omega] at h2
  simp only [ZetaRieszReflectedLinear.linearCoefficient, count_eq_card,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_intCast, Complex.ofReal_natCast]
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  field_simp [hLc]
  norm_num only [Nat.cast_add, Nat.cast_one] at h1 h2 ⊢
  linear_combination
    -(μ n : ℂ)*(((n.primeFactors.card : ℂ)-1)*(L : ℂ)-
      ((n.primeFactors.card : ℂ)-2)*(Real.log n : ℂ))*h1 +
    ((N : ℂ)+1)*(μ n : ℂ)*((n.primeFactors.card : ℂ)-2)*h2

/-- All prime-count classes are coupled before any norm. The conclusion
is an identity for the complete linear polynomial, not for the masked carrier. -/
theorem hasSum_linear_all_counts {L : ℝ} (hL : L ≠ 0) (N : ℕ) {s : ℂ} (hs : 1<s.re) :
    HasSum (fun n => (ZetaRieszReflectedLinear.linearCoefficient L n : ℂ)*
      zetaPrimeLogKernel N s n)
      (-((N+1 : ℕ) : ℂ)*(countMoment (N+1) s-factorialMoment 1 (N+1) s) +
        (((N+1 : ℕ) : ℂ)*((N+2 : ℕ) : ℂ)/(L : ℂ))*
          (countMoment (N+2) s-2*factorialMoment 1 (N+2) s)) := by
  have h := (((hasSum_countMoment (N+1) hs).sub (hasSum_signedMoment (N+1) hs)).mul_left
    (-((N+1 : ℕ) : ℂ))).add
    (((hasSum_countMoment (N+2) hs).sub ((hasSum_signedMoment (N+2) hs).mul_left 2)).mul_left
      (((N+1 : ℕ) : ℂ)*((N+2 : ℕ) : ℂ)/(L : ℂ)))
  apply h.congr_fun
  intro n
  rw [linear_kernel_operator hL]
  ring

/-- On a pair-saturated triple, replacing the residual coefficient by
the balanced polynomial costs exactly the already defined companion. -/
theorem residual_three_sub_polynomial (A : Finset ℕ) (N : ℕ) {L : ℝ} {n : ℕ}
    (hn : Squarefree n) (hk : n.primeFactors.card = 3) (ht : L ≤ Real.log n)
    (hmin : ∀ p ∈ n.primeFactors, Real.log n-L ≤ Real.log p) :
    residualCoefficient A L N n - (((Real.log n/L)*(Real.log n-L) : ℝ) : ℂ) =
      -assignedCoefficient A L N n := by
  rw [← coefficient_three_reflected_unit hn hk ht hmin, residualCoefficient,
    assignedCoefficient, Complex.ofReal_sub, Complex.ofReal_one]
  ring

/-- Quantitative transfer on any actual balanced pair-saturated triple
subband. This pays the allocation only; it does not complete the support. -/
theorem balanced_three_allocation_error_bound (A S : Finset ℕ) {L : ℝ} (hL : 0<L)
    (N : ℕ) (hS : S ⊆ literalWindow N)
    (hshape : ∀ n ∈ S, Squarefree n ∧ n.primeFactors.card = 3 ∧ L ≤ Real.log n ∧
      ∀ p ∈ n.primeFactors, Real.log n-L ≤ Real.log p)
    (hbal : ∀ n ∈ S, ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) →
      Real.log p ≤ Real.log n/2)
    (y : ℝ) {u : ℝ} (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16 : ℝ))) :
    ‖(u : ℂ)^(N+1) * ∑ n ∈ S,
      (residualCoefficient A L N n - (((Real.log n/L)*(Real.log n-L) : ℝ) : ℂ))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (4*((N : ℝ)+1)/3)*(sectorRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) := by
  have he : (∑ n ∈ S,
      (residualCoefficient A L N n - (((Real.log n/L)*(Real.log n-L) : ℝ) : ℂ))*
        zetaPrimeLogKernel N (3/2+Complex.I*y) n) =
      -(∑ n ∈ S, assignedCoefficient A L N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hs,hk,ht,hmin⟩ := hshape n hn
    rw [residual_three_sub_polynomial A N hs hk ht hmin, neg_mul]
  rw [he, mul_neg, norm_neg]
  exact ZetaRieszBalancedCompanion.balanced_companion_bound A S hL N hS hbal y hu huU

/-- The same comparison error is source-scale o(1) for arbitrary
moving heights, prime selections and supported balanced triple subsets. -/
theorem tendsto_balanced_three_allocation_error (A S : ℕ → Finset ℕ) (L y : ℕ → ℝ)
    (hL : ∀ N, 0<L N) (hS : ∀ N, S N ⊆ literalWindow N)
    (hshape : ∀ N n, n ∈ S N → Squarefree n ∧ n.primeFactors.card = 3 ∧ L N ≤ Real.log n ∧
      ∀ p ∈ n.primeFactors, Real.log n-L N ≤ Real.log p)
    (hbal : ∀ N n, n ∈ S N → ∀ p ∈ n.primeFactors, p ∈ A N → eligibleCofactor p (n/p) →
      Real.log p ≤ Real.log n/2)
    {u : ℝ} (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16 : ℝ))) :
    Tendsto (fun N => (u : ℂ)^(N+1) * ∑ n ∈ S N,
      (residualCoefficient (A N) (L N) N n -
        (((Real.log n/L N)*(Real.log n-L N) : ℝ) : ℂ))*
          zetaPrimeLogKernel N (3/2+Complex.I*y N) n) atTop (𝓝 0) := by
  have ht := (ZetaRieszBalancedCompanion.tendsto_balanced_companion A S L y hL hS hbal hu huU).neg
  simp only [neg_zero] at ht
  apply ht.congr'
  filter_upwards [] with N
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hs,hk,ht,hmin⟩ := hshape N n hn
  rw [residual_three_sub_polynomial (A N) N hs hk ht hmin, neg_mul]

/-- The literal surviving balanced triples with all pair products below
the physical cutoff. No original nondominant mask is completed here. -/
def balancedTripleBand (u : ℝ) (N K : ℕ) : Finset ℕ :=
  (nondominantBand u N K).filter (fun n => Squarefree n ∧ n.primeFactors.card = 3 ∧
    SquarefreeVaughanLogSource.length u N ≤ Real.log n ∧
      ∀ p ∈ n.primeFactors,
        Real.log n-SquarefreeVaughanLogSource.length u N ≤ Real.log p ∧
        Real.log p ≤ Real.log n/2)

theorem balancedTripleBand_subset_window (u : ℝ) (N K : ℕ) :
    balancedTripleBand u N K ⊆ literalWindow N := by
  intro n hn
  have hb := (Finset.mem_filter.mp hn).1
  have ho := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hb).1).1
  exact (mem_literalWindow N n).mpr (Finset.mem_filter.mp ho).2

/-- The allocation-removal estimate on an explicit part of the actual
nondominant carrier, with all arithmetic support hypotheses discharged. -/
theorem actual_balanced_three_allocation_error_bound (N K : ℕ) (y : ℝ)
    {u : ℝ} (hu : 0 ≤ u) (huU : u ≤ Real.exp (-(11/16 : ℝ))) :
    ‖(u : ℂ)^(N+1) * ∑ n ∈ balancedTripleBand u N K,
      (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n -
          (((Real.log n/SquarefreeVaughanLogSource.length u N)*
            (Real.log n-SquarefreeVaughanLogSource.length u N) : ℝ) : ℂ))*
              zetaPrimeLogKernel N (3/2+Complex.I*y) n‖ ≤
      (4*((N : ℝ)+1)/3)*(sectorRate^N*
        ((1509/1000 : ℝ)*zetaMoebiusLogMajorantMass (2049/2048))) := by
  apply balanced_three_allocation_error_bound _ _ (SquarefreeVaughanLogSource.length_pos u N)
    N (balancedTripleBand_subset_window u N K) ?_ ?_ y hu huU
  · intro n hn
    obtain ⟨hs,hk,ht,hp⟩ := (Finset.mem_filter.mp hn).2
    exact ⟨hs,hk,ht,fun p hpn => (hp p hpn).1⟩
  · intro n hn p hp _ _
    exact ((Finset.mem_filter.mp hn).2.2.2.2 p hp).2

end
end RiemannGaussian.ZetaRieszCompleteOperators
