/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszJointCountFloor

/-!
# Exact small-composite cancellation in the retained joint core

The smaller count budget and the already paid dominant-prime deletion
leave no Riesz response on a composite quadratic-head factor times two
primes. The complete small-factor divisor signs cancel before estimation.
No phase is removed, and the complementary signed core remains together.
-/

namespace RiemannGaussian.ZetaRieszJointSmoothFloor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszPrimeCountFrequency ZetaRieszJointAllocation ZetaRieszParityPacket
open ZetaRieszAnnulusJoint ZetaRieszWideOwnerAudit ZetaRieszJointCountFloor

/-- A composite cofactor has exact zero response between the two
single-prime saturation thresholds and the two-prime product threshold.
All four cutoff differences are retained before they vanish. -/
theorem coefficient_two_primes_composite_zero {p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hs : Squarefree (p*(q*a)))
    (ha1 : a ≠ 1) (hap : ¬a.Prime) {L : ℝ}
    (hpa : Real.log p+Real.log a ≤ L)
    (hqa : Real.log q+Real.log a ≤ L)
    (hpq : L ≤ Real.log p+Real.log q) :
    SquarefreeVaughanLogSource.coefficient L (p*(q*a)) = 0 := by
  have ha := hs.of_mul_right.of_mul_right
  have hpnd : ¬p ∣ q*a :=
    hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs)
  have hqnd : ¬q ∣ a :=
    hq.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs.of_mul_right)
  have hzero : VaughanLogAverage.riesz L (p*(q*a)) = 0 := by
    rw [ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpnd,
      ZetaSquarefreeRieszWindows.riesz_prime_mul L hq hqnd,
      ZetaSquarefreeRieszWindows.riesz_prime_mul (L-Real.log p) hq hqnd,
      ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 hap
        (show Real.log a ≤ L by linarith [Real.log_natCast_nonneg p]),
      ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 hap
        (show Real.log a ≤ L-Real.log q by linarith),
      ZetaRieszFixedCofactor.riesz_eq_zero_of_saturated ha ha1 hap
        (show Real.log a ≤ L-Real.log p by linarith),
      ZetaRieszFixedCofactor.riesz_eq_zero_of_nonpos
        (show L-Real.log p-Real.log q ≤ 0 by linarith)]
    ring
  simp [SquarefreeVaughanLogSource.coefficient,hzero]

/-- The tighter smooth-factor budget discharges the saturation tests
throughout the full core window below the proved 60.1% prime endpoint.
This is an exact coefficient cancellation, not a norm allowance. -/
theorem coefficient_two_primes_composite_zero_of_geometry {N p q a : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hs : Squarefree (p*(q*a)))
    (ha1 : a ≠ 1) (hap : ¬a.Prime) {L : ℝ}
    (hLlo : (5/4 : ℝ)*N ≤ L) (hLhi : L ≤ (7/5 : ℝ)*N)
    (halo : Real.log a ≤ (N : ℝ)/2048)
    (hlo : (39/20 : ℝ)*N ≤ Real.log (p*(q*a) : ℕ))
    (hhi : Real.log (p*(q*a) : ℕ) ≤ (203/100 : ℝ)*N)
    (hplog : Real.log p ≤ (601/1000 : ℝ)*Real.log (p*(q*a) : ℕ))
    (hqlog : Real.log q ≤ (601/1000 : ℝ)*Real.log (p*(q*a) : ℕ)) :
    SquarefreeVaughanLogSource.coefficient L (p*(q*a)) = 0 := by
  have hlog : Real.log (p*(q*a) : ℕ) = Real.log p+Real.log q+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero)
      (by exact_mod_cast hs.of_mul_right.ne_zero),Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast hs.of_mul_right.of_mul_right.ne_zero)]
    ring
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  apply coefficient_two_primes_composite_zero hp hq hs ha1 hap
  · linarith
  · linarith
  · linarith

/-- The independently reduced core supplies all count, window and
prime-share restrictions used in the following signed inequalities. -/
theorem reduced_core_geometry (j : ℕ) (hj : 64 ≤ j) {u : ℝ} {n : ℕ}
    (hnB : n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount (j-9))).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p)))
    (hcoeff : residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n ≠ 0) :
    Squarefree n ∧ n.primeFactors.card < dyadicPrimeCount (j-9) ∧
      (39/20 : ℝ)*dyadicMomentOrder j < Real.log n ∧
        Real.log n ≤ (203/100 : ℝ)*dyadicMomentOrder j ∧
          ∀ p ∈ n.primeFactors, Real.log p < (601/1000 : ℝ)*Real.log n := by
  have hn : Squarefree n := by
    by_contra h
    exact hcoeff (by simp [residualCoefficient,SquarefreeVaughanLogSource.coefficient,h])
  have hK : dyadicPrimeCount (j-9) ≤ dyadicPrimeCount j := by
    unfold dyadicPrimeCount
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hcore := (Finset.mem_filter.mp hnB).1
  have hcore' : n ∈ coreBand u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
    rw [coreBand_count_filter _ _ _ _ hK] at hcore
    exact (Finset.mem_filter.mp hcore).1
  have hall := ZetaRieszJointDominantFloor.Refined.remaining_prime_log_lt
    j (by omega) u (Finset.mem_filter.mpr ⟨hcore',(Finset.mem_filter.mp hnB).2⟩) hcoeff
  have hc : n.primeFactors.card < dyadicPrimeCount (j-9) := by
    have hnon := (Finset.mem_filter.mp (Finset.mem_filter.mp hcore).1).1
    have hret := (Finset.mem_sdiff.mp hnon).1
    have horig := (Finset.mem_sdiff.mp hret).1
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp horig).1).2.2
  exact ⟨hn,hc,(Finset.mem_filter.mp hcore).2.1,(Finset.mem_filter.mp hcore).2.2,hall⟩

/-- The original reduced core, after the paid dominant-prime deletion,
has exactly zero residual coefficient on every two-prime label with a
composite quadratic-head cofactor. The original allocation is unchanged. -/
theorem residual_two_primes_composite_zero (j : ℕ) (hj : 64 ≤ j)
    {u : ℝ} (hu : 1/2 ≤ u)
    (hL : (5/4 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {n a p q : ℕ}
    (hnB : n ∈ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount (j-9))).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p)))
    (hp : p.Prime) (hq : q.Prime) (he : n = p*(q*a))
    (ha1 : a ≠ 1) (hap : ¬a.Prime)
    (ha : ∀ r ∈ a.primeFactors, r ≤ (dyadicMomentOrder j)^2) :
    residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n = 0 := by
  by_contra hcoeff
  obtain ⟨hn,hc,hwlo,hwhi,hall⟩ := reduced_core_geometry j hj hnB hcoeff
  have hdiv : a ∣ n := by rw [he]; exact dvd_mul_of_dvd_right (dvd_mul_left a q) p
  have hsmall := reduced_smooth_divisor_log_le j hj hn hdiv hc ha
  have hN : 2 ≤ dyadicMomentOrder j := by
    have h := four_le_dyadicPrimeCount j
    unfold dyadicMomentOrder
    nlinarith
  have hlen : SquarefreeVaughanLogSource.length u (dyadicMomentOrder j) ≤
      (7/5 : ℝ)*dyadicMomentOrder j := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu hN
    have hlog : 2*Real.log 2 ≤ (7/5 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg _))
  have hpdiv : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp,by rw [he]; exact dvd_mul_right _ _,hn.ne_zero⟩
  have hqdiv : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hq,by rw [he]; exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _,hn.ne_zero⟩
  have hz := coefficient_two_primes_composite_zero_of_geometry hp hq (he ▸ hn) ha1 hap
    hL hlen hsmall (he ▸ hwlo.le) (he ▸ hwhi) (he ▸ (hall p hpdiv).le)
    (he ▸ (hall q hqdiv).le)
  apply hcoeff
  rw [residualCoefficient,he,hz,mul_zero]

/-- The zero class may be removed from any retained selection before
observing it, with its arbitrary complex weight and phase unchanged.
This spends no allowance and does not complete a cofactor. -/
theorem sum_without_two_primes_composite (j : ℕ) (hj : 64 ≤ j)
    {u : ℝ} (hu : 1/2 ≤ u)
    (hL : (5/4 : ℝ)*dyadicMomentOrder j ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    (S : Finset ℕ)
    (hS : S ⊆ (coreBand u (dyadicMomentOrder j) (dyadicPrimeCount (j-9))).filter (fun n =>
      ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
        ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u (dyadicMomentOrder j) ∧
          eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p)))
    (f : ℕ → ℂ) :
    (∑ n ∈ S.filter (fun n => ¬∃ a p q : ℕ, a ≠ 1 ∧ ¬a.Prime ∧
        (∀ r ∈ a.primeFactors, r ≤ (dyadicMomentOrder j)^2) ∧
          p.Prime ∧ q.Prime ∧ n = p*(q*a)),
      residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*f n) =
    ∑ n ∈ S, residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
      (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*f n := by
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hout
  have hex : ∃ a p q : ℕ, a ≠ 1 ∧ ¬a.Prime ∧
      (∀ r ∈ a.primeFactors, r ≤ (dyadicMomentOrder j)^2) ∧
        p.Prime ∧ q.Prime ∧ n = p*(q*a) := by
    by_contra hh
    exact hout (Finset.mem_filter.mpr ⟨hn,hh⟩)
  obtain ⟨a,p,q,ha1,hap,ha,hp,hq,he⟩ := hex
  rw [residual_two_primes_composite_zero j hj hu hL (hS hn) hp hq he ha1 hap ha,zero_mul]

/-- A direct signed inequality for the WHOLE original core after the
count and large-prime errors already proved small, followed by the exact
small-composite cancellation. The complete remaining signed sum stays
inside one observation. No separate-component floor is assumed. -/
theorem eventually_re_core_ge_without_large_and_composites {u : ℝ}
    (hu : 1/2 ≤ u) (hU : u ≤ radiusCeiling) :
    ∀ᶠ j : ℕ in atTop, ∀ y : ℝ,
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        ∑ n ∈ ((coreBand u (dyadicMomentOrder j) (dyadicPrimeCount (j-9))).filter (fun n =>
          ¬(Squarefree n ∧ 1 < n ∧ ¬n.Prime ∧
            ∃ p ∈ n.primeFactors, p ∈ intermediatePrimes u (dyadicMomentOrder j) ∧
              eligibleCofactor p (n/p) ∧ (601/1000 : ℝ)*Real.log n ≤ Real.log p))).filter
                (fun n => ¬∃ a p q : ℕ, a ≠ 1 ∧ ¬a.Prime ∧
                  (∀ r ∈ a.primeFactors, r ≤ (dyadicMomentOrder j)^2) ∧
                    p.Prime ∧ q.Prime ∧ n = p*(q*a)),
          residualCoefficient (intermediatePrimes u (dyadicMomentOrder j))
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) (dyadicMomentOrder j) n*
              zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n).re-
        ((32*radiusCeiling*Real.log 2)*(dyadicMomentOrder j : ℝ)*
          (49999/50000 : ℝ)^dyadicMomentOrder j+
          2*zetaMoebiusLogMajorantMass (1+1/262144)*
            Real.exp (-(dyadicMomentOrder j : ℝ)/1000000)) ≤
      ((u : ℂ)^(dyadicMomentOrder j+1)*
        coreResponse u y (dyadicMomentOrder j) (dyadicPrimeCount j)).re := by
  have hlen := ZetaRieszMaskSupport.eventually_length_lower
    (show 0 < u by linarith) (hU.trans radius_lt_source.le)
  filter_upwards [eventually_ge_atTop 64,eventually_re_core_ge_smaller_count,
    tendsto_dyadicMomentOrder.eventually hlen] with j hj hc hL
  intro y
  have hN : 320 ≤ dyadicMomentOrder j := by
    have h := four_le_dyadicPrimeCount j
    unfold dyadicMomentOrder
    nlinarith
  have hd := ZetaRieszJointDominantFloor.Refined.re_core_ge_without_large
    (dyadicMomentOrder j) (dyadicPrimeCount (j-9)) hN y hu hU
  have he := sum_without_two_primes_composite j hj hu hL _ (Finset.Subset.refl _)
    (fun n => zetaPrimeLogKernel (dyadicMomentOrder j) (3/2+Complex.I*y) n)
  rw [← he] at hd
  have hb := hc u y (by linarith) hU
  linarith

/-- The total allowance in the whole-core comparison tends to zero.
Exact small-composite cancellation adds no term to that allowance. -/
theorem tendsto_reduction_allowance :
    Tendsto (fun j => (32*radiusCeiling*Real.log 2)*(dyadicMomentOrder j : ℝ)*
        (49999/50000 : ℝ)^dyadicMomentOrder j+
      2*zetaMoebiusLogMajorantMass (1+1/262144)*
        Real.exp (-(dyadicMomentOrder j : ℝ)/1000000)) atTop (𝓝 0) := by
  simpa only [Function.comp_def,add_zero] using tendsto_count_allowance.add
    (ZetaRieszJointDominantFloor.Refined.tendsto_allowance.comp tendsto_dyadicMomentOrder)

end
end RiemannGaussian.ZetaRieszJointSmoothFloor
