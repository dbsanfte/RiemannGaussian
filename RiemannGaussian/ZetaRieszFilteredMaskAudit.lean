/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszHalfPlaneModes
import RiemannGaussian.ZetaRieszParityShareError

/-!
# The total-moment filter does not filter prime legs independently

The literal polynomial kernel shifts the total moment, with the finite
Riesz masks held fixed. On a geometric mixed mode its multiplier is the
filter evaluated at the mixed inverse denominator, not the product of
its evaluations at the separate inverse denominators.

Under a rightmost hypothesis the actual pole-jet filter is nonzero at
every real denominator strictly between 1/2 and the source radius. A
pole mixed with a same-real-part zero at a compensating ordinate can have
exactly such a denominator. No existence of that second zero is asserted.
This audits a false filtering inference, not the actual packet's limit.
-/

namespace RiemannGaussian.ZetaRieszFilteredMaskAudit
noncomputable section
open Filter Set Topology
open scoped BigOperators Classical ComplexConjugate
open ZetaRieszHalfPlaneModes ZetaRieszParityPacket ZetaRieszJointAllocation

/-- The original packet with just its total log kernel replaced by the
repository's polynomial kernel. All finite masks are still at order N. -/
def filteredFullParityPacket (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) : ℂ :=
  ∑ n ∈ coreBand u N K, (fullParitySelection u N K n : ℂ)*
    (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
      (SquarefreeVaughanLogSource.length u N) N n *
      zetaPrimeFilterKernel P N (3/2+Complex.I*y) n)

/-- The requested literal pole-jet specialization, with no decay claim. -/
def poleJetFilteredFullParityPacket (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (N K : ℕ) : ℂ :=
  filteredFullParityPacket (zetaRightHalfPoleJetFilter rho hrho)
    (sourceRadius rho) rho.1.im N K

theorem filterKernel_eq_total_shift (P : Polynomial ℂ) (N n : ℕ) (s : ℂ) :
    zetaPrimeFilterKernel P N s n =
      ∑ k ∈ P.support, P.coeff k*zetaPrimeLogKernel (N+k) s n := by
  rw [zetaPrimeFilterKernel_nat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  unfold zetaPrimeLogKernel
  ring

/-- Exact bridge: only the kernel order shifts. The masks, moving
length and allocation still use N. This is not a product of leg filters. -/
theorem filteredPacket_eq_frozen_total_filter (P : Polynomial ℂ) (u y : ℝ) (N K : ℕ) :
    filteredFullParityPacket P u y N K = zetaMomentSequenceFilter P
      (fun k => ∑ n ∈ coreBand u N K, (fullParitySelection u N K n : ℂ)*
        (residualCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
          (SquarefreeVaughanLogSource.length u N) N n *
          zetaPrimeLogKernel k (3/2+Complex.I*y) n)) N := by
  unfold filteredFullParityPacket zetaMomentSequenceFilter Polynomial.sum
  simp_rw [filterKernel_eq_total_shift, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- A mixed mode is multiplied by P at its own denominator. Killing
either individual denominator says nothing about this evaluation. -/
theorem total_filter_mixed_mode (P : Polynomial ℂ) (z₁ z₂ : ℂ) (q : ℝ) (N : ℕ) :
    zetaMomentSequenceFilter P (fun n => (mix z₁ z₂ q)⁻¹^(n+1)) N =
      (mix z₁ z₂ q)⁻¹^(N+1)*P.eval ((mix z₁ z₂ q)⁻¹) :=
  zetaMomentSequenceFilter_geometric P _ N

private theorem lagrange_eval_ne_zero {ι : Type*} (S : Finset ι) (v : ι → ℂ)
    (hv : Function.Injective v) (i : ι) {x : ℂ} (hx : ∀ j ∈ S, x ≠ v j) :
    (Lagrange.basis S v i).eval x ≠ 0 := by
  rw [Lagrange.basis, Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  obtain ⟨hji, hjS⟩ := Finset.mem_erase.mp hj
  have hij : v i-v j ≠ 0 := sub_ne_zero.mpr (fun h => hji (hv h).symm)
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X]
  exact mul_ne_zero (inv_ne_zero hij) (sub_ne_zero.mpr (hx j hjS))

/-- The exact local zero isolator has no root at a positive real
denominator between the pole's real part and a rightmost zero's radius. -/
theorem zeroFilter_eval_inner_ne_zero (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (hright : Rightmost rho) {a : ℝ}
    (ha : 1/2 < a) (hau : a < sourceRadius rho) :
    (zetaRightHalfZeroModeFilter rho hrho).eval ((a : ℂ)⁻¹) ≠ 0 := by
  unfold zetaRightHalfZeroModeFilter adaptiveZetaZeroModeFilter
  apply lagrange_eval_ne_zero _ _ (neg_injective.comp inv_injective)
  intro j hj he
  change (a : ℂ)⁻¹ = -j⁻¹ at he
  rcases Finset.mem_insert.mp hj with rfl | hj
  · simp only [inv_neg, neg_neg] at he
    have hh := congrArg Complex.re (inv_injective he)
    norm_num at hh
    linarith
  · rw [← inv_neg] at he
    have hh := congrArg Complex.re (inv_injective he)
    have hb := local_direct_re_ge_of_rightmost hright (zetaRightHalfDiscParameter rho hrho) hj
    simp only [Complex.ofReal_re] at hh
    linarith

/-- The actual pole-jet lift also cannot annihilate any such interior
real mixed denominator. No polynomial coefficient is numerically chosen. -/
theorem poleJetFilter_eval_inner_ne_zero (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (hright : Rightmost rho) {a : ℝ}
    (ha : 1/2 < a) (hau : a < sourceRadius rho) :
    (zetaRightHalfPoleJetFilter rho hrho).eval ((a : ℂ)⁻¹) ≠ 0 := by
  have hpole {b : ℝ} (hb : 1/2 < b) :
      (b : ℂ)⁻¹ ≠ ((3/2+Complex.I*(rho.1.im : ℂ))-1)⁻¹ := by
    intro he
    have hh := congrArg Complex.re (inv_injective he)
    norm_num at hh
    linarith
  have hu : 1/2 < sourceRadius rho := by
    dsimp [sourceRadius]
    linarith [NontrivialZetaZero.re_lt_one rho]
  simp only [zetaRightHalfPoleJetFilter, zetaPoleJetLift, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr (hpole hu)))
    (mul_ne_zero (sub_ne_zero.mpr (hpole ha))
      (zeroFilter_eval_inner_ne_zero rho hrho hright ha hau))

/-- Disk exposure makes the obstruction to total-order isolation even
sharper: the exact filter has no root at any inner mixed denominator
whose real part exceeds the pole's real part. No rightmost hypothesis
is needed. The finite local zero roots are all outside that disk. -/
theorem poleJetFilter_eval_exposed_inner_ne_zero (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      sourceRadius rho < ‖direct rho tau‖)
    {w : ℂ} (hwre : 1/2 < w.re) (hwnorm : ‖w‖ < sourceRadius rho) :
    (zetaRightHalfPoleJetFilter rho hrho).eval w⁻¹ ≠ 0 := by
  have hpole : w⁻¹ ≠ ((3/2+Complex.I*(rho.1.im : ℂ))-1)⁻¹ := by
    intro he
    have hh := congrArg Complex.re (inv_injective he)
    norm_num at hh
    linarith
  have hsource : ((sourceRadius rho : ℝ) : ℂ)⁻¹ ≠
      ((3/2+Complex.I*(rho.1.im : ℂ))-1)⁻¹ := by
    intro he
    have hh := congrArg Complex.re (inv_injective he)
    norm_num [sourceRadius] at hh
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hzero : (zetaRightHalfZeroModeFilter rho hrho).eval w⁻¹ ≠ 0 := by
    unfold zetaRightHalfZeroModeFilter adaptiveZetaZeroModeFilter
    apply lagrange_eval_ne_zero _ _ (neg_injective.comp inv_injective)
    intro j hj he
    change w⁻¹ = -j⁻¹ at he
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp only [inv_neg, neg_neg] at he
      apply hpole
      convert he using 1
      congr 1
      ring
    · rw [← inv_neg] at he
      obtain ⟨tau, ht⟩ := local_support_actual_zero rho (zetaRightHalfDiscParameter rho hrho) hj
      have hw : w = direct rho tau := (inv_injective he).trans ht.symm
      by_cases htr : tau = rho
      · rw [hw, htr, direct_self, Complex.norm_real,
          Real.norm_of_nonneg (sourceRadius_pos rho).le] at hwnorm
        exact (lt_irrefl _ hwnorm)
      · rw [hw] at hwnorm
        exact (not_lt_of_ge (hexposed tau htr).le) hwnorm
  simp only [zetaRightHalfPoleJetFilter, zetaPoleJetLift, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hsource))
    (mul_ne_zero (sub_ne_zero.mpr hpole) hzero)

/-- The pole keeps the evaluation ordinate. The displayed real mixture
requires exactly the compensating zero ordinate, which is explicit here. -/
theorem pole_same_real_mix (rho tau : NontrivialZetaZero) {q : ℝ} (hq : q ≠ 1)
    (hre : tau.1.re = rho.1.re) (him : tau.1.im = rho.1.im/(1-q)) :
    mix ((3/2+Complex.I*(rho.1.im : ℂ))-1) (direct rho tau) q =
      ((q/2+(1-q)*sourceRadius rho : ℝ) : ℂ) := by
  have hq' : 1-q ≠ 0 := sub_ne_zero.mpr hq.symm
  apply Complex.ext
  · norm_num [mix, direct, sourceRadius, hre]
    ring
  · norm_num [mix, direct, him]
    field_simp
    ring

/-- Rightmost alone does not algebraically eliminate the pole/zero
mixed denominator, even with the actual total-moment pole-jet filter.
The second zero and its ordinate relation are hypotheses, not an asserted
counterexample to zeta or to the literal filtered packet theorem. -/
theorem pole_same_real_resonance_not_killed (rho tau : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (hright : Rightmost rho)
    (hre : tau.1.re = rho.1.re) (him : tau.1.im = rho.1.im/(1-43/80)) :
    let w := mix ((3/2+Complex.I*(rho.1.im : ℂ))-1) (direct rho tau) (43/80)
    ‖w‖ < sourceRadius rho ∧ (zetaRightHalfPoleJetFilter rho hrho).eval w⁻¹ ≠ 0 := by
  dsimp only
  rw [pole_same_real_mix rho tau (by norm_num) hre him]
  have hu : 1/2 < sourceRadius rho := by
    dsimp [sourceRadius]
    linarith [NontrivialZetaZero.re_lt_one rho]
  have ha : (1/2 : ℝ) < (43/80)/2+(1-43/80)*sourceRadius rho := by linarith
  have hau : (43/80)/2+(1-43/80)*sourceRadius rho < sourceRadius rho := by linarith
  exact ⟨by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact hau,
    poleJetFilter_eval_inner_ne_zero rho hrho hright ha hau⟩

/-- The failed bridge is an exact algebraic inequality for the actual
repository filter. The total-mode multiplier is nonzero whereas the
product of the individual pole/zero multipliers is zero. -/
theorem total_filter_ne_legwise_on_pole_mix (rho tau : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re) (hright : Rightmost rho)
    (hre : tau.1.re = rho.1.re) (him : tau.1.im = rho.1.im/(1-43/80)) :
    let P := zetaRightHalfPoleJetFilter rho hrho
    let c := (3/2+Complex.I*(rho.1.im : ℂ))-1
    P.eval ((mix c (direct rho tau) (43/80))⁻¹) ≠
      P.eval c⁻¹*P.eval ((direct rho tau)⁻¹) := by
  dsimp only
  rw [(zetaRightHalfPoleJetFilter_pole_jet rho hrho).1, zero_mul]
  exact (pole_same_real_resonance_not_killed rho tau hrho hright hre him).2

/-- Exact numerical geometry of the proposed pole/rightmost mixture.
The compensating ordinate condition is still required in the actual
complex-mode theorem above. -/
theorem pole_mix_radius_exact :
    (43/80 : ℝ)/2+(1-43/80)*ZetaRieszParityMaskedPhaseAudit.radius = 800037/1600000 := by
  norm_num [ZetaRieszParityMaskedPhaseAudit.radius]

theorem pole_mix_growth_bounds :
    (1/19000 : ℝ) < Real.log (ZetaRieszParityMaskedPhaseAudit.radius/(800037/1600000)) ∧
      Real.log (ZetaRieszParityMaskedPhaseAudit.radius/(800037/1600000)) < 1/18000 := by
  have hp : 0 < ZetaRieszParityMaskedPhaseAudit.radius/(800037/1600000) := by
    norm_num [ZetaRieszParityMaskedPhaseAudit.radius]
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hu := Real.log_le_sub_one_of_pos hp
  norm_num [ZetaRieszParityMaskedPhaseAudit.radius] at hl hu ⊢
  constructor <;> linarith

end
end RiemannGaussian.ZetaRieszFilteredMaskAudit
