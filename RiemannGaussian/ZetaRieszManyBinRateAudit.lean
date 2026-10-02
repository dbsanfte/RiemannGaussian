/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszManyBinCorrelationAudit

/-!
# The quantitative rate needed from a joined many-bin estimate

Even an inverse power of N PER occupied bin gives at most an
exp(-O(log(N)^2)) discount on the literal logarithmic bin grid. It cannot
pay the source-growing positive envelope for any fixed u>1/2. This audits
that proposed envelope, not the true signed carrier: a joint estimate of
its actual phase and funding weights is still possible and still open.

The exact energy identity below measures how much signed off-diagonal
cancellation a proposed diagonal-relative exponential saving requires.
It does not assert that the actual carrier has that saving.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Filter Topology Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszManyBinRateAudit
open ZetaRieszCofactorPhaseEnergy

/-- Any fixed logarithmic polynomial discount is sublinear in the order. -/
theorem logarithmic_discount_per_order (A B : ℝ) :
    Tendsto (fun N : ℕ =>
      (A*log ((N : ℝ)+1)^2+B*log ((N : ℝ)+1))/((N : ℝ)+1))
      atTop (nhds 0) := by
  have hn : Tendsto (fun N : ℕ => (N : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have h2 := (tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hn
  have h1 := (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hn
  simpa only [Function.comp_def,one_mul,add_zero,pow_one,mul_zero,add_zero,
    mul_div_assoc,add_div] using (h2.const_mul A).add (h1.const_mul B)

/-- The discounted envelope eventually still has a strictly positive
linear exponent. Constants and finite starts are not optimized. -/
theorem eventually_discounted_exponent_lower {g : ℝ} (hg : 0 < g) (A B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      g*(N : ℝ)/2-g/2 ≤
        g*N-A*log ((N : ℝ)+1)^2-B*log ((N : ℝ)+1) := by
  filter_upwards [(logarithmic_discount_per_order A B).eventually_lt_const
    (show (0 : ℝ) < g/2 by positivity)] with N hN
  have h := (div_lt_iff₀ (show (0 : ℝ) < (N : ℝ)+1 by positivity)).mp hN
  nlinarith only [h]

/-- A superpolynomial exp(-A log(N+1)^2) improvement still cannot close
the positive source envelope. No lower bound for the actual carrier is
inferred from this limit. -/
theorem discounted_source_tendsto {u : ℝ} (hu : 1/2 < u) (A B : ℝ) :
    Tendsto (fun N : ℕ =>
      exp (-A*log ((N : ℝ)+1)^2-B*log ((N : ℝ)+1))*(2*u)^N)
      atTop atTop := by
  have hg : 0 < log (2*u) := log_pos (by linarith)
  have ht : Tendsto (fun N : ℕ => log (2*u)*(N : ℝ)/2-log (2*u)/2)
      atTop atTop := by
    have h := tendsto_atTop_add_const_right atTop (-log (2*u)/2)
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (show 0 < log (2*u)/2 by positivity))
    convert h using 1
    ext N
    ring_nf
  have hl := tendsto_atTop_mono' atTop (eventually_discounted_exponent_lower hg A B) ht
  convert tendsto_exp_atTop.comp hl using 1
  ext N
  have hp : (2*u)^N = exp ((N : ℝ)*log (2*u)) := by
    rw [exp_nat_mul,exp_log (show (0 : ℝ) < 2*u by linarith)]
  rw [hp,← exp_add]
  congr 1
  ring_nf

/-- An inverse N^c discount PER bin, stronger than a fixed contraction,
is still insufficient on the existing at-most 2log(N+1)+1 grid. -/
theorem per_bin_power_source_tendsto {u c : ℝ} (hu : 1/2 < u) (hc : 0 ≤ c)
    (b : ℕ → ℕ) (hb : ∀ N,(b N : ℝ) ≤ 2*log ((N : ℝ)+1)+1) (d : ℕ) :
    Tendsto (fun N : ℕ =>
      ((N : ℝ)+1)^(-c*(b N : ℝ))*(2*u)^N/((N : ℝ)+1)^d)
      atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_
    (discounted_source_tendsto hu (2*c) (c+(d : ℝ)))
  filter_upwards [] with N
  have hx : 0 < (N : ℝ)+1 := by positivity
  have hxlog : 0 ≤ log ((N : ℝ)+1) :=
    log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hb' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hb N) hc) hxlog
  have he : exp (-(2*c)*log ((N : ℝ)+1)^2-(c+(d : ℝ))*log ((N : ℝ)+1)) ≤
      exp ((-c*(b N : ℝ)-(d : ℝ))*log ((N : ℝ)+1)) := by
    apply exp_le_exp.mpr
    nlinarith only [hb']
  have hm := mul_le_mul_of_nonneg_right he
    (show 0 ≤ (2*u)^N by positivity)
  convert hm using 1
  have hp : ((N : ℝ)+1)^d = exp ((d : ℝ)*log ((N : ℝ)+1)) := by
    rw [exp_nat_mul,exp_log hx]
  rw [rpow_def_of_pos hx,hp,mul_div_right_comm,← exp_sub]
  congr 1
  ring_nf

/-- Apply the rate test to the ACTUAL occupied-bin definition, with its
original prime-log support bound. This is still a positive-envelope audit,
not an assertion that the signed population attains that envelope. -/
theorem actual_bin_power_source_tendsto {u c : ℝ} (hu : 1/2 < u) (hc : 0 ≤ c)
    (a : ℕ → ℕ) (H : ℕ → ℝ)
    (hlog : ∀ N,∀ p ∈ (a N).primeFactors,log p ≤ 4*H N)
    (hH : ∀ N,H N ≤ 4*((N : ℝ)+1)) (d : ℕ) :
    Tendsto (fun N : ℕ =>
      ((N : ℝ)+1)^(-c*((ZetaRieszFewBinCoverFloor.cofactorBins N (a N)).card : ℝ))*
        (2*u)^N/((N : ℝ)+1)^d) atTop atTop := by
  apply per_bin_power_source_tendsto hu hc
    (fun N => (ZetaRieszFewBinCoverFloor.cofactorBins N (a N)).card) ?_ d
  intro N
  have hs := ZetaRieszFewBinCoverFloor.cofactorBins_subset_available (N := N) (hlog N)
  have hcard : ((ZetaRieszFewBinCoverFloor.cofactorBins N (a N)).card : ℝ) ≤
      (ZetaRieszFewBinCoverFloor.availableBins N (H N)).card := by
    exact_mod_cast Finset.card_le_card hs
  exact hcard.trans (ZetaRieszFewBinCoverFloor.availableBins_card_le (hH N))

/-- The same obstruction holds along the ORIGINAL dyadic moment orders,
so passing to that cofinal sequence does not repair this envelope rate. -/
theorem dyadic_discounted_source_tendsto {u : ℝ} (hu : 1/2 < u) (A B : ℝ) :
    Tendsto (fun j : ℕ =>
      let N := ZetaRieszPrimeCountFrequency.dyadicMomentOrder j
      exp (-A*log ((N : ℝ)+1)^2-B*log ((N : ℝ)+1))*(2*u)^N)
      atTop atTop :=
    (discounted_source_tendsto hu A B).comp
      ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder

/-- Explicit bounds for the amplitude growth exponent at the current
outer radius. A squared-energy ratio needs twice this exponent, before
polynomial factors. These are envelope rates, not carrier estimates. -/
theorem radius_growth_bounds :
    1/10001 ≤ log (2*ZetaRieszWideOwnerAudit.radiusCeiling) ∧
      log (2*ZetaRieszWideOwnerAudit.radiusCeiling) ≤ 1/10000 := by
  constructor
  · have h := one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 2*ZetaRieszWideOwnerAudit.radiusCeiling by
        norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    exact h
  · have h := log_le_sub_one_of_pos
      (show (0 : ℝ) < 2*ZetaRieszWideOwnerAudit.radiusCeiling by
        norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
    norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at h ⊢
    exact h

/-- Expand the SAME whole-prefix energy into its diagonal and all
ordered off-diagonal terms. Every phase/mask/funding weight remains w. -/
theorem phaseEnergy_eq_diagonal_cross (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) :
    phaseEnergy X S w f =
      (∑ k ∈ activeCutoffs X f,
        (∑ n ∈ S,(w n*sharp k n)^2)/(k : ℝ))+
      (∑ k ∈ activeCutoffs X f,
        (∑ n ∈ S,∑ m ∈ S.erase n,
          (w n*sharp k n)*(w m*sharp k m))/(k : ℝ)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← add_div]
  congr 1
  rw [correlation,pow_two,Finset.sum_mul_sum]
  simp only [← Finset.sum_add_distrib,pow_two]
  apply Finset.sum_congr rfl
  intro n hn
  exact (Finset.sum_erase_add S
    (fun m => (w n*sharp k n)*(w m*sharp k m)) hn).symm.trans (by ring_nf)

/-- A proposed saving relative to the diagonal is EXACTLY a required
negative cross-term estimate. Occupancy is not substituted for it. -/
theorem energy_saving_iff_cross (X : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ) (r : ℝ) :
    phaseEnergy X S w f ≤
        r*(∑ k ∈ activeCutoffs X f,(∑ n ∈ S,(w n*sharp k n)^2)/(k : ℝ)) ↔
      (∑ k ∈ activeCutoffs X f,
        (∑ n ∈ S,∑ m ∈ S.erase n,
          (w n*sharp k n)*(w m*sharp k m))/(k : ℝ)) ≤
        -(1-r)*(∑ k ∈ activeCutoffs X f,(∑ n ∈ S,(w n*sharp k n)^2)/(k : ℝ)) := by
  rw [phaseEnergy_eq_diagonal_cross]
  constructor <;> intro h <;> linarith only [h]

end RiemannGaussian.ZetaRieszManyBinRateAudit
