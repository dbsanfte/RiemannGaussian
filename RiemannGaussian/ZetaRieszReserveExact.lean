/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReserveWeights
import RiemannGaussian.ZetaRieszRetainedCarrier

/-!
# Exact positive reserve and the remaining signed source

The whole reserved wing is evaluated, rather than bounded order by order.
Subtracting its exact limit strengthens the deficit that an independent
arithmetic floor would have to contradict. That floor remains open.
-/

namespace RiemannGaussian.ZetaRieszWingReserve
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszMatchedMiddle ZetaRieszPrimeCompletionPhase
open ZetaRieszPrimeCountFrequency

/-- Both products in the literal reserve converge uniformly, including the derivative successor. -/
theorem eventually_reserve_product_errors (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ reserveOrders N,
      ‖weightedComplete (3 / 2 - rho.1.re) rho.1.im k *
          weightedFinite (3 / 2 - rho.1.re) rho.1.im N (N + 1 - k) -
            (analyticZetaZeroMultiplicity rho : ℂ) ^ 2‖ ≤ ε ∧
      ‖weightedComplete (3 / 2 - rho.1.re) rho.1.im k *
          weightedFinite (3 / 2 - rho.1.re) rho.1.im N (N + 1 - k + 1) -
            (analyticZetaZeroMultiplicity rho : ℂ) ^ 2‖ ≤ ε := by
  apply ZetaRieszInfinitePhysical.eventually_forall_of_all_selections
  intro f
  let k : ℕ → ℕ := fun N => if f N ∈ reserveOrders N then f N else N / 2
  have hk : ∀ᶠ N : ℕ in atTop, N ≤ 3 * k N ∧
      N ≤ 3 * (N + 1 - k N) ∧ 5 * (N + 1 - k N + 1) ≤ 3 * N := by
    filter_upwards [eventually_ge_atTop 320] with N hN
    by_cases hf : f N ∈ reserveOrders N
    · obtain ⟨_, _, _, _, hk, hl, hls⟩ := reserveOrders_bounds hN hf
      simpa only [k, if_pos hf] using And.intro hk (And.intro hl hls)
    · simp only [k, if_neg hf]
      omega
  have hkt : Tendsto k atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [hk, eventually_ge_atTop (3 * b)] with N hkN hN
    have := hkN.1
    omega
  have hc := (tendsto_weighted_complete rho hrho hexposed).comp hkt
  have hf := tendsto_reserve_weighted_finite rho hrho hexposed huh
    (fun N => N + 1 - k N) (hk.mono fun N h => ⟨h.2.1, by omega⟩)
  have hfs := tendsto_reserve_weighted_finite rho hrho hexposed huh
    (fun N => N + 1 - k N + 1) (hk.mono fun N h => ⟨by omega, h.2.2⟩)
  have hp := ((hc.mul hf).sub_const ((analyticZetaZeroMultiplicity rho : ℂ) ^ 2)).norm
  have hs := ((hc.mul hfs).sub_const ((analyticZetaZeroMultiplicity rho : ℂ) ^ 2)).norm
  simp only [← pow_two, neg_sq, sub_self, norm_zero] at hp hs
  filter_upwards [hp.eventually (eventually_lt_nhds hε),
    hs.eventually (eventually_lt_nhds hε)] with N hpN hsN
  intro hmem
  constructor
  · simpa only [weightedComplete, Function.comp_def, k, if_pos hmem] using hpN.le
  · simpa only [weightedComplete, Function.comp_def, k, if_pos hmem] using hsN.le

/-- The reserve's positive mass after its exact endpoint subtraction. -/
def reserveMass (u : ℝ) : ℝ :=
  Real.log (19 / 17) + (1 - 1 / (-2 * u * Real.log u)) * Real.log (15 / 13)

/-- The complete reserved wing has an exact complex limit, with no triangle inequality on its endpoint subtraction. -/
theorem tendsto_reserve_exact (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      reserve (3 / 2 - rho.1.re) rho.1.im N) atTop
      (𝓝 ((analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
        (reserveMass (3 / 2 - rho.1.re) : ℂ))) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp only [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hup : u ≤ 3 / 5 := ZetaRieszHeadAdaptive.annular_radius_le_three_fifths
    (huh.trans reserve_radius_lt_annular)
  have hp := FiniteWeightedUniformConvergence.tendsto_nonneg_weighted_sum
    reserveOrders reservePairWeight
    (fun N k => weightedComplete u rho.1.im k * weightedFinite u rho.1.im N (N + 1 - k))
    (b := (analyticZetaZeroMultiplicity rho : ℂ) ^ 2)
    (Eventually.of_forall fun N k _ => by unfold reservePairWeight; positivity)
    tendsto_sum_reservePairWeight (fun ε hε =>
      (eventually_reserve_product_errors rho hrho hexposed huh hε).mono
        fun N h k hk => (h k hk).1)
  have hh := FiniteWeightedUniformConvergence.tendsto_nonneg_weighted_sum
    reserveOrders (reserveHeadWeight u)
    (fun N k => weightedComplete u rho.1.im k * weightedFinite u rho.1.im N (N + 1 - k + 1))
    (b := (analyticZetaZeroMultiplicity rho : ℂ) ^ 2)
    (Eventually.of_forall fun N k _ => by
      have hL := SquarefreeVaughanLogSource.length_pos u N
      unfold reserveHeadWeight
      positivity)
    (tendsto_sum_reserveHeadWeight hu hup) (fun ε hε =>
      (eventually_reserve_product_errors rho hrho hexposed huh hε).mono
        fun N h k hk => (h k hk).2)
  have h := hp.sub hh
  have he : ((Real.log (15 / 13) + Real.log (19 / 17) : ℝ) : ℂ) *
      (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 -
      ((Real.log (15 / 13) / (-2 * u * Real.log u) : ℝ) : ℂ) *
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 =
      (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 * (reserveMass u : ℂ) := by
    unfold reserveMass
    push_cast
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 320] with N hN
  rw [← Finset.sum_sub_distrib]
  dsimp only [reserve]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨_, hkp, hkM, hlp, _, _, _⟩ := reserveOrders_bounds hN hk
  rw [normalized_wingAtom_eq u rho.1.im N k hu.ne' hkp hkM hlp]
  have he : (k : ℂ) + ((N + 1 - k : ℕ) : ℂ) = ((N + 1 : ℕ) : ℂ) := by
    exact_mod_cast (show k + (N + 1 - k) = N + 1 by omega)
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hkp.ne'
  have hl0 : ((N + 1 - k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hlp.ne'
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hL0 : (SquarefreeVaughanLogSource.length u N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (SquarefreeVaughanLogSource.length_pos u N).ne'
  unfold reservePairWeight reserveHeadWeight
  push_cast
  push_cast at he
  rw [← he]
  field_simp
  ring

end
end RiemannGaussian.ZetaRieszWingReserve
