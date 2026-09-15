/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReflectedCarrier

/-!
# Uniform central product phases at arbitrary precision

One eventual threshold controls both actual prime-product errors throughout the central orders, including the derivative successor and complete complementary head leg.
-/

namespace RiemannGaussian.ZetaRieszCentralProductPhase
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszMatchedMiddle ZetaRieszWiderMatched ZetaRieszReflectedCarrier
open ZetaRieszPrimeCompletionRate ZetaRieszPrimeCompletionPhase

/-- Both prime-product errors vanish uniformly over the actual central
orders. The complete product phases are retained, at arbitrary precision,
under the explicit original exposed-zero assumptions. -/
theorem eventually_central_product_errors (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k ∈ centralOrders N,
      ‖weightedFinite (3 / 2 - rho.1.re) rho.1.im N k *
          weightedFinite (3 / 2 - rho.1.re) rho.1.im N (N + 1 - k) -
            (analyticZetaZeroMultiplicity rho : ℂ) ^ 2‖ ≤ ε ∧
      ‖weightedFinite (3 / 2 - rho.1.re) rho.1.im N (k + 1) *
          weightedComplete (3 / 2 - rho.1.re) rho.1.im (N + 1 - k) -
            (analyticZetaZeroMultiplicity rho : ℂ) ^ 2‖ ≤ ε := by
  apply ZetaRieszInfinitePhysical.eventually_forall_of_all_selections
  intro f
  let k : ℕ → ℕ := fun N => if f N ∈ centralOrders N then f N else N / 2
  have hk : ∀ᶠ N : ℕ in atTop,
      ZetaRieszWiderMatched.completionOrder N (k N) ∧
      ZetaRieszWiderMatched.completionOrder N (N + 1 - k N) ∧
      ZetaRieszWiderMatched.completionOrder N (k N + 1) := by
    filter_upwards [eventually_ge_atTop 256] with N hN
    by_cases hf : f N ∈ centralOrders N
    · have hh := (Finset.mem_filter.mp (centralOrders_subset_wider N hf)).2
      simpa only [k, if_pos hf] using hh
    · simp only [k, if_neg hf, ZetaRieszWiderMatched.completionOrder]
      omega
  have hfk := tendsto_wider_weighted_finite rho hrho hexposed huh k
    (hk.mono fun _ h => h.1)
  have hfl := tendsto_wider_weighted_finite rho hrho hexposed huh (fun N => N + 1 - k N)
    (hk.mono fun _ h => h.2.1)
  have hfks := tendsto_wider_weighted_finite rho hrho hexposed huh (fun N => k N + 1)
    (hk.mono fun _ h => h.2.2)
  have hlt : Tendsto (fun N => N + 1 - k N) atTop atTop := by
    refine tendsto_atTop.2 (fun b => ?_)
    filter_upwards [hk, eventually_ge_atTop (3 * b)] with N hkN hN
    have hh := hkN.2.1.1
    omega
  have hcl := (tendsto_weighted_complete rho hrho hexposed).comp hlt
  have hp := ((hfk.mul hfl).sub_const ((analyticZetaZeroMultiplicity rho : ℂ) ^ 2)).norm
  have hh := ((hfks.mul hcl).sub_const ((analyticZetaZeroMultiplicity rho : ℂ) ^ 2)).norm
  simp only [← pow_two, neg_sq, sub_self, norm_zero] at hp hh
  filter_upwards [hp.eventually (eventually_lt_nhds hε),
    hh.eventually (eventually_lt_nhds hε)] with N hpN hhN
  intro hf
  constructor
  · simpa only [weightedFinite, k, if_pos hf] using hpN.le
  · simpa only [weightedFinite, weightedComplete, Function.comp_def, k, if_pos hf] using hhN.le

end
end RiemannGaussian.ZetaRieszCentralProductPhase
