/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReflectedCarrier
import RiemannGaussian.ZetaRieszLowHeadCorrection

/-!
# The complete head and tapered arithmetic carrier

All selected completion errors vanish at their actual product scale. The remaining carrier retains the three-prime and higher-prime sums, central block, tapered wing and negative complete head.
-/

namespace RiemannGaussian.ZetaRieszCompletedCarrier
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedPrimeMoments ZetaRieszPrimePairConvolution ZetaRieszAnnulusJoint
open ZetaRieszReflectedCompletion ZetaRieszReflectedCarrier
open ZetaRieszLowHeadCorrection

/-- The actual low head is an instance of the array interface whose
two completion corrections have now been paid. -/
theorem lowHead_eq_headArray (u y : ℝ) (N : ℕ) :
    lowHead u y N = headArray u y N (lowHeadOrders N)
      (fun k => finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y)) := rfl

/-- The complete low-head product retains its negative sign, derivative
successor and full complementary prime moment. -/
def completeLowHead (u y : ℝ) (N : ℕ) : ℂ :=
  headArray u y N (lowHeadOrders N)
    (fun k => ordinaryPrimeMoment k (3 / 2 + Complex.I * y))

/-- Both actual low-head completion corrections vanish with their
original product weights, under the explicit exposed-zero premises. -/
theorem tendsto_lowHead_sub_complete (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (lowHead (3 / 2 - rho.1.re) rho.1.im N -
        completeLowHead (3 / 2 - rho.1.re) rho.1.im N)) atTop (nhds 0) := by
  exact tendsto_finite_headArray_sub_complete_exposed rho hrho hexposed huh lowHeadOrders
    (Eventually.of_forall (fun N k hk => (Finset.mem_filter.mp hk).2))

/-- Every negative completed head order retained outside the central
matched subset, with its two original selections kept disjoint. -/
def completeHeadOrders (N : ℕ) : Finset ℕ := lowHeadOrders N ∪ lowerWing N

/-- The completed low head and reflected head have no order overlap. -/
theorem lowHead_disjoint_lowerWing (N : ℕ) : Disjoint (lowHeadOrders N) (lowerWing N) := by
  apply Finset.disjoint_left.mpr
  intro k hk hl
  have hh := (Finset.mem_filter.mp hk).2
  have hm := (Finset.mem_filter.mp hl).1
  have hp := (Finset.mem_filter.mp hm).2.1
  omega

/-- The entire surviving negative complete-head product, with no
boundary term, prime phase or factorial shift suppressed. -/
def completeHead (u y : ℝ) (N : ℕ) : ℂ :=
  headArray u y N (completeHeadOrders N)
    (fun k => ordinaryPrimeMoment k (3 / 2 + Complex.I * y))

/-- The retained complete-head orders form one exact initial interval;
its two former selections introduce no gap or overlap. -/
theorem completeHeadOrders_eq_range (N : ℕ) (hN : 256 ≤ N) :
    completeHeadOrders N = Finset.range ((15 * N + 64) / 32 + 1) := by
  ext k
  simp only [completeHeadOrders, lowHeadOrders, lowerWing, ZetaRieszPairOrders.middleOrders,
    Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  omega

/-- Every complete-head order stays in the lower half, keeping its
complementary factorial denominator uniformly comparable to the full order. -/
theorem completeHeadOrders_le_half (N : ℕ) (hN : 256 ≤ N) :
    ∀ k ∈ completeHeadOrders N, 2 * k ≤ N + 1 := by
  intro k hk
  rw [completeHeadOrders_eq_range N hN, Finset.mem_range] at hk
  omega

/-- The high finite prime leg keeps its literal vanishing endpoint
weight, coupled to the full lower complete moment. -/
def taperedWing (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) * ∑ k ∈ lowerWing N,
    ordinaryPrimeMoment k (3 / 2 + Complex.I * y) *
      ZetaRieszEndpointTaper.taperedMoment (intermediatePrimes u N) (N + 1 - k)
        (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N)

/-- Completing the low head and retaining the reflected cancellation
produces one tapered sum and one complete signed head, exactly once. -/
theorem completeLowHead_add_wingCore (u y : ℝ) (N : ℕ) :
    completeLowHead u y N + wingCore u y N = taperedWing u y N + completeHead u y N := by
  unfold completeHead completeHeadOrders headArray
  rw [Finset.sum_union (lowHead_disjoint_lowerWing N)]
  unfold completeLowHead headArray wingCore reflectedCore taperedWing
  rw [Finset.sum_sub_distrib]
  have hf : (∑ k ∈ lowerWing N,
      ((k + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
        ordinaryPrimeMoment (k + 1) (3 / 2 + Complex.I * y) *
          ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)) =
      (1 / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        ∑ k ∈ lowerWing N, ((k + 1 : ℕ) : ℂ) *
          ordinaryPrimeMoment (k + 1) (3 / 2 + Complex.I * y) *
            ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hf]
  ring

/-- The remaining carrier now has four retained components: unpaired
prime layers, the bounded central block, tapered wing, and complete head. -/
def completedCarrier (u y : ℝ) (N : ℕ) : ℂ :=
  ZetaRieszCentralPair.centralUnpairedResponse 1 u y N + centralBlock u y N +
    taperedWing u y N + completeHead u y N

/-- The whole source is preserved by an explicit low-head error;
no vanishing claim is silently built into the carrier definition. -/
theorem retainedCarrier_eq_completed_add_error (u y : ℝ) (N : ℕ) :
    retainedCarrier u y N = completedCarrier u y N +
      (lowHead u y N - completeLowHead u y N) := by
  have h := completeLowHead_add_wingCore u y N
  unfold retainedCarrier completedCarrier
  linear_combination h

/-- The complete retained arithmetic carrier still tends to the
original full multiplicity source. Its joint signed lower bound remains open. -/
theorem tendsto_completedCarrier_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      completedCarrier (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_retainedCarrier_exposed rho hrho hexposed huh).sub
    (tendsto_lowHead_sub_complete rho hrho hexposed huh)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [retainedCarrier_eq_completed_add_error]
  ring

/-- Every prime-factor layer and signed head remains visible at the
current endpoint. Only the central component has its source-conditioned
signed budget; no floor is asserted for the other three components. -/
theorem eventually_completedCarrier_eq_prime_layers (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, completedCarrier u y N =
      ZetaRieszCentralPrimeLayers.centralThreePrimeResponse 1 u y N +
      ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse 1 u y N +
      centralBlock u y N + taperedWing u y N + completeHead u y N := by
  filter_upwards [ZetaRieszCentralPrimeLayers.eventually_unpaired_eq_three_add_higher
    1 y hu huh] with N he
  rw [completedCarrier, he]

end
end RiemannGaussian.ZetaRieszCompletedCarrier
