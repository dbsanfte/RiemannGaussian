/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszReflectedCompletion
import RiemannGaussian.ZetaRieszWiderMatched

/-!
# The retained carrier after reflected completion

An exact partition keeps the low head, actual prime-factor layers, tapered core and bounded central subset. The entire original source is preserved only with all retained pieces.
-/

namespace RiemannGaussian.ZetaRieszReflectedCarrier
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszReflectedCompletion ZetaRieszPrimePairConvolution
open ZetaRieszAnnulusJoint ZetaExposedPrimeMoments ZetaRieszMatchedMiddle

/-- The two disjoint selected sides of the original middle order range. -/
def wingOrders (N : ℕ) : Finset ℕ :=
  lowerWing N ∪ (lowerWing N).image (fun k => N + 1 - k)

/-- Every selected side remains within the original middle pair. -/
theorem wingOrders_subset_middle (N : ℕ) :
    wingOrders N ⊆ ZetaRieszPairOrders.middleOrders (N + 1) := by
  intro k hk
  rcases Finset.mem_union.mp hk with hk | hk
  · exact (Finset.mem_filter.mp hk).1
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact reflected_mem_middle hj

/-- The exact middle orders remaining after the reflected sides are removed. -/
def centralOrders (N : ℕ) : Finset ℕ :=
  ZetaRieszPairOrders.middleOrders (N + 1) \ wingOrders N

/-- Every remaining central order lies in the already bounded wider
matched block, including its shifted head completion constraint. -/
theorem centralOrders_subset_wider (N : ℕ) :
    centralOrders N ⊆ ZetaRieszWiderMatched.matchedOrders N := by
  intro k hk
  obtain ⟨hmid, hnot⟩ := Finset.mem_sdiff.mp hk
  obtain ⟨hkR, hklo, hkhi⟩ := Finset.mem_filter.mp hmid
  have hkM := Finset.mem_range.mp hkR
  have hklow : 15 * N + 64 < 32 * k := by
    by_contra h
    apply hnot
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hmid, by omega⟩
  have hlmid : N + 1 - k ∈ ZetaRieszPairOrders.middleOrders (N + 1) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by omega), by omega, by omega⟩
  have hllow : 15 * N + 64 < 32 * (N + 1 - k) := by
    by_contra h
    apply hnot
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨N + 1 - k, Finset.mem_filter.mpr ⟨hlmid, by omega⟩, by omega⟩
  apply Finset.mem_filter.mpr
  refine ⟨by simpa only [Nat.add_assoc, show (1 : ℕ) + 1 = 2 by norm_num] using hkR, ?_⟩
  dsimp only [ZetaRieszWiderMatched.completionOrder]
  omega

/-- The low head orders remain present although their pair partners
belong to the previously paid outer-pair range. -/
def lowHeadOrders (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 2)).filter (fun k => 8 * k ≤ N + 1)

/-- The literal negative low-head contribution, with its complete prime
leg and original derivative and length factors. -/
def lowHead (u y : ℝ) (N : ℕ) : ℂ :=
  -((N + 1 : ℕ) : ℂ) * (1 / (SquarefreeVaughanLogSource.length u N : ℂ)) *
    ∑ k ∈ lowHeadOrders N, ((k + 1 : ℕ) : ℂ) *
      finiteMoment (intermediatePrimes u N) (k + 1) (3 / 2 + Complex.I * y) *
        ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)

/-- The original unfiltered carrier splits into its unpaired response,
low head and shared middle atoms, with no arithmetic term discarded. -/
theorem middleJoint_eq_lowHead_add_middle (u y : ℝ) (N : ℕ) :
    ZetaRieszPairOrders.middleJoint 1 u y N =
      ZetaRieszCentralPair.centralUnpairedResponse 1 u y N + lowHead u y N +
        ((N + 1 : ℕ) : ℂ) * ∑ k ∈ ZetaRieszPairOrders.middleOrders (N + 1),
          sharedAtom u y N k (N + 1 - k) := by
  let H : Finset ℕ := (Finset.range (N + 2)).filter (fun k => 8 * k < 7 * (N + 1))
  have hsub : lowHeadOrders N ⊆ H := by
    intro k hk
    obtain ⟨hkR, hk⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hkR, by omega⟩
  have hdiff : H \ lowHeadOrders N = ZetaRieszPairOrders.middleOrders (N + 1) := by
    ext k
    simp only [H, lowHeadOrders, ZetaRieszPairOrders.middleOrders, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_range]
    omega
  have hsum := Finset.sum_sdiff (f := fun k => ((k + 1 : ℕ) : ℂ) *
    finiteMoment (intermediatePrimes u N) (k + 1) (3 / 2 + Complex.I * y) *
      ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)) hsub
  rw [hdiff] at hsum
  have hsupport : (1 : Polynomial ℂ).support = {0} := by
    ext k
    by_cases hk : k = 0 <;> simp [Polynomial.mem_support_iff, Polynomial.coeff_one, hk]
  rw [ZetaRieszPairOrders.middleJoint_eq_unpaired_add_form, sum_sharedAtom_eq]
  simp only [ZetaRieszPairOrders.jointPrimeForm, hsupport, Finset.sum_singleton,
    Polynomial.coeff_one_zero, one_mul, Nat.add_zero]
  change ZetaRieszCentralPair.centralUnpairedResponse 1 u y N + ((N + 1 : ℕ) : ℂ) *
    ((1 / 2 : ℂ) * ∑ k ∈ ZetaRieszPairOrders.middleOrders (N + 1),
      finiteMoment (intermediatePrimes u N) k (3 / 2 + Complex.I * y) *
        finiteMoment (intermediatePrimes u N) (N + 1 - k) (3 / 2 + Complex.I * y) -
      (1 / (SquarefreeVaughanLogSource.length u N : ℂ)) * ∑ k ∈ H,
        ((k + 1 : ℕ) : ℂ) * finiteMoment (intermediatePrimes u N) (k + 1)
          (3 / 2 + Complex.I * y) * ordinaryPrimeMoment (N + 1 - k) (3 / 2 + Complex.I * y)) = _
  rw [← hsum, lowHead]
  ring

/-- The central matched subset, retaining its original source prefactor. -/
def centralBlock (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) * ∑ k ∈ centralOrders N, sharedAtom u y N k (N + 1 - k)

/-- The entire remaining arithmetic core after both reflected
completion corrections have been paid independently. -/
def retainedCarrier (u y : ℝ) (N : ℕ) : ℂ :=
  ZetaRieszCentralPair.centralUnpairedResponse 1 u y N + lowHead u y N +
    centralBlock u y N + wingCore u y N

/-- Exact transport of the original whole carrier keeps the central
subset, low head, tapered core and unpaired prime labels together. -/
theorem middleJoint_eq_retained_add_error (u y : ℝ) (N : ℕ) (hN : 256 ≤ N) :
    ZetaRieszPairOrders.middleJoint 1 u y N = retainedCarrier u y N + wingError u y N := by
  have hs := Finset.sum_sdiff (f := fun k => sharedAtom u y N k (N + 1 - k))
    (wingOrders_subset_middle N)
  rw [middleJoint_eq_lowHead_add_middle, ← hs]
  change ZetaRieszCentralPair.centralUnpairedResponse 1 u y N + lowHead u y N +
    ((N + 1 : ℕ) : ℂ) * ((∑ k ∈ centralOrders N, sharedAtom u y N k (N + 1 - k)) +
      ∑ k ∈ wingOrders N, sharedAtom u y N k (N + 1 - k)) = _
  rw [mul_add]
  have hw := wingSource_eq_union u y N hN
  change wingSource u y N = ((N + 1 : ℕ) : ℂ) * ∑ k ∈ wingOrders N,
    sharedAtom u y N k (N + 1 - k) at hw
  rw [← hw, wingSource_eq_core_add_error]
  unfold retainedCarrier centralBlock
  ring

/-- The complete retained carrier inherits the original exposed source
after the independently decaying error is removed. Its remaining signed
lower bound is not assumed or proved here. -/
theorem tendsto_retainedCarrier_exposed (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      retainedCarrier (3 / 2 - rho.1.re) rho.1.im N)
      atTop (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : (0 : ℝ) < 3 / 2 - rho.1.re := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (ZetaRieszPairOrders.tendsto_middleJoint_exposed rho hrho hexposed huh).sub
    (tendsto_wingError (fun _ => rho.1.im) hu huh)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 256] with N hN
  rw [middleJoint_eq_retained_add_error _ _ N hN]
  ring

/-- Taking the real part of any actual selected shared sum preserves
the common source scale and the original order prefactor. -/
theorem re_normalized_sharedSum (u y : ℝ) (N : ℕ) (S : Finset ℕ) :
    ((u : ℂ) ^ (N + 1) * (((N + 1 : ℕ) : ℂ) *
      ∑ k ∈ S, sharedAtom u y N k (N + 1 - k))).re =
        ((N + 1 : ℕ) : ℝ) * ∑ k ∈ S,
          ((u : ℂ) ^ (N + 1) * sharedAtom u y N k (N + 1 - k)).re := by
  simp only [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show (u : ℂ) ^ (N + 1) * (((N + 1 : ℕ) : ℂ) *
    sharedAtom u y N k (N + 1 - k)) = ((N + 1 : ℕ) : ℂ) *
      ((u : ℂ) ^ (N + 1) * sharedAtom u y N k (N + 1 - k)) by ring]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]

/-- Every subset of the wider matched orders has the same signed lower
budget. This allows exact partitions without paying overlapping blocks twice.
The source phases and the full multiplicity remain explicit hypotheses. -/
theorem eventually_sharedSubblock_re_bounds (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ S : Finset ℕ, S ⊆ ZetaRieszWiderMatched.matchedOrders N →
      -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 8 ≤
        (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * (((N + 1 : ℕ) : ℂ) *
          ∑ k ∈ S, sharedAtom (3 / 2 - rho.1.re) rho.1.im N k (N + 1 - k))).re ∧
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * (((N + 1 : ℕ) : ℂ) *
        ∑ k ∈ S, sharedAtom (3 / 2 - rho.1.re) rho.1.im N k (N + 1 - k))).re ≤ 0 := by
  filter_upwards [ZetaRieszWiderMatched.eventually_normalized_sharedAtom_bounds
    rho hrho hexposed huh, ZetaRieszWiderMatched.eventually_matchedBlock_re_bounds
    rho hrho hexposed huh, eventually_ge_atTop 256] with N hsource hblock hN
  intro S hS
  let v : ℕ → ℝ := fun k => (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    sharedAtom (3 / 2 - rho.1.re) rho.1.im N k (N + 1 - k)).re
  have hv (k : ℕ) (hk : k ∈ ZetaRieszWiderMatched.matchedOrders N) : v k ≤ 0 := by
    obtain ⟨hkp, hlp⟩ := ZetaRieszWiderMatched.matchedOrders_pos (by omega) hk
    obtain ⟨hkM, hk, hl, hsucc⟩ := Finset.mem_filter.mp hk
    have hkM' : k ≤ N + 1 := by have h := Finset.mem_range.mp hkM; omega
    have hb := (hsource (N + 1) k (by omega) hkM' hk hl hsucc).2
    have hp : 0 < (k : ℝ) * ((N + 1 - k : ℕ) : ℝ) := by positivity
    have he : ((k : ℂ) * ((N + 1 - k : ℕ) : ℂ) *
        ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          sharedAtom (3 / 2 - rho.1.re) rho.1.im N k (N + 1 - k)).re =
        (k : ℝ) * ((N + 1 - k : ℕ) : ℝ) * v k := by
      dsimp only [v]
      simp only [mul_assoc, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im, zero_mul, sub_zero]
    rw [he] at hb
    nlinarith [sq_nonneg (analyticZetaZeroMultiplicity rho : ℝ)]
  have hdiff : (∑ k ∈ ZetaRieszWiderMatched.matchedOrders N \ S, v k) ≤ 0 := by
    exact Finset.sum_nonpos fun k hk => hv k (Finset.mem_sdiff.mp hk).1
  have hsum : (∑ k ∈ ZetaRieszWiderMatched.matchedOrders N, v k) ≤ ∑ k ∈ S, v k := by
    have he := Finset.sum_sdiff (f := v) hS
    linarith
  have hwhole := hblock.1
  unfold ZetaRieszWiderMatched.matchedBlock at hwhole
  rw [re_normalized_sharedSum] at hwhole
  rw [re_normalized_sharedSum]
  change -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 8 ≤
      ((N + 1 : ℕ) : ℝ) * (∑ k ∈ S, v k) ∧
    ((N + 1 : ℕ) : ℝ) * (∑ k ∈ S, v k) ≤ 0
  constructor
  · exact hwhole.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  · exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (Finset.sum_nonpos fun k hk => hv k (hS hk))

/-- The exact central complement of the reflected sides is bounded
without overlap: its original signed cost is at most one eighth of the
full multiplicity square. -/
theorem eventually_centralBlock_re_bounds (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop,
      -(analyticZetaZeroMultiplicity rho : ℝ) ^ 2 / 8 ≤
        (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          centralBlock (3 / 2 - rho.1.re) rho.1.im N).re ∧
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        centralBlock (3 / 2 - rho.1.re) rho.1.im N).re ≤ 0 := by
  filter_upwards [eventually_sharedSubblock_re_bounds rho hrho hexposed huh] with N hN
  exact hN (centralOrders N) (centralOrders_subset_wider N)

/-- Every surviving prime-factor layer remains visible in the retained
source: the actual three-prime and higher-prime responses, low head,
bounded central subset and the signed tapered core. -/
theorem eventually_retainedCarrier_eq_prime_layers (y : ℝ)
    {u : ℝ} (hu : 0 < u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, retainedCarrier u y N =
      ZetaRieszCentralPrimeLayers.centralThreePrimeResponse 1 u y N +
      ZetaRieszCentralPrimeLayers.centralHigherPrimeResponse 1 u y N +
      lowHead u y N + centralBlock u y N + wingCore u y N := by
  filter_upwards [ZetaRieszCentralPrimeLayers.eventually_unpaired_eq_three_add_higher
    1 y hu huh] with N he
  rw [retainedCarrier, he]

end
end RiemannGaussian.ZetaRieszReflectedCarrier
