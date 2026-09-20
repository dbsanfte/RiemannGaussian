/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszWingReserve

/-!
# Decay at the other end of the original tapered wing

The large high-leg factorial orders have a geometric bound at the actual
source normalization. The positive wing reserve and the complete lower-
prime-count response remain intact. The intervening wing stays signed.
-/

namespace RiemannGaussian.ZetaRieszWingHighOrders
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszWingReserve ZetaRieszEndpointTaper ZetaRieszReflectedCompletion
open ZetaRieszAnnulusJoint ZetaExposedPrimeMoments

/-- The positive tilt cost for a high tapered moment decays uniformly
on the smaller harmonic source interval. -/
theorem high_taper_scalar {u L : ℝ} (hu : 0 < u)
    (huh : u < Real.exp (-(11 / 16 : ℝ))) (N l : ℕ)
    (hl : 4 * N ≤ 5 * l) (hL : L ≤ (139 / 100 : ℝ) * N) :
    u ^ l * ((3 / 5 : ℝ)⁻¹ ^ l *
      Real.exp (((3 / 5 : ℝ) + 8193 / 8192 - 3 / 2) * L)) ≤
        Real.exp (-(1 / 1024 : ℝ) * N) := by
  have hlu : Real.log u ≤ -(11 / 16 : ℝ) := by
    simpa only [Real.log_exp] using (Real.log_lt_log hu huh).le
  have hlq : Real.log (5 / 3 : ℝ) ≤ 511 / 1000 := by
    rw [Real.log_div (by norm_num) (by norm_num)]
    linarith [Real.log_five_lt_d9, Real.log_three_gt_d9]
  have hpow (x : ℝ) (hx : 0 < x) : x ^ l = Real.exp ((l : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hx]
  rw [show (3 / 5 : ℝ)⁻¹ = 5 / 3 by norm_num, hpow u hu,
    hpow (5 / 3) (by norm_num), ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_left hlu (Nat.cast_nonneg (α := ℝ) l)
  have h2 := mul_le_mul_of_nonneg_left hlq (Nat.cast_nonneg (α := ℝ) l)
  have hlc : 4 * (N : ℝ) ≤ 5 * l := by exact_mod_cast hl
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The finite high tapered moment has a geometric source-scale bound
at every height, with the original endpoint weight and physical cutoff. -/
theorem eventually_norm_high_taper {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(11 / 16 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ l : ℕ, 4 * N ≤ 5 * l → ∀ y : ℝ,
      ‖(u : ℂ) ^ l * taperedMoment (intermediatePrimes u N) l
        (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N)‖ ≤
        Real.exp (-(1 / 1024 : ℝ) * N) *
          ∑' n, zetaPrimeExpWeight (8193 / 8192) n := by
  have hu0 : 0 < u := by linarith
  filter_upwards [ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent hu0
    (by norm_num : (0 : ℝ) ≤ 11 / 16) huh, eventually_ge_atTop 16] with N hLN hN
  intro l hl y
  let a : ℝ := (3 / 5 : ℝ) + 8193 / 8192 - 3 / 2
  let L := SquarefreeVaughanLogSource.length u N
  have ha : 0 < a := by norm_num [a]
  have hL : 0 < L := SquarefreeVaughanLogSource.length_pos u N
  have hLL : L ≤ (139 / 100 : ℝ) * N := by
    have hb := ZetaRieszHeadOrders.length_le_two_log_two hu (by omega : 2 ≤ N)
    have hc : 2 * Real.log 2 ≤ (139 / 100 : ℝ) := by linarith [Real.log_two_lt_d9]
    exact hb.trans (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))
  have haL : 1 ≤ a * L := by
    have hNc : (16 : ℝ) ≤ N := by exact_mod_cast hN
    dsimp only [a, L]
    nlinarith [hLN]
  have hb := norm_actual_taperedMoment_le u y N l
    (q := 3 / 5) (sigma := 8193 / 8192) (by norm_num) (by norm_num) ha
  have he : Real.exp (a * L) / (a * L) ≤ Real.exp (a * L) :=
    div_le_self (Real.exp_pos _).le haL
  have hs := high_taper_scalar hu0 huh N l hl hLL
  have hZ : 0 ≤ ∑' n, zetaPrimeExpWeight (8193 / 8192) n :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu0.le]
  calc
    _ ≤ u ^ l * ((((3 / 5 : ℝ)⁻¹ ^ l * (Real.exp (a * L) / (a * L)))) *
        ∑' n, zetaPrimeExpWeight (8193 / 8192) n) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hu0.le _)
    _ ≤ u ^ l * (((3 / 5 : ℝ)⁻¹ ^ l * Real.exp (a * L)) *
        ∑' n, zetaPrimeExpWeight (8193 / 8192) n) := by
      gcongr
    _ = (u ^ l * ((3 / 5 : ℝ)⁻¹ ^ l * Real.exp (a * L))) *
        ∑' n, zetaPrimeExpWeight (8193 / 8192) n := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hs hZ

/-- The selected original wing orders whose high leg is independently
small; membership does not depend on the prime phases. -/
def highOrders (N : ℕ) : Finset ℕ :=
  (lowerWing N).filter (fun k => 4 * N ≤ 5 * (N + 1 - k))

/-- The actual high-order wing response retains its complete low leg. -/
def highWing (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ highOrders N, wingAtom u y N k

/-- The high-order deletion is disjoint from the positive reserve. -/
theorem highOrders_disjoint_reserve (N : ℕ) (hN : 320 ≤ N) :
    Disjoint (highOrders N) (reserveOrders N) := by
  apply Finset.disjoint_left.mpr
  intro k hk hr
  have hhigh := (Finset.mem_filter.mp hk).2
  have hlow := Finset.mem_Icc.mp hr
  omega

/-- All original high wing orders have the existing finite order-count
budget; no independent prime selections are introduced. -/
theorem highOrders_card_le (N : ℕ) : (highOrders N).card ≤ N + 2 :=
  (Finset.card_filter_le _ _).trans (lowerWing_card_le N)

/-- A bounded complete low moment and the independent high-leg estimate
pay the whole selected wing, including its order count and prefactor. -/
theorem eventually_norm_highWing (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ‖((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        highWing (3 / 2 - rho.1.re) rho.1.im N‖ ≤
          C * (N + 1 : ℝ) ^ 2 * Real.exp (-(1 / 1024 : ℝ) * N) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 1 / 2 ≤ u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu0 : 0 < u := by linarith
  obtain ⟨C, hC, hb⟩ := exists_normalized_unlogged_prime_moment_bound rho hrho hexposed
  let Z : ℝ := ∑' n, zetaPrimeExpWeight (8193 / 8192) n
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨2 * (C / u) * Z, by positivity, ?_⟩
  have hlo (k : ℕ) : ‖(u : ℂ) ^ k * ordinaryPrimeMoment k
      (3 / 2 + Complex.I * (rho.1.im : ℂ))‖ ≤ C / u := by
    have he : (u : ℂ) ^ k * ordinaryPrimeMoment k (3 / 2 + Complex.I * (rho.1.im : ℂ)) =
        ((u : ℂ) ^ (k + 1) * ordinaryPrimeMoment k
          (3 / 2 + Complex.I * (rho.1.im : ℂ))) / (u : ℂ) := by
      rw [pow_succ]
      field_simp [Complex.ofReal_ne_zero.mpr hu0.ne']
    rw [he, norm_div, Complex.norm_real, Real.norm_of_nonneg hu0.le]
    exact div_le_div_of_nonneg_right (hb k) hu0.le
  filter_upwards [eventually_norm_high_taper hu huh] with N hhigh
  have hterm (k : ℕ) (hk : k ∈ highOrders N) :
      ‖(u : ℂ) ^ (N + 1) * wingAtom u rho.1.im N k‖ ≤
        (N + 1 : ℝ) * (C / u) * Real.exp (-(1 / 1024 : ℝ) * N) * Z := by
    obtain ⟨hkw, hkh⟩ := Finset.mem_filter.mp hk
    have hkM := (lowerWing_bounds hkw).2.2
    have hpow : (u : ℂ) ^ (N + 1) = (u : ℂ) ^ k * (u : ℂ) ^ (N + 1 - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkM]
    have he : (u : ℂ) ^ (N + 1) * wingAtom u rho.1.im N k =
        ((N + 1 : ℕ) : ℂ) *
          ((u : ℂ) ^ k * ordinaryPrimeMoment k (3 / 2 + Complex.I * (rho.1.im : ℂ))) *
          ((u : ℂ) ^ (N + 1 - k) * taperedMoment (intermediatePrimes u N) (N + 1 - k)
            (3 / 2 + Complex.I * (rho.1.im : ℂ)) (SquarefreeVaughanLogSource.length u N)) := by
      rw [hpow]
      unfold wingAtom
      ring
    rw [he, norm_mul, norm_mul, Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul
      (mul_le_mul_of_nonneg_left (hlo k) (by positivity)) (hhigh _ hkh rho.1.im)
      (norm_nonneg _) (by positivity)).trans_eq (by dsimp only [Z]; ring)
  change ‖(u : ℂ) ^ (N + 1) * highWing u rho.1.im N‖ ≤ _
  rw [highWing, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  have hs := Finset.sum_le_sum hterm
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  apply hs.trans
  have hc : ((highOrders N).card : ℝ) ≤ 2 * (N + 1) := by
    have hc' : ((highOrders N).card : ℝ) ≤ N + 2 := by exact_mod_cast highOrders_card_le N
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have h := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ (N + 1 : ℝ) * (C / u) * Real.exp (-(1 / 1024 : ℝ) * N) * Z by positivity)
  exact h.trans_eq (by ring)

/-- The complete high-order wing vanishes at the original source scale,
with no cancellation premise for the remaining wing or lower prime counts. -/
theorem tendsto_highWing (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      highWing (3 / 2 - rho.1.re) rho.1.im N) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := eventually_norm_highWing rho hrho hexposed huh
  have h := (ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric
    (Real.exp_pos (-(1 / 1024 : ℝ))).le
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 1024 : ℝ) < 0))).const_mul C
  simp only [mul_zero] at h
  apply squeeze_zero_norm' (a := fun N : ℕ => C * ((N + 1 : ℝ) ^ 2 *
    Real.exp (-(1 / 1024 : ℝ)) ^ N)) _ h
  filter_upwards [hb] with N hN
  simpa only [mul_assoc, ← Real.exp_nat_mul, mul_comm (N : ℝ)] using hN

/-- The original wing orders left after its positive block and
independently vanishing high-leg tail have been accounted for. -/
def unpaidOrders (N : ℕ) : Finset ℕ :=
  (lowerWing N \ reserveOrders N) \ highOrders N

/-- Every unpaid wing order lies in the remaining middle interval.
Both endpoints are literal integer inequalities from the original cuts. -/
theorem unpaidOrders_support {N k : ℕ} (hk : k ∈ unpaidOrders N) :
    k ∈ lowerWing N ∧ k ≤ 13 * N / 32 ∧ 5 * (N + 1 - k) < 4 * N := by
  obtain ⟨hkrem, hknot⟩ := Finset.mem_sdiff.mp hk
  obtain ⟨hkw, hkr⟩ := Finset.mem_sdiff.mp hkrem
  have hkw' := lowerWing_bounds hkw
  have hki : ¬ (13 * N / 32 + 1 ≤ k ∧ k ≤ (15 * N + 64) / 32) := by
    simpa only [reserveOrders, Finset.mem_Icc] using hkr
  have hkh : ¬ 4 * N ≤ 5 * (N + 1 - k) := by
    intro hh
    exact hknot (Finset.mem_filter.mpr ⟨hkw, hh⟩)
  exact ⟨hkw, by omega, by omega⟩

/-- The whole unselected middle wing, with every original signed atom. -/
def unpaidWing (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ k ∈ unpaidOrders N, wingAtom u y N k

/-- The two paid wing components and the intervening signed component
are an exact partition; no endpoint or cross term is silently omitted. -/
theorem remainingWing_eq (u y : ℝ) (N : ℕ) (hN : 320 ≤ N) :
    remainingWing u y N = highWing u y N + unpaidWing u y N := by
  have hsub : highOrders N ⊆ lowerWing N \ reserveOrders N := by
    intro k hk
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hk).1,
      fun hr => Finset.disjoint_left.mp (highOrders_disjoint_reserve N hN) hk hr⟩
  have hs := Finset.sum_sdiff (f := wingAtom u y N) hsub
  simpa only [remainingWing, highWing, unpaidWing, unpaidOrders, add_comm] using hs.symm

open ZetaRieszPrimeCountFrequency

/-- The fixed remaining arithmetic target: all lower prime counts
coupled to only the unpaid middle wing on the existing cofinal schedule. -/
def remainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ) ^ (dyadicMomentOrder j + 1) *
    ((1 / (2 * (Real.pi : ℂ))) *
      (∫ xi : ℝ in Set.Ioi 0,
        fewPrimeFrequency 1 u y (dyadicMomentOrder j) (dyadicPrimeCount j) xi) +
      unpaidWing u y (dyadicMomentOrder j))

/-- The preceding unpaid response differs from the new target by exactly
the independently vanishing high-order wing, at its original scale. -/
theorem unpaid_eq_remainder_add_high (u y : ℝ) (j : ℕ)
    (hj : 320 ≤ dyadicMomentOrder j) :
    unpaid u y j = remainder u y j +
      (u : ℂ) ^ (dyadicMomentOrder j + 1) * highWing u y (dyadicMomentOrder j) := by
  unfold unpaid remainder
  rw [remainingWing_eq u y (dyadicMomentOrder j) hj]
  ring

/-- The evaluated harmonic source survives with its exact multiplicity
and paid cost. Its surviving response is the fixed joint target plus the
positive wing reserve; no floor for the joint target is presumed. -/
theorem tendsto_remainder_add_reserve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (fun j : ℕ => remainder (3 / 2 - rho.1.re) rho.1.im j +
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (dyadicMomentOrder j + 1) *
        reserve (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder j)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hs := (ZetaRieszPrimeCountMass.tendsto_few_add_wing_source rho hrho hexposed
    (huh.trans reserve_radius_lt_annular)).sub
      ((tendsto_highWing rho hrho hexposed huh).comp tendsto_dyadicMomentOrder)
  simp only [sub_zero] at hs
  apply hs.congr'
  filter_upwards [tendsto_dyadicMomentOrder.eventually (eventually_ge_atTop 320)] with j hj
  rw [few_add_wing_eq _ _ j hj, unpaid_eq_remainder_add_high _ _ j hj]
  dsimp only [Function.comp_def]
  ring

/-- A sufficient independent floor for precisely the surviving lower-
count sum and middle wing would close the restricted simple-zero case.
The larger negative allowance is paid by the actual positive wing block. -/
theorem false_of_remainder_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ)))
    (hsimple : analyticZetaZeroMultiplicity rho = 1)
    {eta : ℝ}
    (heta : eta < 1 - RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) + 15 / 544)
    (hfloor : ∃ᶠ j in atTop, -eta ≤ (remainder (3 / 2 - rho.1.re) rho.1.im j).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_remainder_add_reserve rho hrho hexposed huh)
  simp only [hsimple, Nat.cast_one, one_pow, one_mul, Complex.add_re,
    Complex.neg_re, Complex.one_re, Complex.ofReal_re] at hs
  have hr := tendsto_dyadicMomentOrder.eventually
    (eventually_re_reserve_ge rho hrho hexposed huh)
  simp only [hsimple, Nat.cast_one, one_pow, mul_one] at hr
  have hfreq := (hfloor.and_eventually hr).mono (fun _ hj => add_le_add hj.1 hj.2)
  have hc := ge_of_tendsto_of_frequently hs hfreq
  linarith

end
end RiemannGaussian.ZetaRieszWingHighOrders
