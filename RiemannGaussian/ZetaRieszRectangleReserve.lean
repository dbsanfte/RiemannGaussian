/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangleWeights

/-!
# A positive reserve from the literal allocation-safe rectangle

The reserve is minus the second-incidence correction contribution, as in
the carrier's subtraction of ownerCompletionCorrection. All literal mask
and old allocation errors are paid independently before using zero phases.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszWideOwnerAudit ZetaRieszAnnulusJoint ZetaRieszPrimePairConvolution
open ZetaRieszMatchedMiddle ZetaRieszPrimeCountFrequency

private theorem normalized_rectangle_order {u : ℝ} (hu : 0 < u) (y : ℝ)
    {N j h : ℕ} (hN : 1000 ≤ N) (hh : h ∈ rectangleOrders N j) :
    (u : ℂ) ^ (N + 1) *
      ((((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)) *
        (((h + 1 : ℕ) : ℂ) * finiteMoment (intermediatePrimes u N) j (3 / 2 + Complex.I * y) *
          finiteMoment (intermediatePrimes u N) (N + 1 - j - h) (3 / 2 + Complex.I * y) *
          finiteMoment (intermediatePrimes u N) (h + 1) (3 / 2 + Complex.I * y))) =
    (rectangleSourceWeight u N j h : ℂ) *
      (weightedFinite u y N j * weightedFinite u y N (N + 1 - j - h) *
        weightedFinite u y N (h + 1)) := by
  obtain ⟨hj, hℓ, _⟩ := rectangle_phase_orders (by omega : 20 ≤ N) hh
  have hjp : 0 < j := by omega
  have hℓp : 0 < N + 1 - j - h := by omega
  have hjM : j < N + 2 := by omega
  have horder : j + (N + 1 - j - h) + (h + 1) = N + 2 := by
    have := rectangle_orders_sum hjM hh
    omega
  have hp : (u : ℂ) ^ j * (u : ℂ) ^ (N + 1 - j - h) * (u : ℂ) ^ (h + 1) =
      (u : ℂ) ^ (N + 2) := by rw [← pow_add, ← pow_add, horder]
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hL0 : (SquarefreeVaughanLogSource.length u N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (SquarefreeVaughanLogSource.length_pos u N).ne'
  have hj0 : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hjp.ne'
  have hl0 : ((N + 1 - j - h : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hℓp.ne'
  symm
  unfold weightedFinite
  calc
    _ = (rectangleSourceWeight u N j h : ℂ) * (j : ℂ) * (N + 1 - j - h : ℕ) * (h + 1 : ℕ) *
        ((u : ℂ) ^ j * (u : ℂ) ^ (N + 1 - j - h) * (u : ℂ) ^ (h + 1)) *
          finiteMoment (intermediatePrimes u N) j (3 / 2 + Complex.I * y) *
          finiteMoment (intermediatePrimes u N) (N + 1 - j - h) (3 / 2 + Complex.I * y) *
          finiteMoment (intermediatePrimes u N) (h + 1) (3 / 2 + Complex.I * y) := by ring
    _ = _ := by
      rw [hp, show N + 2 = (N + 1) + 1 by omega, pow_succ]
      unfold rectangleSourceWeight
      push_cast
      field_simp

/-- Exact source normalization of the three separate finite prime legs. -/
theorem normalized_separatePrimeRectangle {u : ℝ} (hu : 0 < u) (y : ℝ)
    {N : ℕ} (hN : 1000 ≤ N) :
    (u : ℂ) ^ (N + 1) * separatePrimeRectangle u y N =
      ∑ j ∈ Finset.range (N + 2), ∑ h ∈ rectangleOrders N j,
        (rectangleSourceWeight u N j h : ℂ) *
          (weightedFinite u y N j * weightedFinite u y N (N + 1 - j - h) *
            weightedFinite u y N (h + 1)) := by
  rw [separatePrimeRectangle_eq_moments]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro h hh
  exact normalized_rectangle_order hu y hN hh

/-- A simple exposed zero forces a negative finite prime-leg rectangle
of magnitude at least 1/150. Only an exact discrete density is used. -/
theorem eventually_re_separateRectangle_le (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1) :
    ∀ᶠ N : ℕ in atTop,
      (((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        separatePrimeRectangle (3 / 2 - rho.1.re) rho.1.im N).re ≤ -(1 / 150 : ℝ) := by
  let u := 3 / 2 - rho.1.re
  have hu : 1 / 2 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu0 : 0 < u := by linarith
  filter_upwards [eventually_rectangle_triple_phase rho hrho hexposed huU,
    eventually_ge_atTop 1000] with N hphase hN
  rw [normalized_separatePrimeRectangle hu0 rho.1.im hN]
  simp only [Complex.re_sum]
  have hterm (j : ℕ) (hj : j ∈ Finset.range (N + 2)) (h : ℕ) (hh : h ∈ rectangleOrders N j) :
      ((rectangleSourceWeight u N j h : ℂ) *
        (weightedFinite u rho.1.im N j * weightedFinite u rho.1.im N (N + 1 - j - h) *
          weightedFinite u rho.1.im N (h + 1))).re ≤
      rectangleSourceWeight u N j h * (-(99 / 100 : ℝ)) := by
    have hp := hphase j (Finset.mem_range.mp hj) h hh
    simp only [hsimple, Nat.cast_one, one_pow] at hp
    have hr := (Complex.re_le_norm _).trans hp
    simp only [Complex.add_re, Complex.one_re] at hr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left (by linarith :
      (weightedFinite u rho.1.im N j * weightedFinite u rho.1.im N (N + 1 - j - h) *
        weightedFinite u rho.1.im N (h + 1)).re ≤ -(99 / 100 : ℝ))
      (rectangleSourceWeight_nonneg hu0.le N j h)
  calc
    _ ≤ ∑ j ∈ Finset.range (N + 2), ∑ h ∈ rectangleOrders N j,
        rectangleSourceWeight u N j h * (-(99 / 100 : ℝ)) :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun h hh => hterm j hj h hh))
    _ = (∑ j ∈ Finset.range (N + 2), ∑ h ∈ rectangleOrders N j,
        rectangleSourceWeight u N j h) * (-(99 / 100 : ℝ)) := by simp only [Finset.sum_mul]
    _ ≤ (1 / 147 : ℝ) * (-(99 / 100 : ℝ)) :=
      mul_le_mul_of_nonpos_right (sum_rectangleSourceWeight_lower hu huU hN) (by norm_num)
    _ ≤ _ := by norm_num

/-- The reserve has the sign with which this rectangle enters the
subtraction of the original ownership correction. -/
def rectangleReserve (u y : ℝ) (N K : ℕ) : ℂ := -rectangleResponse u y N K

/-- The actual masked, unassigned rectangle supplies at least 1/160
in the reserve orientation. Every mask and allocation error is paid;
the only analytic hypotheses are the original simple exposed zero. -/
theorem eventually_rectangleReserve_ge (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (huU : 3 / 2 - rho.1.re ≤ radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1) :
    ∀ᶠ t : ℕ in atTop, (1 / 160 : ℝ) ≤
      ((((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (dyadicMomentOrder t + 1)) *
        rectangleReserve (3 / 2 - rho.1.re) rho.1.im (dyadicMomentOrder t) (dyadicPrimeCount t)).re := by
  let u := 3 / 2 - rho.1.re
  have hu : 1 / 2 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have he := (tendsto_separate_sub_rectangle (fun _ => rho.1.im) hu huU).norm
  simp only [norm_zero] at he
  have he' := he.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2400))
  filter_upwards [tendsto_dyadicMomentOrder.eventually
    (eventually_re_separateRectangle_le rho hrho hexposed huU hsimple), he'] with t hs heN
  have hr := (Complex.abs_re_le_norm _).trans heN.le
  rw [mul_sub, Complex.sub_re] at hr
  obtain ⟨hrlo, _⟩ := abs_le.mp hr
  simp only [rectangleReserve, mul_neg, Complex.neg_re]
  change _ ≤ -((u : ℂ) ^ (dyadicMomentOrder t + 1) *
    rectangleResponse u rho.1.im (dyadicMomentOrder t) (dyadicPrimeCount t)).re
  change ((u : ℂ) ^ (dyadicMomentOrder t + 1) *
    separatePrimeRectangle u rho.1.im (dyadicMomentOrder t)).re ≤ _ at hs
  linarith

end
end RiemannGaussian.ZetaRieszSkewAllocation
