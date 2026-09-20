/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCofactorPrimeRepairs

/-!
# Independent joint cancellation of the wing and composite companion

The original unpaid wing plus an explicit complete signed composite
companion has norm at most C(N+1)^2 exp(-N/64) after source scaling,
for 1/2 <= u < exp(-2/3) and every fixed ordinate of absolute value
greater than one. All unit, saturation, prime-prefix and diagonal
corrections are accounted for. No hypothetical zero is needed.

The actual finite lower-count sum minus this companion retains the
original harmonic source and reserve. Its independent lower bound
remains open. In particular, the complete companion is not silently
identified with a masked finite subfamily or counted once per integer.
-/

namespace RiemannGaussian.ZetaRieszJointCofactor
noncomputable section
open Complex Filter Topology
open scoped Classical BigOperators ArithmeticFunction.Moebius

/-- The original signed composite Riesz profile with one distinguished prime and its
exact pair of complementary factorial orders. -/
def compositeAtom (L y : ℝ) (k l p a : ℕ) : ℂ :=
  (if Squarefree a ∧ a ≠ 1 ∧ ¬a.Prime ∧ ¬p ∣ a then
    -(VaughanLogAverage.riesz L (p * a) : ℂ) else 0) *
      zetaPrimeLogKernel k (3 / 2 + I * y) a * zetaPrimeLogKernel l (3 / 2 + I * y) p

/-- Each original prime/composite pair equals its coupled coefficient plus the exact
clipped-prefix and repeated-prime corrections. -/
theorem coupling_atom_eq {p : ℕ} (hp : p.Prime) (L y : ℝ) (k l a : ℕ) :
    compositeAtom L y k l p a +
      ((L - Real.log p : ℝ) : ℂ) *
        (if a.Prime then zetaPrimeLogKernel k (3 / 2 + I * y) a else 0) *
          zetaPrimeLogKernel l (3 / 2 + I * y) p =
    coupledCoefficient p L a * zetaPrimeLogKernel k (3 / 2 + I * y) a *
        zetaPrimeLogKernel l (3 / 2 + I * y) p + prefixAtom L y k l p a +
      if a = p then ((L - Real.log p : ℝ) : ℂ) *
        zetaPrimeLogKernel k (3 / 2 + I * y) p * zetaPrimeLogKernel l (3 / 2 + I * y) p else 0 := by
  by_cases ha : a.Prime
  · have hnot : ¬(Squarefree a ∧ a ≠ 1 ∧ ¬a.Prime ∧ ¬p ∣ a) := fun h => h.2.2.1 ha
    by_cases hd : p ∣ a
    · have he : a = p := ((Nat.prime_dvd_prime_iff_eq hp ha).mp hd).symm
      subst a
      simp [compositeAtom, coupledCoefficient, prefixAtom, hp]
    · have hne : a ≠ p := fun he => hd (he ▸ dvd_rfl)
      have hgood : a.Prime ∧ ¬p ∣ a := ⟨ha, hd⟩
      simp only [compositeAtom, coupledCoefficient, prefixAtom, if_neg hnot,
        if_pos ha, if_pos hgood, if_neg hne, zero_mul, zero_add, add_zero]
      push_cast
      ring
  · have hne : a ≠ p := fun he => ha (he ▸ hp)
    have hnot : ¬(a.Prime ∧ ¬p ∣ a) := fun h => ha h.1
    simp only [compositeAtom, coupledCoefficient, prefixAtom, if_neg ha,
      if_neg hnot, if_neg hne, mul_zero, zero_mul, add_zero]

/-- The signed composite companion is a genuinely convergent arithmetic series, with
every prime and completion correction retained. -/
theorem hasSum_compositeAtom {p : ℕ} (hp : p.Prime) {L : ℝ}
    (hpL : Real.log p ≤ L) {k : ℕ} (hk : 0 < k) (l : ℕ) (y : ℝ) :
    HasSum (fun a => compositeAtom L y k l p a)
      (coupledResponse p L k (3 / 2 + I * y) * zetaPrimeLogKernel l (3 / 2 + I * y) p +
        (∑' a, prefixAtom L y k l p a) +
        ((L - Real.log p : ℝ) : ℂ) * zetaPrimeLogKernel k (3 / 2 + I * y) p *
          zetaPrimeLogKernel l (3 / 2 + I * y) p -
        ((L - Real.log p : ℝ) : ℂ) * ZetaExposedPrimeMoments.ordinaryPrimeMoment k (3 / 2 + I * y) *
          zetaPrimeLogKernel l (3 / 2 + I * y) p) := by
  have hL : 0 ≤ L := (Real.log_natCast_nonneg p).trans hpL
  have hc := (hasSum_coupledResponse hp hpL hk y).summable.hasSum.mul_right
    (zetaPrimeLogKernel l (3 / 2 + I * y) p)
  have hprefix : Summable (fun a => prefixAtom L y k l p a) :=
    ((summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ) < 101 / 100)).mul_left
      (L * (10 / 7 : ℝ) ^ (k + l) * Real.exp ((21 / 100 : ℝ) * L) *
        zetaPrimeExpWeight (101 / 100) p)).of_norm_bounded
          (fun a => prefix_atom_bound y k l p a hL)
  have hd : HasSum (fun a : ℕ => if a = p then
      ((L - Real.log p : ℝ) : ℂ) * zetaPrimeLogKernel k (3 / 2 + I * y) p *
        zetaPrimeLogKernel l (3 / 2 + I * y) p else 0)
      (((L - Real.log p : ℝ) : ℂ) * zetaPrimeLogKernel k (3 / 2 + I * y) p *
        zetaPrimeLogKernel l (3 / 2 + I * y) p) := by
    exact hasSum_ite_eq p _
  have hprime := ((ZetaExposedPrimeMoments.summable_ordinaryPrimeMoment
    (by norm_num : (1 : ℝ) < (3 / 2 + I * (y : ℂ)).re) k).hasSum.mul_left
      (((L - Real.log p : ℝ) : ℂ))).mul_right (zetaPrimeLogKernel l (3 / 2 + I * y) p)
  apply (((hc.add hprefix.hasSum).add hd).sub hprime).congr_fun
  intro a
  have h := coupling_atom_eq hp L y k l a
  linear_combination h

/-- The complete signed composite companion of the original unpaid wing. All
squarefree nonunit composite cofactors coprime to the distinguished prime are
included; the finite carrier masks are not presumed. -/
def compositeWing (u y : ℝ) (N : ℕ) : ℂ :=
  ((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ) *
    ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      ∑ p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N,
        ∑' a, compositeAtom (SquarefreeVaughanLogSource.length u N) y k (N + 1 - k) p a

/-- The original unpaid wing and its explicit composite companion equal the three
bounded joint terms, with no change to the prime selection or order set. -/
theorem unpaidWing_add_compositeWing (u y : ℝ) (N : ℕ) :
    ZetaRieszWingHighOrders.unpaidWing u y N + compositeWing u y N =
      coupledWing u y N + prefixWing u y N + diagonalWing u y N := by
  have hL := SquarefreeVaughanLogSource.length_pos u N
  have hLc : (SquarefreeVaughanLogSource.length u N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  unfold ZetaRieszWingHighOrders.unpaidWing compositeWing coupledWing prefixWing diagonalWing
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : 0 < k := by have h := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.2; omega
  unfold ZetaRieszWingReserve.wingAtom ZetaRieszEndpointTaper.taperedMoment prefixBlock diagonalBlock
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hprime, _, hpX⟩ := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hp
  have hpL : Real.log p ≤ SquarefreeVaughanLogSource.length u N :=
    (Real.log_lt_log (by exact_mod_cast hprime.pos) (by exact_mod_cast hpX)).le
  rw [(hasSum_compositeAtom hprime hpL hk0 (N + 1 - k) y).tsum_eq]
  unfold ZetaRieszEndpointTaper.endpointWeight
  push_cast
  field_simp [hLc]
  ring

private theorem tendsto_of_wing_bound (f : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᶠ N in atTop, ‖f N‖ ≤ C * (N + 1 : ℝ) ^ 2 * Real.exp (-(N + 1 : ℝ) / 64)) :
    Tendsto f atTop (𝓝 0) := by
  have h := (ZetaRieszShiftedHeadBudget.tendsto_quadratic_geometric
    (Real.exp_pos (-(1 / 64 : ℝ))).le
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 64 : ℝ) < 0))).const_mul C
  simp only [mul_zero] at h
  apply squeeze_zero_norm' (a := fun N : ℕ => C * ((N + 1 : ℝ) ^ 2 *
    Real.exp (-(1 / 64 : ℝ)) ^ N)) _ h
  filter_upwards [hb] with N hN
  apply hN.trans
  have he : Real.exp (-(N + 1 : ℝ) / 64) ≤ Real.exp (-(1 / 64 : ℝ)) ^ N := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    linarith
  nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ C * (N + 1 : ℝ) ^ 2 by positivity)]

/-- The original unpaid wing cancels its complete signed composite companion at
source scale, independently of hypothetical zeros. -/
theorem tendsto_unpaidWing_add_compositeWing (y : ℝ) (hy : 1 < |y|) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      (ZetaRieszWingHighOrders.unpaidWing u y N + compositeWing u y N)) atTop (𝓝 0) := by
  have hpref : Tendsto (fun N => (u : ℂ) ^ (N + 1) * prefixWing u y N) atTop (𝓝 0) := by
    apply tendsto_of_wing_bound _ (2 * (∑' n, zetaPrimeExpWeight (101 / 100) n) ^ 2) (by positivity)
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact norm_prefixWing_le hu huh.le hN y
  have hdiag : Tendsto (fun N => (u : ℂ) ^ (N + 1) * diagonalWing u y N) atTop (𝓝 0) := by
    have hZ : 0 ≤ ∑' n, zetaPrimeExpWeight (3 / 2) n := tsum_nonneg (fun _ => (Real.exp_pos _).le)
    apply tendsto_of_wing_bound _ (2 * ∑' n, zetaPrimeExpWeight (3 / 2) n) (by positivity)
    exact Eventually.of_forall (fun N => norm_diagonalWing_le (by linarith) huh.le N y)
  have h := ((tendsto_coupledWing y hy hu huh).add hpref).add hdiag
  simpa only [add_zero, unpaidWing_add_compositeWing, mul_add] using h


/-- The actual wing plus its complete composite companion has the independent bound
C(N+1)^2 exp(-N/64). One constant works across the original radius interval at
each fixed eligible height. -/
theorem exists_unpaidWing_add_compositeWing_bound (y : ℝ) (hy : 1 < |y|) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ), 1 / 2 ≤ u → u < Real.exp (-(2 / 3 : ℝ)) →
      ∀ᶠ N : ℕ in atTop,
        ‖(u : ℂ) ^ (N + 1) * (ZetaRieszWingHighOrders.unpaidWing u y N + compositeWing u y N)‖ ≤
          C * (N + 1 : ℝ) ^ 2 * Real.exp (-(N : ℝ) / 64) := by
  obtain ⟨C0, hC0, hb0⟩ := exists_completedWing_bound y hy
  obtain ⟨C1, hC1, hb1⟩ := exists_boundaryWing_bound
  let C2 := 2 * (∑' n, zetaPrimeExpWeight (101 / 100) n) ^ 2
  let C3 := 2 * ∑' n, zetaPrimeExpWeight (3 / 2) n
  have hC2 : 0 ≤ C2 := by dsimp only [C2]; positivity
  have hC3 : 0 ≤ C3 := mul_nonneg (by norm_num) (tsum_nonneg (fun _ => (Real.exp_pos _).le))
  refine ⟨C0 + C1 + C2 + C3, by positivity, ?_⟩
  intro u hu huh
  filter_upwards [hb1 u hu huh, eventually_ge_atTop 2] with N hN1 hN
  have hscale (A : ℝ) (hA : 0 ≤ A) :
      A * (N + 1 : ℝ) ^ 2 * Real.exp (-(N + 1 : ℝ) / 64) ≤
        A * (N + 1 : ℝ) ^ 2 * Real.exp (-(N : ℝ) / 64) := by
    gcongr
    linarith
  have h0 := (hb0 u hu huh.le N hN).trans (hscale C0 hC0.le)
  have h1 := hN1 y
  have h2 := (norm_prefixWing_le hu huh.le hN y).trans (hscale C2 hC2)
  have h3 := (norm_diagonalWing_le (by linarith) huh.le N y).trans (hscale C3 hC3)
  rw [unpaidWing_add_compositeWing, coupledWing_eq, mul_add, mul_add, mul_sub]
  have hn :
      ‖(u : ℂ) ^ (N + 1) * completedWing u y N - (u : ℂ) ^ (N + 1) * boundaryWing u y N +
          (u : ℂ) ^ (N + 1) * prefixWing u y N + (u : ℂ) ^ (N + 1) * diagonalWing u y N‖ ≤
        ‖(u : ℂ) ^ (N + 1) * completedWing u y N‖ + ‖(u : ℂ) ^ (N + 1) * boundaryWing u y N‖ +
          ‖(u : ℂ) ^ (N + 1) * prefixWing u y N‖ + ‖(u : ℂ) ^ (N + 1) * diagonalWing u y N‖ := by
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  apply hn.trans
  nlinarith only [h0, h1, h2, h3]

-- The exact original finite count response stays present. The complete
-- companion is subtracted, not silently equated to a masked subfamily.
/-- The original finite lower-count response minus the complete signed composite
companion. This keeps all finite carrier masks explicit; no independent floor
for this difference is assumed or proved. -/
def arithmeticRemainder (u y : ℝ) (j : ℕ) : ℂ :=
  (u : ℂ) ^ (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j + 1) *
    (ZetaRieszHarmonicWindow.windowResponse 1 u y (7 / 4) (9 / 4)
      (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j) -
      compositeWing u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j))

/-- The new purely arithmetic difference and the original coupled remainder differ
by the independently vanishing joint wing/composite sum. -/
theorem tendsto_remainder_sub_arithmetic (y : ℝ) (hy : 1 < |y|) {u : ℝ}
    (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    Tendsto (fun j => ZetaRieszHarmonicWindow.remainder u y j - arithmeticRemainder u y j)
      atTop (𝓝 0) := by
  have h := (tendsto_unpaidWing_add_compositeWing y hy hu huh).comp
    ZetaRieszPrimeCountFrequency.tendsto_dyadicMomentOrder
  apply h.congr'
  filter_upwards [] with j
  dsimp only [Function.comp_def, ZetaRieszHarmonicWindow.remainder, arithmeticRemainder]
  ring

/-- The exact harmonic source and positive reserve survive the proved joint
cancellation. The independent floor for the remaining arithmetic difference is
still open. -/
theorem tendsto_arithmeticRemainder_add_reserve (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + I * (rho.1.im : ℂ)) - tau.1‖)
    (huh : 3 / 2 - rho.1.re < Real.exp (-(11 / 16 : ℝ))) :
    Tendsto (fun j : ℕ => arithmeticRemainder (3 / 2 - rho.1.re) rho.1.im j +
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j + 1) *
        ZetaRieszWingReserve.reserve (3 / 2 - rho.1.re) rho.1.im
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ) +
        (analyticZetaZeroMultiplicity rho : ℂ) ^ 2 *
          (RieszHarmonicCostBounds.paidHarmonicCost (3 / 2 - rho.1.re) : ℂ))) := by
  have hu : (1 / 2 : ℝ) ≤ 3 / 2 - rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have huAnn := huh.trans ZetaRieszWingReserve.reserve_radius_lt_annular
  have he := tendsto_remainder_sub_arithmetic rho.1.im (nontrivialZetaZero_one_lt_abs_im rho) hu huAnn
  have hs := (ZetaRieszHarmonicWindow.tendsto_remainder_add_reserve rho hrho hexposed huh).sub he
  simp only [sub_zero] at hs
  exact hs.congr' (Eventually.of_forall (fun _ => by ring))

end
end RiemannGaussian.ZetaRieszJointCofactor
