import RiemannGaussian.FiniteToEntireRadialRootCount
import RiemannGaussian.FiniteToEntireGaussianTail

/-!
# Expanding radial polynomial heat tails

This file selects the literal upper polynomial-root multiset inside a radial
disk.  Its multiset complement consists exactly of upper roots on or outside
that disk, so every unused occurrence has a checked distance lower bound from
any fixed observation point.  A fixed exponential degree bound is then shown
to be dominated by the resulting quadratic Gaussian as the radius tends to
infinity.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The multiplicity-counted upper roots of a real polynomial in the open
disk centered at zero with radius `R`. -/
def realPolynomialUpperRootMultisetInsideBall
    (A : ℝ[X]) (R : ℝ) : Multiset ℂ :=
  (realPolynomialUpperRootMultiset A).filter fun alpha ↦
    alpha ∈ ball 0 R

/-- The selected inside-root multiset is a submultiset of the complete upper
polynomial divisor. -/
theorem realPolynomialUpperRootMultisetInsideBall_le
    (A : ℝ[X]) (R : ℝ) :
    realPolynomialUpperRootMultisetInsideBall A R ≤
      realPolynomialUpperRootMultiset A := by
  exact Multiset.filter_le _ _

/-- Removing the inside-root multiset leaves exactly the upper roots outside
the corresponding open disk. -/
theorem realPolynomialUpperRootMultiset_sub_insideBall
    (A : ℝ[X]) (R : ℝ) :
    realPolynomialUpperRootMultiset A -
        realPolynomialUpperRootMultisetInsideBall A R =
      (realPolynomialUpperRootMultiset A).filter fun alpha ↦
        alpha ∉ ball 0 R := by
  exact Multiset.sub_filter_eq_filter_not _ _

/-- Every upper-root occurrence outside the selected open disk has norm at
least the disk radius. -/
theorem radius_le_norm_of_mem_upperRoot_sub_insideBall
    (A : ℝ[X]) (R : ℝ) {alpha : ℂ}
    (halpha : alpha ∈ realPolynomialUpperRootMultiset A -
      realPolynomialUpperRootMultisetInsideBall A R) :
    R ≤ ‖alpha‖ := by
  rw [realPolynomialUpperRootMultiset_sub_insideBall] at halpha
  have houtside := (Multiset.mem_filter.mp halpha).2
  simpa [mem_ball, dist_zero_right] using houtside

/-- Relative to any observation point, an unused upper root is at least the
radial disk radius minus the norm of the observation point away. -/
theorem sub_norm_le_dist_of_mem_upperRoot_sub_insideBall
    (A : ℝ[X]) (R : ℝ) (z : ℂ) {alpha : ℂ}
    (halpha : alpha ∈ realPolynomialUpperRootMultiset A -
      realPolynomialUpperRootMultisetInsideBall A R) :
    R - ‖z‖ ≤ dist z alpha := by
  calc
    R - ‖z‖ ≤ ‖alpha‖ - ‖z‖ :=
      sub_le_sub_right
        (radius_le_norm_of_mem_upperRoot_sub_insideBall A R halpha) _
    _ ≤ ‖alpha - z‖ := norm_sub_norm_le alpha z
    _ = dist z alpha := by rw [dist_eq_norm, norm_sub_rev]

/-- The complete upper polynomial heat sum splits into the literal heat of
the roots inside a radial disk and the exact outside-root remainder. -/
theorem realPolynomialUpperHeatSum_eq_insideBall_add_remainder
    (A : ℝ[X]) (R : ℝ) (z : ℂ) (tau : ℝ) :
    realPolynomialUpperHyperbolicHeatSum A z tau =
      finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInsideBall A R) tau +
      realPolynomialUpperHeatRemainderOutsideRootMultiset A
        (realPolynomialUpperRootMultisetInsideBall A R) z tau := by
  exact realPolynomialUpperHeatSum_eq_selected_add_remainder A
    (realPolynomialUpperRootMultisetInsideBall_le A R) z tau

/-- A fixed exponential index bound is dominated by the quadratic Gaussian
at any radius tending to infinity. -/
theorem tendsto_natDegree_mul_radialGaussian_of_exponential_index_bound
    (B : ℕ → ℝ[X]) (index : ℕ → ℕ) (r : ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hdegree : ∀ n, (B n).natDegree ≤ max (index n) 3)
    (hindex : ∀ n, (index n : ℝ) ≤ K * Real.exp (5 * r n))
    (hr : Tendsto r atTop atTop)
    (z : ℂ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ ((B n).natDegree : ℝ) *
        (tau⁻¹ * Real.exp (-((r n - ‖z‖) ^ 2 * tau))))
      atTop (nhds 0) := by
  have hGaussian : Tendsto
      (fun T : ℝ ↦ (K + 3) * Real.exp (5 * T) *
        (tau⁻¹ * Real.exp (-((T - ‖z‖) ^ 2 * tau))))
      atTop (nhds 0) := by
    have hbase := tendsto_exp_neg_quadratic_add_linear_atTop
      htau ‖z‖ 5 0
    have hscaled : Tendsto
        (fun T : ℝ ↦ ((K + 3) * tau⁻¹) *
          Real.exp (-tau * (T - ‖z‖) ^ 2 + 5 * T + 0))
        atTop (nhds 0) := by
      simpa using hbase.const_mul ((K + 3) * tau⁻¹)
    apply hscaled.congr'
    filter_upwards with T
    calc
      ((K + 3) * tau⁻¹) *
          Real.exp (-tau * (T - ‖z‖) ^ 2 + 5 * T + 0) =
        ((K + 3) * tau⁻¹) *
          Real.exp (5 * T - (T - ‖z‖) ^ 2 * tau) := by
        congr 2
        ring
      _ = ((K + 3) * tau⁻¹) *
          (Real.exp (5 * T) *
            Real.exp (-((T - ‖z‖) ^ 2 * tau))) := by
        rw [sub_eq_add_neg, Real.exp_add]
      _ = (K + 3) * Real.exp (5 * T) *
          (tau⁻¹ * Real.exp (-((T - ‖z‖) ^ 2 * tau))) := by ring
  have hmajor := hGaussian.comp hr
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [hr.eventually (eventually_ge_atTop 0)] with n hrn
    have hE : 1 ≤ Real.exp (5 * r n) :=
      Real.one_le_exp (mul_nonneg (by norm_num) hrn)
    have hmax : ((max (index n) 3 : ℕ) : ℝ) ≤
        (K + 3) * Real.exp (5 * r n) := by
      rw [Nat.cast_max]
      apply max_le
      · calc
          (index n : ℝ) ≤ K * Real.exp (5 * r n) := hindex n
          _ ≤ (K + 3) * Real.exp (5 * r n) := by
            gcongr
            linarith
      · calc
          (3 : ℝ) ≤ 3 * Real.exp (5 * r n) := by nlinarith
          _ ≤ (K + 3) * Real.exp (5 * r n) := by
            gcongr
            linarith
    have hdegreeCast : ((B n).natDegree : ℝ) ≤
        ((max (index n) 3 : ℕ) : ℝ) := by
      exact_mod_cast hdegree n
    have hdegreeReal : ((B n).natDegree : ℝ) ≤
        (K + 3) * Real.exp (5 * r n) :=
      hdegreeCast.trans hmax
    exact mul_le_mul_of_nonneg_right hdegreeReal (by positivity)
  · exact hmajor

/-- For exponentially degree-controlled polynomials, selecting every upper
root inside an expanding radial disk makes the complementary fixed-time heat
vanish at every fixed upper observation point. -/
theorem tendsto_upperHeatRemainderOutsideInsideBall_zero
    (B : ℕ → ℝ[X]) (index : ℕ → ℕ) (r : ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hdegree : ∀ n, (B n).natDegree ≤ max (index n) 3)
    (hindex : ∀ n, (index n : ℝ) ≤ K * Real.exp (5 * r n))
    (hr : Tendsto r atTop atTop)
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ realPolynomialUpperHeatRemainderOutsideRootMultiset
        (B n) (realPolynomialUpperRootMultisetInsideBall (B n) (r n))
        z tau)
      atTop (nhds 0) := by
  apply
    tendsto_realPolynomialUpperHeatRemainderOutsideRootMultiset_zero_of_degreeGaussian
      B (fun n ↦ realPolynomialUpperRootMultisetInsideBall (B n) (r n))
      hz htau (fun n ↦ r n - ‖z‖)
  · exact hr.eventually (eventually_ge_atTop ‖z‖) |>.mono fun _ hn ↦ sub_nonneg.mpr hn
  · filter_upwards with n alpha halpha
    exact sub_norm_le_dist_of_mem_upperRoot_sub_insideBall
      (B n) (r n) z halpha
  · exact tendsto_natDegree_mul_radialGaussian_of_exponential_index_bound
      B index r K hK hdegree hindex hr z htau

/-- The explicit Rouché schedule's exponential degree bound makes the heat
carried by upper roots outside the selected radial circle tend to zero. -/
theorem tendsto_radialRouche_upperHeatRemainderOutsideInsideBall_zero
    {A L C : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (B : ℕ → ℝ[X])
    (hdegree : ∀ n,
      (B n).natDegree ≤ max (radialRoucheIndex A L C n) 3)
    (hindex : ∀ n, (radialRoucheIndex A L C n : ℝ) <
      radialRoucheIndexGrowthConstant A L C *
        Real.exp (5 * quantitativeSpectralRadialBoundary n))
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ realPolynomialUpperHeatRemainderOutsideRootMultiset
        (B n) (realPolynomialUpperRootMultisetInsideBall (B n)
          (quantitativeSpectralRadialBoundary n)) z tau)
      atTop (nhds 0) := by
  have hK : 0 ≤ radialRoucheIndexGrowthConstant A L C := by
    dsimp [radialRoucheIndexGrowthConstant]
    positivity
  apply tendsto_upperHeatRemainderOutsideInsideBall_zero
    B (radialRoucheIndex A L C) quantitativeSpectralRadialBoundary
    (radialRoucheIndexGrowthConstant A L C) hK hdegree
    (fun n ↦ (hindex n).le)
    tendsto_quantitativeSpectralRadialBoundary_atTop hz htau

/-- Along the explicit Rouché schedule, the full upper polynomial heat and
the heat of the roots inside the selected circle have vanishing difference. -/
theorem tendsto_radialRouche_upperHeatSum_sub_insideBall_zero
    {A L C : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (B : ℕ → ℝ[X])
    (hdegree : ∀ n,
      (B n).natDegree ≤ max (radialRoucheIndex A L C n) 3)
    (hindex : ∀ n, (radialRoucheIndex A L C n : ℝ) <
      radialRoucheIndexGrowthConstant A L C *
        Real.exp (5 * quantitativeSpectralRadialBoundary n))
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ realPolynomialUpperHyperbolicHeatSum (B n) z tau -
        finiteUpperHyperbolicHeatSum z
          (realPolynomialUpperRootMultisetInsideBall (B n)
            (quantitativeSpectralRadialBoundary n)) tau)
      atTop (nhds 0) := by
  have htail :=
    tendsto_radialRouche_upperHeatRemainderOutsideInsideBall_zero
      hA hL hC B hdegree hindex hz htau
  apply htail.congr'
  filter_upwards with n
  rw [realPolynomialUpperHeatSum_eq_insideBall_add_remainder]
  ring

/-- Under failure of RH, the exact-divisor scheduled canonical Hardy sequence
also has vanishing fixed-time heat outside its selected expanding circles at
every fixed upper observation point. -/
theorem exists_radialRouche_exactDivisor_vanishingHeatTail_sequence_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ A : ℝ, 1 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
        ∃ B : ℕ → ℝ[X],
          let L := finiteERootPinnedRadialConstant A eta z
          Tendsto (radialRoucheIndex A L C) atTop atTop ∧
          TendstoLocallyUniformlyOn
            (fun n w => ((B n).map Complex.ofRealHom).eval w)
            riemannXiSpectral atTop Set.univ ∧
          (∀ n, CanonicalFiniteHardyFrontier (B n) eta z ∧
            (B n).natDegree ≤ max (radialRoucheIndex A L C n) 3) ∧
          (∀ n, (radialRoucheIndex A L C n : ℝ) <
            radialRoucheIndexGrowthConstant A L C *
              Real.exp (5 * quantitativeSpectralRadialBoundary n)) ∧
          (∀ (n : ℕ) {w : ℂ},
            ‖w‖ = quantitativeSpectralRadialBoundary n →
              Real.exp
                  (-C * Real.exp
                    (5 * quantitativeSpectralRadialBoundary n)) ≤
                ‖riemannXiSpectral w‖) ∧
          (∀ n : ℕ,
            realPolynomialRootCountInBall (B n) 0
                (quantitativeSpectralRadialBoundary n) =
              riemannXiSpectralRadialDivisorCount
                (quantitativeSpectralRadialBoundary n)) ∧
          ∀ (u : ℂ) (tau : ℝ), 0 < u.im → 0 < tau →
            Tendsto
              (fun n ↦ realPolynomialUpperHeatRemainderOutsideRootMultiset
                (B n) (realPolynomialUpperRootMultisetInsideBall (B n)
                  (quantitativeSpectralRadialBoundary n)) u tau)
              atTop (nhds 0) := by
  obtain ⟨eta, heta, z, hz, A, hA, C, hC, B,
      hindexLimit, hlimit, hfrontier, hgrowth, hfloor, hcount⟩ :=
    exists_radialRouche_exactDivisor_sequence_of_not_rh hRH
  let L : ℝ := finiteERootPinnedRadialConstant A eta z
  have hL : 0 < L := by
    simpa [L] using
      (finiteERootPinnedRadialConstant_pos (A := A) (eta := eta) (z := z))
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  refine ⟨eta, heta, z, hz, A, hA, C, hC, B, ?_⟩
  dsimp only
  refine ⟨by simpa [L] using hindexLimit, hlimit, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simpa [L] using hfrontier n
  · intro n
    simpa [L] using hgrowth n
  · intro n w hw
    exact hfloor n hw
  · intro n
    simpa [L] using hcount n
  · intro u tau hu htau
    apply tendsto_radialRouche_upperHeatRemainderOutsideInsideBall_zero
      hA0 hL.le hC.le B
    · intro n
      simpa [L] using (hfrontier n).2
    · intro n
      simpa [L] using hgrowth n
    · exact hu
    · exact htau

end

end RiemannGaussian
