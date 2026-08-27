import RiemannGaussian.FiniteToEntireRadialShellSummability

/-!
# Complete fixed-time radial heat limit

This file applies the summable shell majorant and Tannery's theorem to the
cross-stage radial divisor counts.  Every polynomial shell before stage `n`
is dominated by the same summable sequence, every fixed shell converges to
its genuine spectral-xi counterpart, and the selected radial spectral windows
exhaust the complete fixed-time heat series.

The resulting theorem identifies the varying inside-circle polynomial heat
with the complete spectral-xi heat sum.  Adding the already-vanishing outer
root remainder then proves convergence of the full upper polynomial heat for
the canonical finite Hardy sequence forced by failure of RH.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- Every upper polynomial root in a radial annulus is separated from an
arbitrary observation point by the nonnegative radial clearance. -/
theorem max_sub_norm_zero_le_dist_of_mem_upperRootRadialAnnulus
    (A : ℝ[X]) (r R : ℝ) (z : ℂ) {alpha : ℂ}
    (halpha : alpha ∈
      realPolynomialUpperRootMultisetInRadialAnnulus A r R) :
    max (r - ‖z‖) 0 ≤ dist z alpha := by
  have hout : alpha ∉ ball 0 r :=
    (Multiset.mem_filter.mp halpha).2.2
  have hrnorm : r ≤ ‖alpha‖ := by
    simpa [mem_ball, dist_zero_right] using hout
  apply max_le
  · calc
      r - ‖z‖ ≤ ‖alpha‖ - ‖z‖ := sub_le_sub_right hrnorm _
      _ ≤ ‖alpha - z‖ := norm_sub_norm_le alpha z
      _ = dist z alpha := by rw [dist_eq_norm, norm_sub_rev]
  · exact dist_nonneg

/-- Exact spectral counts on two nested circles and Jensen's divisor bound
give a quadratic-Gaussian heat estimate with nonnegative radial clearance,
without assuming that the inner circle already surrounds the observation
point. -/
theorem finiteUpperHeatInRadialAnnulus_le_quadraticMaxGaussian_of_growth
    (P : ℝ[X]) {K r R : ℝ} (z : ℂ) {tau : ℝ}
    (hK : 1 ≤ K) (hR : 0 < R)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (K * (‖w‖ + 1) ^ 2))
    (htau : 0 < tau) (hrR : r ≤ R)
    (hinner : realPolynomialRootCountInBall P 0 r =
      riemannXiSpectralRadialDivisorCount r)
    (houter : realPolynomialRootCountInBall P 0 R =
      riemannXiSpectralRadialDivisorCount R) :
    finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus P r R) tau ≤
      (K * (2 * (R + 1) + 1) ^ 2 / Real.log 2) *
        (tau⁻¹ * Real.exp (-((max (r - ‖z‖) 0) ^ 2 * tau))) := by
  let upper := realPolynomialUpperRootMultisetInRadialAnnulus P r R
  let d : ℝ := max (r - ‖z‖) 0
  have hd : 0 ≤ d := le_max_right _ _
  have hdist : ∀ alpha ∈ upper, d ≤ dist z alpha := by
    intro alpha halpha
    exact max_sub_norm_zero_le_dist_of_mem_upperRootRadialAnnulus
      P r R z halpha
  have hheat := finiteUpperHyperbolicHeatSum_le_card_mul_radialGaussian
    z upper htau hd hdist
  have hcard :=
    upperRootMultisetInRadialAnnulus_card_le_spectralDivisor_sub
      P hrR hinner houter
  have hsub :
      ((riemannXiSpectralRadialDivisorCount R -
          riemannXiSpectralRadialDivisorCount r : ℕ) : ℝ) ≤
        (riemannXiSpectralRadialDivisorCount R : ℝ) := by
    exact_mod_cast Nat.sub_le
      (riemannXiSpectralRadialDivisorCount R)
      (riemannXiSpectralRadialDivisorCount r)
  have hdivisor :
      ((riemannXiSpectralRadialDivisorCount R -
          riemannXiSpectralRadialDivisorCount r : ℕ) : ℝ) ≤
        K * (2 * (R + 1) + 1) ^ 2 / Real.log 2 :=
    hsub.trans
      (riemannXiSpectralRadialDivisorCount_cast_le_of_growth
        hK hR hbound)
  have hGaussian :
      0 ≤ tau⁻¹ * Real.exp (-(d ^ 2 * tau)) := by positivity
  calc
    finiteUpperHyperbolicHeatSum z upper tau ≤
        (upper.card : ℝ) *
          (tau⁻¹ * Real.exp (-(d ^ 2 * tau))) := hheat
    _ ≤ ((riemannXiSpectralRadialDivisorCount R -
          riemannXiSpectralRadialDivisorCount r : ℕ) : ℝ) *
          (tau⁻¹ * Real.exp (-(d ^ 2 * tau))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hGaussian
    _ ≤ (K * (2 * (R + 1) + 1) ^ 2 / Real.log 2) *
          (tau⁻¹ * Real.exp (-(d ^ 2 * tau))) :=
      mul_le_mul_of_nonneg_right hdivisor hGaussian
    _ = (K * (2 * (R + 1) + 1) ^ 2 / Real.log 2) *
          (tau⁻¹ * Real.exp (-((max (r - ‖z‖) 0) ^ 2 * tau))) := rfl

/-- If stage `n` has the genuine divisor count on its own selected circle
and on every earlier selected circle, then every shell `m < n` is bounded by
the fixed selected-shell majorant. -/
theorem finiteUpperHeatInSelectedRadialAnnulus_le_majorant
    (P : ℝ[X]) {K : ℝ} (hK : 1 ≤ K)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (K * (‖w‖ + 1) ^ 2))
    {m n : ℕ} (hmn : m < n)
    (hcurrent : realPolynomialRootCountInBall P 0
        (quantitativeSpectralRadialBoundary n) =
      riemannXiSpectralRadialDivisorCount
        (quantitativeSpectralRadialBoundary n))
    (hearlier : ∀ k : ℕ, k + 1 ≤ n →
      realPolynomialRootCountInBall P 0
          (quantitativeSpectralRadialBoundary k) =
        riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary k))
    (z : ℂ) {tau : ℝ} (htau : 0 < tau) :
    finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus P
          (quantitativeSpectralRadialBoundary m)
          (quantitativeSpectralRadialBoundary (m + 1))) tau ≤
      selectedRadialHeatShellMajorant K z tau m := by
  have hinner := hearlier m (by omega)
  have houter :
      realPolynomialRootCountInBall P 0
          (quantitativeSpectralRadialBoundary (m + 1)) =
        riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary (m + 1)) := by
    by_cases hlast : m + 1 = n
    · simpa [hlast] using hcurrent
    · exact hearlier (m + 1) (by omega)
  simpa [selectedRadialHeatShellMajorant] using
    finiteUpperHeatInRadialAnnulus_le_quadraticMaxGaussian_of_growth
      P z hK (quantitativeSpectralRadialBoundary_pos (m + 1))
      hbound htau
      (quantitativeSpectralRadialBoundary_lt_of_succ_le
        (m := m) (n := m + 1) (by omega)).le
      hinner houter

/-- Cross-stage counts, fixed-shell transport, and the summable radial
majorant satisfy Tannery's theorem.  Thus the genuine spectral annular heats
are summable and the moving sum of all polynomial shells before stage `n`
converges to their complete topological sum. -/
theorem summable_spectralRadialAnnularHeat_and_tendsto_polynomialShellSum
    (B : ℕ → ℝ[X])
    (hlimit : TendstoLocallyUniformlyOn
      (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
      riemannXiSpectral atTop Set.univ)
    {K : ℝ} (hK : 1 ≤ K)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (K * (‖w‖ + 1) ^ 2))
    (hcurrent : ∀ n : ℕ,
      realPolynomialRootCountInBall (B n) 0
          (quantitativeSpectralRadialBoundary n) =
        riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary n))
    (hearlier : ∀ (n m : ℕ), m + 1 ≤ n →
      realPolynomialRootCountInBall (B n) 0
          (quantitativeSpectralRadialBoundary m) =
        riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary m))
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Summable (fun m : ℕ ↦
      riemannXiUpperHyperbolicHeatRadialAnnulus z tau
        (quantitativeSpectralRadialBoundary m)
        (quantitativeSpectralRadialBoundary (m + 1))) ∧
    Tendsto
      (fun n ↦ ∑ m ∈ Finset.range n,
        finiteUpperHyperbolicHeatSum z
          (realPolynomialUpperRootMultisetInRadialAnnulus (B n)
            (quantitativeSpectralRadialBoundary m)
            (quantitativeSpectralRadialBoundary (m + 1))) tau)
      atTop
      (nhds (∑' m : ℕ,
        riemannXiUpperHyperbolicHeatRadialAnnulus z tau
          (quantitativeSpectralRadialBoundary m)
          (quantitativeSpectralRadialBoundary (m + 1)))) := by
  apply summable_limit_and_tendsto_sum_range_of_dominated
    (fun n m ↦ finiteUpperHyperbolicHeatSum z
      (realPolynomialUpperRootMultisetInRadialAnnulus (B n)
        (quantitativeSpectralRadialBoundary m)
        (quantitativeSpectralRadialBoundary (m + 1))) tau)
    (fun m ↦ riemannXiUpperHyperbolicHeatRadialAnnulus z tau
      (quantitativeSpectralRadialBoundary m)
      (quantitativeSpectralRadialBoundary (m + 1)))
    (selectedRadialHeatShellMajorant K z tau)
  · intro m
    exact selectedRadialHeatShellMajorant_nonneg
      (zero_le_one.trans hK) z htau m
  · exact summable_selectedRadialHeatShellMajorant
      (zero_le_one.trans hK) z htau
  · intro m
    exact tendsto_finiteUpperHeatInSelectedRadialAnnulus
      B hlimit m hz htau
  · intro n m hmn
    have hnonneg :
        0 ≤ finiteUpperHyperbolicHeatSum z
          (realPolynomialUpperRootMultisetInRadialAnnulus (B n)
            (quantitativeSpectralRadialBoundary m)
            (quantitativeSpectralRadialBoundary (m + 1))) tau := by
      apply finiteUpperHyperbolicHeatSum_nonneg hz
      · intro alpha halpha
        have hupper : alpha ∈ realPolynomialUpperRootMultiset (B n) :=
          Multiset.mem_of_mem_filter halpha
        exact (Multiset.mem_filter.mp hupper).2
      · exact htau
    rw [abs_of_nonneg hnonneg]
    exact finiteUpperHeatInSelectedRadialAnnulus_le_majorant
      (B n) hK hbound hmn (hcurrent n)
        (fun k hkn ↦ hearlier n k hkn) z htau

/-- The heat inside the `n`th selected disk is exactly the heat inside the
first disk plus the sum of the first `n` selected annular heats. -/
theorem finiteUpperHeatInsideFirstBall_add_sum_selectedAnnuli
    (P : ℝ[X]) (n : ℕ) (z : ℂ) (tau : ℝ) :
    finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInsideBall P
          (quantitativeSpectralRadialBoundary 0)) tau +
      ∑ m ∈ Finset.range n,
        finiteUpperHyperbolicHeatSum z
          (realPolynomialUpperRootMultisetInRadialAnnulus P
            (quantitativeSpectralRadialBoundary m)
            (quantitativeSpectralRadialBoundary (m + 1))) tau =
      finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInsideBall P
          (quantitativeSpectralRadialBoundary n)) tau := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        finiteUpperHyperbolicHeatSum z
              (realPolynomialUpperRootMultisetInsideBall P
                (quantitativeSpectralRadialBoundary 0)) tau +
            ((∑ m ∈ Finset.range n,
                finiteUpperHyperbolicHeatSum z
                  (realPolynomialUpperRootMultisetInRadialAnnulus P
                    (quantitativeSpectralRadialBoundary m)
                    (quantitativeSpectralRadialBoundary (m + 1))) tau) +
              finiteUpperHyperbolicHeatSum z
                (realPolynomialUpperRootMultisetInRadialAnnulus P
                  (quantitativeSpectralRadialBoundary n)
                  (quantitativeSpectralRadialBoundary (n + 1))) tau) =
            (finiteUpperHyperbolicHeatSum z
                (realPolynomialUpperRootMultisetInsideBall P
                  (quantitativeSpectralRadialBoundary 0)) tau +
              ∑ m ∈ Finset.range n,
                finiteUpperHyperbolicHeatSum z
                  (realPolynomialUpperRootMultisetInRadialAnnulus P
                    (quantitativeSpectralRadialBoundary m)
                    (quantitativeSpectralRadialBoundary (m + 1))) tau) +
              finiteUpperHyperbolicHeatSum z
                (realPolynomialUpperRootMultisetInRadialAnnulus P
                  (quantitativeSpectralRadialBoundary n)
                  (quantitativeSpectralRadialBoundary (n + 1))) tau := by
          ring
        _ = finiteUpperHyperbolicHeatSum z
                (realPolynomialUpperRootMultisetInsideBall P
                  (quantitativeSpectralRadialBoundary n)) tau +
              finiteUpperHyperbolicHeatSum z
                (realPolynomialUpperRootMultisetInRadialAnnulus P
                  (quantitativeSpectralRadialBoundary n)
                  (quantitativeSpectralRadialBoundary (n + 1))) tau := by
          rw [ih]
        _ = finiteUpperHyperbolicHeatSum z
              (realPolynomialUpperRootMultisetInsideBall P
                (quantitativeSpectralRadialBoundary (n + 1))) tau :=
          finiteUpperHeatInsideBall_add_annulus P
            (quantitativeSpectralRadialBoundary_lt_of_succ_le
              (m := n) (n := n + 1) (by omega)).le z tau

/-- The genuine radial spectral windows obey the same exact finite
telescoping identity. -/
theorem riemannXiUpperHeatFirstRadialWindow_add_sum_annuli
    (z : ℂ) (tau : ℝ) (n : ℕ) :
    riemannXiUpperHyperbolicHeatRadialWindow z tau
        (quantitativeSpectralRadialBoundary 0) +
      ∑ m ∈ Finset.range n,
        riemannXiUpperHyperbolicHeatRadialAnnulus z tau
          (quantitativeSpectralRadialBoundary m)
          (quantitativeSpectralRadialBoundary (m + 1)) =
      riemannXiUpperHyperbolicHeatRadialWindow z tau
        (quantitativeSpectralRadialBoundary n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        riemannXiUpperHyperbolicHeatRadialWindow z tau
              (quantitativeSpectralRadialBoundary 0) +
            ((∑ m ∈ Finset.range n,
                riemannXiUpperHyperbolicHeatRadialAnnulus z tau
                  (quantitativeSpectralRadialBoundary m)
                  (quantitativeSpectralRadialBoundary (m + 1))) +
              riemannXiUpperHyperbolicHeatRadialAnnulus z tau
                (quantitativeSpectralRadialBoundary n)
                (quantitativeSpectralRadialBoundary (n + 1))) =
            (riemannXiUpperHyperbolicHeatRadialWindow z tau
                (quantitativeSpectralRadialBoundary 0) +
              ∑ m ∈ Finset.range n,
                riemannXiUpperHyperbolicHeatRadialAnnulus z tau
                  (quantitativeSpectralRadialBoundary m)
                  (quantitativeSpectralRadialBoundary (m + 1))) +
              riemannXiUpperHyperbolicHeatRadialAnnulus z tau
                (quantitativeSpectralRadialBoundary n)
                (quantitativeSpectralRadialBoundary (n + 1)) := by ring
        _ = riemannXiUpperHyperbolicHeatRadialWindow z tau
                (quantitativeSpectralRadialBoundary n) +
              riemannXiUpperHyperbolicHeatRadialAnnulus z tau
                (quantitativeSpectralRadialBoundary n)
                (quantitativeSpectralRadialBoundary (n + 1)) := by rw [ih]
        _ = riemannXiUpperHyperbolicHeatRadialWindow z tau
              (quantitativeSpectralRadialBoundary (n + 1)) := by
          unfold riemannXiUpperHyperbolicHeatRadialAnnulus
          ring

/-- Every fixed nontrivial zeta zero eventually belongs to the selected
expanding radial windows. -/
theorem eventually_mem_spectralZetaZeroRadialWindow_selected
    (rho : NontrivialZetaZero) :
    ∀ᶠ n in atTop,
      rho ∈ spectralZetaZeroRadialWindow
        (quantitativeSpectralRadialBoundary n) := by
  have hradius : ∀ᶠ n in atTop,
      ‖zetaSpectralCoordinate rho.1‖ <
        quantitativeSpectralRadialBoundary n :=
    tendsto_quantitativeSpectralRadialBoundary_atTop
      (eventually_gt_atTop ‖zetaSpectralCoordinate rho.1‖)
  filter_upwards [hradius] with n hn
  exact (mem_spectralZetaZeroRadialWindow
    (quantitativeSpectralRadialBoundary_pos n).le rho).mpr hn

/-- The selected finite radial zero windows are cofinal among all finite
sets of nontrivial zeta zeros. -/
theorem tendsto_spectralZetaZeroRadialWindow_selected_atTop :
    Tendsto
      (fun n ↦ spectralZetaZeroRadialWindow
        (quantitativeSpectralRadialBoundary n))
      atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | @insert rho S hrho ih =>
      filter_upwards
        [ih, eventually_mem_spectralZetaZeroRadialWindow_selected rho]
        with n hnS hnrho
      exact Finset.insert_subset hnrho hnS

/-- Along the selected expanding circles, the genuine finite radial upper
heat windows converge to the already-constructed complete spectral-xi heat
sum. -/
theorem tendsto_riemannXiUpperHeatRadialWindow_selected
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ riemannXiUpperHyperbolicHeatRadialWindow z tau
        (quantitativeSpectralRadialBoundary n))
      atTop (nhds (riemannXiUpperHyperbolicHeatSum z tau)) := by
  have hHasSum := (summable_zetaUpperHyperbolicHeatSummand hz htau).hasSum
  have hSelected := hHasSum.comp
    tendsto_spectralZetaZeroRadialWindow_selected_atTop
  unfold riemannXiUpperHyperbolicHeatRadialWindow
    riemannXiUpperHyperbolicHeatSum
  apply hSelected.congr'
  exact Eventually.of_forall fun n ↦
    Finset.sum_subtype
      (spectralZetaZeroRadialWindow
        (quantitativeSpectralRadialBoundary n))
      (fun _ ↦ Iff.rfl) (zetaUpperHyperbolicHeatSummand z tau)

/-- The first selected radial heat window plus the topological sum of all
consecutive selected annular heats is exactly the complete spectral-xi heat
sum. -/
theorem riemannXiUpperHeatFirstRadialWindow_add_tsum_annuli_eq_complete
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (hsum : Summable fun m : ℕ ↦
      riemannXiUpperHyperbolicHeatRadialAnnulus z tau
        (quantitativeSpectralRadialBoundary m)
        (quantitativeSpectralRadialBoundary (m + 1))) :
    riemannXiUpperHyperbolicHeatRadialWindow z tau
        (quantitativeSpectralRadialBoundary 0) +
      ∑' m : ℕ, riemannXiUpperHyperbolicHeatRadialAnnulus z tau
        (quantitativeSpectralRadialBoundary m)
        (quantitativeSpectralRadialBoundary (m + 1)) =
      riemannXiUpperHyperbolicHeatSum z tau := by
  have hconstant :
      Tendsto
        (fun _ : ℕ ↦ riemannXiUpperHyperbolicHeatRadialWindow z tau
          (quantitativeSpectralRadialBoundary 0))
        atTop
        (nhds (riemannXiUpperHyperbolicHeatRadialWindow z tau
          (quantitativeSpectralRadialBoundary 0))) := tendsto_const_nhds
  have hpartial := hconstant.add hsum.hasSum.tendsto_sum_nat
  have hpartialRadial :
      Tendsto
        (fun n ↦ riemannXiUpperHyperbolicHeatRadialWindow z tau
          (quantitativeSpectralRadialBoundary n))
        atTop
        (nhds
          (riemannXiUpperHyperbolicHeatRadialWindow z tau
              (quantitativeSpectralRadialBoundary 0) +
            ∑' m : ℕ, riemannXiUpperHyperbolicHeatRadialAnnulus z tau
              (quantitativeSpectralRadialBoundary m)
              (quantitativeSpectralRadialBoundary (m + 1)))) := by
    apply hpartial.congr'
    exact Eventually.of_forall fun n ↦
      riemannXiUpperHeatFirstRadialWindow_add_sum_annuli z tau n
  exact tendsto_nhds_unique hpartialRadial
    (tendsto_riemannXiUpperHeatRadialWindow_selected hz htau)

/-- The heat of the upper polynomial roots in the moving selected disk
converges to the complete fixed-time spectral-xi heat sum. -/
theorem tendsto_finiteUpperHeatInsideSelectedRadialBall
    (B : ℕ → ℝ[X])
    (hlimit : TendstoLocallyUniformlyOn
      (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
      riemannXiSpectral atTop Set.univ)
    {K : ℝ} (hK : 1 ≤ K)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (K * (‖w‖ + 1) ^ 2))
    (hcurrent : ∀ n : ℕ,
      realPolynomialRootCountInBall (B n) 0
          (quantitativeSpectralRadialBoundary n) =
        riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary n))
    (hearlier : ∀ (n m : ℕ), m + 1 ≤ n →
      realPolynomialRootCountInBall (B n) 0
          (quantitativeSpectralRadialBoundary m) =
        riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary m))
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n ↦ finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInsideBall (B n)
          (quantitativeSpectralRadialBoundary n)) tau)
      atTop (nhds (riemannXiUpperHyperbolicHeatSum z tau)) := by
  obtain ⟨hshellSummable, hshellLimit⟩ :=
    summable_spectralRadialAnnularHeat_and_tendsto_polynomialShellSum
      B hlimit hK hbound hcurrent hearlier hz htau
  have hbase :
      Tendsto
        (fun n ↦ finiteUpperHyperbolicHeatSum z
          (realPolynomialUpperRootMultisetInsideBall (B n)
            (quantitativeSpectralRadialBoundary 0)) tau)
        atTop
        (nhds (riemannXiUpperHyperbolicHeatRadialWindow z tau
          (quantitativeSpectralRadialBoundary 0))) := by
    apply tendsto_finiteUpperHeatInsideRadialBall
      B hlimit (quantitativeSpectralRadialBoundary_pos 0)
    · intro w hw
      apply riemannXiSpectral_ne_zero_on_quantitativeRadialBoundary 0
      simpa [mem_sphere, dist_zero_right] using hw
    · exact hz
    · exact htau
  have hcombined := hbase.add hshellLimit
  have htarget :=
    riemannXiUpperHeatFirstRadialWindow_add_tsum_annuli_eq_complete
      hz htau hshellSummable
  rw [htarget] at hcombined
  apply hcombined.congr'
  exact Eventually.of_forall fun n ↦
    finiteUpperHeatInsideFirstBall_add_sum_selectedAnnuli (B n) n z tau

/-- If the moving outside-root heat tends to zero, the complete upper
polynomial heat converges to the complete spectral-xi heat sum. -/
theorem tendsto_realPolynomialUpperHeatSum_of_radialCounts
    (B : ℕ → ℝ[X])
    (hlimit : TendstoLocallyUniformlyOn
      (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
      riemannXiSpectral atTop Set.univ)
    {K : ℝ} (hK : 1 ≤ K)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (K * (‖w‖ + 1) ^ 2))
    (hcurrent : ∀ n : ℕ,
      realPolynomialRootCountInBall (B n) 0
          (quantitativeSpectralRadialBoundary n) =
        riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary n))
    (hearlier : ∀ (n m : ℕ), m + 1 ≤ n →
      realPolynomialRootCountInBall (B n) 0
          (quantitativeSpectralRadialBoundary m) =
        riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary m))
    {z : ℂ} (hz : 0 < z.im) {tau : ℝ} (htau : 0 < tau)
    (htail : Tendsto
      (fun n ↦ realPolynomialUpperHeatRemainderOutsideRootMultiset
        (B n) (realPolynomialUpperRootMultisetInsideBall (B n)
          (quantitativeSpectralRadialBoundary n)) z tau)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ realPolynomialUpperHyperbolicHeatSum (B n) z tau)
      atTop (nhds (riemannXiUpperHyperbolicHeatSum z tau)) := by
  have hinside := tendsto_finiteUpperHeatInsideSelectedRadialBall
    B hlimit hK hbound hcurrent hearlier hz htau
  have hfull :
      Tendsto (fun n ↦ realPolynomialUpperHyperbolicHeatSum (B n) z tau)
        atTop (nhds (riemannXiUpperHyperbolicHeatSum z tau + 0)) := by
    apply (hinside.add htail).congr'
    exact Eventually.of_forall fun n ↦
      (realPolynomialUpperHeatSum_eq_insideBall_add_remainder
        (B n) (quantitativeSpectralRadialBoundary n) z tau).symm
  simpa using hfull

/-- Under failure of RH, the same canonical finite Hardy sequence used
throughout the reductio has full fixed-time upper-root heat converging to the
complete spectral-xi logarithmic-residue heat sum at every upper observation
point and every positive proper time. -/
theorem exists_canonicalFiniteHardyFrontier_fullHeat_tendsto_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      riemannXiSpectral z ≠ 0 ∧ ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        ∀ (u : ℂ) (tau : ℝ), 0 < u.im → 0 < tau →
          Tendsto
            (fun n ↦ realPolynomialUpperHyperbolicHeatSum (B n) u tau)
            atTop (nhds (riemannXiUpperHyperbolicHeatSum u tau)) := by
  obtain ⟨eta, heta, z, hz, hxi, _, _, _, _, B, hdata⟩ :=
    exists_radialRouche_crossStageDivisor_vanishingHeatTail_sequence_of_not_rh
      hRH
  dsimp only at hdata
  rcases hdata with
    ⟨_, hlimit, hfrontier, _, _, _, hcurrent, hearlier, htail⟩
  obtain ⟨K, hK, hKbound⟩ := riemannXi_quadraticGrowth
  refine ⟨eta, heta, z, hz, hxi, B, hlimit, ?_, ?_⟩
  · intro n
    exact (hfrontier n).1
  · intro u tau hu htau
    apply tendsto_realPolynomialUpperHeatSum_of_radialCounts
      B hlimit hK hKbound hcurrent hearlier hu htau
    exact htail u tau hu htau

end

end RiemannGaussian
