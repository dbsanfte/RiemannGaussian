import RiemannGaussian.FiniteToEntireRadialCrossStage

/-!
# Radial annular root and heat bounds

This file decomposes polynomial roots between nested radial disks, retaining
algebraic multiplicity.  Upper roots in an annulus form a submultiset of the
complete annular root multiset, so a cross-stage Rouché count bounds their
number by the genuine outer spectral-xi divisor.  Jensen's theorem supplies a
quadratic bound for that genuine radial divisor, yielding a summable Gaussian
majorant for the later shellwise heat passage.
-/

open Complex Filter MeromorphicOn Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- All complex polynomial-root occurrences in the radial annulus between
the open disks of radii `r` and `R`. -/
def realPolynomialRootMultisetInRadialAnnulus
    (A : ℝ[X]) (r R : ℝ) : Multiset ℂ :=
  (A.map Complex.ofRealHom).roots.filter fun w ↦
    w ∈ ball 0 R ∧ w ∉ ball 0 r

/-- The upper polynomial-root occurrences in the radial annulus between the
open disks of radii `r` and `R`. -/
def realPolynomialUpperRootMultisetInRadialAnnulus
    (A : ℝ[X]) (r R : ℝ) : Multiset ℂ :=
  (realPolynomialUpperRootMultiset A).filter fun w ↦
    w ∈ ball 0 R ∧ w ∉ ball 0 r

/-- For nested radii, the inner disk multiset plus the annular multiset is
the outer disk multiset, with every root occurrence retained. -/
theorem rootMultisetInBall_add_rootMultisetInRadialAnnulus
    (A : ℝ[X]) {r R : ℝ} (hrR : r ≤ R) :
    realPolynomialRootMultisetInBall A 0 r +
        realPolynomialRootMultisetInRadialAnnulus A r R =
      realPolynomialRootMultisetInBall A 0 R := by
  let roots := (A.map Complex.ofRealHom).roots
  change roots.filter (fun w ↦ w ∈ ball 0 r) +
      roots.filter (fun w ↦ w ∈ ball 0 R ∧ w ∉ ball 0 r) =
    roots.filter fun w ↦ w ∈ ball 0 R
  ext w
  simp only [Multiset.count_add, Multiset.count_filter]
  by_cases hwr : w ∈ ball 0 r
  · have hwR : w ∈ ball 0 R := ball_subset_ball hrR hwr
    simp [hwr, hwR]
  · by_cases hwR : w ∈ ball 0 R
    · simp [hwr, hwR]
    · simp [hwr, hwR]

/-- The total annular root count plus the inner root count equals the outer
root count. -/
theorem rootMultisetInRadialAnnulus_card_add_rootCountInBall
    (A : ℝ[X]) {r R : ℝ} (hrR : r ≤ R) :
    (realPolynomialRootMultisetInRadialAnnulus A r R).card +
        realPolynomialRootCountInBall A 0 r =
      realPolynomialRootCountInBall A 0 R := by
  have h := congrArg Multiset.card
    (rootMultisetInBall_add_rootMultisetInRadialAnnulus A hrR)
  simpa [realPolynomialRootCountInBall,
    realPolynomialRootMultisetInBall, Nat.add_comm] using h

/-- If the polynomial counts on two nested circles are the genuine spectral
divisor counts, its complete annular root multiplicity is their exact
difference. -/
theorem rootMultisetInRadialAnnulus_card_eq_spectralDivisor_sub
    (A : ℝ[X]) {r R : ℝ} (hrR : r ≤ R)
    (hinner : realPolynomialRootCountInBall A 0 r =
      riemannXiSpectralRadialDivisorCount r)
    (houter : realPolynomialRootCountInBall A 0 R =
      riemannXiSpectralRadialDivisorCount R) :
    (realPolynomialRootMultisetInRadialAnnulus A r R).card =
      riemannXiSpectralRadialDivisorCount R -
        riemannXiSpectralRadialDivisorCount r := by
  have hcount :=
    rootMultisetInRadialAnnulus_card_add_rootCountInBall A hrR
  rw [hinner, houter] at hcount
  omega

/-- The upper annular multiset is a submultiset of the complete annular root
multiset. -/
theorem upperRootMultisetInRadialAnnulus_le_rootMultisetInRadialAnnulus
    (A : ℝ[X]) (r R : ℝ) :
    realPolynomialUpperRootMultisetInRadialAnnulus A r R ≤
      realPolynomialRootMultisetInRadialAnnulus A r R := by
  unfold realPolynomialUpperRootMultisetInRadialAnnulus
    realPolynomialRootMultisetInRadialAnnulus
    realPolynomialUpperRootMultiset
  rw [Multiset.filter_filter]
  exact Multiset.monotone_filter_right _ fun w hw ↦ hw.1

/-- Upper roots in a radial annulus never outnumber all polynomial roots in
the outer disk. -/
theorem upperRootMultisetInRadialAnnulus_card_le_rootCountInBall
    (A : ℝ[X]) (r R : ℝ) :
    (realPolynomialUpperRootMultisetInRadialAnnulus A r R).card ≤
      realPolynomialRootCountInBall A 0 R := by
  let roots := (A.map Complex.ofRealHom).roots
  calc
    (realPolynomialUpperRootMultisetInRadialAnnulus A r R).card ≤
        (realPolynomialRootMultisetInRadialAnnulus A r R).card :=
      Multiset.card_le_card
        (upperRootMultisetInRadialAnnulus_le_rootMultisetInRadialAnnulus
          A r R)
    _ ≤ (realPolynomialRootMultisetInBall A 0 R).card := by
      apply Multiset.card_le_card
      exact Multiset.monotone_filter_right roots fun w hw ↦ hw.1
    _ = realPolynomialRootCountInBall A 0 R := rfl

/-- Under exact counts on two nested circles, the number of upper polynomial
roots in their annulus is bounded by the exact genuine spectral-divisor
increment. -/
theorem upperRootMultisetInRadialAnnulus_card_le_spectralDivisor_sub
    (A : ℝ[X]) {r R : ℝ} (hrR : r ≤ R)
    (hinner : realPolynomialRootCountInBall A 0 r =
      riemannXiSpectralRadialDivisorCount r)
    (houter : realPolynomialRootCountInBall A 0 R =
      riemannXiSpectralRadialDivisorCount R) :
    (realPolynomialUpperRootMultisetInRadialAnnulus A r R).card ≤
      riemannXiSpectralRadialDivisorCount R -
        riemannXiSpectralRadialDivisorCount r := by
  calc
    (realPolynomialUpperRootMultisetInRadialAnnulus A r R).card ≤
        (realPolynomialRootMultisetInRadialAnnulus A r R).card :=
      Multiset.card_le_card
        (upperRootMultisetInRadialAnnulus_le_rootMultisetInRadialAnnulus
          A r R)
    _ = riemannXiSpectralRadialDivisorCount R -
          riemannXiSpectralRadialDivisorCount r :=
      rootMultisetInRadialAnnulus_card_eq_spectralDivisor_sub
        A hrR hinner houter

/-- A positive radial spectral divisor is bounded by the Jensen divisor in
an ordinary xi disk and hence by an explicit quadratic expression. -/
theorem riemannXiSpectralRadialDivisorCount_cast_le_of_growth
    {A R : ℝ} (hA : 1 ≤ A) (hR : 0 < R)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ 2)) :
    (riemannXiSpectralRadialDivisorCount R : ℝ) ≤
      A * (2 * (R + 1) + 1) ^ 2 / Real.log 2 := by
  let S := spectralZetaZeroRadialWindow R
  have hSinBall : ∀ rho ∈ S, ‖(rho.1 : ℂ)‖ ≤ R + 1 := by
    intro rho hrho
    have hwindow :
        |(zetaSpectralCoordinate rho.1).re| ≤ R := by
      exact (Complex.abs_re_le_norm _).trans
        ((mem_spectralZetaZeroRadialWindow hR.le rho).mp hrho).le
    have hnorm := Complex.norm_le_abs_re_add_abs_im rho.1
    have hre : |rho.1.re| < 1 := by
      rw [abs_of_pos (NontrivialZetaZero.zero_lt_re rho)]
      exact NontrivialZetaZero.re_lt_one rho
    have him : |rho.1.im| ≤ R := by
      simpa only [zetaSpectralCoordinate_re] using hwindow
    linarith
  calc
    (riemannXiSpectralRadialDivisorCount R : ℝ) =
        ∑ rho ∈ S, (analyticZetaZeroMultiplicity rho : ℝ) := by
      simp [riemannXiSpectralRadialDivisorCount, S]
    _ ≤ ((∑ᶠ u,
        divisor riemannXi (closedBall 0 (R + 1)) u : ℤ) : ℝ) :=
      sum_analyticZetaZeroMultiplicity_le_riemannXi_divisor S hSinBall
    _ ≤ A * (2 * (R + 1) + 1) ^ 2 / Real.log 2 :=
      jensen_riemannXi_divisor_le hA (by linarith) hbound

/-- Spectral xi has one fixed quadratic upper bound for every positive radial
divisor count. -/
theorem exists_riemannXiSpectralRadialDivisorCount_quadratic_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ R : ℝ, 0 < R →
      (riemannXiSpectralRadialDivisorCount R : ℝ) ≤
        A * (2 * (R + 1) + 1) ^ 2 / Real.log 2 := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_quadraticGrowth
  exact ⟨A, hA, fun R hR ↦
    riemannXiSpectralRadialDivisorCount_cast_le_of_growth hA hR hbound⟩

/-- At a positive inner clearance from the observation point, the heat of
all upper roots in a radial annulus is bounded by their cardinality times one
Gaussian envelope. -/
theorem finiteUpperHeatInRadialAnnulus_le_card_mul_Gaussian
    (A : ℝ[X]) (r R : ℝ) (z : ℂ) {tau : ℝ} (htau : 0 < tau)
    (hrz : ‖z‖ ≤ r) :
    finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus A r R) tau ≤
      ((realPolynomialUpperRootMultisetInRadialAnnulus A r R).card : ℝ) *
        (tau⁻¹ * Real.exp (-((r - ‖z‖) ^ 2 * tau))) := by
  let upper := realPolynomialUpperRootMultisetInRadialAnnulus A r R
  let d : ℝ := r - ‖z‖
  have hd : 0 ≤ d := sub_nonneg.mpr hrz
  have hdist : ∀ alpha ∈ upper, d ≤ dist z alpha := by
    intro alpha halpha
    have hout : alpha ∉ ball 0 r :=
      (Multiset.mem_filter.mp halpha).2.2
    have hrnorm : r ≤ ‖alpha‖ := by
      simpa [mem_ball, dist_zero_right] using hout
    calc
      d = r - ‖z‖ := rfl
      _ ≤ ‖alpha‖ - ‖z‖ := sub_le_sub_right hrnorm _
      _ ≤ ‖alpha - z‖ := norm_sub_norm_le alpha z
      _ = dist z alpha := by rw [dist_eq_norm, norm_sub_rev]
  have hsum := finiteUpperHyperbolicHeatSum_le_card_mul_radialGaussian
    z upper htau hd hdist
  simpa [upper, d] using hsum

/-- At a positive inner clearance from the observation point, the heat of
all upper roots in a radial annulus is bounded by the outer polynomial root
count times one Gaussian envelope. -/
theorem finiteUpperHeatInRadialAnnulus_le_rootCount_mul_Gaussian
    (A : ℝ[X]) (r R : ℝ) (z : ℂ) {tau : ℝ} (htau : 0 < tau)
    (hrz : ‖z‖ ≤ r) :
    finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus A r R) tau ≤
      (realPolynomialRootCountInBall A 0 R : ℝ) *
        (tau⁻¹ * Real.exp (-((r - ‖z‖) ^ 2 * tau))) := by
  have hcard :
      (realPolynomialUpperRootMultisetInRadialAnnulus A r R).card ≤
        realPolynomialRootCountInBall A 0 R :=
    upperRootMultisetInRadialAnnulus_card_le_rootCountInBall A r R
  have hGaussian :
      0 ≤ tau⁻¹ * Real.exp (-((r - ‖z‖) ^ 2 * tau)) := by positivity
  calc
    finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus A r R) tau ≤
        ((realPolynomialUpperRootMultisetInRadialAnnulus A r R).card : ℝ) *
          (tau⁻¹ * Real.exp (-((r - ‖z‖) ^ 2 * tau))) :=
      finiteUpperHeatInRadialAnnulus_le_card_mul_Gaussian
        A r R z htau hrz
    _ ≤ (realPolynomialRootCountInBall A 0 R : ℝ) *
          (tau⁻¹ * Real.exp (-((r - ‖z‖) ^ 2 * tau))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hGaussian

/-- With exact spectral counts on the two boundary circles, the polynomial
upper-annulus heat is bounded by the genuine divisor increment times the
Gaussian clearance envelope. -/
theorem finiteUpperHeatInRadialAnnulus_le_spectralDivisorSub_mul_Gaussian
    (A : ℝ[X]) {r R : ℝ} (z : ℂ) {tau : ℝ} (htau : 0 < tau)
    (hrz : ‖z‖ ≤ r) (hrR : r ≤ R)
    (hinner : realPolynomialRootCountInBall A 0 r =
      riemannXiSpectralRadialDivisorCount r)
    (houter : realPolynomialRootCountInBall A 0 R =
      riemannXiSpectralRadialDivisorCount R) :
    finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus A r R) tau ≤
      ((riemannXiSpectralRadialDivisorCount R -
          riemannXiSpectralRadialDivisorCount r : ℕ) : ℝ) *
        (tau⁻¹ * Real.exp (-((r - ‖z‖) ^ 2 * tau))) := by
  have hcard :=
    upperRootMultisetInRadialAnnulus_card_le_spectralDivisor_sub
      A hrR hinner houter
  have hGaussian :
      0 ≤ tau⁻¹ * Real.exp (-((r - ‖z‖) ^ 2 * tau)) := by positivity
  exact (finiteUpperHeatInRadialAnnulus_le_card_mul_Gaussian
    A r R z htau hrz).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hGaussian)

/-- Jensen's quadratic divisor bound turns the exact annular comparison into
a stage-independent polynomial-times-Gaussian shell majorant. -/
theorem finiteUpperHeatInRadialAnnulus_le_quadraticGaussian_of_growth
    (P : ℝ[X]) {K r R : ℝ} (z : ℂ) {tau : ℝ}
    (hK : 1 ≤ K) (hR : 0 < R)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (K * (‖w‖ + 1) ^ 2))
    (htau : 0 < tau) (hrz : ‖z‖ ≤ r) (hrR : r ≤ R)
    (hinner : realPolynomialRootCountInBall P 0 r =
      riemannXiSpectralRadialDivisorCount r)
    (houter : realPolynomialRootCountInBall P 0 R =
      riemannXiSpectralRadialDivisorCount R) :
    finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus P r R) tau ≤
      (K * (2 * (R + 1) + 1) ^ 2 / Real.log 2) *
        (tau⁻¹ * Real.exp (-((r - ‖z‖) ^ 2 * tau))) := by
  have hdivisorSub :
      ((riemannXiSpectralRadialDivisorCount R -
          riemannXiSpectralRadialDivisorCount r : ℕ) : ℝ) ≤
        K * (2 * (R + 1) + 1) ^ 2 / Real.log 2 := by
    have hsub :
        riemannXiSpectralRadialDivisorCount R -
            riemannXiSpectralRadialDivisorCount r ≤
          riemannXiSpectralRadialDivisorCount R := Nat.sub_le _ _
    have hsubCast :
        ((riemannXiSpectralRadialDivisorCount R -
            riemannXiSpectralRadialDivisorCount r : ℕ) : ℝ) ≤
          (riemannXiSpectralRadialDivisorCount R : ℝ) := by
      exact_mod_cast hsub
    exact hsubCast.trans
      (riemannXiSpectralRadialDivisorCount_cast_le_of_growth
        hK hR hbound)
  have hGaussian :
      0 ≤ tau⁻¹ * Real.exp (-((r - ‖z‖) ^ 2 * tau)) := by positivity
  exact (finiteUpperHeatInRadialAnnulus_le_spectralDivisorSub_mul_Gaussian
    P z htau hrz hrR hinner houter).trans
      (mul_le_mul_of_nonneg_right hdivisorSub hGaussian)

/-- A polynomial whose cross-stage counts are synchronized through stage
`n` obeys the uniform quadratic-Gaussian bound on every consecutive selected
annulus ending at least one circle before `n`. -/
theorem finiteUpperHeatInEarlierScheduledRadialAnnulus_le_quadraticGaussian
    (P : ℝ[X]) {K : ℝ}
    (hK : 1 ≤ K)
    (hbound : ∀ w : ℂ,
      ‖riemannXi w‖ ≤ Real.exp (K * (‖w‖ + 1) ^ 2))
    {m n : ℕ} (hmn : m + 2 ≤ n)
    (hcounts : ∀ k : ℕ, k + 1 ≤ n →
      realPolynomialRootCountInBall P 0
          (quantitativeSpectralRadialBoundary k) =
        riemannXiSpectralRadialDivisorCount
          (quantitativeSpectralRadialBoundary k))
    (z : ℂ) {tau : ℝ} (htau : 0 < tau)
    (hrz : ‖z‖ ≤ quantitativeSpectralRadialBoundary m) :
    finiteUpperHyperbolicHeatSum z
        (realPolynomialUpperRootMultisetInRadialAnnulus P
          (quantitativeSpectralRadialBoundary m)
          (quantitativeSpectralRadialBoundary (m + 1))) tau ≤
      (K *
          (2 * (quantitativeSpectralRadialBoundary (m + 1) + 1) + 1) ^ 2 /
            Real.log 2) *
        (tau⁻¹ * Real.exp
          (-((quantitativeSpectralRadialBoundary m - ‖z‖) ^ 2 * tau))) := by
  apply finiteUpperHeatInRadialAnnulus_le_quadraticGaussian_of_growth
    P z hK (quantitativeSpectralRadialBoundary_pos (m + 1)) hbound
      htau hrz
  · exact (quantitativeSpectralRadialBoundary_lt_of_succ_le
      (m := m) (n := m + 1) (by omega)).le
  · exact hcounts m (by omega)
  · exact hcounts (m + 1) (by omega)

end

end RiemannGaussian
