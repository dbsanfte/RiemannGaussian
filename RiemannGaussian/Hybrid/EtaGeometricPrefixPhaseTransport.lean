import RiemannGaussian.Hybrid.EtaGeometricPrefixVandermonde
import RiemannGaussian.Hybrid.EtaGeometricPhaseDecorrelation

/-!
# Transporting phase decorrelation to literal eta prefixes

This module transports the quantitative unit-mode decorrelation estimate to
the project's literal finite eta prefixes. On a fixed real-coordinate layer
`Re(rho) = sigma`, it applies three exact nonzero normalizations to the prefix
at consecutive geometric cutoffs: the checked row asymptotic scale, the
inverse nonzero leading constant, and the common coordinate factor
`q^(sigma*j)`. The resulting length-`M` vector converges coordinatewise to the
first `M` powers of the unit eta mode.

Lean passes this convergence through the complete complex correlation, both
squared norms, and their normalized squared coherence. Combining that limit
with the checked finite phase-gap theorem gives an eventual, uniform
`4/M^2 + epsilon` ceiling for all distinct pairs in an arbitrary finite
same-real-part zeta-zero layer after selecting one odd prime. The statement is
also specialized to every critical-zero window.

This is a quantitative theorem about literal eta-prefix values, not only their
limiting modes. It still uses row and coordinate normalization and treats one
real-decay layer at a time. The next step must carry the estimate through the
actual packed reflection-even features, retain cross-layer off-line real
decay, and aggregate the pair bounds in the certificate reserve. No improved
zero proportion is claimed here.
-/

open Complex Filter Topology Finset
open scoped BigOperators ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- Literal multiplicity-minus-one eta prefixes after exact row, leading-term,
and same-real-layer coordinate normalization. -/
def pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
    (q : ℕ) (σ : ℝ) (rho : NontrivialZetaZero)
    (n M : ℕ) : Fin M → ℂ := fun j ↦
  (pairedEtaLowerMomentGeometricLimit rho)⁻¹ *
    (((q : ℂ) ^ rho.val) ^ n *
      (((q : ℂ) ^ (σ : ℂ)) ^ (j : ℕ) *
        pairedEtaLowerMomentGeometricPrefix q rho (n + (j : ℕ))))

/-- Each fixed coordinate of the normalized literal eta-prefix block
converges to the corresponding power of the normalized eta mode. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {σ : ℝ}
    (rho : NontrivialZetaZero) (hre : rho.val.re = σ)
    (M : ℕ) (j : Fin M) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
        q σ rho n M j) atTop
      (nhds (finiteGeometricPhaseVector M
        (etaGeometricNormalizedMode q rho.val) j)) := by
  have hprefix := tendsto_pairedEtaLowerMomentGeometricPrefix_rowScaled
    rho hqOdd hq (j : ℕ)
  have hscaled := Filter.Tendsto.const_mul
    ((pairedEtaLowerMomentGeometricLimit rho)⁻¹ *
      ((q : ℂ) ^ (σ : ℂ)) ^ (j : ℕ)) hprefix
  convert hscaled using 1
  · funext n
    unfold pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
    ring
  · unfold finiteGeometricPhaseVector
    have hlimit := pairedEtaLowerMomentGeometricLimit_ne_zero rho
    have hmode := etaGeometricNormalizedMode_eq_real_cpow_mul_decayMode
      hq.le rho.val
    rw [hre] at hmode
    rw [hmode, mul_pow]
    field_simp

/-- The complete fixed-length normalized literal prefix vector converges to
the corresponding unit-mode phase vector. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {σ : ℝ}
    (rho : NontrivialZetaZero) (hre : rho.val.re = σ) (M : ℕ) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
        q σ rho n M) atTop
      (nhds (finiteGeometricPhaseVector M
        (etaGeometricNormalizedMode q rho.val))) := by
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply
    hqOdd hq rho hre M j

/-- Full complex correlation of two phase-normalized literal eta-prefix
blocks. -/
def pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation
    (q : ℕ) (σ : ℝ) (rho zeta : NontrivialZetaZero)
    (n M : ℕ) : ℂ :=
  star (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
      q σ zeta n M) ⬝ᵥ
    pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector q σ rho n M

/-- Literal normalized-prefix correlations converge to the exact finite
geometric-mode correlations with their complex phase intact. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {σ : ℝ}
    (rho zeta : NontrivialZetaZero)
    (hrho : rho.val.re = σ) (hzeta : zeta.val.re = σ) (M : ℕ) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation
        q σ rho zeta n M) atTop
      (nhds (star (finiteGeometricPhaseVector M
          (etaGeometricNormalizedMode q zeta.val)) ⬝ᵥ
        finiteGeometricPhaseVector M
          (etaGeometricNormalizedMode q rho.val))) := by
  unfold pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation
    dotProduct
  simpa using tendsto_finsetSum (Finset.univ : Finset (Fin M))
    (fun j _hj ↦
      (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply
        hqOdd hq zeta hzeta M j).star.mul
      (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply
        hqOdd hq rho hrho M j))

/-- Squared Euclidean norm of a phase-normalized literal eta-prefix block. -/
def pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
    (q : ℕ) (σ : ℝ) (rho : NontrivialZetaZero)
    (n M : ℕ) : ℝ :=
  ∑ j : Fin M,
    ‖pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
      q σ rho n M j‖ ^ 2

/-- The normalized literal prefix norm square converges to the exact unit-mode
value `M`. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {σ : ℝ}
    (rho : NontrivialZetaZero) (hre : rho.val.re = σ) (M : ℕ) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
        q σ rho n M) atTop (nhds (M : ℝ)) := by
  unfold pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin M))
    (fun j _hj ↦
      (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply
        hqOdd hq rho hre M j).norm.pow 2)
  convert hsum using 1
  simp [norm_etaGeometricNormalizedMode hq.le,
    finiteGeometricPhaseVector_normSq]

/-- Squared absolute correlation divided by the product of both literal
normalized-prefix norm squares. -/
def pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
    (q : ℕ) (σ : ℝ) (rho zeta : NontrivialZetaZero)
    (n M : ℕ) : ℝ :=
  ‖pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation
      q σ rho zeta n M‖ ^ 2 /
    (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq q σ rho n M *
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq q σ zeta n M)

/-- At every positive fixed block length, literal normalized-prefix squared
coherence converges to the finite unit-mode squared coherence. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {σ : ℝ}
    (rho zeta : NontrivialZetaZero)
    (hrho : rho.val.re = σ) (hzeta : zeta.val.re = σ)
    (M : ℕ) (hM : 0 < M) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
        q σ rho zeta n M) atTop
      (nhds (finiteGeometricPhaseCoherenceSq M
        (etaGeometricNormalizedMode q rho.val)
        (etaGeometricNormalizedMode q zeta.val))) := by
  have hcorr :=
    (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation
      hqOdd hq rho zeta hrho hzeta M).norm.pow 2
  have hnormRho :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
      hqOdd hq rho hrho M
  have hnormZeta :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
      hqOdd hq zeta hzeta M
  have hMne : (M : ℝ) * (M : ℝ) ≠ 0 := by
    positivity
  have hquot := hcorr.div (hnormRho.mul hnormZeta) hMne
  unfold pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
    finiteGeometricPhaseCoherenceSq
  convert hquot.congr'
    (Filter.Eventually.of_forall fun _ ↦ rfl) using 1
  · funext n
    rfl
  · simp [pow_two]

/-- For one same-layer zero pair, the literal normalized-prefix coherence
inherits the exact phase-gap bound up to any positive asymptotic slack. -/
theorem eventually_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq_mul_gap_sq_lt
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {σ : ℝ}
    (rho zeta : NontrivialZetaZero)
    (hrho : rho.val.re = σ) (hzeta : zeta.val.re = σ)
    (M : ℕ) (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
          q σ rho zeta n M *
          ‖star (etaGeometricNormalizedMode q zeta.val) *
              etaGeometricNormalizedMode q rho.val - 1‖ ^ 2 <
        4 / (M : ℝ) ^ 2 + ε := by
  let gapSq :=
    ‖star (etaGeometricNormalizedMode q zeta.val) *
        etaGeometricNormalizedMode q rho.val - 1‖ ^ 2
  have ht :=
    (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
      hqOdd hq rho zeta hrho hzeta M hM).mul_const gapSq
  have hphase := finiteGeometricPhaseCoherenceSq_mul_gap_sq_le
    M (etaGeometricNormalizedMode q rho.val)
      (etaGeometricNormalizedMode q zeta.val)
    (norm_etaGeometricNormalizedMode hq.le rho.val)
    (norm_etaGeometricNormalizedMode hq.le zeta.val)
  have hlt :
      finiteGeometricPhaseCoherenceSq M
          (etaGeometricNormalizedMode q rho.val)
          (etaGeometricNormalizedMode q zeta.val) * gapSq <
        4 / (M : ℝ) ^ 2 + ε :=
    lt_of_le_of_lt hphase (lt_add_of_pos_right _ hε)
  exact ht.eventually (Iio_mem_nhds hlt)

/-- On any finite same-real-part zero layer, one odd prime and one positive
gap give the eventual `4/M^2 + epsilon` bound simultaneously for every
distinct pair of literal normalized eta-prefix blocks. -/
theorem exists_prime_uniform_eventually_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
    (s : Finset NontrivialZetaZero) {σ : ℝ}
    (hre : ∀ rho : NontrivialZetaZero, rho ∈ s → rho.val.re = σ)
    (hcard : 1 < s.card) (M : ℕ) (hM : 0 < M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∃ g : ℝ, 0 < g ∧
        ∀ᶠ n in atTop, ∀ rho zeta : s, rho ≠ zeta →
          pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
              q σ rho.1 zeta.1 n M * g ^ 2 <
            4 / (M : ℝ) ^ 2 + ε := by
  obtain ⟨q, hqPrime, hqOdd, hq, g, hg, hphase⟩ :=
    exists_prime_uniform_etaGeometricNormalizedModeCoherence_bound
      s hre hcard
  refine ⟨q, hqPrime, hqOdd, hq, g, hg, ?_⟩
  apply Filter.eventually_all.mpr
  intro rho
  apply Filter.eventually_all.mpr
  intro zeta
  by_cases hrz : rho = zeta
  · exact Filter.Eventually.of_forall fun _ hrzne ↦ (hrzne hrz).elim
  · have ht :=
      (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
        hqOdd hq rho.1 zeta.1 (hre rho.1 rho.2) (hre zeta.1 zeta.2)
          M hM).mul_const (g ^ 2)
    have hlt :
        finiteGeometricPhaseCoherenceSq M
            (etaGeometricNormalizedMode q rho.1.val)
            (etaGeometricNormalizedMode q zeta.1.val) * g ^ 2 <
          4 / (M : ℝ) ^ 2 + ε :=
      lt_of_le_of_lt (hphase M rho zeta hrz)
        (lt_add_of_pos_right _ hε)
    exact (ht.eventually (Iio_mem_nhds hlt)).mono fun _ hn _ ↦ hn

/-- Every critical-zero window with at least two zeros satisfies the uniform
literal-prefix coherence bound at one collision-free odd prime. -/
theorem exists_prime_uniform_eventually_spectralCriticalZetaZeroWindowPhaseNormalizedPrefixCoherenceSq
    (T : ℝ) (hcard : 1 < (spectralCriticalZetaZeroWindow T).card)
    (M : ℕ) (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∃ g : ℝ, 0 < g ∧
        ∀ᶠ n in atTop,
          ∀ rho zeta : (spectralCriticalZetaZeroWindow T), rho ≠ zeta →
            pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
                q (1 / 2) rho.1 zeta.1 n M * g ^ 2 <
              4 / (M : ℝ) ^ 2 + ε := by
  refine
    exists_prime_uniform_eventually_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
      (spectralCriticalZetaZeroWindow T) (σ := (1 / 2 : ℝ)) ?_
        hcard M hM hε
  intro rho hρ
  exact (zetaSpectralCoordinate_im_eq_zero_iff rho.val).1
    (mem_spectralCriticalZetaZeroWindow.mp hρ).2

end

end RiemannGaussian
