import RiemannGaussian.Hybrid.EtaGeometricPrefixPhaseTransport
import RiemannGaussian.Hybrid.EtaGeometricPackedFeatureRank

/-!
# Phase transport through the packed eta coordinates

The literal eta certificate stores each complex completed channel in two
reflection-even hyperbolic coordinates.  This module identifies that packing
with an injective realification, computes its correlation and norm exactly,
and transports the geometric-prefix phase bound into the packed coordinates.

The checked bound currently applies to phase-normalized same-real-part layers,
including the critical window.  It does not yet control the differently
decaying off-line-real colour or imply an improved zeta-zero proportion.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The two real hyperbolic coordinates carrying one complex vector. -/
def complexHyperbolicRealification {d : Type*} (v : d → ℂ) :
    d × Fin 2 → ℂ := fun x ↦
  ![v x.1 + star (v x.1), I * (v x.1 - star (v x.1))] x.2

/-- Every coordinate of the hyperbolic realification is fixed by conjugation. -/
theorem star_complexHyperbolicRealification
    {d : Type*} (v : d → ℂ) :
    star (complexHyperbolicRealification v) =
      complexHyperbolicRealification v := by
  funext x
  rcases x with ⟨j, k⟩
  fin_cases k <;>
    simp [complexHyperbolicRealification] <;>
    ring

/-- The original complex coordinate is recovered exactly from its two real
hyperbolic coordinates. -/
theorem complexHyperbolicRealification_recover
    {d : Type*} (v : d → ℂ) (j : d) :
    (complexHyperbolicRealification v (j, 0) -
        I * complexHyperbolicRealification v (j, 1)) / 2 = v j := by
  simp [complexHyperbolicRealification]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

/-- Hyperbolic realification loses no information. -/
theorem complexHyperbolicRealification_injective
    {d : Type*} :
    Function.Injective (complexHyperbolicRealification (d := d)) := by
  intro v w h
  funext j
  rw [← complexHyperbolicRealification_recover v j,
    ← complexHyperbolicRealification_recover w j, h]

/-- The packed Hermitian correlation is four times the real part of the
original complex correlation. -/
theorem star_complexHyperbolicRealification_dot_eq_four_mul_re
    {d : Type*} [Fintype d] (v w : d → ℂ) :
    star (complexHyperbolicRealification w) ⬝ᵥ
        complexHyperbolicRealification v =
      4 * ((star w ⬝ᵥ v).re : ℂ) := by
  apply Complex.ext
  · simp [complexHyperbolicRealification, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  · simp [complexHyperbolicRealification, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im]

/-- Hyperbolic realification multiplies squared Euclidean norm by four. -/
theorem sum_norm_sq_complexHyperbolicRealification
    {d : Type*} [Fintype d] (v : d → ℂ) :
    ∑ x, ‖complexHyperbolicRealification v x‖ ^ 2 =
      4 * ∑ j, ‖v j‖ ^ 2 := by
  rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Fin.sum_univ_two]
  simp [complexHyperbolicRealification, Complex.sq_norm,
    Complex.normSq_apply]
  ring

/-- Squared absolute coherence of two finite complex vectors. -/
def complexVectorAbsoluteCoherenceSq
    {d : Type*} [Fintype d] (v w : d → ℂ) : ℝ :=
  ‖star w ⬝ᵥ v‖ ^ 2 /
    ((∑ j, ‖v j‖ ^ 2) * (∑ j, ‖w j‖ ^ 2))

/-- Squared real correlation normalized by the two packed squared norms. -/
def complexHyperbolicRealificationCoherenceSq
    {d : Type*} [Fintype d] (v w : d → ℂ) : ℝ :=
  (star (complexHyperbolicRealification w) ⬝ᵥ
      complexHyperbolicRealification v).re ^ 2 /
    ((∑ x, ‖complexHyperbolicRealification v x‖ ^ 2) *
      (∑ x, ‖complexHyperbolicRealification w x‖ ^ 2))

/-- Packed coherence is the squared real part of the complex correlation over
the original norm product. -/
theorem complexHyperbolicRealificationCoherenceSq_eq
    {d : Type*} [Fintype d] (v w : d → ℂ)
    (hv : 0 < ∑ j, ‖v j‖ ^ 2) (hw : 0 < ∑ j, ‖w j‖ ^ 2) :
    complexHyperbolicRealificationCoherenceSq v w =
      (star w ⬝ᵥ v).re ^ 2 /
        ((∑ j, ‖v j‖ ^ 2) * (∑ j, ‖w j‖ ^ 2)) := by
  unfold complexHyperbolicRealificationCoherenceSq
  rw [star_complexHyperbolicRealification_dot_eq_four_mul_re,
    sum_norm_sq_complexHyperbolicRealification,
    sum_norm_sq_complexHyperbolicRealification]
  have hden :
      (∑ j, ‖v j‖ ^ 2) * (∑ j, ‖w j‖ ^ 2) ≠ 0 := by
    positivity
  field_simp
  norm_num
  ring

/-- Discarding the imaginary correlation cannot increase the full absolute
complex coherence. -/
theorem complexHyperbolicRealificationCoherenceSq_le_absolute
    {d : Type*} [Fintype d] (v w : d → ℂ)
    (hv : 0 < ∑ j, ‖v j‖ ^ 2) (hw : 0 < ∑ j, ‖w j‖ ^ 2) :
    complexHyperbolicRealificationCoherenceSq v w ≤
      complexVectorAbsoluteCoherenceSq v w := by
  rw [complexHyperbolicRealificationCoherenceSq_eq v w hv hw]
  unfold complexVectorAbsoluteCoherenceSq
  apply div_le_div_of_nonneg_right _ (mul_nonneg hv.le hw.le)
  simpa [pow_two, Complex.normSq_eq_norm_sq] using
    Complex.re_sq_le_normSq (star w ⬝ᵥ v)

/-- On the critical line, the literal packed cutoff feature is exactly the
hyperbolic realification of its original completed eta channel. -/
theorem pairedEtaTopPrefixFiniteCutoffFamilyFeature_eq_complexHyperbolicRealification_originalChannel
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero)
    (hre : rho.val.re = 1 / 2) :
    pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho =
      complexHyperbolicRealification
        (fun j ↦ pairedEtaTopPrefixFiniteOriginalChannelTerm rho (cutoff j)) := by
  have hpartner : NontrivialZetaZero.conjugatePartner rho = rho :=
    conjugatePartner_eq_self_of_re_eq_half rho hre
  funext x
  rcases x with ⟨j, k⟩
  fin_cases k <;>
    simp only [pairedEtaTopPrefixFiniteCutoffFamilyFeature,
      pairedEtaTopPrefixFiniteHyperbolicFeature,
      pairedEtaTopPrefixFiniteEvenCoordinate,
      pairedEtaTopPrefixFiniteOddCoordinate,
      complexHyperbolicRealification]
  · rw [topPrefixFinitePartnerTerm_eq_originalChannelTerm_conjugatePartner,
      hpartner,
      topPrefixFiniteAlignedConjugateTerm_eq_star_originalChannelTerm]
    simp [RCLike.star_def]
  · rw [topPrefixFinitePartnerTerm_eq_originalChannelTerm_conjugatePartner,
      hpartner,
      topPrefixFiniteAlignedConjugateTerm_eq_star_originalChannelTerm]
    simp [RCLike.star_def]

/-- The phase-normalized geometric eta-prefix vector in packed coordinates. -/
def pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixFeature
    (q : ℕ) (σ : ℝ) (rho : NontrivialZetaZero)
    (n M : ℕ) : Fin M × Fin 2 → ℂ :=
  complexHyperbolicRealification
    (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
      q σ rho n M)

/-- Normalized packed coherence of two phase-normalized eta-prefix blocks. -/
def pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq
    (q : ℕ) (σ : ℝ) (rho zeta : NontrivialZetaZero)
    (n M : ℕ) : ℝ :=
  (star (pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixFeature
      q σ zeta n M) ⬝ᵥ
      pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixFeature
        q σ rho n M).re ^ 2 /
    ((∑ x, ‖pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixFeature
        q σ rho n M x‖ ^ 2) *
      (∑ x, ‖pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixFeature
        q σ zeta n M x‖ ^ 2))

/-- Packed eta-prefix coherence is bounded by the full complex coherence when
both prefix blocks have positive norm. -/
theorem pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq_le
    (q : ℕ) (σ : ℝ) (rho zeta : NontrivialZetaZero)
    (n M : ℕ)
    (hrho : 0 < pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
      q σ rho n M)
    (hzeta : 0 < pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
      q σ zeta n M) :
    pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq
        q σ rho zeta n M ≤
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
        q σ rho zeta n M := by
  simpa [pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq,
    pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixFeature,
    complexHyperbolicRealificationCoherenceSq,
    pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq,
    pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation,
    pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq,
    complexVectorAbsoluteCoherenceSq] using
    complexHyperbolicRealificationCoherenceSq_le_absolute
      (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector q σ rho n M)
      (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector q σ zeta n M)
      hrho hzeta

/-- One collision-free odd prime gives a simultaneous eventual packed
coherence bound on every distinct pair in a finite same-real-part layer. -/
theorem exists_prime_uniform_eventually_pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq
    (s : Finset NontrivialZetaZero) {σ : ℝ}
    (hre : ∀ rho : NontrivialZetaZero, rho ∈ s → rho.val.re = σ)
    (hcard : 1 < s.card) (M : ℕ) (hM : 0 < M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∃ g : ℝ, 0 < g ∧
        ∀ᶠ n in atTop, ∀ rho zeta : s, rho ≠ zeta →
          pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq
              q σ rho.1 zeta.1 n M * g ^ 2 <
            4 / (M : ℝ) ^ 2 + ε := by
  obtain ⟨q, hqPrime, hqOdd, hq, g, hg, hprefix⟩ :=
    exists_prime_uniform_eventually_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
      s hre hcard M hM hε
  refine ⟨q, hqPrime, hqOdd, hq, g, hg, ?_⟩
  have hnorm : ∀ rho : s, ∀ᶠ n in atTop,
      0 < pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
        q σ rho.1 n M := by
    intro rho
    exact
      (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
        hqOdd hq rho.1 (hre rho.1 rho.2) M).eventually
        (Ioi_mem_nhds (by exact_mod_cast hM))
  have hnormAll : ∀ᶠ n in atTop, ∀ rho : s,
      0 < pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
        q σ rho.1 n M :=
    Filter.eventually_all.mpr hnorm
  filter_upwards [hprefix, hnormAll] with n hn hnormn
  intro rho zeta hrz
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right
      (pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq_le
        q σ rho.1 zeta.1 n M (hnormn rho) (hnormn zeta))
      (sq_nonneg g))
    (hn rho zeta hrz)

/-- The simultaneous eventual packed coherence bound specializes to every
finite critical-zero window containing at least two zeros. -/
theorem exists_prime_uniform_eventually_spectralCriticalZetaZeroWindowPhaseNormalizedPackedPrefixCoherenceSq
    (T : ℝ) (hcard : 1 < (spectralCriticalZetaZeroWindow T).card)
    (M : ℕ) (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∃ g : ℝ, 0 < g ∧
        ∀ᶠ n in atTop,
          ∀ rho zeta : (spectralCriticalZetaZeroWindow T), rho ≠ zeta →
            pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq
                q (1 / 2) rho.1 zeta.1 n M * g ^ 2 <
              4 / (M : ℝ) ^ 2 + ε := by
  refine
    exists_prime_uniform_eventually_pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq
      (spectralCriticalZetaZeroWindow T) (σ := (1 / 2 : ℝ)) ?_
        hcard M hM hε
  intro rho hρ
  exact (zetaSpectralCoordinate_im_eq_zero_iff rho.val).1
    (mem_spectralCriticalZetaZeroWindow.mp hρ).2

end

end RiemannGaussian
