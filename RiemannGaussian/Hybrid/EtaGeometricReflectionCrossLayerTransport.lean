import RiemannGaussian.Hybrid.EtaGeometricPackedPhaseTransport
import RiemannGaussian.Hybrid.EtaGeometricReflectionEvenDecorrelationReserve

/-!
# Cross-layer transport for the reflection-even eta frame

The unit-phase transport treats one real-coordinate layer at a time.  This
module retains the missing radial colour under one common coordinate tilt.
The shifted geometric mode at tilt `sigma` has exact radius
`q^(sigma - Re(s))`; at the critical tilt, a reflected off-line pair has the
same unit phase and reciprocal radii on opposite sides of one.

The module also identifies both colours of the actual reflection-even frame.
A critical atom is the injective hyperbolic realification of its completed
original channel.  An upper off-line atom is one half of the same
realification applied to the sum of the original channels at the zero and its
reflected partner, and that reflection sum is explicitly recoverable from the
two retained coordinates.

Finally, the literal eta-prefix convergence and coherence transport are
generalized from unit modes to arbitrary shifted modes.  This preserves the
critical/off-line radial distinction at the quantitative frontier.  It does
not yet bound the reflection-summed cross-layer correlations or improve the
zeta-zero proportion.
-/

open Complex Filter Topology Finset
open scoped BigOperators ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- Raw eta decay mode after applying one common real-coordinate tilt. -/
def etaGeometricShiftedMode (q : ℕ) (σ : ℝ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (σ : ℂ) * etaGeometricDecayMode q s

/-- A shifted mode factors into its positive radial colour and its retained
unit phase. -/
theorem etaGeometricShiftedMode_eq_real_rpow_mul_normalized
    {q : ℕ} (hq : 0 < q) (σ : ℝ) (s : ℂ) :
    etaGeometricShiftedMode q σ s =
      (((q : ℝ) ^ (σ - s.re) : ℝ) : ℂ) *
        etaGeometricNormalizedMode q s := by
  rw [etaGeometricNormalizedMode_eq_real_cpow_mul_decayMode hq]
  unfold etaGeometricShiftedMode
  have hcast : (q : ℂ) = ((q : ℝ) : ℂ) := by norm_cast
  rw [hcast,
    ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ q) σ,
    ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ q) s.re]
  have hrpow :
      (q : ℝ) ^ σ =
        (q : ℝ) ^ (σ - s.re) * (q : ℝ) ^ s.re := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < q)]
    congr 1
    ring
  rw [hrpow, Complex.ofReal_mul]
  ring_nf

/-- The shifted-mode norm records the exact displacement from the chosen
real-coordinate layer. -/
theorem norm_etaGeometricShiftedMode
    {q : ℕ} (hq : 0 < q) (σ : ℝ) (s : ℂ) :
    ‖etaGeometricShiftedMode q σ s‖ =
      (q : ℝ) ^ (σ - s.re) := by
  rw [etaGeometricShiftedMode_eq_real_rpow_mul_normalized hq,
    norm_mul, norm_etaGeometricNormalizedMode hq, mul_one]
  simpa using abs_of_pos
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < q) (σ - s.re))

/-- On the selected layer, the shifted mode is exactly the normalized unit
mode. -/
theorem etaGeometricShiftedMode_eq_normalized_of_re_eq
    {q : ℕ} (hq : 0 < q) {σ : ℝ} {s : ℂ} (hs : s.re = σ) :
    etaGeometricShiftedMode q σ s = etaGeometricNormalizedMode q s := by
  rw [etaGeometricShiftedMode_eq_real_rpow_mul_normalized hq, hs,
    sub_self, Real.rpow_zero]
  norm_num

/-- Critical-line reflection preserves the logarithmic unit phase. -/
theorem etaGeometricNormalizedMode_conjugatePartner
    {q : ℕ} (hq : 0 < q) (rho : NontrivialZetaZero) :
    etaGeometricNormalizedMode q
        (NontrivialZetaZero.conjugatePartner rho).val =
      etaGeometricNormalizedMode q rho.val := by
  rw [etaGeometricNormalizedMode_eq_phase hq,
    etaGeometricNormalizedMode_eq_phase hq]
  congr 1
  simp [NontrivialZetaZero.conjugatePartner_coe]

/-- At the critical tilt, the reflected mode has the reciprocal radial
exponent and the same unit phase. -/
theorem etaGeometricCriticalShiftedMode_conjugatePartner
    {q : ℕ} (hq : 0 < q) (rho : NontrivialZetaZero) :
    etaGeometricShiftedMode q (1 / 2)
        (NontrivialZetaZero.conjugatePartner rho).val =
      (((q : ℝ) ^ (rho.val.re - 1 / 2) : ℝ) : ℂ) *
        etaGeometricNormalizedMode q rho.val := by
  rw [etaGeometricShiftedMode_eq_real_rpow_mul_normalized hq,
    etaGeometricNormalizedMode_conjugatePartner hq]
  congr 2
  simp [NontrivialZetaZero.conjugatePartner_coe]
  ring_nf

/-- The two critical-tilted radii in every reflection pair multiply to one. -/
theorem norm_etaGeometricCriticalShiftedMode_mul_partner
    {q : ℕ} (hq : 0 < q) (rho : NontrivialZetaZero) :
    ‖etaGeometricShiftedMode q (1 / 2) rho.val‖ *
        ‖etaGeometricShiftedMode q (1 / 2)
          (NontrivialZetaZero.conjugatePartner rho).val‖ = 1 := by
  rw [norm_etaGeometricShiftedMode hq,
    norm_etaGeometricShiftedMode hq,
    ← Real.rpow_add (by exact_mod_cast hq)]
  simp [NontrivialZetaZero.conjugatePartner_coe]
  convert Real.rpow_zero (q : ℝ) using 1
  ring_nf

/-- A zero to the left of the critical line has critical-shifted radius
strictly greater than one. -/
theorem one_lt_norm_etaGeometricCriticalShiftedMode_of_re_lt_half
    {q : ℕ} (hq : 1 < q) (rho : NontrivialZetaZero)
    (hrho : rho.val.re < 1 / 2) :
    1 < ‖etaGeometricShiftedMode q (1 / 2) rho.val‖ := by
  rw [norm_etaGeometricShiftedMode hq.le]
  exact Real.one_lt_rpow (by exact_mod_cast hq) (sub_pos.mpr hrho)

/-- The reflected partner of a left-half zero has critical-shifted radius
strictly less than one. -/
theorem norm_etaGeometricCriticalShiftedMode_conjugatePartner_lt_one_of_re_lt_half
    {q : ℕ} (hq : 1 < q) (rho : NontrivialZetaZero)
    (hrho : rho.val.re < 1 / 2) :
    ‖etaGeometricShiftedMode q (1 / 2)
        (NontrivialZetaZero.conjugatePartner rho).val‖ < 1 := by
  rw [norm_etaGeometricShiftedMode hq.le]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq)
  simp [NontrivialZetaZero.conjugatePartner_coe]
  linarith

/-- Every upper-spectral-window representative and its reflection have
strictly reciprocal critical-shifted radii. -/
theorem spectralUpperZetaZeroWindow_criticalShiftedMode_radii
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T)) :
    1 < ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖ ∧
      ‖etaGeometricShiftedMode q (1 / 2)
        (NontrivialZetaZero.conjugatePartner rho.1).val‖ < 1 ∧
      ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖ *
        ‖etaGeometricShiftedMode q (1 / 2)
          (NontrivialZetaZero.conjugatePartner rho.1).val‖ = 1 := by
  have hre : rho.1.val.re < 1 / 2 := by
    have hupper := (mem_spectralUpperZetaZeroWindow.mp rho.2).2
    rw [zetaSpectralCoordinate_im] at hupper
    linarith
  exact ⟨one_lt_norm_etaGeometricCriticalShiftedMode_of_re_lt_half
      hq rho.1 hre,
    norm_etaGeometricCriticalShiftedMode_conjugatePartner_lt_one_of_re_lt_half
      hq rho.1 hre,
    norm_etaGeometricCriticalShiftedMode_mul_partner hq.le rho.1⟩

/-- Sum of the completed original eta channels at a zero and its critical-line
reflection over a finite cutoff family. -/
def pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) : d → ℂ :=
  fun j ↦
    pairedEtaTopPrefixFiniteOriginalChannelTerm
        (NontrivialZetaZero.conjugatePartner rho) (cutoff j) +
      pairedEtaTopPrefixFiniteOriginalChannelTerm rho (cutoff j)

/-- The retained real part of an arbitrary packed eta feature is exactly half
the hyperbolic realification of its reflection-summed original channel. -/
theorem complexVectorReal_pairedEtaTopPrefixFiniteCutoffFamilyFeature_eq_half_realification_reflectionSum
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    complexVectorReal
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) =
      (1 / 2 : ℂ) • complexHyperbolicRealification
        (pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
          cutoff rho) := by
  funext x
  rcases x with ⟨j, k⟩
  fin_cases k <;>
    simp only [complexVectorReal,
      pairedEtaTopPrefixFiniteCutoffFamilyFeature,
      pairedEtaTopPrefixFiniteHyperbolicFeature,
      pairedEtaTopPrefixFiniteEvenCoordinate,
      pairedEtaTopPrefixFiniteOddCoordinate,
      pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel,
      complexHyperbolicRealification, Pi.smul_apply, smul_eq_mul]
  · rw [topPrefixFinitePartnerTerm_eq_originalChannelTerm_conjugatePartner,
      topPrefixFiniteAlignedConjugateTerm_eq_star_originalChannelTerm]
    apply Complex.ext
    · simp [RCLike.star_def, Complex.mul_re]
      ring
    · simp [RCLike.star_def, Complex.mul_im]
      ring
  · rw [topPrefixFinitePartnerTerm_eq_originalChannelTerm_conjugatePartner,
      topPrefixFiniteAlignedConjugateTerm_eq_star_originalChannelTerm]
    apply Complex.ext
    · simp [RCLike.star_def, Complex.mul_re, Complex.mul_im]
      ring
    · simp [RCLike.star_def, Complex.mul_re, Complex.mul_im]

/-- The reflection-summed channel is invariant under exchanging the two
members of a critical-line reflection pair. -/
theorem pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel_conjugatePartner
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel cutoff
        (NontrivialZetaZero.conjugatePartner rho) =
      pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel cutoff rho := by
  funext j
  simp [pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel,
    add_comm]

/-- The two retained real coordinates reconstruct the complex reflection-sum
channel at every cutoff. -/
theorem pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel_recover
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) (j : d) :
    complexVectorReal
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) (j, 0) -
        I * complexVectorReal
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) (j, 1) =
      pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
        cutoff rho j := by
  have hfeature :=
    complexVectorReal_pairedEtaTopPrefixFiniteCutoffFamilyFeature_eq_half_realification_reflectionSum
      cutoff rho
  have hzero := congrFun hfeature (j, 0)
  have hone := congrFun hfeature (j, 1)
  rw [hzero, hone]
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (1 / 2 : ℂ) *
          complexHyperbolicRealification
            (pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
              cutoff rho) (j, 0) -
        I * ((1 / 2 : ℂ) *
          complexHyperbolicRealification
            (pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
              cutoff rho) (j, 1)) =
      (complexHyperbolicRealification
            (pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
              cutoff rho) (j, 0) -
          I * complexHyperbolicRealification
            (pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
              cutoff rho) (j, 1)) / 2 := by ring
    _ = _ := complexHyperbolicRealification_recover
      (pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel cutoff rho) j

/-- A literal critical reflection-even frame atom is exactly the
realification of its completed original eta channel. -/
theorem pairedEtaReflectionEvenFrameVector_critical_eq_realification_originalChannel
    {d : Type*} (cutoff : d → ℕ) (T : ℝ)
    (rho : ↥(spectralCriticalZetaZeroWindow T)) :
    pairedEtaReflectionEvenFrameVector cutoff T (Sum.inl rho) =
      complexHyperbolicRealification
        (fun j ↦ pairedEtaTopPrefixFiniteOriginalChannelTerm
          rho.1 (cutoff j)) := by
  unfold pairedEtaReflectionEvenFrameVector
  apply
    pairedEtaTopPrefixFiniteCutoffFamilyFeature_eq_complexHyperbolicRealification_originalChannel
  exact (zetaSpectralCoordinate_im_eq_zero_iff rho.1.val).1
    (mem_spectralCriticalZetaZeroWindow.mp rho.2).2

/-- A literal upper off-line frame atom is exactly half the realification of
the reflection-summed completed eta channel. -/
theorem pairedEtaReflectionEvenFrameVector_upper_eq_half_realification_reflectionSum
    {d : Type*} (cutoff : d → ℕ) (T : ℝ)
    (rho : ↥(spectralUpperZetaZeroWindow T)) :
    pairedEtaReflectionEvenFrameVector cutoff T (Sum.inr rho) =
      (1 / 2 : ℂ) • complexHyperbolicRealification
        (pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
          cutoff rho.1) := by
  unfold pairedEtaReflectionEvenFrameVector
  exact
    complexVectorReal_pairedEtaTopPrefixFiniteCutoffFamilyFeature_eq_half_realification_reflectionSum
      cutoff rho.1

/-- The literal upper off-line frame atom reconstructs its complex
reflection-summed channel without further information loss. -/
theorem pairedEtaReflectionEvenFrameVector_upper_recover_reflectionSum
    {d : Type*} (cutoff : d → ℕ) (T : ℝ)
    (rho : ↥(spectralUpperZetaZeroWindow T)) (j : d) :
    pairedEtaReflectionEvenFrameVector cutoff T (Sum.inr rho) (j, 0) -
        I * pairedEtaReflectionEvenFrameVector cutoff T
          (Sum.inr rho) (j, 1) =
      pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel
        cutoff rho.1 j := by
  exact
    pairedEtaTopPrefixFiniteCutoffFamilyReflectionSumChannel_recover
      cutoff rho.1 j

/-- Each commonly tilted literal eta-prefix coordinate converges to the
matching power of its shifted mode, without a same-layer assumption. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply_shifted
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (σ : ℝ)
    (rho : NontrivialZetaZero) (M : ℕ) (j : Fin M) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
        q σ rho n M j) atTop
      (nhds (finiteGeometricPhaseVector M
        (etaGeometricShiftedMode q σ rho.val) j)) := by
  have hprefix := tendsto_pairedEtaLowerMomentGeometricPrefix_rowScaled
    rho hqOdd hq (j : ℕ)
  have hscaled := Filter.Tendsto.const_mul
    ((pairedEtaLowerMomentGeometricLimit rho)⁻¹ *
      ((q : ℂ) ^ (σ : ℂ)) ^ (j : ℕ)) hprefix
  convert hscaled using 1
  · funext n
    unfold pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
    ring
  · unfold finiteGeometricPhaseVector etaGeometricShiftedMode
    rw [mul_pow]
    field_simp [pairedEtaLowerMomentGeometricLimit_ne_zero rho]

/-- A complete fixed-length commonly tilted eta-prefix block converges to its
finite shifted-mode vector. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_shifted
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (σ : ℝ)
    (rho : NontrivialZetaZero) (M : ℕ) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
        q σ rho n M) atTop
      (nhds (finiteGeometricPhaseVector M
        (etaGeometricShiftedMode q σ rho.val))) := by
  rw [tendsto_pi_nhds]
  intro j
  exact
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply_shifted
      hqOdd hq σ rho M j

/-- Squared Euclidean norm of a finite geometric vector with arbitrary
complex radius. -/
def finiteGeometricModeNormSq (M : ℕ) (z : ℂ) : ℝ :=
  ∑ j : Fin M, ‖finiteGeometricPhaseVector M z j‖ ^ 2

/-- Every nonempty finite geometric vector has positive squared norm. -/
theorem finiteGeometricModeNormSq_pos
    {M : ℕ} (hM : 0 < M) (z : ℂ) :
    0 < finiteGeometricModeNormSq M z := by
  unfold finiteGeometricModeNormSq
  apply Finset.sum_pos'
  · intro j _hj
    positivity
  · let j : Fin M := ⟨0, hM⟩
    refine ⟨j, Finset.mem_univ j, ?_⟩
    simp [j, finiteGeometricPhaseVector]

/-- Squared absolute coherence of two arbitrary finite geometric modes. -/
def finiteGeometricModeCoherenceSq (M : ℕ) (z w : ℂ) : ℝ :=
  ‖star (finiteGeometricPhaseVector M w) ⬝ᵥ
      finiteGeometricPhaseVector M z‖ ^ 2 /
    (finiteGeometricModeNormSq M z * finiteGeometricModeNormSq M w)

/-- Squared real, reflection-even coherence of two arbitrary finite geometric
modes. -/
def finiteGeometricModePackedCoherenceSq (M : ℕ) (z w : ℂ) : ℝ :=
  (star (finiteGeometricPhaseVector M w) ⬝ᵥ
      finiteGeometricPhaseVector M z).re ^ 2 /
    (finiteGeometricModeNormSq M z * finiteGeometricModeNormSq M w)

/-- Packed real coherence is bounded by full complex coherence for every
nonempty block. -/
theorem finiteGeometricModePackedCoherenceSq_le
    {M : ℕ} (hM : 0 < M) (z w : ℂ) :
    finiteGeometricModePackedCoherenceSq M z w ≤
      finiteGeometricModeCoherenceSq M z w := by
  unfold finiteGeometricModePackedCoherenceSq
    finiteGeometricModeCoherenceSq
  apply div_le_div_of_nonneg_right _
    (mul_nonneg (finiteGeometricModeNormSq_pos hM z).le
      (finiteGeometricModeNormSq_pos hM w).le)
  simpa [pow_two, Complex.normSq_eq_norm_sq] using
    Complex.re_sq_le_normSq
      (star (finiteGeometricPhaseVector M w) ⬝ᵥ
        finiteGeometricPhaseVector M z)

/-- Commonly tilted literal correlations converge with their full complex
phase to shifted-mode correlations. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation_shifted
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (σ : ℝ)
    (rho zeta : NontrivialZetaZero) (M : ℕ) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation
        q σ rho zeta n M) atTop
      (nhds (star (finiteGeometricPhaseVector M
          (etaGeometricShiftedMode q σ zeta.val)) ⬝ᵥ
        finiteGeometricPhaseVector M
          (etaGeometricShiftedMode q σ rho.val))) := by
  unfold pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation
    dotProduct
  simpa using tendsto_finsetSum (Finset.univ : Finset (Fin M))
    (fun j _hj ↦
      (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply_shifted
        hqOdd hq σ zeta M j).star.mul
      (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply_shifted
        hqOdd hq σ rho M j))

/-- Commonly tilted literal squared norms converge to shifted-mode squared
norms. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq_shifted
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (σ : ℝ)
    (rho : NontrivialZetaZero) (M : ℕ) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
        q σ rho n M) atTop
      (nhds (finiteGeometricModeNormSq M
        (etaGeometricShiftedMode q σ rho.val))) := by
  unfold pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
    finiteGeometricModeNormSq
  exact tendsto_finsetSum (Finset.univ : Finset (Fin M))
    (fun j _hj ↦
      (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector_apply_shifted
        hqOdd hq σ rho M j).norm.pow 2)

/-- Commonly tilted literal absolute coherence converges to the corresponding
arbitrary-radius geometric coherence. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq_shifted
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (σ : ℝ)
    (rho zeta : NontrivialZetaZero) (M : ℕ) (hM : 0 < M) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCoherenceSq
        q σ rho zeta n M) atTop
      (nhds (finiteGeometricModeCoherenceSq M
        (etaGeometricShiftedMode q σ rho.val)
        (etaGeometricShiftedMode q σ zeta.val))) := by
  have hcorr :=
    (tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation_shifted
      hqOdd hq σ rho zeta M).norm.pow 2
  have hnormRho :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq_shifted
      hqOdd hq σ rho M
  have hnormZeta :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq_shifted
      hqOdd hq σ zeta M
  have hden :
      finiteGeometricModeNormSq M
          (etaGeometricShiftedMode q σ rho.val) *
        finiteGeometricModeNormSq M
          (etaGeometricShiftedMode q σ zeta.val) ≠ 0 := by
    positivity [finiteGeometricModeNormSq_pos hM
      (etaGeometricShiftedMode q σ rho.val),
      finiteGeometricModeNormSq_pos hM
        (etaGeometricShiftedMode q σ zeta.val)]
  exact hcorr.div (hnormRho.mul hnormZeta) hden

/-- Commonly tilted packed coherence converges to the real coherence of the
arbitrary-radius geometric modes. -/
theorem tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq_shifted
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (σ : ℝ)
    (rho zeta : NontrivialZetaZero) (M : ℕ) (hM : 0 < M) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq
        q σ rho zeta n M) atTop
      (nhds (finiteGeometricModePackedCoherenceSq M
        (etaGeometricShiftedMode q σ rho.val)
        (etaGeometricShiftedMode q σ zeta.val))) := by
  have hcorr :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation_shifted
      hqOdd hq σ rho zeta M
  have hnormRho :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq_shifted
      hqOdd hq σ rho M
  have hnormZeta :=
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq_shifted
      hqOdd hq σ zeta M
  have hlimitRho := finiteGeometricModeNormSq_pos hM
    (etaGeometricShiftedMode q σ rho.val)
  have hlimitZeta := finiteGeometricModeNormSq_pos hM
    (etaGeometricShiftedMode q σ zeta.val)
  have hden :
      finiteGeometricModeNormSq M
          (etaGeometricShiftedMode q σ rho.val) *
        finiteGeometricModeNormSq M
          (etaGeometricShiftedMode q σ zeta.val) ≠ 0 := by
    positivity
  have hcorrRe :=
    Complex.continuous_re.continuousAt.tendsto.comp hcorr
  have hquot := (hcorrRe.pow 2).div
    (hnormRho.mul hnormZeta) hden
  have hnormRhoEventually : ∀ᶠ n in atTop,
      0 < pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
        q σ rho n M :=
    hnormRho.eventually (Ioi_mem_nhds hlimitRho)
  have hnormZetaEventually : ∀ᶠ n in atTop,
      0 < pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq
        q σ zeta n M :=
    hnormZeta.eventually (Ioi_mem_nhds hlimitZeta)
  apply hquot.congr'
  filter_upwards [hnormRhoEventually, hnormZetaEventually] with n hnRho hnZeta
  simpa [finiteGeometricModePackedCoherenceSq,
    pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq,
    pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixFeature,
    complexHyperbolicRealificationCoherenceSq,
    pairedEtaLowerMomentGeometricPhaseNormalizedPrefixCorrelation,
    pairedEtaLowerMomentGeometricPhaseNormalizedPrefixNormSq] using
    (complexHyperbolicRealificationCoherenceSq_eq
      (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
        q σ rho n M)
      (pairedEtaLowerMomentGeometricPhaseNormalizedPrefixVector
        q σ zeta n M) hnRho hnZeta).symm

/-- For a critical/upper pair, packed literal coherence has the checked
cross-layer limit while the critical mode stays unit and the off-line pair
retains equal phase with strictly reciprocal radii. -/
theorem spectralCriticalUpperZetaZeroWindow_criticalShiftedPackedCoherence_colourLaw
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralCriticalZetaZeroWindow T))
    (zeta : ↥(spectralUpperZetaZeroWindow T))
    (M : ℕ) (hM : 0 < M) :
    Tendsto (fun n : ℕ ↦
      pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq
        q (1 / 2) rho.1 zeta.1 n M) atTop
      (nhds (finiteGeometricModePackedCoherenceSq M
        (etaGeometricShiftedMode q (1 / 2) rho.1.val)
        (etaGeometricShiftedMode q (1 / 2) zeta.1.val))) ∧
    ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖ = 1 ∧
    1 < ‖etaGeometricShiftedMode q (1 / 2) zeta.1.val‖ ∧
    ‖etaGeometricShiftedMode q (1 / 2)
        (NontrivialZetaZero.conjugatePartner zeta.1).val‖ < 1 ∧
    ‖etaGeometricShiftedMode q (1 / 2) zeta.1.val‖ *
        ‖etaGeometricShiftedMode q (1 / 2)
          (NontrivialZetaZero.conjugatePartner zeta.1).val‖ = 1 ∧
    etaGeometricNormalizedMode q
        (NontrivialZetaZero.conjugatePartner zeta.1).val =
      etaGeometricNormalizedMode q zeta.1.val := by
  have hcritical : rho.1.val.re = 1 / 2 :=
    (zetaSpectralCoordinate_im_eq_zero_iff rho.1.val).1
      (mem_spectralCriticalZetaZeroWindow.mp rho.2).2
  obtain ⟨hupper, hpartner, hproduct⟩ :=
    spectralUpperZetaZeroWindow_criticalShiftedMode_radii hq zeta
  refine ⟨
    tendsto_pairedEtaLowerMomentGeometricPhaseNormalizedPackedPrefixCoherenceSq_shifted
      hqOdd hq (1 / 2) rho.1 zeta.1 M hM, ?_, hupper,
    hpartner, hproduct, etaGeometricNormalizedMode_conjugatePartner hq.le zeta.1⟩
  rw [norm_etaGeometricShiftedMode hq.le, hcritical,
    sub_self, Real.rpow_zero]

end

end RiemannGaussian
