import RiemannGaussian.EtaEnergyHyperbolicPairBlock
import RiemannGaussian.RiemannXiSpectralReflectionPairing

/-!
# Finite zero-window blocks for the eta hyperbolic feature

This module performs the first finite-window compression of the eta energy.
A finite family of cutoff indices is packed into one complex feature vector
for each genuine nontrivial zeta zero.  The previously proved two-coordinate
energy identity is retained on every cutoff slice, and critical-line
reflection sends the full packed feature to its componentwise conjugate.

On a symmetric finite spectral zero window, Lean then forms the literal
multiplicity-weighted complex-symmetric outer-product sum.  The window splits
exactly into critical-line terms and reflected off-line pairs.  Each off-line
pair is the difference of an explicit positive-semidefinite real rank-one
block and an explicit positive-semidefinite imaginary rank-one block.  The
critical-line part is positive semidefinite.  Consequently the complete
finite eta zero-window block is Hermitian and has an exact

`onLine + (offReal - offImag)`

decomposition.  No trace, Frobenius, rank, or arithmetic estimate is assumed
or proved here; those are the next obligations.
-/

open Complex
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-! ## A finite family of cutoff features -/

/-- Pack the two-dimensional eta hyperbolic features at finitely indexed
cutoffs into one product-indexed complex vector. -/
def pairedEtaTopPrefixFiniteCutoffFamilyFeature
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    d × Fin 2 → ℂ :=
  fun j ↦ pairedEtaTopPrefixFiniteHyperbolicFeature rho (cutoff j.1) j.2

/-- Each two-coordinate slice of the packed feature retains the exact signed
finite eta energy. -/
theorem topPrefixFiniteEnergyDifference_eq_cutoffFamilySliceHyperbolicForm
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) (j : d) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho (cutoff j) =
      pairedEtaTopPrefixFiniteHyperbolicForm
        (fun k ↦ pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho (j, k)) := by
  simpa only [pairedEtaTopPrefixFiniteCutoffFamilyFeature] using
    topPrefixFiniteEnergyDifference_eq_hyperbolicForm rho (cutoff j)

/-- Reflection sends the complete packed cutoff feature to its componentwise
complex conjugate. -/
theorem topPrefixFiniteCutoffFamilyFeature_conjugatePartner
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
        (NontrivialZetaZero.conjugatePartner rho) =
      star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) := by
  funext j
  exact congrFun
    (topPrefixFiniteHyperbolicFeature_conjugatePartner rho (cutoff j.1)) j.2

/-! ## Generic finite-window splitting under reflection -/

/-- A sum over the full symmetric spectral window splits into its upper,
critical-line, and lower spectral pieces. -/
theorem sum_spectralZetaZeroWindow_eq_upper_add_critical_add_lower
    {M : Type*} [AddCommMonoid M] (f : NontrivialZetaZero → M) (T : ℝ) :
    (∑ rho ∈ spectralZetaZeroWindow T, f rho) =
      (∑ rho ∈ spectralUpperZetaZeroWindow T, f rho) +
        (∑ rho ∈ spectralCriticalZetaZeroWindow T, f rho) +
          ∑ rho ∈ spectralLowerZetaZeroWindow T, f rho := by
  unfold spectralUpperZetaZeroWindow spectralCriticalZetaZeroWindow
    spectralLowerZetaZeroWindow
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _hrho
  let y : ℝ := (zetaSpectralCoordinate rho.1).im
  by_cases hypos : 0 < y
  · change 0 < (zetaSpectralCoordinate rho.1).im at hypos
    have hyzero : (zetaSpectralCoordinate rho.1).im ≠ 0 := ne_of_gt hypos
    have hyneg : ¬(zetaSpectralCoordinate rho.1).im < 0 :=
      not_lt_of_ge hypos.le
    rw [if_pos hypos, if_neg hyzero, if_neg hyneg]
    simp
  · by_cases hyzero : y = 0
    · change ¬0 < (zetaSpectralCoordinate rho.1).im at hypos
      change (zetaSpectralCoordinate rho.1).im = 0 at hyzero
      have hyneg : ¬(zetaSpectralCoordinate rho.1).im < 0 := by
        linarith
      rw [if_neg hypos, if_pos hyzero, if_neg hyneg]
      simp
    · have hyneg : y < 0 := lt_of_le_of_ne (not_lt.mp hypos) hyzero
      change ¬0 < (zetaSpectralCoordinate rho.1).im at hypos
      change (zetaSpectralCoordinate rho.1).im ≠ 0 at hyzero
      change (zetaSpectralCoordinate rho.1).im < 0 at hyneg
      rw [if_neg hypos, if_neg hyzero, if_pos hyneg]
      simp

/-- Reflection bijects the upper spectral part of a nonnegative symmetric
window with its lower part, for an arbitrary additive summand. -/
theorem sum_spectralLowerZetaZeroWindow_eq_upper_conjugatePartner
    {M : Type*} [AddCommMonoid M] {T : ℝ} (hT : 0 ≤ T)
    (f : NontrivialZetaZero → M) :
    (∑ rho ∈ spectralLowerZetaZeroWindow T, f rho) =
      ∑ rho ∈ spectralUpperZetaZeroWindow T,
        f (NontrivialZetaZero.conjugatePartner rho) := by
  symm
  refine Finset.sum_bij
    (fun rho _hrho ↦ NontrivialZetaZero.conjugatePartner rho)
    ?_ ?_ ?_ ?_
  · intro rho hrho
    have hmem := (mem_spectralUpperZetaZeroWindow.mp hrho).1
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    apply mem_spectralLowerZetaZeroWindow.mpr
    constructor
    · exact (conjugatePartner_mem_spectralZetaZeroWindow_iff hT rho).2 hmem
    · rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
      simp only [Complex.conj_im]
      linarith
  · intro rho₁ _hrho₁ rho₂ _hrho₂ heq
    exact NontrivialZetaZero.conjugatePartnerEquiv.injective heq
  · intro rho hrho
    have hmem := (mem_spectralLowerZetaZeroWindow.mp hrho).1
    have hlower := (mem_spectralLowerZetaZeroWindow.mp hrho).2
    refine ⟨NontrivialZetaZero.conjugatePartner rho, ?_, ?_⟩
    · apply mem_spectralUpperZetaZeroWindow.mpr
      constructor
      · exact (conjugatePartner_mem_spectralZetaZeroWindow_iff hT rho).2 hmem
      · rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
        simp only [Complex.conj_im]
        linarith
    · simp
  · intro rho _hrho
    rfl

/-! ## The literal eta zero-window matrix and its three pieces -/

/-- Multiplicity-weighted complex-symmetric eta block over one genuine finite
spectral zero window. -/
def pairedEtaTopPrefixFiniteZeroWindowBlock
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) : Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      Matrix.vecMulVec
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)

/-- The critical-line portion of the finite eta zero-window block. -/
def pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) : Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ spectralCriticalZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      Matrix.vecMulVec
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)

/-- The positive real rank-one portion of all represented off-line pairs. -/
def pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) : Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      ((2 : ℂ) • Matrix.vecMulVec
        (complexVectorReal
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
        (complexVectorReal
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)))

/-- The positive imaginary rank-one portion of all represented off-line
pairs.  It is subtracted from the real block in the full matrix. -/
def pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) : Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      ((2 : ℂ) • Matrix.vecMulVec
        (complexVectorImag
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
        (complexVectorImag
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)))

/-- A multiplicity-weighted reflected eta pair is exactly its positive real
rank-one block minus its positive imaginary rank-one block. -/
theorem topPrefixFiniteCutoffFamilyFeature_weightedPairBlock_eq_real_sub_imag
    {d : Type*} (cutoff : d → ℕ) (rho : NontrivialZetaZero) :
    (analyticZetaZeroMultiplicity rho : ℂ) •
          Matrix.vecMulVec
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) +
        (analyticZetaZeroMultiplicity
            (NontrivialZetaZero.conjugatePartner rho) : ℂ) •
          Matrix.vecMulVec
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
              (NontrivialZetaZero.conjugatePartner rho))
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
              (NontrivialZetaZero.conjugatePartner rho)) =
      (analyticZetaZeroMultiplicity rho : ℂ) •
          ((2 : ℂ) • Matrix.vecMulVec
            (complexVectorReal
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
            (complexVectorReal
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))) -
        (analyticZetaZeroMultiplicity rho : ℂ) •
          ((2 : ℂ) • Matrix.vecMulVec
            (complexVectorImag
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
            (complexVectorImag
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))) := by
  rw [analyticZetaZeroMultiplicity_conjugatePartner,
    topPrefixFiniteCutoffFamilyFeature_conjugatePartner, ← smul_add]
  change (analyticZetaZeroMultiplicity rho : ℂ) •
      complexSymmetricConjugatePairBlock
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) = _
  rw [complexSymmetricConjugatePairBlock_eq_real_sub_imag, smul_sub]

/-- Exact finite-window block structure: the full eta matrix is its
critical-line positive block plus the difference of the two off-line positive
blocks. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
    {d : Type*} (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T =
      pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T +
        (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T -
          pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T) := by
  unfold pairedEtaTopPrefixFiniteZeroWindowBlock
  rw [sum_spectralZetaZeroWindow_eq_upper_add_critical_add_lower,
    sum_spectralLowerZetaZeroWindow_eq_upper_conjugatePartner hT]
  unfold pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
    pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
    pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock
  calc
    (∑ rho ∈ spectralUpperZetaZeroWindow T,
          (analyticZetaZeroMultiplicity rho : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
          (∑ rho ∈ spectralCriticalZetaZeroWindow T,
            (analyticZetaZeroMultiplicity rho : ℂ) •
              Matrix.vecMulVec
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
        ∑ rho ∈ spectralUpperZetaZeroWindow T,
          (analyticZetaZeroMultiplicity
              (NontrivialZetaZero.conjugatePartner rho) : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
                (NontrivialZetaZero.conjugatePartner rho))
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
                (NontrivialZetaZero.conjugatePartner rho)) =
      (∑ rho ∈ spectralCriticalZetaZeroWindow T,
          (analyticZetaZeroMultiplicity rho : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
        ∑ rho ∈ spectralUpperZetaZeroWindow T,
          ((analyticZetaZeroMultiplicity rho : ℂ) •
              Matrix.vecMulVec
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) +
            (analyticZetaZeroMultiplicity
                (NontrivialZetaZero.conjugatePartner rho) : ℂ) •
              Matrix.vecMulVec
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
                  (NontrivialZetaZero.conjugatePartner rho))
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
                  (NontrivialZetaZero.conjugatePartner rho))) := by
      rw [Finset.sum_add_distrib]
      abel
    _ = (∑ rho ∈ spectralCriticalZetaZeroWindow T,
          (analyticZetaZeroMultiplicity rho : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
        ∑ rho ∈ spectralUpperZetaZeroWindow T,
          ((analyticZetaZeroMultiplicity rho : ℂ) •
              ((2 : ℂ) • Matrix.vecMulVec
                (complexVectorReal
                  (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
                (complexVectorReal
                  (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))) -
            (analyticZetaZeroMultiplicity rho : ℂ) •
              ((2 : ℂ) • Matrix.vecMulVec
                (complexVectorImag
                  (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
                (complexVectorImag
                  (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)))) := by
      apply congrArg ((∑ rho ∈ spectralCriticalZetaZeroWindow T,
        (analyticZetaZeroMultiplicity rho : ℂ) •
          Matrix.vecMulVec
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) + ·)
      apply Finset.sum_congr rfl
      intro rho _hrho
      exact
        topPrefixFiniteCutoffFamilyFeature_weightedPairBlock_eq_real_sub_imag
          cutoff rho
    _ = _ := by rw [Finset.sum_sub_distrib]

private theorem posSemidef_finset_sum
    {d α : Type*} (s : Finset α) (f : α → Matrix d d ℂ)
    (hf : ∀ a ∈ s, (f a).PosSemidef) :
    (∑ a ∈ s, f a).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
      exact Matrix.PosSemidef.zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))

/-- The critical-line block is positive semidefinite. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_posSemidef
    {d : Type*} [Fintype d]
    (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T).PosSemidef := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
  apply posSemidef_finset_sum
  intro rho hrho
  have hre : rho.1.re = 1 / 2 :=
    (zetaSpectralCoordinate_im_eq_zero_iff rho.1).1
      (mem_spectralCriticalZetaZeroWindow.mp hrho).2
  have hpartner : NontrivialZetaZero.conjugatePartner rho = rho :=
    conjugatePartner_eq_self_of_re_eq_half rho hre
  have hstar :
      star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) =
        pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho := by
    rw [← topPrefixFiniteCutoffFamilyFeature_conjugatePartner, hpartner]
  have hbase := Matrix.posSemidef_vecMulVec_self_star
    (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
  rw [hstar] at hbase
  exact hbase.smul
    (Complex.zero_le_real.mpr (Nat.cast_nonneg _))

/-- The real off-line block is positive semidefinite. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_posSemidef
    {d : Type*} [Fintype d]
    (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T).PosSemidef := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
  apply posSemidef_finset_sum
  intro rho _hrho
  exact
    (complexVectorRealPairBlock_posSemidef
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)).smul
        (Complex.zero_le_real.mpr (Nat.cast_nonneg _))

/-- The imaginary off-line block is positive semidefinite. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_posSemidef
    {d : Type*} [Fintype d]
    (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T).PosSemidef := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock
  apply posSemidef_finset_sum
  intro rho _hrho
  exact
    (complexVectorImagPairBlock_posSemidef
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)).smul
        (Complex.zero_le_real.mpr (Nat.cast_nonneg _))

/-- The complete multiplicity-weighted eta block on every nonnegative finite
spectral window is Hermitian. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_isHermitian
    {d : Type*} [Fintype d]
    (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T).IsHermitian := by
  rw [pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
    cutoff hT]
  exact
    (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_posSemidef cutoff T).isHermitian.add
      ((pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_posSemidef cutoff T).isHermitian.sub
        (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_posSemidef cutoff T).isHermitian)

end

end RiemannGaussian
