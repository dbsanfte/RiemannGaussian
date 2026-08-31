import RiemannGaussian.External.Zeta23EtaWindowBridge
import RiemannGaussian.EtaEnergyFiniteWindowInertia

/-!
# Reflection-paired eta blocks on Zeta23 dyadic windows

The project-native Zeta23 bridge supplies the finite positive-ordinate window
whose critical and total cardinalities occur in the imported benchmark. This
module equips that same window with the reflection and eta-matrix structure
used by the certificate branch.

Critical-line reflection preserves the ordinate, hence preserves every
half-open positive window. Lean splits the window into upper, critical, and
lower spectral colours, proves that reflection bijects the upper and lower
pieces, and obtains the exact cardinality identity

`total = critical + 2 * upper`.

The literal multiplicity-weighted eta block on this window then decomposes as

`onLine + (offLineReal - offLineImag)`.

Lean then bounds the block's negative inertia by the number of upper
off-critical reflection pairs and applies the imported exact `HD(1)` theorem.
Thus every finite eta cutoff family inherits the full asymptotic Zeta23 defect
bound, with a fixed strict saving over the old two-thirds ceiling. This
reproduces the external benchmark inside the sign-preserving eta carrier; it
does not improve the zero proportion.
-/

open Complex
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

/-- The upper spectral colour in a project-native positive ordinate window.
Here upper/lower refer to the imaginary part of the rotated spectral
coordinate, equivalently the two sides of the critical line. -/
def positiveSpectralUpperZetaZeroWindow (T₁ T₂ : ℝ) :
    Finset NontrivialZetaZero :=
  (positiveSpectralZetaZeroWindow T₁ T₂).filter fun rho ↦
    0 < (zetaSpectralCoordinate rho.1).im

/-- The lower spectral colour in a project-native positive ordinate window.
-/
def positiveSpectralLowerZetaZeroWindow (T₁ T₂ : ℝ) :
    Finset NontrivialZetaZero :=
  (positiveSpectralZetaZeroWindow T₁ T₂).filter fun rho ↦
    (zetaSpectralCoordinate rho.1).im < 0

@[simp]
theorem mem_positiveSpectralUpperZetaZeroWindow
    {T₁ T₂ : ℝ} {rho : NontrivialZetaZero} :
    rho ∈ positiveSpectralUpperZetaZeroWindow T₁ T₂ ↔
      rho ∈ positiveSpectralZetaZeroWindow T₁ T₂ ∧
        0 < (zetaSpectralCoordinate rho.1).im := by
  simp [positiveSpectralUpperZetaZeroWindow]

@[simp]
theorem mem_positiveSpectralLowerZetaZeroWindow
    {T₁ T₂ : ℝ} {rho : NontrivialZetaZero} :
    rho ∈ positiveSpectralLowerZetaZeroWindow T₁ T₂ ↔
      rho ∈ positiveSpectralZetaZeroWindow T₁ T₂ ∧
        (zetaSpectralCoordinate rho.1).im < 0 := by
  simp [positiveSpectralLowerZetaZeroWindow]

/-- The already named critical window is the zero-spectral-imaginary-part
filter of the same full window. -/
theorem positiveSpectralCriticalZetaZeroWindow_eq_spectral_filter
    (T₁ T₂ : ℝ) :
    positiveSpectralCriticalZetaZeroWindow T₁ T₂ =
      (positiveSpectralZetaZeroWindow T₁ T₂).filter fun rho ↦
        (zetaSpectralCoordinate rho.1).im = 0 := by
  ext rho
  rw [mem_positiveSpectralCriticalZetaZeroWindow, Finset.mem_filter,
    mem_positiveSpectralZetaZeroWindow,
    zetaSpectralCoordinate_im_eq_zero_iff]

/-- Critical-line reflection preserves every project-native ordinate window.
-/
theorem conjugatePartner_mem_positiveSpectralZetaZeroWindow_iff
    (T₁ T₂ : ℝ) (rho : NontrivialZetaZero) :
    NontrivialZetaZero.conjugatePartner rho ∈
        positiveSpectralZetaZeroWindow T₁ T₂ ↔
      rho ∈ positiveSpectralZetaZeroWindow T₁ T₂ := by
  simp only [mem_positiveSpectralZetaZeroWindow]
  simp [NontrivialZetaZero.conjugatePartner_coe]

/-- A sum over a positive ordinate window splits exactly into upper,
critical, and lower spectral colours. -/
theorem sum_positiveSpectralZetaZeroWindow_eq_upper_add_critical_add_lower
    {M : Type*} [AddCommMonoid M]
    (f : NontrivialZetaZero → M) (T₁ T₂ : ℝ) :
    (∑ rho ∈ positiveSpectralZetaZeroWindow T₁ T₂, f rho) =
      (∑ rho ∈ positiveSpectralUpperZetaZeroWindow T₁ T₂, f rho) +
        (∑ rho ∈ positiveSpectralCriticalZetaZeroWindow T₁ T₂, f rho) +
          ∑ rho ∈ positiveSpectralLowerZetaZeroWindow T₁ T₂, f rho := by
  unfold positiveSpectralUpperZetaZeroWindow
    positiveSpectralLowerZetaZeroWindow
  rw [positiveSpectralCriticalZetaZeroWindow_eq_spectral_filter]
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

/-- Reflection bijects the upper and lower spectral colours of an arbitrary
positive ordinate window. -/
theorem sum_positiveSpectralLowerZetaZeroWindow_eq_upper_conjugatePartner
    {M : Type*} [AddCommMonoid M] (T₁ T₂ : ℝ)
    (f : NontrivialZetaZero → M) :
    (∑ rho ∈ positiveSpectralLowerZetaZeroWindow T₁ T₂, f rho) =
      ∑ rho ∈ positiveSpectralUpperZetaZeroWindow T₁ T₂,
        f (NontrivialZetaZero.conjugatePartner rho) := by
  symm
  refine Finset.sum_bij
    (fun rho _hrho ↦ NontrivialZetaZero.conjugatePartner rho)
    ?_ ?_ ?_ ?_
  · intro rho hrho
    have hmem := (mem_positiveSpectralUpperZetaZeroWindow.mp hrho).1
    have hupper := (mem_positiveSpectralUpperZetaZeroWindow.mp hrho).2
    apply mem_positiveSpectralLowerZetaZeroWindow.mpr
    constructor
    · exact
        (conjugatePartner_mem_positiveSpectralZetaZeroWindow_iff T₁ T₂ rho).2
          hmem
    · rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
      simp only [Complex.conj_im]
      linarith
  · intro rho₁ _hrho₁ rho₂ _hrho₂ heq
    exact NontrivialZetaZero.conjugatePartnerEquiv.injective heq
  · intro rho hrho
    have hmem := (mem_positiveSpectralLowerZetaZeroWindow.mp hrho).1
    have hlower := (mem_positiveSpectralLowerZetaZeroWindow.mp hrho).2
    refine ⟨NontrivialZetaZero.conjugatePartner rho, ?_, ?_⟩
    · apply mem_positiveSpectralUpperZetaZeroWindow.mpr
      constructor
      · exact
          (conjugatePartner_mem_positiveSpectralZetaZeroWindow_iff T₁ T₂ rho).2
            hmem
      · rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
        simp only [Complex.conj_im]
        linarith
    · simp
  · intro rho _hrho
    rfl

/-- A positive ordinate window contains its critical-line zeros together
with equally many upper and lower off-line zeros. -/
theorem card_positiveSpectralZetaZeroWindow_eq_critical_add_two_mul_upper
    (T₁ T₂ : ℝ) :
    (positiveSpectralZetaZeroWindow T₁ T₂).card =
      (positiveSpectralCriticalZetaZeroWindow T₁ T₂).card +
        2 * (positiveSpectralUpperZetaZeroWindow T₁ T₂).card := by
  have hsplit :=
    sum_positiveSpectralZetaZeroWindow_eq_upper_add_critical_add_lower
      (fun _ : NontrivialZetaZero ↦ (1 : ℕ)) T₁ T₂
  have hlower :=
    sum_positiveSpectralLowerZetaZeroWindow_eq_upper_conjugatePartner
      T₁ T₂ (fun _ : NontrivialZetaZero ↦ (1 : ℕ))
  simp only [← Finset.card_eq_sum_ones] at hsplit hlower
  omega

/-! ## Literal eta block on the benchmark window -/

/-- Multiplicity-weighted complex-symmetric eta block over a project-native
positive ordinate window. -/
def pairedEtaTopPrefixFinitePositiveWindowBlock
    {d : Type*} (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ positiveSpectralZetaZeroWindow T₁ T₂,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      Matrix.vecMulVec
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)

/-- Critical-line part of the eta block on a positive ordinate window. -/
def pairedEtaTopPrefixFinitePositiveWindowOnLineBlock
    {d : Type*} (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ positiveSpectralCriticalZetaZeroWindow T₁ T₂,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      Matrix.vecMulVec
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)

/-- Positive real rank-one part of the off-line reflection pairs in a
positive ordinate window. -/
def pairedEtaTopPrefixFinitePositiveWindowOffLineRealBlock
    {d : Type*} (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ positiveSpectralUpperZetaZeroWindow T₁ T₂,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      ((2 : ℂ) • Matrix.vecMulVec
        (complexVectorReal
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
        (complexVectorReal
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)))

/-- Positive imaginary rank-one part of the off-line reflection pairs in a
positive ordinate window. It is subtracted in the signed eta block. -/
def pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock
    {d : Type*} (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  ∑ rho ∈ positiveSpectralUpperZetaZeroWindow T₁ T₂,
    (analyticZetaZeroMultiplicity rho : ℂ) •
      ((2 : ℂ) • Matrix.vecMulVec
        (complexVectorImag
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
        (complexVectorImag
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)))

/-- Exact sign-preserving block decomposition on the same finite window used
by the project-native Zeta23 benchmark. -/
theorem pairedEtaTopPrefixFinitePositiveWindowBlock_eq_onLine_add_offLineReal_sub_imag
    {d : Type*} (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    pairedEtaTopPrefixFinitePositiveWindowBlock cutoff T₁ T₂ =
      pairedEtaTopPrefixFinitePositiveWindowOnLineBlock cutoff T₁ T₂ +
        (pairedEtaTopPrefixFinitePositiveWindowOffLineRealBlock cutoff T₁ T₂ -
          pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock cutoff T₁ T₂) := by
  unfold pairedEtaTopPrefixFinitePositiveWindowBlock
  rw [sum_positiveSpectralZetaZeroWindow_eq_upper_add_critical_add_lower,
    sum_positiveSpectralLowerZetaZeroWindow_eq_upper_conjugatePartner]
  unfold pairedEtaTopPrefixFinitePositiveWindowOnLineBlock
    pairedEtaTopPrefixFinitePositiveWindowOffLineRealBlock
    pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock
  calc
    (∑ rho ∈ positiveSpectralUpperZetaZeroWindow T₁ T₂,
          (analyticZetaZeroMultiplicity rho : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
          (∑ rho ∈ positiveSpectralCriticalZetaZeroWindow T₁ T₂,
            (analyticZetaZeroMultiplicity rho : ℂ) •
              Matrix.vecMulVec
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
        ∑ rho ∈ positiveSpectralUpperZetaZeroWindow T₁ T₂,
          (analyticZetaZeroMultiplicity
              (NontrivialZetaZero.conjugatePartner rho) : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
                (NontrivialZetaZero.conjugatePartner rho))
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff
                (NontrivialZetaZero.conjugatePartner rho)) =
      (∑ rho ∈ positiveSpectralCriticalZetaZeroWindow T₁ T₂,
          (analyticZetaZeroMultiplicity rho : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
        ∑ rho ∈ positiveSpectralUpperZetaZeroWindow T₁ T₂,
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
    _ = (∑ rho ∈ positiveSpectralCriticalZetaZeroWindow T₁ T₂,
          (analyticZetaZeroMultiplicity rho : ℂ) •
            Matrix.vecMulVec
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
              (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)) +
        ∑ rho ∈ positiveSpectralUpperZetaZeroWindow T₁ T₂,
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
      apply congrArg ((∑ rho ∈
        positiveSpectralCriticalZetaZeroWindow T₁ T₂,
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

/-! ## Hermitian inertia on the literal benchmark block -/

private theorem positiveWindow_posSemidef_finset_sum
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

/-- The critical part of every positive-ordinate eta block is positive
semidefinite. -/
theorem pairedEtaTopPrefixFinitePositiveWindowOnLineBlock_posSemidef
    {d : Type*} [Fintype d]
    (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    (pairedEtaTopPrefixFinitePositiveWindowOnLineBlock
      cutoff T₁ T₂).PosSemidef := by
  unfold pairedEtaTopPrefixFinitePositiveWindowOnLineBlock
  apply positiveWindow_posSemidef_finset_sum
  intro rho hrho
  have hre : rho.1.re = 1 / 2 :=
    (mem_positiveSpectralCriticalZetaZeroWindow.mp hrho).2
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

/-- The real off-line part of every positive-ordinate eta block is positive
semidefinite. -/
theorem pairedEtaTopPrefixFinitePositiveWindowOffLineRealBlock_posSemidef
    {d : Type*} [Fintype d]
    (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    (pairedEtaTopPrefixFinitePositiveWindowOffLineRealBlock
      cutoff T₁ T₂).PosSemidef := by
  unfold pairedEtaTopPrefixFinitePositiveWindowOffLineRealBlock
  apply positiveWindow_posSemidef_finset_sum
  intro rho _hrho
  exact
    (complexVectorRealPairBlock_posSemidef
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)).smul
        (Complex.zero_le_real.mpr (Nat.cast_nonneg _))

/-- The imaginary off-line part of every positive-ordinate eta block is
positive semidefinite. It is the part subtracted by the signed block. -/
theorem pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock_posSemidef
    {d : Type*} [Fintype d]
    (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    (pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock
      cutoff T₁ T₂).PosSemidef := by
  unfold pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock
  apply positiveWindow_posSemidef_finset_sum
  intro rho _hrho
  exact
    (complexVectorImagPairBlock_posSemidef
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)).smul
        (Complex.zero_le_real.mpr (Nat.cast_nonneg _))

/-- The literal signed eta block on a positive ordinate window is Hermitian.
-/
theorem pairedEtaTopPrefixFinitePositiveWindowBlock_isHermitian
    {d : Type*} [Fintype d]
    (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    (pairedEtaTopPrefixFinitePositiveWindowBlock
      cutoff T₁ T₂).IsHermitian := by
  rw [pairedEtaTopPrefixFinitePositiveWindowBlock_eq_onLine_add_offLineReal_sub_imag]
  exact
    (pairedEtaTopPrefixFinitePositiveWindowOnLineBlock_posSemidef
        cutoff T₁ T₂).isHermitian.add
      ((pairedEtaTopPrefixFinitePositiveWindowOffLineRealBlock_posSemidef
          cutoff T₁ T₂).isHermitian.sub
        (pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock_posSemidef
          cutoff T₁ T₂).isHermitian)

/-- The rank of the subtracted imaginary block is at most the number of
upper off-line reflection pairs in the same window. -/
theorem pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock_rank_le_card
    {d : Type*} [Fintype d]
    (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    (pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock
        cutoff T₁ T₂).rank ≤
      (positiveSpectralUpperZetaZeroWindow T₁ T₂).card := by
  unfold pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock
  refine (matrixRank_finsetSum_le _ _ (fun _ ↦ 1) ?_).trans ?_
  · intro rho _hrho
    simpa only [smul_smul] using
      matrixRank_smul_vecMulVec_le
        ((analyticZetaZeroMultiplicity rho : ℂ) * 2)
        (complexVectorImag
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
        (complexVectorImag
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
  · simp

/-- The negative inertia of the literal positive-window eta block is at most
the number of upper off-line reflection pairs. It is expressed as the
positive index of the negated Hermitian block. -/
theorem pairedEtaTopPrefixFinitePositiveWindowBlock_negativeIndex_le_upper
    {d : Type*} [Fintype d]
    (cutoff : d → ℕ) (T₁ T₂ : ℝ) :
    HermitianInertia.posIndex
        (pairedEtaTopPrefixFinitePositiveWindowBlock_isHermitian
          cutoff T₁ T₂).neg ≤
      (positiveSpectralUpperZetaZeroWindow T₁ T₂).card := by
  let onLine :=
    pairedEtaTopPrefixFinitePositiveWindowOnLineBlock cutoff T₁ T₂
  let offReal :=
    pairedEtaTopPrefixFinitePositiveWindowOffLineRealBlock cutoff T₁ T₂
  let offImag :=
    pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock cutoff T₁ T₂
  let positivePart := onLine + offReal
  have hOnLine : onLine.PosSemidef :=
    pairedEtaTopPrefixFinitePositiveWindowOnLineBlock_posSemidef
      cutoff T₁ T₂
  have hOffReal : offReal.PosSemidef :=
    pairedEtaTopPrefixFinitePositiveWindowOffLineRealBlock_posSemidef
      cutoff T₁ T₂
  have hOffImag : offImag.PosSemidef :=
    pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock_posSemidef
      cutoff T₁ T₂
  have hPositivePart : positivePart.PosSemidef := hOnLine.add hOffReal
  have hdecomp :
      -pairedEtaTopPrefixFinitePositiveWindowBlock cutoff T₁ T₂ =
        offImag - positivePart := by
    rw [pairedEtaTopPrefixFinitePositiveWindowBlock_eq_onLine_add_offLineReal_sub_imag]
    simp only [positivePart, onLine, offReal, offImag]
    abel
  calc
    HermitianInertia.posIndex
        (pairedEtaTopPrefixFinitePositiveWindowBlock_isHermitian
          cutoff T₁ T₂).neg =
      HermitianInertia.posIndex
        (hOffImag.isHermitian.sub hPositivePart.isHermitian) :=
      HermitianInertia.posIndex_congr _ _ hdecomp
    _ ≤ offImag.rank :=
      HermitianInertia.posIndex_sub_le_rank hOffImag hPositivePart
    _ ≤ (positiveSpectralUpperZetaZeroWindow T₁ T₂).card :=
      pairedEtaTopPrefixFinitePositiveWindowOffLineImagBlock_rank_le_card
        cutoff T₁ T₂

/-! ## Unconditional Zeta23 defect inside the eta block -/

/-- The imported exact Montgomery--Taylor benchmark bounds the number of
upper off-line reflection pairs in the same project-native dyadic window.
This is the full epsilon form of the benchmark defect. -/
theorem externalZeta23_montgomeryTaylor_upperPairDefect_projectFiniteWindows :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      2 * ((positiveSpectralUpperZetaZeroWindow T (2 * T)).card : ℝ) ≤
        (1 - Zeta23.ThmD.HD 1 + ε) *
          (positiveSpectralZetaZeroWindow T (2 * T)).card := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    externalZeta23_montgomeryTaylor_projectFiniteWindows ε hε
  refine ⟨T₀, fun T hT ↦ ?_⟩
  have hcount := hT₀ T hT
  have hcardNat :=
    card_positiveSpectralZetaZeroWindow_eq_critical_add_two_mul_upper
      T (2 * T)
  have hcard :
      ((positiveSpectralZetaZeroWindow T (2 * T)).card : ℝ) =
        (positiveSpectralCriticalZetaZeroWindow T (2 * T)).card +
          2 * (positiveSpectralUpperZetaZeroWindow T (2 * T)).card := by
    exact_mod_cast hcardNat
  nlinarith

/-- The exact external Zeta23 defect bound holds for the negative inertia of
the literal multiplicity-weighted signed eta block. This is an unconditional
reproduction of the imported benchmark inside the eta certificate carrier,
not a stronger zero-proportion theorem. -/
theorem externalZeta23_montgomeryTaylor_etaBlockNegativeInertia
    {d : Type*} [Fintype d] (cutoff : d → ℕ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      2 * (HermitianInertia.posIndex
          (pairedEtaTopPrefixFinitePositiveWindowBlock_isHermitian
            cutoff T (2 * T)).neg : ℝ) ≤
        (1 - Zeta23.ThmD.HD 1 + ε) *
          (positiveSpectralZetaZeroWindow T (2 * T)).card := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ :=
    externalZeta23_montgomeryTaylor_upperPairDefect_projectFiniteWindows
      ε hε
  refine ⟨T₀, fun T hT ↦ ?_⟩
  have hindexNat :=
    pairedEtaTopPrefixFinitePositiveWindowBlock_negativeIndex_le_upper
      cutoff T (2 * T)
  have hindex :
      (HermitianInertia.posIndex
          (pairedEtaTopPrefixFinitePositiveWindowBlock_isHermitian
            cutoff T (2 * T)).neg : ℝ) ≤
        (positiveSpectralUpperZetaZeroWindow T (2 * T)).card := by
    exact_mod_cast hindexNat
  nlinarith [hT₀ T hT]

/-- A fixed exact positive saving over the old two-thirds defect ceiling,
now proved directly for the negative inertia of every literal eta cutoff
family on all sufficiently high dyadic windows. -/
theorem externalZeta23_etaBlockNegativeInertia_strictSavingOverTwoThirds
    {d : Type*} [Fintype d] (cutoff : d → ℕ) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      2 * (HermitianInertia.posIndex
          (pairedEtaTopPrefixFinitePositiveWindowBlock_isHermitian
            cutoff T (2 * T)).neg : ℝ) ≤
        ((1 : ℝ) / 3 - externalZeta23StrictGainOverTwoThirds) *
          (positiveSpectralZetaZeroWindow T (2 * T)).card := by
  have hgain : 0 < externalZeta23StrictGainOverTwoThirds :=
    externalZeta23_strictGainOverTwoThirds_pos
  obtain ⟨T₀, hT₀⟩ :=
    externalZeta23_montgomeryTaylor_etaBlockNegativeInertia cutoff
      externalZeta23StrictGainOverTwoThirds hgain
  refine ⟨T₀, fun T hT ↦ ?_⟩
  have h := hT₀ T hT
  convert h using 1
  unfold externalZeta23StrictGainOverTwoThirds
  ring

end

end RiemannGaussian
