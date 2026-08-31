import RiemannGaussian.Hybrid.EtaGeometricReflectionEffectiveRank
import RiemannGaussian.EtaEnergyFiniteWindowPairCorrelation

/-!
# Literal reflection-even eta frame potential

This module opens the first two colour-resolved coordinate paths into their
underlying eta feature atoms. The reflection-even frame has one atom for each
critical zero and one real-coordinate atom for each upper off-line pair, with
the exact analytic multiplicity weights retained.

Lean identifies the coordinate carrier with the frame operator, its trace
with the weighted frame mass, and its Frobenius square with the full weighted
frame potential. Every pair correlation in that potential is real and
nonnegative after squaring; no triangle inequality is used. The previously
checked `13/18` and finite-window `18/18` sufficient conditions therefore
become explicit eta frame-potential inequalities. Those inequalities remain
open arithmetic premises, so this module proves no improved zero proportion.
-/

open Complex Matrix Finset Filter
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- The two retained reflection-even atom colours: critical zeros and upper
representatives of off-line reflection pairs. -/
abbrev PairedEtaReflectionEvenFrameIndex (T : ℝ) :=
  ↑(spectralCriticalZetaZeroWindow T) ⊕ ↑(spectralUpperZetaZeroWindow T)

/-- The frame has one atom per critical zero and one per upper off-line pair. -/
theorem card_pairedEtaReflectionEvenFrameIndex (T : ℝ) :
    Fintype.card (PairedEtaReflectionEvenFrameIndex T) =
      (spectralCriticalZetaZeroWindow T).card +
        (spectralUpperZetaZeroWindow T).card := by
  simp [PairedEtaReflectionEvenFrameIndex]

/-- Multiplicity weight of a reflection-even frame atom. An upper off-line
representative carries both members of its reflected pair. -/
def pairedEtaReflectionEvenFrameWeight (T : ℝ) :
    PairedEtaReflectionEvenFrameIndex T → ℝ
  | Sum.inl rho => analyticZetaZeroMultiplicity rho
  | Sum.inr rho => 2 * analyticZetaZeroMultiplicity rho

/-- Literal packed eta vector of a reflection-even frame atom. Critical
features are already real; an off-line pair retains its real coordinate. -/
def pairedEtaReflectionEvenFrameVector
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    PairedEtaReflectionEvenFrameIndex T → d × Fin 2 → ℂ
  | Sum.inl rho => pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho
  | Sum.inr rho => complexVectorReal
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)

/-- Weighted sum of squared norms of the reflection-even eta atoms. -/
def pairedEtaReflectionEvenFrameTraceMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ a : PairedEtaReflectionEvenFrameIndex T,
    pairedEtaReflectionEvenFrameWeight T a *
      ∑ j, ‖pairedEtaReflectionEvenFrameVector cutoff T a j‖ ^ 2

/-- Full phase-preserving weighted double correlation of the reflection-even
eta atoms. Reality of every correlation is proved below rather than assumed
in this definition. -/
def pairedEtaReflectionEvenFramePotential
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) : ℝ :=
  ∑ a : PairedEtaReflectionEvenFrameIndex T,
    ∑ b : PairedEtaReflectionEvenFrameIndex T,
      (((pairedEtaReflectionEvenFrameWeight T a *
          pairedEtaReflectionEvenFrameWeight T b : ℝ) : ℂ) *
        (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
          pairedEtaReflectionEvenFrameVector cutoff T a) ^ 2).re

/-- Every reflection-even frame weight is strictly positive. -/
theorem pairedEtaReflectionEvenFrameWeight_pos
    (T : ℝ) (a : PairedEtaReflectionEvenFrameIndex T) :
    0 < pairedEtaReflectionEvenFrameWeight T a := by
  cases a with
  | inl rho =>
      change 0 < (analyticZetaZeroMultiplicity rho : ℝ)
      exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  | inr rho =>
      change 0 < 2 * (analyticZetaZeroMultiplicity rho : ℝ)
      have hrho : 0 < (analyticZetaZeroMultiplicity rho : ℝ) := by
        exact_mod_cast analyticZetaZeroMultiplicity_positive rho
      positivity

/-- Every retained frame vector is fixed by componentwise conjugation. -/
theorem star_pairedEtaReflectionEvenFrameVector
    {d : Type*} (cutoff : d → ℕ) (T : ℝ)
    (a : PairedEtaReflectionEvenFrameIndex T) :
    star (pairedEtaReflectionEvenFrameVector cutoff T a) =
      pairedEtaReflectionEvenFrameVector cutoff T a := by
  cases a with
  | inl rho =>
      have hre : rho.1.1.re = 1 / 2 :=
        (zetaSpectralCoordinate_im_eq_zero_iff rho.1.1).1
          (mem_spectralCriticalZetaZeroWindow.mp rho.2).2
      have hpartner : NontrivialZetaZero.conjugatePartner rho.1 = rho.1 :=
        conjugatePartner_eq_self_of_re_eq_half rho.1 hre
      unfold pairedEtaReflectionEvenFrameVector
      rw [← topPrefixFiniteCutoffFamilyFeature_conjugatePartner, hpartner]
  | inr rho =>
      exact star_complexVectorReal
        (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)

/-- Every pair correlation in the reflection-even frame is real. -/
theorem pairedEtaReflectionEvenFrameCorrelation_star_eq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    (a b : PairedEtaReflectionEvenFrameIndex T) :
    starRingEnd ℂ
        (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
          pairedEtaReflectionEvenFrameVector cutoff T a) =
      star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
        pairedEtaReflectionEvenFrameVector cutoff T a := by
  change star
      (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
        pairedEtaReflectionEvenFrameVector cutoff T a) = _
  calc
    _ = star (pairedEtaReflectionEvenFrameVector cutoff T a) ⬝ᵥ
        pairedEtaReflectionEvenFrameVector cutoff T b :=
      (Matrix.star_dotProduct _ _).symm
    _ = pairedEtaReflectionEvenFrameVector cutoff T a ⬝ᵥ
        pairedEtaReflectionEvenFrameVector cutoff T b := by
      rw [star_pairedEtaReflectionEvenFrameVector]
    _ = pairedEtaReflectionEvenFrameVector cutoff T b ⬝ᵥ
        pairedEtaReflectionEvenFrameVector cutoff T a := dotProduct_comm _ _
    _ = star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
        pairedEtaReflectionEvenFrameVector cutoff T a := by
      rw [star_pairedEtaReflectionEvenFrameVector]

/-- Each individual weighted frame-potential term is nonnegative. -/
theorem pairedEtaReflectionEvenFramePairTerm_nonneg
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    (a b : PairedEtaReflectionEvenFrameIndex T) :
    0 ≤ (((pairedEtaReflectionEvenFrameWeight T a *
          pairedEtaReflectionEvenFrameWeight T b : ℝ) : ℂ) *
        (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
          pairedEtaReflectionEvenFrameVector cutoff T a) ^ 2).re := by
  let z := star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
    pairedEtaReflectionEvenFrameVector cutoff T a
  have hz : ((z.re : ℝ) : ℂ) = z :=
    Complex.conj_eq_iff_re.mp
      (pairedEtaReflectionEvenFrameCorrelation_star_eq cutoff T a b)
  change 0 ≤ (((pairedEtaReflectionEvenFrameWeight T a *
    pairedEtaReflectionEvenFrameWeight T b : ℝ) : ℂ) * z ^ 2).re
  rw [← hz]
  norm_cast
  exact mul_nonneg
    (mul_nonneg (pairedEtaReflectionEvenFrameWeight_pos T a).le
      (pairedEtaReflectionEvenFrameWeight_pos T b).le)
    (sq_nonneg z.re)

/-- The complete reflection-even frame potential is nonnegative. -/
theorem pairedEtaReflectionEvenFramePotential_nonneg
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    0 ≤ pairedEtaReflectionEvenFramePotential cutoff T := by
  unfold pairedEtaReflectionEvenFramePotential
  exact Finset.sum_nonneg fun a _ha ↦
    Finset.sum_nonneg fun b _hb ↦
      pairedEtaReflectionEvenFramePairTerm_nonneg cutoff T a b

/-- The frame potential is exactly a sum of weights times squared real
correlations, with the critical/off-line-real colour index still explicit. -/
theorem pairedEtaReflectionEvenFramePotential_eq_sum_weight_mul_re_sq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    pairedEtaReflectionEvenFramePotential cutoff T =
      ∑ a : PairedEtaReflectionEvenFrameIndex T,
        ∑ b : PairedEtaReflectionEvenFrameIndex T,
          pairedEtaReflectionEvenFrameWeight T a *
            pairedEtaReflectionEvenFrameWeight T b *
              (star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
                pairedEtaReflectionEvenFrameVector cutoff T a).re ^ 2 := by
  unfold pairedEtaReflectionEvenFramePotential
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  let z := star (pairedEtaReflectionEvenFrameVector cutoff T b) ⬝ᵥ
    pairedEtaReflectionEvenFrameVector cutoff T a
  have hz : ((z.re : ℝ) : ℂ) = z :=
    Complex.conj_eq_iff_re.mp
      (pairedEtaReflectionEvenFrameCorrelation_star_eq cutoff T a b)
  change
    ((((pairedEtaReflectionEvenFrameWeight T a *
      pairedEtaReflectionEvenFrameWeight T b : ℝ) : ℂ) * z ^ 2).re) = _
  rw [← hz]
  norm_cast

/-- The literal reflection-even frame operator is exactly the sum of the
on-line and off-line-real eta coordinate blocks. -/
theorem sum_pairedEtaReflectionEvenFrame_eq_onLine_add_offLineReal
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    (∑ a : PairedEtaReflectionEvenFrameIndex T,
      (pairedEtaReflectionEvenFrameWeight T a : ℂ) • Matrix.vecMulVec
        (pairedEtaReflectionEvenFrameVector cutoff T a)
        (pairedEtaReflectionEvenFrameVector cutoff T a)) =
      pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T +
        pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T := by
  rw [Fintype.sum_sum_type]
  unfold pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
    pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
  simp only [pairedEtaReflectionEvenFrameWeight,
    pairedEtaReflectionEvenFrameVector, Finset.univ_eq_attach]
  congr 1
  · simpa using Finset.sum_attach (spectralCriticalZetaZeroWindow T)
      (fun rho ↦ (analyticZetaZeroMultiplicity rho : ℂ) •
        Matrix.vecMulVec
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho)
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
  · calc
      _ = ∑ rho ∈ spectralUpperZetaZeroWindow T,
          (((2 * analyticZetaZeroMultiplicity rho : ℝ) : ℂ) •
            Matrix.vecMulVec
              (complexVectorReal
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
              (complexVectorReal
                (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))) := by
            simpa using Finset.sum_attach (spectralUpperZetaZeroWindow T)
              (fun rho ↦ (((2 * analyticZetaZeroMultiplicity rho : ℝ) : ℂ) •
                Matrix.vecMulVec
                  (complexVectorReal
                    (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
                  (complexVectorReal
                    (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro rho _hrho
        module

/-- The reflection-even coordinate carrier's Frobenius square is exactly the
literal eta frame potential. -/
theorem pairedEtaGeometricReflectionEvenCoordinateCarrier_frobSq_eq_framePotential
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    HermitianRankTrace.frobSq
        (pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n) =
      pairedEtaReflectionEvenFramePotential
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T := by
  rw [pairedEtaGeometricReflectionEvenCoordinateCarrier_eq_onLine_add_offLineReal
    q hT n, ← sum_pairedEtaReflectionEvenFrame_eq_onLine_add_offLineReal]
  change HermitianInertia.frobSq _ = _
  unfold pairedEtaReflectionEvenFramePotential
  simpa using
    (HermitianInertia.frobSq_finsetSum_real_smul_vecMulVec_eq_pairCorrelation
      (Finset.univ : Finset (PairedEtaReflectionEvenFrameIndex T))
      (pairedEtaReflectionEvenFrameWeight T)
      (pairedEtaReflectionEvenFrameVector
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T))

/-- The reflection-even coordinate carrier's real trace is exactly the
literal eta frame trace mass. -/
theorem pairedEtaGeometricReflectionEvenCoordinateCarrier_rtrace_eq_frameTraceMass
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    HermitianRankTrace.rtrace
        (pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n) =
      pairedEtaReflectionEvenFrameTraceMass
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T := by
  change HermitianInertia.rtrace _ = _
  rw [pairedEtaGeometricReflectionEvenCoordinateCarrier_eq_onLine_add_offLineReal
      q hT n,
    HermitianInertia.rtrace_add,
    pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_eq,
    pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_rtrace_eq]
  unfold pairedEtaReflectionEvenFrameTraceMass
  rw [Fintype.sum_sum_type]
  simp only [pairedEtaReflectionEvenFrameWeight,
    pairedEtaReflectionEvenFrameVector, Finset.univ_eq_attach]
  congr 1
  · symm
    simpa using Finset.sum_attach (spectralCriticalZetaZeroWindow T)
      (fun rho ↦ (analyticZetaZeroMultiplicity rho : ℝ) *
        ∑ j, ‖pairedEtaTopPrefixFiniteCutoffFamilyFeature
          (fun k : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n k) rho j‖ ^ 2)
  · symm
    simpa using Finset.sum_attach (spectralUpperZetaZeroWindow T)
      (fun rho ↦ (2 * analyticZetaZeroMultiplicity rho : ℝ) *
        ∑ j, ‖complexVectorReal
          (pairedEtaTopPrefixFiniteCutoffFamilyFeature
            (fun k : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n k) rho) j‖ ^ 2)

/-- The length-one colour-resolved closed path is the literal frame mass. -/
theorem pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum_one_eq_frameTraceMass
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
        q T n 1).re =
      pairedEtaReflectionEvenFrameTraceMass
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T := by
  calc
    _ = HermitianRankTrace.rtrace
        (pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n) := by
      simpa using
        (pairedEtaGeometricReflectionEvenCoordinateCarrier_rtrace_pow_eq_re_colouredClosedPathSum
          q hT n 1).symm
    _ = _ :=
      pairedEtaGeometricReflectionEvenCoordinateCarrier_rtrace_eq_frameTraceMass
        q hT n

/-- The length-two colour-resolved closed path is the literal frame
potential. -/
theorem pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum_two_eq_framePotential
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
        q T n 2).re =
      pairedEtaReflectionEvenFramePotential
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T := by
  rw [← pairedEtaGeometricReflectionEvenCoordinateCarrier_frobSq_eq_re_colouredClosedPathSum_two
    q hT n]
  exact
    pairedEtaGeometricReflectionEvenCoordinateCarrier_frobSq_eq_framePotential
      q hT n

/-- The explicit strict eta frame-potential inequality is sufficient to beat
the `13/18` critical-zero proportion. -/
theorem pairedEtaGeometricReflectionEven_thirteen_eighteen_of_framePotential
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (hmoment :
      (31 : ℝ) * (spectralZetaZeroWindow T).card *
          pairedEtaReflectionEvenFramePotential
            (fun j : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n j) T <
        36 * pairedEtaReflectionEvenFrameTraceMass
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T ^ 2) :
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card := by
  apply pairedEtaGeometricReflectionEven_thirteen_eighteen_of_colouredTwoMoment
    q hT n hwindow hK
  rw [pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum_one_eq_frameTraceMass
      q hT n,
    pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum_two_eq_framePotential
      q hT n]
  exact hmoment

/-- The endpoint eta frame-potential ceiling is sufficient for every zero in
the represented finite window to be critical. -/
theorem pairedEtaGeometricReflectionEven_allCritical_of_framePotentialCeiling
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (hmoment :
      (spectralZetaZeroWindow T).card *
          pairedEtaReflectionEvenFramePotential
            (fun j : Fin (spectralZetaZeroWindow T).card ↦
              pairedEtaGeometricHyperbolicCutoff q n j) T ≤
        pairedEtaReflectionEvenFrameTraceMass
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T ^ 2) :
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card := by
  apply pairedEtaGeometricReflectionEven_allCritical_of_colouredEffectiveRankCeiling
    q hT n hwindow hK
  rw [pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum_one_eq_frameTraceMass
      q hT n,
    pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum_two_eq_framePotential
      q hT n]
  exact hmoment

/-- The two open eta frame-potential premises paired with their checked
`13/18` and finite-window `18/18` consequences. -/
def PairedEtaGeometricReflectionEvenFramePotentialTargets
    (q : ℕ) (T : ℝ) (n : ℕ) : Prop :=
  (((31 : ℝ) * (spectralZetaZeroWindow T).card *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T <
      36 * pairedEtaReflectionEvenFrameTraceMass
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T ^ 2) →
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card) ∧
  ((((spectralZetaZeroWindow T).card : ℝ) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin (spectralZetaZeroWindow T).card ↦
            pairedEtaGeometricHyperbolicCutoff q n j) T ≤
      pairedEtaReflectionEvenFrameTraceMass
        (fun j : Fin (spectralZetaZeroWindow T).card ↦
          pairedEtaGeometricHyperbolicCutoff q n j) T ^ 2) →
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card)

/-- The literal frame-potential targets are exactly the preceding coloured
coordinate-path targets. -/
theorem pairedEtaGeometricReflectionEvenFramePotentialTargets_iff_colouredTargets
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    PairedEtaGeometricReflectionEvenFramePotentialTargets q T n ↔
      PairedEtaGeometricReflectionEvenColouredEffectiveRankTargets q T n := by
  unfold PairedEtaGeometricReflectionEvenFramePotentialTargets
    PairedEtaGeometricReflectionEvenColouredEffectiveRankTargets
  rw [pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum_one_eq_frameTraceMass
      q hT n,
    pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum_two_eq_framePotential
      q hT n]

/-- Both frame-potential implications hold whenever the actual eta features
are separated; this theorem does not assert either open premise. -/
theorem pairedEtaGeometricReflectionEvenFramePotentialCertificateInterface
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    PairedEtaGeometricReflectionEvenFramePotentialTargets q T n := by
  exact
    ⟨pairedEtaGeometricReflectionEven_thirteen_eighteen_of_framePotential
      q hT n hwindow hK,
    pairedEtaGeometricReflectionEven_allCritical_of_framePotentialCeiling
      q hT n hwindow hK⟩

/-- For every nonempty finite window, one odd prime base makes the complete
frame-potential interface valid at all sufficiently late blocks. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenFramePotentialCertificateInterface
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        PairedEtaGeometricReflectionEvenFramePotentialTargets q T n := by
  obtain ⟨q, hqPrime, hqOdd, hq, hpos⟩ :=
    exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hpos] with n hn
  exact pairedEtaGeometricReflectionEvenFramePotentialCertificateInterface
    q hT n hwindow hn.1

end

end RiemannGaussian
