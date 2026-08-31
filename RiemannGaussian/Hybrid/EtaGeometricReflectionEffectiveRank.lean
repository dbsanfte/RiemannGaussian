import RiemannGaussian.Hybrid.EtaGeometricReflectionCoordinateHeat
import Mathlib.Algebra.Order.Chebyshev

/-!
# Effective-rank certificate targets for the reflection-even eta carrier

This module turns the first two moments of the literal, colour-preserving eta
coordinate carrier into sufficient zero-proportion criteria.  The generic
Hermitian inequality

`rtrace(A)^2 ≤ rank(A) * frobSq(A)`

is proved from the nonzero eigenvalues by finite Cauchy–Schwarz.  The eta
coordinate carrier has rank exactly `critical + upper-off-line`; its trace and
Frobenius square are exactly the real parts of the retained length-one and
length-two coloured closed-path sums.

Consequently an explicit strict two-moment inequality implies a critical-zero
proportion above `13/18`.  A stronger endpoint ceiling implies that every zero
in the finite window is critical.  Both estimates remain open premises: this
file proves the reductions and does not claim a new zero proportion.
-/

open Matrix Finset Filter
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian.HermitianRankTrace

noncomputable section

variable {K : Type*} [RCLike K]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The square of a Hermitian matrix's real trace is at most its rank times
its squared Frobenius norm. The proof applies finite Cauchy--Schwarz only to
the nonzero eigenvalues, so the sharp dimension factor is `rank A`. -/
theorem rtrace_sq_le_rank_mul_frobSq
    {A : Matrix d d K} (hA : A.IsHermitian) :
    rtrace A ^ 2 ≤ (A.rank : ℝ) * frobSq A := by
  classical
  let s : Finset d := Finset.univ.filter fun i ↦ hA.eigenvalues i ≠ 0
  have hsum : (∑ i ∈ s, hA.eigenvalues i) = rtrace A := by
    rw [rtrace_eq_sum_eigenvalues hA]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _hi hi_not_mem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi_not_mem
    exact hi_not_mem
  have hsumSq : (∑ i ∈ s, hA.eigenvalues i ^ 2) = frobSq A := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hA]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _hi hi_not_mem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi_not_mem
    simp [hi_not_mem]
  have hcard : s.card = A.rank := by
    rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := s) (f := fun i ↦ hA.eigenvalues i)
  rw [hsum, hsumSq, hcard] at hcs
  exact_mod_cast hcs

/-- For a Hermitian matrix the squared Frobenius norm is its second real
trace moment. -/
theorem frobSq_eq_rtrace_pow_two {A : Matrix d d K} (hA : A.IsHermitian) :
    frobSq A = rtrace (A ^ 2) := by
  unfold frobSq rtrace
  rw [hA.eq]
  simp only [pow_two]

end

end RiemannGaussian.HermitianRankTrace

namespace RiemannGaussian

noncomputable section

open HermitianRankTrace

/-- Under actual eta-feature separation, the coordinate carrier has one rank
direction for every critical zero and one for every upper off-line pair. -/
theorem pairedEtaGeometricReflectionEvenCoordinateCarrier_rank
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    (pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n).rank =
      (spectralCriticalZetaZeroWindow T).card +
        (spectralUpperZetaZeroWindow T).card := by
  let W := pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix q T hT n
  have hgram : Wᴴ * W =
      pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n :=
    pairedEtaGeometricReflectionEvenFeatureSynthesisMatrix_conjTranspose_mul_self
      q T hT n
  calc
    (pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n).rank =
        (W * Wᴴ).rank := rfl
    _ = W.rank := Matrix.rank_self_mul_conjTranspose W
    _ = (Wᴴ * W).rank := (Matrix.rank_conjTranspose_mul_self W).symm
    _ = (pairedEtaGeometricReflectionEvenCompressedZeroGram q T hT n).rank :=
      congrArg Matrix.rank hgram
    _ = _ := pairedEtaGeometricReflectionEvenCompressedZeroGram_rank q hT n hK

/-- The carrier's squared Frobenius norm is exactly its length-two
colour-resolved closed-path sum. -/
theorem pairedEtaGeometricReflectionEvenCoordinateCarrier_frobSq_eq_re_colouredClosedPathSum_two
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    frobSq (pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n) =
      (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
        q T n 2).re := by
  rw [frobSq_eq_rtrace_pow_two
    (pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
      q T hT n).isHermitian]
  exact pairedEtaGeometricReflectionEvenCoordinateCarrier_rtrace_pow_eq_re_colouredClosedPathSum
    q hT n 2

/-- A lower bound for the normalized effective rank of the literal carrier
forces the corresponding lower bound for its critical-zero proportion. -/
theorem pairedEtaGeometricReflectionEven_criticalFraction_gt_of_effectiveRank
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (target : ℝ) (htarget : -1 ≤ target)
    (hmoment :
      (1 + target) * (spectralZetaZeroWindow T).card *
          frobSq (pairedEtaGeometricReflectionEvenCoordinateCarrier
            q T hT n) <
        2 * rtrace (pairedEtaGeometricReflectionEvenCoordinateCarrier
          q T hT n) ^ 2) :
    target < (spectralCriticalZetaZeroWindow T).card /
      (spectralZetaZeroWindow T).card := by
  let B := pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n
  have hB := pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
    q T hT n
  have heffective := rtrace_sq_le_rank_mul_frobSq hB.isHermitian
  have hfrob : 0 ≤ frobSq B := by
    rw [frobSq_hermitian_eq_sum_sq_eigenvalues hB.isHermitian]
    exact Finset.sum_nonneg fun i _hi ↦ sq_nonneg _
  have hleftNonneg :
      0 ≤ (1 + target) * (spectralZetaZeroWindow T).card * frobSq B := by
    have : 0 ≤ 1 + target := by linarith
    positivity
  have htraceSq : 0 < rtrace B ^ 2 := by
    change (1 + target) * (spectralZetaZeroWindow T).card * frobSq B <
      2 * rtrace B ^ 2 at hmoment
    nlinarith
  have hfrobPos : 0 < frobSq B := by
    by_contra hf
    have hfrobZero : frobSq B = 0 :=
      le_antisymm (not_lt.mp hf) hfrob
    rw [hfrobZero] at heffective
    nlinarith
  have hrankTarget :
      (1 + target) * (spectralZetaZeroWindow T).card <
        2 * B.rank := by
    have hscaled :
        ((1 + target) * (spectralZetaZeroWindow T).card) * frobSq B <
          (2 * B.rank) * frobSq B := by
      change (1 + target) * (spectralZetaZeroWindow T).card * frobSq B <
        2 * rtrace B ^ 2 at hmoment
      nlinarith
    exact lt_of_mul_lt_mul_right hscaled hfrobPos.le
  have hrank := pairedEtaGeometricReflectionEvenCoordinateCarrier_rank
    q hT n hK
  change B.rank = _ at hrank
  rw [hrank] at hrankTarget
  push_cast at hrankTarget
  have hcard : ((spectralZetaZeroWindow T).card : ℝ) =
      (spectralCriticalZetaZeroWindow T).card +
        2 * (spectralUpperZetaZeroWindow T).card := by
    exact_mod_cast spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper hT
  have hcardPos : 0 < ((spectralZetaZeroWindow T).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hwindow
  rw [lt_div_iff₀ hcardPos]
  nlinarith

/-- The endpoint effective-rank ceiling is a sufficient finite-window
`18/18` criterion: it forces every represented zero to be critical.  This
criterion is deliberately one-sided; no claim is made here that the eta
carrier satisfies the required moment inequality. -/
theorem pairedEtaGeometricReflectionEven_allCritical_of_effectiveRankCeiling
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (hmoment :
      (spectralZetaZeroWindow T).card *
          frobSq (pairedEtaGeometricReflectionEvenCoordinateCarrier
            q T hT n) ≤
        rtrace (pairedEtaGeometricReflectionEvenCoordinateCarrier
          q T hT n) ^ 2) :
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card := by
  let B := pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n
  have hB := pairedEtaGeometricReflectionEvenCoordinateCarrier_posSemidef
    q T hT n
  have heffective := rtrace_sq_le_rank_mul_frobSq hB.isHermitian
  have hrank := pairedEtaGeometricReflectionEvenCoordinateCarrier_rank
    q hT n hK
  change B.rank = _ at hrank
  have hcard := spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper hT
  have hcardPos : 0 < (spectralZetaZeroWindow T).card :=
    Finset.card_pos.mpr hwindow
  have hrankPos : 0 < B.rank := by
    rw [hrank]
    omega
  have hBne : B ≠ 0 := by
    intro hzero
    rw [hzero] at hrankPos
    simp at hrankPos
  have htracePos : 0 < rtrace B :=
    rtrace_pos_of_posSemidef_of_ne_zero hB hBne
  have hfrobPos : 0 < frobSq B := by
    by_contra hf
    have hfrobNonpos : frobSq B ≤ 0 := not_lt.mp hf
    nlinarith [sq_pos_of_pos htracePos]
  have hscaled :
      ((spectralZetaZeroWindow T).card : ℝ) * frobSq B ≤
        (B.rank : ℝ) * frobSq B := by
    change ((spectralZetaZeroWindow T).card : ℝ) * frobSq B ≤
      rtrace B ^ 2 at hmoment
    exact hmoment.trans heffective
  have hcardLeRankReal :
      ((spectralZetaZeroWindow T).card : ℝ) ≤ B.rank :=
    le_of_mul_le_mul_right hscaled hfrobPos
  have hcardLeRank : (spectralZetaZeroWindow T).card ≤ B.rank := by
    exact_mod_cast hcardLeRankReal
  rw [hrank] at hcardLeRank
  omega

/-- Colour-resolved endpoint target for a finite window: the length-one and
length-two eta paths alone imply that every represented zero is critical. -/
theorem pairedEtaGeometricReflectionEven_allCritical_of_colouredEffectiveRankCeiling
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (hmoment :
      (spectralZetaZeroWindow T).card *
          (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
            q T n 2).re ≤
        (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
          q T n 1).re ^ 2) :
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card := by
  apply pairedEtaGeometricReflectionEven_allCritical_of_effectiveRankCeiling
    q hT n hwindow hK
  have htrace :
      rtrace (pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n) =
        (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
          q T n 1).re := by
    simpa using
      pairedEtaGeometricReflectionEvenCoordinateCarrier_rtrace_pow_eq_re_colouredClosedPathSum
        q hT n 1
  rw [pairedEtaGeometricReflectionEvenCoordinateCarrier_frobSq_eq_re_colouredClosedPathSum_two
    q hT n, htrace]
  exact hmoment

/-- A strict effective-rank estimate on the literal reflection-even
coordinate carrier is sufficient to beat the `13/18` critical-zero
proportion. -/
theorem pairedEtaGeometricReflectionEven_thirteen_eighteen_of_effectiveRank
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (hmoment :
      (31 : ℝ) * (spectralZetaZeroWindow T).card *
          frobSq (pairedEtaGeometricReflectionEvenCoordinateCarrier
            q T hT n) <
        36 * rtrace (pairedEtaGeometricReflectionEvenCoordinateCarrier
          q T hT n) ^ 2) :
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card := by
  apply pairedEtaGeometricReflectionEven_criticalFraction_gt_of_effectiveRank
    q hT n hwindow hK ((13 : ℝ) / 18) (by norm_num)
  nlinarith

/-- Fully colour-resolved two-moment target: an inequality involving only
length-one and length-two ordered paths through the on-line/off-line-real
eta carrier already forces a critical-zero proportion above `13/18`. -/
theorem pairedEtaGeometricReflectionEven_thirteen_eighteen_of_colouredTwoMoment
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef)
    (hmoment :
      (31 : ℝ) * (spectralZetaZeroWindow T).card *
          (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
            q T n 2).re <
        36 *
          (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
            q T n 1).re ^ 2) :
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card := by
  apply pairedEtaGeometricReflectionEven_thirteen_eighteen_of_effectiveRank
    q hT n hwindow hK
  have htrace :
      rtrace (pairedEtaGeometricReflectionEvenCoordinateCarrier q T hT n) =
        (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
          q T n 1).re := by
    simpa using
      pairedEtaGeometricReflectionEvenCoordinateCarrier_rtrace_pow_eq_re_colouredClosedPathSum
        q hT n 1
  rw [pairedEtaGeometricReflectionEvenCoordinateCarrier_frobSq_eq_re_colouredClosedPathSum_two
    q hT n, htrace]
  exact hmoment

/-- The pair of open colour-path premises and the zero-proportion conclusions
they are intended to certify. This definition asserts only the implications,
not either arithmetic premise. -/
def PairedEtaGeometricReflectionEvenColouredEffectiveRankTargets
    (q : ℕ) (T : ℝ) (n : ℕ) : Prop :=
    (((31 : ℝ) * (spectralZetaZeroWindow T).card *
          (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
            q T n 2).re <
        36 *
          (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
            q T n 1).re ^ 2) →
      (13 : ℝ) / 18 <
        (spectralCriticalZetaZeroWindow T).card /
          (spectralZetaZeroWindow T).card) ∧
    ((((spectralZetaZeroWindow T).card : ℝ) *
          (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
            q T n 2).re ≤
        (pairedEtaGeometricReflectionEvenCoordinateColouredClosedPathSum
          q T n 1).re ^ 2) →
      (spectralCriticalZetaZeroWindow T).card =
        (spectralZetaZeroWindow T).card)

/-- Terminal two-moment certificate interface.  It records, without
asserting either open premise, the exact colour-path inequalities sufficient
for the first `13/18` milestone and for the finite-window `18/18` endpoint. -/
theorem pairedEtaGeometricReflectionEvenColouredEffectiveRankCertificateInterface
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    PairedEtaGeometricReflectionEvenColouredEffectiveRankTargets q T n := by
  exact
    ⟨pairedEtaGeometricReflectionEven_thirteen_eighteen_of_colouredTwoMoment
      q hT n hwindow hK,
    pairedEtaGeometricReflectionEven_allCritical_of_colouredEffectiveRankCeiling
      q hT n hwindow hK⟩

/-- The positive-definiteness hypothesis in the two-moment interface is
already discharged by the literal eta features: one odd prime base makes both
certificate implications valid at every sufficiently late geometric block. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenColouredEffectiveRankCertificateInterface
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        PairedEtaGeometricReflectionEvenColouredEffectiveRankTargets q T n := by
  obtain ⟨q, hqPrime, hqOdd, hq, hpos⟩ :=
    exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hpos] with n hn
  exact
    pairedEtaGeometricReflectionEvenColouredEffectiveRankCertificateInterface
      q hT n hwindow hn.1

end

end RiemannGaussian
