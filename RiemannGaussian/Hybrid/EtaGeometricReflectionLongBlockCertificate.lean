import RiemannGaussian.Hybrid.EtaGeometricReflectionEvenStrictDecorrelation
import RiemannGaussian.Hybrid.EtaGeometricReflectionSumFullReserveLowerBound

/-!
# Arbitrary-length geometric eta certificate blocks

The original literal reflection-even certificate used exactly as many
geometric coordinates as zeros in the represented finite window. That square
block proves feature separation, but it prevents the quantitative reserve
from being strengthened by retaining additional later coordinates.

This module removes that restriction without adding an assumption. Restriction
to the first square sub-block proves that every longer consecutive block
inherits linear independence. A generic positive frame operator then reruns
the rank--trace argument for any finite coordinate family, with exact trace
mass and frame-potential identities. Consequently the existing explicit
upper-sector reserve floor feeds the `13/18` and finite-window `18/18`
certificate implications at every block length `M` at least the zero-window
cardinality.

The two quantitative floor inequalities remain open arithmetic antecedents.
The advance is that their left and right sides can now be studied as functions
of an unrestricted block length, while all rank and separation obligations
remain discharged in Lean.
-/

open Complex Matrix Finset Filter
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Restrict a two-colour coordinate vector to its first `K` coordinates. -/
def pairedEtaFinPairRestrictionLinearMap {K M : ℕ} (hKM : K ≤ M) :
    (Fin M × Fin 2 → ℂ) →ₗ[ℂ] (Fin K × Fin 2 → ℂ) where
  toFun v j := v (Fin.castLE hKM j.1, j.2)
  map_add' v w := by
    funext j
    rfl
  map_smul' c v := by
    funext j
    rfl

/-- Restricting a long consecutive geometric block recovers its square
initial block exactly. -/
theorem pairedEtaFinPairRestrictionLinearMap_geometricFrameVector
    {K M : ℕ} (hKM : K ≤ M) (q n : ℕ) (T : ℝ)
    (a : PairedEtaReflectionEvenFrameIndex T) :
    pairedEtaFinPairRestrictionLinearMap hKM
        (pairedEtaReflectionEvenFrameVector
          (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T a) =
      pairedEtaReflectionEvenFrameVector
        (fun j : Fin K ↦ pairedEtaGeometricHyperbolicCutoff q n j) T a := by
  funext j
  rcases j with ⟨j, c⟩
  cases a with
  | inl rho => rfl
  | inr rho => rfl

/-- Linear independence of the checked square geometric eta block persists
after appending any number of later geometric coordinates. -/
theorem linearIndependent_pairedEtaGeometricReflectionEvenFrameVector_longBlock
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n M : ℕ)
    (hKM : (spectralZetaZeroWindow T).card ≤ M)
    (hK : (pairedEtaGeometricMultiplicityWeightedZeroGram q
      (spectralZetaZeroWindow T) n).PosDef) :
    LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameVector
        (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T) := by
  let K := (spectralZetaZeroWindow T).card
  let restrict := pairedEtaFinPairRestrictionLinearMap hKM
  let v := pairedEtaReflectionEvenFrameVector
    (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T
  have hshort : LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameVector
        (fun j : Fin K ↦ pairedEtaGeometricHyperbolicCutoff q n j) T) := by
    simpa only [K] using
      linearIndependent_pairedEtaGeometricReflectionEvenFrameVector
        q hT n hK
  have heq : (⇑restrict ∘ v) =
      pairedEtaReflectionEvenFrameVector
        (fun j : Fin K ↦ pairedEtaGeometricHyperbolicCutoff q n j) T := by
    funext a
    exact pairedEtaFinPairRestrictionLinearMap_geometricFrameVector
      hKM q n T a
  have hcomp : LinearIndependent ℂ (⇑restrict ∘ v) := by
    rw [heq]
    exact hshort
  exact LinearIndependent.of_comp restrict hcomp

/-- Positive frame operator on an arbitrary retained coordinate family. -/
def pairedEtaReflectionEvenFrameOperator
    {d : Type*} (cutoff : d → ℕ) (T : ℝ) :
    Matrix (d × Fin 2) (d × Fin 2) ℂ :=
  pairedEtaReflectionEvenFrameSynthesisMatrix cutoff T *
    (pairedEtaReflectionEvenFrameSynthesisMatrix cutoff T)ᴴ

/-- Every arbitrary-coordinate reflection-even frame operator is positive
semidefinite. -/
theorem pairedEtaReflectionEvenFrameOperator_posSemidef
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    (pairedEtaReflectionEvenFrameOperator cutoff T).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Linear independence of the literal atoms gives the arbitrary-coordinate
frame operator exactly one rank direction per atom. -/
theorem pairedEtaReflectionEvenFrameOperator_rank_of_linearIndependent
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ)
    (hLI : LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameVector cutoff T)) :
    (pairedEtaReflectionEvenFrameOperator cutoff T).rank =
      Fintype.card (PairedEtaReflectionEvenFrameIndex T) := by
  let v := pairedEtaReflectionEvenFrameVector cutoff T
  let w : PairedEtaReflectionEvenFrameIndex T → ℂˣ := fun a ↦
    Units.mk0 (pairedEtaReflectionEvenFrameSqrtWeight T a)
      (pairedEtaReflectionEvenFrameSqrtWeight_ne_zero T a)
  have hscaled : LinearIndependent ℂ (w • v) :=
    (LinearIndependent.units_smul_iff v w).2 hLI
  have hcols :
      (pairedEtaReflectionEvenFrameSynthesisMatrix cutoff T).col =
        w • v := by
    funext a j
    rfl
  have hcolsLI : LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameSynthesisMatrix cutoff T).col := by
    rw [hcols]
    exact hscaled
  have hrank :
      (pairedEtaReflectionEvenFrameSynthesisMatrix cutoff T).rank =
        Fintype.card (PairedEtaReflectionEvenFrameIndex T) := by
    rw [linearIndependent_iff_card_eq_finrank_span] at hcolsLI
    change Fintype.card (PairedEtaReflectionEvenFrameIndex T) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range
        (pairedEtaReflectionEvenFrameSynthesisMatrix cutoff T).col)) at hcolsLI
    rw [← Matrix.rank_eq_finrank_span_cols] at hcolsLI
    exact hcolsLI.symm
  unfold pairedEtaReflectionEvenFrameOperator
  rw [Matrix.rank_self_mul_conjTranspose]
  exact hrank

/-- The arbitrary-coordinate frame operator's Frobenius square is exactly the
literal phase-preserving frame potential. -/
theorem pairedEtaReflectionEvenFrameOperator_frobSq_eq_framePotential
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianRankTrace.frobSq
        (pairedEtaReflectionEvenFrameOperator cutoff T) =
      pairedEtaReflectionEvenFramePotential cutoff T := by
  unfold pairedEtaReflectionEvenFrameOperator
  rw [pairedEtaReflectionEvenFrameSynthesisMatrix_self_mul_conjTranspose]
  change HermitianInertia.frobSq _ = _
  unfold pairedEtaReflectionEvenFramePotential
  simpa using
    (HermitianInertia.frobSq_finsetSum_real_smul_vecMulVec_eq_pairCorrelation
      (Finset.univ : Finset (PairedEtaReflectionEvenFrameIndex T))
      (pairedEtaReflectionEvenFrameWeight T)
      (pairedEtaReflectionEvenFrameVector cutoff T))

/-- The arbitrary-coordinate frame operator's real trace is exactly the
weighted literal eta frame mass. -/
theorem pairedEtaReflectionEvenFrameOperator_rtrace_eq_frameTraceMass
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianRankTrace.rtrace
        (pairedEtaReflectionEvenFrameOperator cutoff T) =
      pairedEtaReflectionEvenFrameTraceMass cutoff T := by
  unfold pairedEtaReflectionEvenFrameOperator
  rw [pairedEtaReflectionEvenFrameSynthesisMatrix_self_mul_conjTranspose]
  unfold HermitianRankTrace.rtrace pairedEtaReflectionEvenFrameTraceMass
  simp only [Matrix.trace_sum, map_sum, Matrix.trace_smul,
    Matrix.trace_vecMulVec]
  apply Finset.sum_congr rfl
  intro a _ha
  have hstar := star_pairedEtaReflectionEvenFrameVector cutoff T a
  have hdot :
      pairedEtaReflectionEvenFrameVector cutoff T a ⬝ᵥ
          pairedEtaReflectionEvenFrameVector cutoff T a =
        ((∑ j, ‖pairedEtaReflectionEvenFrameVector cutoff T a j‖ ^ 2 : ℝ) : ℂ) := by
    unfold dotProduct
    push_cast
    apply Finset.sum_congr rfl
    intro j _hj
    have hj := congrFun hstar j
    simp only [Pi.star_apply, RCLike.star_def] at hj
    calc
      pairedEtaReflectionEvenFrameVector cutoff T a j *
          pairedEtaReflectionEvenFrameVector cutoff T a j =
        starRingEnd ℂ (pairedEtaReflectionEvenFrameVector cutoff T a j) *
          pairedEtaReflectionEvenFrameVector cutoff T a j := by rw [hj]
      _ = (‖pairedEtaReflectionEvenFrameVector cutoff T a j‖ : ℂ) ^ 2 := by
        rw [RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal]
  rw [hdot]
  change (((pairedEtaReflectionEvenFrameWeight T a : ℂ) *
    ((∑ j, ‖pairedEtaReflectionEvenFrameVector cutoff T a j‖ ^ 2 : ℝ) : ℂ)).re) = _
  norm_cast

/-- An effective-rank inequality for any linearly independent literal eta
frame forces the corresponding lower bound for the represented critical-zero
fraction. The coordinate family is arbitrary. -/
theorem pairedEtaReflectionEven_criticalFraction_gt_of_framePotential
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hLI : LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameVector cutoff T))
    (target : ℝ) (htarget : -1 ≤ target)
    (hmoment :
      (1 + target) * (spectralZetaZeroWindow T).card *
          pairedEtaReflectionEvenFramePotential cutoff T <
        2 * pairedEtaReflectionEvenFrameTraceMass cutoff T ^ 2) :
    target < (spectralCriticalZetaZeroWindow T).card /
      (spectralZetaZeroWindow T).card := by
  let B := pairedEtaReflectionEvenFrameOperator cutoff T
  have hB := pairedEtaReflectionEvenFrameOperator_posSemidef cutoff T
  have heffective := HermitianRankTrace.rtrace_sq_le_rank_mul_frobSq
    hB.isHermitian
  have hfrob : 0 ≤ HermitianRankTrace.frobSq B :=
    HermitianInertia.frobSq_nonneg B
  have hmomentB :
      (1 + target) * (spectralZetaZeroWindow T).card *
          HermitianRankTrace.frobSq B <
        2 * HermitianRankTrace.rtrace B ^ 2 := by
    rw [pairedEtaReflectionEvenFrameOperator_frobSq_eq_framePotential,
      pairedEtaReflectionEvenFrameOperator_rtrace_eq_frameTraceMass]
    exact hmoment
  have hleftNonneg :
      0 ≤ (1 + target) * (spectralZetaZeroWindow T).card *
        HermitianRankTrace.frobSq B := by
    have : 0 ≤ 1 + target := by linarith
    positivity
  have htraceSq : 0 < HermitianRankTrace.rtrace B ^ 2 := by
    nlinarith
  have hfrobPos : 0 < HermitianRankTrace.frobSq B := by
    by_contra hf
    have hfrobZero : HermitianRankTrace.frobSq B = 0 :=
      le_antisymm (not_lt.mp hf) hfrob
    rw [hfrobZero] at heffective
    nlinarith
  have hrankTarget :
      (1 + target) * (spectralZetaZeroWindow T).card <
        2 * B.rank := by
    have hscaled :
        ((1 + target) * (spectralZetaZeroWindow T).card) *
            HermitianRankTrace.frobSq B <
          (2 * B.rank) * HermitianRankTrace.frobSq B := by
      nlinarith
    exact lt_of_mul_lt_mul_right hscaled hfrobPos.le
  have hrank :=
    pairedEtaReflectionEvenFrameOperator_rank_of_linearIndependent
      cutoff T hLI
  change B.rank = _ at hrank
  rw [hrank, card_pairedEtaReflectionEvenFrameIndex] at hrankTarget
  push_cast at hrankTarget
  have hcard : ((spectralZetaZeroWindow T).card : ℝ) =
      (spectralCriticalZetaZeroWindow T).card +
        2 * (spectralUpperZetaZeroWindow T).card := by
    exact_mod_cast spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper hT
  have hcardPos : 0 < ((spectralZetaZeroWindow T).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hwindow
  rw [lt_div_iff₀ hcardPos]
  nlinarith

/-- The arbitrary-coordinate frame-potential inequality sufficient to beat
`13/18`. -/
theorem pairedEtaReflectionEven_thirteen_eighteen_of_framePotential
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hLI : LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameVector cutoff T))
    (hmoment :
      (31 : ℝ) * (spectralZetaZeroWindow T).card *
          pairedEtaReflectionEvenFramePotential cutoff T <
        36 * pairedEtaReflectionEvenFrameTraceMass cutoff T ^ 2) :
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card := by
  apply pairedEtaReflectionEven_criticalFraction_gt_of_framePotential
    cutoff hT hwindow hLI ((13 : ℝ) / 18) (by norm_num)
  nlinarith

/-- The arbitrary-coordinate endpoint frame-potential ceiling forces every
represented zero to be critical. -/
theorem pairedEtaReflectionEven_allCritical_of_framePotentialCeiling
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ}
    (hT : 0 ≤ T) (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hLI : LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameVector cutoff T))
    (hmoment :
      (spectralZetaZeroWindow T).card *
          pairedEtaReflectionEvenFramePotential cutoff T ≤
        pairedEtaReflectionEvenFrameTraceMass cutoff T ^ 2) :
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card := by
  let B := pairedEtaReflectionEvenFrameOperator cutoff T
  have hB := pairedEtaReflectionEvenFrameOperator_posSemidef cutoff T
  have heffective := HermitianRankTrace.rtrace_sq_le_rank_mul_frobSq
    hB.isHermitian
  have hrank :=
    pairedEtaReflectionEvenFrameOperator_rank_of_linearIndependent
      cutoff T hLI
  change B.rank = _ at hrank
  have hcard := spectralZetaZeroWindow_card_eq_critical_add_two_mul_upper hT
  have hcardPos : 0 < (spectralZetaZeroWindow T).card :=
    Finset.card_pos.mpr hwindow
  have hrankPos : 0 < B.rank := by
    rw [hrank, card_pairedEtaReflectionEvenFrameIndex]
    omega
  have hBne : B ≠ 0 := by
    intro hzero
    rw [hzero] at hrankPos
    simp at hrankPos
  have htracePos : 0 < HermitianRankTrace.rtrace B :=
    HermitianRankTrace.rtrace_pos_of_posSemidef_of_ne_zero hB hBne
  have hfrobPos : 0 < HermitianRankTrace.frobSq B := by
    by_contra hf
    have hfrobNonpos : HermitianRankTrace.frobSq B ≤ 0 := not_lt.mp hf
    nlinarith [sq_pos_of_pos htracePos]
  have hmomentB :
      ((spectralZetaZeroWindow T).card : ℝ) *
          HermitianRankTrace.frobSq B ≤
        HermitianRankTrace.rtrace B ^ 2 := by
    rw [pairedEtaReflectionEvenFrameOperator_frobSq_eq_framePotential,
      pairedEtaReflectionEvenFrameOperator_rtrace_eq_frameTraceMass]
    exact hmoment
  have hscaled :
      ((spectralZetaZeroWindow T).card : ℝ) *
          HermitianRankTrace.frobSq B ≤
        (B.rank : ℝ) * HermitianRankTrace.frobSq B :=
    hmomentB.trans heffective
  have hcardLeRankReal :
      ((spectralZetaZeroWindow T).card : ℝ) ≤ B.rank :=
    le_of_mul_le_mul_right hscaled hfrobPos
  have hcardLeRank : (spectralZetaZeroWindow T).card ≤ B.rank := by
    exact_mod_cast hcardLeRankReal
  rw [hrank, card_pairedEtaReflectionEvenFrameIndex] at hcardLeRank
  omega

/-- The two explicit upper-reserve-floor certificate targets evaluated on an
arbitrary-length consecutive geometric coordinate block. -/
def PairedEtaGeometricReflectionEvenLongBlockUpperReserveGapFloorTargets
    (q : ℕ) (T : ℝ) (n M : ℕ) (ε : ℝ) : Prop :=
  ((((31 : ℝ) * (spectralZetaZeroWindow T).card - 36) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T <
      36 * pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
        q T n M ε) →
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card) ∧
  (((((spectralZetaZeroWindow T).card : ℝ) - 1) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T ≤
      pairedEtaGeometricUpperWindowNonnegativeReserveGapLower
        q T n M ε) →
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card)

/-- Once the long frame is separated and its explicit floor lies below the
full reserve, the long-block floor inequalities rigorously imply the `13/18`
and `18/18` conclusions. -/
theorem pairedEtaGeometricReflectionEvenLongBlockUpperReserveGapFloorCertificateInterface
    (q : ℕ) {T : ℝ} (hT : 0 ≤ T) (n M : ℕ)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (hLI : LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameVector
        (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T))
    (ε : ℝ)
    (hfloor :
      pairedEtaGeometricUpperWindowNonnegativeReserveGapLower q T n M ε ≤
        pairedEtaReflectionEvenFrameDecorrelationReserve
          (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T) :
    PairedEtaGeometricReflectionEvenLongBlockUpperReserveGapFloorTargets
      q T n M ε := by
  unfold PairedEtaGeometricReflectionEvenLongBlockUpperReserveGapFloorTargets
  let cutoff : Fin M → ℕ := fun j ↦
    pairedEtaGeometricHyperbolicCutoff q n j
  constructor
  · intro hthirteen
    apply pairedEtaReflectionEven_thirteen_eighteen_of_framePotential
      cutoff hT hwindow hLI
    apply (pairedEtaReflectionEvenFrame_thirteenEighteenMoment_iff_reserve
      cutoff T (spectralZetaZeroWindow T).card).2
    exact hthirteen.trans_le
      (mul_le_mul_of_nonneg_left hfloor (by norm_num))
  · intro hendpoint
    apply pairedEtaReflectionEven_allCritical_of_framePotentialCeiling
      cutoff hT hwindow hLI
    apply (pairedEtaReflectionEvenFrame_endpointMoment_iff_reserve
      cutoff T (spectralZetaZeroWindow T).card).2
    exact hendpoint.trans hfloor

/-- For a separated odd-base family, every sufficiently late arbitrary block
that contains the checked square sub-block validates both long-block floor
certificate implications. -/
theorem eventually_pairedEtaGeometricReflectionEvenLongBlockUpperReserveGapFloorCertificateInterface
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (hT : 0 ≤ T) (hwindow : (spectralZetaZeroWindow T).Nonempty)
    {M : ℕ} (hKM : (spectralZetaZeroWindow T).card ≤ M)
    (hM : 1 < M) {ε : ℝ} (hε : 0 < ε)
    (hK : ∀ᶠ n in atTop,
      (pairedEtaGeometricMultiplicityWeightedZeroGram q
        (spectralZetaZeroWindow T) n).PosDef) :
    ∀ᶠ n in atTop,
      PairedEtaGeometricReflectionEvenLongBlockUpperReserveGapFloorTargets
        q T n M ε := by
  have hfloor :=
    eventually_pairedEtaGeometricUpperWindowNonnegativeReserveGapLower_le_fullDecorrelationReserve
      hqOdd hq T hM hε
  filter_upwards [hK, hfloor] with n hKn hfloorN
  have hLI :=
    linearIndependent_pairedEtaGeometricReflectionEvenFrameVector_longBlock
      q hT n M hKM hKn
  exact
    pairedEtaGeometricReflectionEvenLongBlockUpperReserveGapFloorCertificateInterface
      q hT n M hwindow hLI ε hfloorN

/-- For every eligible finite zero window and every sufficiently long
coordinate block, there is one odd prime base for which the literal long-block
floor certificate interface is valid eventually. The floor inequalities
remain open arithmetic antecedents. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenLongBlockUpperReserveGapFloorCertificateInterface
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    {M : ℕ} (hKM : (spectralZetaZeroWindow T).card ≤ M)
    (hM : 1 < M) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        PairedEtaGeometricReflectionEvenLongBlockUpperReserveGapFloorTargets
          q T n M ε := by
  obtain ⟨q, hqPrime, hqOdd, hq, hpos⟩ :=
    exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  exact
    eventually_pairedEtaGeometricReflectionEvenLongBlockUpperReserveGapFloorCertificateInterface
      hqOdd hq hT hwindow hKM hM hε (hpos.mono fun _ hn ↦ hn.1)

end

end RiemannGaussian
