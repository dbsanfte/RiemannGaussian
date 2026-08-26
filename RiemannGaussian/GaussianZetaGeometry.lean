import Mathlib.Topology.Algebra.Module.Cardinality
import RiemannGaussian.GaussianZetaBridge

/-!
# Geometry of zeta Gaussian packets

This file turns the exact zeta symmetries from `GaussianZetaBridge` into the
packet geometry needed by the infinite Gaussian detector.  Critical-line
reflection `ρ ↦ 1 - conj ρ` becomes conjugation in the rotated spectral
coordinate, so its two zeros have one common Gaussian envelope.

The file selects an off-axis packet whose envelope is strictly maximal at a
real observation center.  The distinct zero set is countable and two
genuinely distinct packets can tie at at most one center, so all packet-tie
centers form a countable exceptional set.  Absolute summability then makes a
maximum attainable.  The final theorem proves global translated-Gaussian
zero-divisor separation and derives the translated and symmetric RH
equivalences, conditional only on the stated explicit-formula `HasSum`
representations.
-/

namespace RiemannGaussian

noncomputable section

open Filter Topology

/-- The distinct nontrivial zeta-zero set is countable.  This follows from
Mathlib's discreteness theorem and second countability of `ℂ`. -/
theorem nontrivialZetaZeroSet_countable :
    nontrivialZetaZeroSet.Countable := by
  exact (HereditarilyLindelofSpace.isLindelof
    nontrivialZetaZeroSet).countable_of_isDiscrete
      (isDiscrete_riemannZetaZeros.mono
        nontrivialZetaZeroSet_subset_riemannZetaZeros)

noncomputable instance : Countable NontrivialZetaZero :=
  nontrivialZetaZeroSet_countable.to_subtype

namespace NontrivialZetaZero

/-- Every nontrivial zero lies strictly to the left of `Re s = 1`. -/
theorem re_lt_one (ρ : NontrivialZetaZero) : ρ.1.re < 1 := by
  exact lt_of_not_ge fun h =>
    riemannZeta_ne_zero_of_one_le_re h ρ.2.1

/-- Every nontrivial zero lies strictly to the right of `Re s = 0`.  This is
the preceding zero-free half-plane transported through the functional
equation. -/
theorem zero_lt_re (ρ : NontrivialZetaZero) : 0 < ρ.1.re := by
  have hpartner := re_lt_one (functionalPartner ρ)
  simpa using hpartner

/-- Hence the imaginary part of the rotated spectral coordinate has absolute
value strictly below `1/2`. -/
theorem abs_spectralCoordinate_im_lt_half (ρ : NontrivialZetaZero) :
    |(zetaSpectralCoordinate ρ.1).im| < 1 / 2 := by
  rw [zetaSpectralCoordinate_im, abs_lt]
  constructor <;> linarith [zero_lt_re ρ, re_lt_one ρ]

end NontrivialZetaZero

/-- The affine rotation from zeta coordinates to spectral coordinates is
injective. -/
theorem zetaSpectralCoordinate_injective :
    Function.Injective zetaSpectralCoordinate := by
  intro s w h
  apply Complex.ext
  · have him := congrArg Complex.im h
    simpa using him
  · have hre := congrArg Complex.re h
    simpa using hre

/-- Two zeros represent the same critical-reflection packet when they are
equal or exchanged by `ρ ↦ 1 - conj ρ`. -/
def SameZetaConjugatePacket
    (ρ σ : NontrivialZetaZero) : Prop :=
  σ = ρ ∨ σ = NontrivialZetaZero.conjugatePartner ρ

@[refl]
theorem SameZetaConjugatePacket.refl (ρ : NontrivialZetaZero) :
    SameZetaConjugatePacket ρ ρ :=
  Or.inl rfl

theorem SameZetaConjugatePacket.symm
    {ρ σ : NontrivialZetaZero}
    (h : SameZetaConjugatePacket ρ σ) :
    SameZetaConjugatePacket σ ρ := by
  rcases h with rfl | rfl
  · exact .refl _
  · exact Or.inr (NontrivialZetaZero.conjugatePartner_conjugatePartner ρ).symm

@[simp]
theorem sameZetaConjugatePacket_conjugatePartner_left
    (ρ σ : NontrivialZetaZero) :
    SameZetaConjugatePacket
        (NontrivialZetaZero.conjugatePartner ρ) σ ↔
      SameZetaConjugatePacket ρ σ := by
  simp [SameZetaConjugatePacket, or_comm]

theorem NontrivialZetaZero.ne_conjugatePartner_of_spectral_im_ne_zero
    (ρ : NontrivialZetaZero)
    (hoffAxis : (zetaSpectralCoordinate ρ.1).im ≠ 0) :
    ρ ≠ NontrivialZetaZero.conjugatePartner ρ := by
  intro heq
  have hspectral := congrArg
    (fun σ : NontrivialZetaZero => zetaSpectralCoordinate σ.1) heq
  have him := congrArg Complex.im hspectral
  simp only [NontrivialZetaZero.spectralCoordinate_conjugatePartner,
    Complex.conj_im] at him
  apply hoffAxis
  linarith

/-- Envelope exponent attached to the critical-reflection packet containing
`ρ`, at a real observation center `t`. -/
def zetaPacketEnvelopeExponent
    (t : ℝ) (ρ : NontrivialZetaZero) : ℝ :=
  offAxisEnvelopeExponent t
    (zetaSpectralCoordinate ρ.1).re
    (zetaSpectralCoordinate ρ.1).im

@[simp]
theorem zetaPacketEnvelopeExponent_conjugatePartner
    (t : ℝ) (ρ : NontrivialZetaZero) :
    zetaPacketEnvelopeExponent t
        (NontrivialZetaZero.conjugatePartner ρ) =
      zetaPacketEnvelopeExponent t ρ := by
  simp [zetaPacketEnvelopeExponent, offAxisEnvelopeExponent]
  ring

/-- Equal ordinate and equal squared off-axis height characterize the same
critical-reflection packet. -/
theorem sameZetaConjugatePacket_of_re_eq_of_im_sq_eq
    {ρ σ : NontrivialZetaZero}
    (hre : (zetaSpectralCoordinate σ.1).re =
      (zetaSpectralCoordinate ρ.1).re)
    (him : (zetaSpectralCoordinate σ.1).im ^ 2 =
      (zetaSpectralCoordinate ρ.1).im ^ 2) :
    SameZetaConjugatePacket ρ σ := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with him | him
  · left
    apply Subtype.ext
    apply zetaSpectralCoordinate_injective
    apply Complex.ext
    · exact hre
    · exact him
  · right
    apply Subtype.ext
    apply zetaSpectralCoordinate_injective
    rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
    apply Complex.ext
    · simpa using hre
    · simpa using him

/-- Centers at which two specified packet envelopes tie. -/
def zetaPacketTieCenters
    (ρ σ : NontrivialZetaZero) : Set ℝ :=
  {t | zetaPacketEnvelopeExponent t ρ =
    zetaPacketEnvelopeExponent t σ}

/-- Two genuinely distinct packets can tie at no more than one observation
center. -/
theorem zetaPacketTieCenters_subsingleton
    {ρ σ : NontrivialZetaZero}
    (hdifferent : ¬ SameZetaConjugatePacket ρ σ) :
    (zetaPacketTieCenters ρ σ).Subsingleton := by
  intro t ht u hu
  by_cases hre : (zetaSpectralCoordinate σ.1).re =
      (zetaSpectralCoordinate ρ.1).re
  · exfalso
    apply hdifferent
    apply sameZetaConjugatePacket_of_re_eq_of_im_sq_eq hre
    have ht' := ht
    change zetaPacketEnvelopeExponent t ρ =
      zetaPacketEnvelopeExponent t σ at ht'
    unfold zetaPacketEnvelopeExponent offAxisEnvelopeExponent at ht'
    rw [hre] at ht'
    nlinarith
  · change zetaPacketEnvelopeExponent t ρ =
      zetaPacketEnvelopeExponent t σ at ht
    change zetaPacketEnvelopeExponent u ρ =
      zetaPacketEnvelopeExponent u σ at hu
    unfold zetaPacketEnvelopeExponent
      offAxisEnvelopeExponent at ht hu
    have hproduct :
        ((zetaSpectralCoordinate ρ.1).re -
          (zetaSpectralCoordinate σ.1).re) * (t - u) = 0 := by
      linear_combination (ht - hu) / 2
    rcases mul_eq_zero.mp hproduct with hordinate | htu
    · exfalso
      apply hre
      linarith
    · linarith

/-- The countable exceptional set containing every center at which two
genuinely distinct zeta packets have equal Gaussian envelope. -/
noncomputable def zetaPacketTieCenterSet : Set ℝ := by
  classical
  exact ⋃ ρ : NontrivialZetaZero, ⋃ σ : NontrivialZetaZero,
    if SameZetaConjugatePacket ρ σ then ∅
    else zetaPacketTieCenters ρ σ

theorem zetaPacketTieCenterSet_countable :
    zetaPacketTieCenterSet.Countable := by
  classical
  unfold zetaPacketTieCenterSet
  apply Set.countable_iUnion
  intro ρ
  apply Set.countable_iUnion
  intro σ
  split_ifs with hsame
  · exact Set.countable_empty
  · exact (zetaPacketTieCenters_subsingleton hsame).countable

/-- Outside the exceptional set, equality of envelopes forces equality of
critical-reflection packets. -/
theorem sameZetaConjugatePacket_of_envelope_eq_of_not_mem_tieCenterSet
    {t : ℝ} (ht : t ∉ zetaPacketTieCenterSet)
    {ρ σ : NontrivialZetaZero}
    (henvelope : zetaPacketEnvelopeExponent t ρ =
      zetaPacketEnvelopeExponent t σ) :
    SameZetaConjugatePacket ρ σ := by
  classical
  by_contra hdifferent
  apply ht
  unfold zetaPacketTieCenterSet
  apply Set.mem_iUnion_of_mem ρ
  apply Set.mem_iUnion_of_mem σ
  simpa [hdifferent, zetaPacketTieCenters] using henvelope

/-- The set of all packet ordinates.  Avoiding it guarantees a nonzero phase
slope for every off-axis packet. -/
def zetaPacketOrdinateSet : Set ℝ :=
  Set.range fun ρ : NontrivialZetaZero =>
    (zetaSpectralCoordinate ρ.1).re

theorem zetaPacketOrdinateSet_countable :
    zetaPacketOrdinateSet.Countable := by
  exact Set.countable_range _

/-- Centers excluded either because two distinct packets tie or because the
center equals a packet ordinate. -/
def zetaPacketExceptionalCenterSet : Set ℝ :=
  zetaPacketTieCenterSet ∪ zetaPacketOrdinateSet

theorem zetaPacketExceptionalCenterSet_countable :
    zetaPacketExceptionalCenterSet.Countable :=
  zetaPacketTieCenterSet_countable.union
    zetaPacketOrdinateSet_countable

/-- Every off-axis packet has an observation center where its own envelope is
positive, no two distinct packets tie, and every packet has nonzero phase
slope.  Countability makes the good centers dense. -/
theorem exists_goodCenter_for_offAxisZetaPacket
    (ρ : NontrivialZetaZero)
    (hoffAxis : (zetaSpectralCoordinate ρ.1).im ≠ 0) :
    ∃ t : ℝ,
      0 < zetaPacketEnvelopeExponent t ρ ∧
      t ∉ zetaPacketTieCenterSet ∧
      ∀ σ : NontrivialZetaZero,
        t ≠ (zetaSpectralCoordinate σ.1).re := by
  let γ := (zetaSpectralCoordinate ρ.1).re
  let a := (zetaSpectralCoordinate ρ.1).im
  have haAbs : 0 < |a| := abs_pos.mpr hoffAxis
  have hopen : IsOpen (Set.Ioo (γ - |a|) (γ + |a|)) := isOpen_Ioo
  have hnonempty : (Set.Ioo (γ - |a|) (γ + |a|)).Nonempty := by
    rw [Set.nonempty_Ioo]
    linarith
  obtain ⟨t, htexceptional, htinterval⟩ :=
    (zetaPacketExceptionalCenterSet_countable.dense_compl ℝ).exists_mem_open
      hopen hnonempty
  have htTie : t ∉ zetaPacketTieCenterSet := by
    exact fun ht => htexceptional (Or.inl ht)
  have htOrdinate : t ∉ zetaPacketOrdinateSet := by
    exact fun ht => htexceptional (Or.inr ht)
  have habs : |γ - t| < |a| := by
    rw [abs_lt]
    constructor <;> linarith [htinterval.1, htinterval.2]
  have hsquare : (γ - t) ^ 2 < a ^ 2 := by
    rw [sq_lt_sq]
    simpa only [abs_abs] using habs
  refine ⟨t, ?_, htTie, ?_⟩
  · unfold zetaPacketEnvelopeExponent offAxisEnvelopeExponent γ a at *
    nlinarith
  · intro σ ht
    apply htOrdinate
    exact ⟨σ, ht.symm⟩

/-- Absolute convergence plus a tie-free positive center selects a globally
maximal off-axis packet, unique modulo critical-line reflection. -/
theorem exists_strictlyMaximalOffAxisZetaPacket_of_representation
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum
      analyticZetaZeroMultiplicity Q)
    (hoffAxis : ∃ ρ : NontrivialZetaZero,
      (zetaSpectralCoordinate ρ.1).im ≠ 0) :
    ∃ (t : ℝ) (ρ : NontrivialZetaZero),
      (zetaSpectralCoordinate ρ.1).im ≠ 0 ∧
      t ≠ (zetaSpectralCoordinate ρ.1).re ∧
      (∀ σ : NontrivialZetaZero,
        zetaPacketEnvelopeExponent t σ ≤
          zetaPacketEnvelopeExponent t ρ) ∧
      (∀ σ : NontrivialZetaZero,
        ¬ SameZetaConjugatePacket ρ σ →
          zetaPacketEnvelopeExponent t σ <
            zetaPacketEnvelopeExponent t ρ) := by
  classical
  obtain ⟨ρ₀, hρ₀offAxis⟩ := hoffAxis
  obtain ⟨t, hρ₀positive, htTie, htOrdinate⟩ :=
    exists_goodCenter_for_offAxisZetaPacket ρ₀ hρ₀offAxis
  let envelope : NontrivialZetaZeroOccurrence
      analyticZetaZeroMultiplicity → ℝ := fun occurrence =>
    Real.exp (zetaPacketEnvelopeExponent t occurrence.1)
  have henvelopeSummable : Summable envelope := by
    have h := summable_zetaGaussianZeroEnvelope_of_representation
      analyticZetaZeroMultiplicity Q hRep 1 t zero_lt_one
    simpa only [envelope, zetaPacketEnvelopeExponent,
      offAxisEnvelopeExponent, one_mul] using h
  have heventuallySmall : ∀ᶠ occurrence in
      (cofinite : Filter
        (NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity)),
      envelope occurrence < 1 :=
    henvelopeSummable.tendsto_cofinite_zero.eventually_lt_const zero_lt_one
  let high : Set (NontrivialZetaZeroOccurrence
      analyticZetaZeroMultiplicity) :=
    {occurrence | 1 ≤ envelope occurrence}
  have hhighFinite : high.Finite := by
    have hfinite := Filter.mem_cofinite.mp heventuallySmall
    simpa only [high, Set.compl_ofPred, not_lt] using hfinite
  let occurrence₀ : NontrivialZetaZeroOccurrence
      analyticZetaZeroMultiplicity :=
    ⟨ρ₀, ⟨0, analyticZetaZeroMultiplicity_positive ρ₀⟩⟩
  have hoccurrence₀High : occurrence₀ ∈ high := by
    change 1 ≤ Real.exp (zetaPacketEnvelopeExponent t ρ₀)
    exact (Real.one_lt_exp_iff.mpr hρ₀positive).le
  have hhighNonempty : hhighFinite.toFinset.Nonempty := by
    exact ⟨occurrence₀, by simpa using hoccurrence₀High⟩
  obtain ⟨occurrence, hoccurrenceHigh, hmaxHigh⟩ :=
    Finset.exists_max_image hhighFinite.toFinset
      (fun occurrence => zetaPacketEnvelopeExponent t occurrence.1)
      hhighNonempty
  let ρ := occurrence.1
  have hρ₀le : zetaPacketEnvelopeExponent t ρ₀ ≤
      zetaPacketEnvelopeExponent t ρ := by
    apply hmaxHigh occurrence₀
    simpa using hoccurrence₀High
  have hρpositive : 0 < zetaPacketEnvelopeExponent t ρ :=
    hρ₀positive.trans_le hρ₀le
  have hglobalMax (σ : NontrivialZetaZero) :
      zetaPacketEnvelopeExponent t σ ≤
        zetaPacketEnvelopeExponent t ρ := by
    let σoccurrence : NontrivialZetaZeroOccurrence
        analyticZetaZeroMultiplicity :=
      ⟨σ, ⟨0, analyticZetaZeroMultiplicity_positive σ⟩⟩
    by_cases hσHigh : σoccurrence ∈ high
    · apply hmaxHigh σoccurrence
      simpa using hσHigh
    · have hσexp : Real.exp (zetaPacketEnvelopeExponent t σ) < 1 := by
        change ¬1 ≤ envelope σoccurrence at hσHigh
        exact lt_of_not_ge hσHigh
      have hσnegative : zetaPacketEnvelopeExponent t σ < 0 :=
        Real.exp_lt_one_iff.mp hσexp
      exact hσnegative.le.trans hρpositive.le
  have hρoffAxis : (zetaSpectralCoordinate ρ.1).im ≠ 0 := by
    intro hzero
    have hzero' : 1 / 2 - ρ.1.re = 0 := by
      simpa using hzero
    unfold zetaPacketEnvelopeExponent offAxisEnvelopeExponent at hρpositive
    simp [pow_two] at hρpositive
    nlinarith [hzero', mul_self_nonneg (ρ.1.im - t)]
  refine ⟨t, ρ, hρoffAxis, htOrdinate ρ, hglobalMax, ?_⟩
  intro σ hdifferent
  exact (hglobalMax σ).lt_of_ne fun heq =>
    hdifferent
      (sameZetaConjugatePacket_of_envelope_eq_of_not_mem_tieCenterSet
        htTie heq.symm)

/-- Oriented form of the selector: choose the representative of the maximal
critical-reflection packet for which the odd-`π` width sequence has positive
denominator. -/
theorem exists_oriented_strictlyMaximalOffAxisZetaPacket_of_representation
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum
      analyticZetaZeroMultiplicity Q)
    (hoffAxis : ∃ ρ : NontrivialZetaZero,
      (zetaSpectralCoordinate ρ.1).im ≠ 0) :
    ∃ (t : ℝ) (ρ : NontrivialZetaZero),
      0 < 2 * (zetaSpectralCoordinate ρ.1).im *
        ((zetaSpectralCoordinate ρ.1).re - t) ∧
      (∀ σ : NontrivialZetaZero,
        zetaPacketEnvelopeExponent t σ ≤
          zetaPacketEnvelopeExponent t ρ) ∧
      (∀ σ : NontrivialZetaZero,
        ¬ SameZetaConjugatePacket ρ σ →
          zetaPacketEnvelopeExponent t σ <
            zetaPacketEnvelopeExponent t ρ) := by
  obtain ⟨t, ρ, hρoffAxis, ht, hmax, hstrict⟩ :=
    exists_strictlyMaximalOffAxisZetaPacket_of_representation
      Q hRep hoffAxis
  let slope := 2 * (zetaSpectralCoordinate ρ.1).im *
    ((zetaSpectralCoordinate ρ.1).re - t)
  have hslopeNe : slope ≠ 0 := by
    unfold slope
    exact mul_ne_zero
      (mul_ne_zero two_ne_zero hρoffAxis)
      (sub_ne_zero.mpr ht.symm)
  by_cases hslope : 0 < slope
  · exact ⟨t, ρ, hslope, hmax, hstrict⟩
  · let ρ' := NontrivialZetaZero.conjugatePartner ρ
    have hslopeNeg : slope < 0 :=
      lt_of_le_of_ne (le_of_not_gt hslope) hslopeNe
    have hslope' : 0 < 2 * (zetaSpectralCoordinate ρ'.1).im *
        ((zetaSpectralCoordinate ρ'.1).re - t) := by
      unfold ρ'
      rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
      simp only [Complex.conj_re, Complex.conj_im]
      nlinarith
    refine ⟨t, ρ', hslope', ?_, ?_⟩
    · intro σ
      simpa [ρ'] using hmax σ
    · intro σ hdifferent
      have hdifferent' : ¬ SameZetaConjugatePacket ρ σ := by
        simpa [ρ'] using hdifferent
      simpa [ρ'] using hstrict σ hdifferent'

/-- Exact real contribution of a distinct zero and its critical-reflection
partner, with their common analytic multiplicity. -/
theorem sum_zetaGaussianDistinctZeroSummand_re_over_conjugatePacket
    (ε t : ℝ) (ρ : NontrivialZetaZero)
    (hoffAxis : (zetaSpectralCoordinate ρ.1).im ≠ 0) :
    ∑ σ ∈ ({ρ, NontrivialZetaZero.conjugatePartner ρ} :
        Finset NontrivialZetaZero),
        (zetaGaussianDistinctZeroSummand
          analyticZetaZeroMultiplicity ε t σ).re =
      (analyticZetaZeroMultiplicity ρ : ℝ) *
        offAxisPacketContribution ε t
          (zetaSpectralCoordinate ρ.1).re
          (zetaSpectralCoordinate ρ.1).im := by
  rw [Finset.sum_pair
    (NontrivialZetaZero.ne_conjugatePartner_of_spectral_im_ne_zero
      ρ hoffAxis)]
  rw [zetaGaussianDistinctZeroSummand_re,
    zetaGaussianDistinctZeroSummand_re]
  simp only [analyticZetaZeroMultiplicity_conjugatePartner,
    NontrivialZetaZero.spectralCoordinate_conjugatePartner,
    Complex.conj_re, Complex.conj_im,
    offAxisSingleContribution_neg_height]
  rw [offAxisPacketContribution_eq_two_mul_single]
  ring

/-- A strictly maximal oriented zeta packet eventually dominates the complete
weighted sum over all distinct zeros outside that packet.  Absolute
summability is supplied by the represented zero sum itself. -/
theorem eventually_maximalZetaPacket_add_externalSum_negative
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum
      analyticZetaZeroMultiplicity Q)
    (t : ℝ) (ρ : NontrivialZetaZero)
    (hslope : 0 < 2 * (zetaSpectralCoordinate ρ.1).im *
      ((zetaSpectralCoordinate ρ.1).re - t))
    (hstrict : ∀ σ : NontrivialZetaZero,
      ¬ SameZetaConjugatePacket ρ σ →
        zetaPacketEnvelopeExponent t σ <
          zetaPacketEnvelopeExponent t ρ) :
    let targetSet : Finset NontrivialZetaZero :=
      {ρ, NontrivialZetaZero.conjugatePartner ρ}
    ∀ᶠ n : ℕ in atTop,
      0 < offAxisOddPiWidth t
          (zetaSpectralCoordinate ρ.1).re
          (zetaSpectralCoordinate ρ.1).im n ∧
        offAxisPacketContribution
            (offAxisOddPiWidth t
              (zetaSpectralCoordinate ρ.1).re
              (zetaSpectralCoordinate ρ.1).im n)
            t (zetaSpectralCoordinate ρ.1).re
              (zetaSpectralCoordinate ρ.1).im +
          ∑' σ : {σ : NontrivialZetaZero // σ ∉ targetSet},
            (analyticZetaZeroMultiplicity σ.1 : ℝ) *
              offAxisSingleContribution
                (offAxisOddPiWidth t
                  (zetaSpectralCoordinate ρ.1).re
                  (zetaSpectralCoordinate ρ.1).im n)
                t (zetaSpectralCoordinate σ.1.1).re
                  (zetaSpectralCoordinate σ.1.1).im < 0 := by
  classical
  dsimp only
  let targetSet : Finset NontrivialZetaZero :=
    {ρ, NontrivialZetaZero.conjugatePartner ρ}
  have hnotSame
      (σ : {σ : NontrivialZetaZero // σ ∉ targetSet}) :
      ¬ SameZetaConjugatePacket ρ σ.1 := by
    simpa [targetSet, SameZetaConjugatePacket] using σ.2
  have hgap
      (σ : {σ : NontrivialZetaZero // σ ∉ targetSet}) :
      0 < fixedCenterPacketGap t
        (zetaSpectralCoordinate ρ.1).re
        (zetaSpectralCoordinate ρ.1).im
        (zetaSpectralCoordinate σ.1.1).re
        (zetaSpectralCoordinate σ.1.1).im := by
    have hlt := hstrict σ.1 (hnotSame σ)
    simpa [fixedCenterPacketGap, zetaPacketEnvelopeExponent] using
      (sub_pos.mpr hlt)
  have hrelativeAll :=
    summable_weightedDistinct_fixedCenter_relativeEnvelope_of_representation
      analyticZetaZeroMultiplicity Q hRep 1 t
        (zetaSpectralCoordinate ρ.1).re
        (zetaSpectralCoordinate ρ.1).im zero_lt_one
  have hrelative : Summable fun
      σ : {σ : NontrivialZetaZero // σ ∉ targetSet} =>
        (analyticZetaZeroMultiplicity σ.1 : ℝ) * Real.exp
          (-1 * fixedCenterPacketGap t
            (zetaSpectralCoordinate ρ.1).re
            (zetaSpectralCoordinate ρ.1).im
            (zetaSpectralCoordinate σ.1.1).re
            (zetaSpectralCoordinate σ.1.1).im) := by
    convert hrelativeAll.subtype (fun σ => σ ∉ targetSet) using 1 <;> rfl
  simpa only [targetSet] using
    (eventually_offAxisPacketContribution_add_tsum_weightedSingle_negative_at_fixedCenter
      (ι := {σ : NontrivialZetaZero // σ ∉ targetSet})
      t (zetaSpectralCoordinate ρ.1).re
        (zetaSpectralCoordinate ρ.1).im
      (fun σ => (zetaSpectralCoordinate σ.1.1).re)
      (fun σ => (zetaSpectralCoordinate σ.1.1).im)
      (fun σ => (analyticZetaZeroMultiplicity σ.1 : ℝ))
      hslope (fun σ => Nat.cast_nonneg _)
      hgap 1 hrelative)

/-- The global zero-divisor separation theorem for represented translated
Gaussian sums.

If any zero were off the critical line, the tie-free selector would produce
a strictly maximal conjugate packet.  Along its odd-`π` widths, dominated
convergence makes the complete external divisor smaller than that packet's
negative contribution.  Analytic multiplicity only makes the selected
negative packet larger in magnitude, contradicting all-Gaussian
nonnegativity. -/
theorem zetaGaussianZeroDivisorSeparation_proved :
    ZetaGaussianZeroDivisorSeparation := by
  classical
  intro Q hRep hnonnegative ρ₀
  by_contra hρ₀offAxis
  obtain ⟨t, ρ, hslope, _hmax, hstrict⟩ :=
    exists_oriented_strictlyMaximalOffAxisZetaPacket_of_representation
      Q hRep ⟨ρ₀, hρ₀offAxis⟩
  let γ := (zetaSpectralCoordinate ρ.1).re
  let a := (zetaSpectralCoordinate ρ.1).im
  let targetSet : Finset NontrivialZetaZero :=
    {ρ, NontrivialZetaZero.conjugatePartner ρ}
  have ha : a ≠ 0 := by
    intro hzero
    unfold a at hzero
    rw [hzero] at hslope
    norm_num at hslope
  have heventuallyNegative :=
    eventually_maximalZetaPacket_add_externalSum_negative
      Q hRep t ρ hslope hstrict
  obtain ⟨n, hn⟩ := heventuallyNegative.exists
  let ε := offAxisOddPiWidth t γ a n
  have hε : 0 < ε := by
    exact hn.1
  have hnegative :
      offAxisPacketContribution ε t γ a +
        ∑' σ : {σ : NontrivialZetaZero // σ ∉ targetSet},
          (analyticZetaZeroMultiplicity σ.1 : ℝ) *
            offAxisSingleContribution ε t
              (zetaSpectralCoordinate σ.1.1).re
              (zetaSpectralCoordinate σ.1.1).im < 0 := by
    exact hn.2
  have hdistinct := hasSum_zetaGaussianDistinctZeroSummand
    analyticZetaZeroMultiplicity ε t (Q ε t) (hRep ε t hε)
  have hre := Complex.hasSum_re hdistinct
  have hsplit := hre.summable.sum_add_tsum_subtype_compl targetSet
  have htarget :
      ∑ σ ∈ targetSet,
          (zetaGaussianDistinctZeroSummand
            analyticZetaZeroMultiplicity ε t σ).re =
        (analyticZetaZeroMultiplicity ρ : ℝ) *
          offAxisPacketContribution ε t γ a := by
    simpa [targetSet, γ, a] using
      sum_zetaGaussianDistinctZeroSummand_re_over_conjugatePacket
        ε t ρ ha
  have hexternal :
      ∑' σ : {σ : NontrivialZetaZero // σ ∉ targetSet},
          (zetaGaussianDistinctZeroSummand
            analyticZetaZeroMultiplicity ε t σ.1).re =
        ∑' σ : {σ : NontrivialZetaZero // σ ∉ targetSet},
          (analyticZetaZeroMultiplicity σ.1 : ℝ) *
            offAxisSingleContribution ε t
              (zetaSpectralCoordinate σ.1.1).re
              (zetaSpectralCoordinate σ.1.1).im := by
    apply tsum_congr
    intro σ
    exact zetaGaussianDistinctZeroSummand_re
      analyticZetaZeroMultiplicity ε t σ.1
  have hdecomposition :
      Q ε t =
        (analyticZetaZeroMultiplicity ρ : ℝ) *
            offAxisPacketContribution ε t γ a +
          ∑' σ : {σ : NontrivialZetaZero // σ ∉ targetSet},
            (analyticZetaZeroMultiplicity σ.1 : ℝ) *
              offAxisSingleContribution ε t
                (zetaSpectralCoordinate σ.1.1).re
                (zetaSpectralCoordinate σ.1.1).im := by
    calc
      Q ε t = ∑' σ : NontrivialZetaZero,
          (zetaGaussianDistinctZeroSummand
            analyticZetaZeroMultiplicity ε t σ).re := hre.tsum_eq.symm
      _ = (∑ σ ∈ targetSet,
            (zetaGaussianDistinctZeroSummand
              analyticZetaZeroMultiplicity ε t σ).re) +
          ∑' σ : {σ : NontrivialZetaZero // σ ∉ targetSet},
            (zetaGaussianDistinctZeroSummand
              analyticZetaZeroMultiplicity ε t σ.1).re := hsplit.symm
      _ = _ := by rw [htarget, hexternal]
  have hpacketNegative : offAxisPacketContribution ε t γ a < 0 := by
    unfold ε
    rw [offAxisPacketContribution_at_oddPiWidth t γ a hslope n]
    nlinarith [Real.exp_pos
      (offAxisOddPiWidth t γ a n * offAxisEnvelopeExponent t γ a)]
  have hmultiplicity :
      1 ≤ (analyticZetaZeroMultiplicity ρ : ℝ) := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive ρ
  have hweightedPacket :
      (analyticZetaZeroMultiplicity ρ : ℝ) *
          offAxisPacketContribution ε t γ a ≤
        offAxisPacketContribution ε t γ a := by
    have hnonnegative :
        0 ≤ (analyticZetaZeroMultiplicity ρ : ℝ) - 1 :=
      sub_nonneg.mpr hmultiplicity
    have hproduct :
        ((analyticZetaZeroMultiplicity ρ : ℝ) - 1) *
            offAxisPacketContribution ε t γ a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hnonnegative hpacketNegative.le
    nlinarith
  have hQnegative : Q ε t < 0 := by
    rw [hdecomposition]
    exact lt_of_le_of_lt
      (by
        simpa only [add_comm] using
          add_le_add_right hweightedPacket
            (∑' σ : {σ : NontrivialZetaZero // σ ∉ targetSet},
              (analyticZetaZeroMultiplicity σ.1 : ℝ) *
                offAxisSingleContribution ε t
                  (zetaSpectralCoordinate σ.1.1).re
                  (zetaSpectralCoordinate σ.1.1).im))
      hnegative
  exact (not_lt_of_ge (hnonnegative ε t hε)) hQnegative

/-! ## Consequences and the symmetric normalization -/

namespace NontrivialZetaZero

/-- Functional-equation reflection as an equivalence of the distinct zero
indexing type. -/
def functionalPartnerEquiv :
    NontrivialZetaZero ≃ NontrivialZetaZero where
  toFun := functionalPartner
  invFun := functionalPartner
  left_inv := functionalPartner_functionalPartner
  right_inv := functionalPartner_functionalPartner

@[simp]
theorem functionalPartnerEquiv_apply (ρ : NontrivialZetaZero) :
    functionalPartnerEquiv ρ = functionalPartner ρ := rfl

/-- Critical-line reflection as an equivalence of distinct zeros. -/
def conjugatePartnerEquiv :
    NontrivialZetaZero ≃ NontrivialZetaZero where
  toFun := conjugatePartner
  invFun := conjugatePartner
  left_inv := conjugatePartner_conjugatePartner
  right_inv := conjugatePartner_conjugatePartner

@[simp]
theorem conjugatePartnerEquiv_apply (ρ : NontrivialZetaZero) :
    conjugatePartnerEquiv ρ = conjugatePartner ρ := rfl

end NontrivialZetaZero

/-- A weighted distinct-zero summand at the reflected zero equals the
original zero's summand at the reflected center. -/
theorem zetaGaussianDistinctZeroSummand_functionalPartner
    (ε t : ℝ) (ρ : NontrivialZetaZero) :
    zetaGaussianDistinctZeroSummand analyticZetaZeroMultiplicity ε t
        (NontrivialZetaZero.functionalPartner ρ) =
      zetaGaussianDistinctZeroSummand analyticZetaZeroMultiplicity ε (-t) ρ := by
  simp [zetaGaussianDistinctZeroSummand,
    complexTranslatedGaussian_neg_center]

/-- Critical-line reflection conjugates a weighted distinct-zero summand. -/
theorem zetaGaussianDistinctZeroSummand_conjugatePartner
    (ε t : ℝ) (ρ : NontrivialZetaZero) :
    zetaGaussianDistinctZeroSummand analyticZetaZeroMultiplicity ε t
        (NontrivialZetaZero.conjugatePartner ρ) =
      starRingEnd ℂ
        (zetaGaussianDistinctZeroSummand
          analyticZetaZeroMultiplicity ε t ρ) := by
  simp [zetaGaussianDistinctZeroSummand,
    complexTranslatedGaussian_conj]

/-- Every represented translated zeta-Gaussian zero sum is even in its
center, by functional-equation reindexing. -/
theorem representedZetaGaussianZeroSum_even
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum
      analyticZetaZeroMultiplicity Q)
    (ε t : ℝ) (hε : 0 < ε) :
    Q ε (-t) = Q ε t := by
  have ht := hasSum_zetaGaussianDistinctZeroSummand
    analyticZetaZeroMultiplicity ε t (Q ε t) (hRep ε t hε)
  have hminus := hasSum_zetaGaussianDistinctZeroSummand
    analyticZetaZeroMultiplicity ε (-t) (Q ε (-t)) (hRep ε (-t) hε)
  have hreindexed :
      HasSum
        (zetaGaussianDistinctZeroSummand
          analyticZetaZeroMultiplicity ε t ∘
            NontrivialZetaZero.functionalPartnerEquiv)
        (Q ε t : ℂ) :=
    (NontrivialZetaZero.functionalPartnerEquiv.hasSum_iff).2 ht
  have hminus' :
      HasSum
        (zetaGaussianDistinctZeroSummand
          analyticZetaZeroMultiplicity ε (-t))
        (Q ε t : ℂ) := by
    refine hreindexed.congr_fun fun ρ => ?_
    exact (zetaGaussianDistinctZeroSummand_functionalPartner ε t ρ).symm
  exact_mod_cast hminus.unique hminus'

/-- The formerly conditional translated-Gaussian equivalence now follows
from the proved global separation theorem. -/
theorem zetaGaussianZeroSumNonnegative_iff_riemannHypothesis_proved
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum
      analyticZetaZeroMultiplicity Q) :
    ZetaGaussianZeroSumNonnegative Q ↔ RiemannHypothesis :=
  zetaGaussianZeroSumNonnegative_iff_riemannHypothesis
    zetaGaussianZeroDivisorSeparation_proved Q hRep

/-- Likewise, coherent-kernel positive semidefiniteness is unconditionally
equivalent to RH once the translated zero-sum representation is supplied. -/
theorem gaussianCoherentKernelPositiveSemidefinite_iff_riemannHypothesis_proved
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum
      analyticZetaZeroMultiplicity Q) :
    GaussianCoherentKernelPositiveSemidefinite Q ↔ RiemannHypothesis :=
  gaussianCoherentKernelPositiveSemidefinite_iff_riemannHypothesis
    (zetaGaussianCoherentKernelSeparation_of_zeroDivisorSeparation
      zetaGaussianZeroDivisorSeparation_proved) Q hRep

/-- If `Q` represents the translated family and `G` represents its symmetric
normalization, uniqueness of unconditional sums and functional symmetry give
`G(ε,t)=2Q(ε,t)`. -/
theorem representedZetaSymmetricGaussianZeroSum_eq_two_mul_translated
    (Q G : ℝ → ℝ → ℝ)
    (hQ : RepresentsZetaGaussianZeroSum
      analyticZetaZeroMultiplicity Q)
    (hG : RepresentsZetaSymmetricGaussianZeroSum
      analyticZetaZeroMultiplicity G)
    (ε t : ℝ) (hε : 0 < ε) :
    G ε t = 2 * Q ε t := by
  have hfromQ :=
    (representsZetaSymmetricGaussianZeroSum_of_translated
      analyticZetaZeroMultiplicity Q hQ) ε t hε
  have heq := (hG ε t hε).unique hfromQ
  have heven := representedZetaGaussianZeroSum_even Q hQ ε t hε
  norm_cast at heq
  change G ε t = Q ε t + Q ε (-t) at heq
  rw [heven] at heq
  linarith

/-- Positivity of the symmetric certificate normalization implies positivity
of the translated family whenever both zero-sum representations are known. -/
theorem zetaGaussianZeroSumNonnegative_of_symmetric
    (Q G : ℝ → ℝ → ℝ)
    (hQ : RepresentsZetaGaussianZeroSum
      analyticZetaZeroMultiplicity Q)
    (hG : RepresentsZetaSymmetricGaussianZeroSum
      analyticZetaZeroMultiplicity G)
    (hGnonnegative : ZetaSymmetricGaussianZeroSumNonnegative G) :
    ZetaGaussianZeroSumNonnegative Q := by
  intro ε t hε
  have heq := representedZetaSymmetricGaussianZeroSum_eq_two_mul_translated
    Q G hQ hG ε t hε
  have hnonnegative := hGnonnegative ε t hε
  nlinarith

/-- Final analytic equivalence in the exact even normalization used by the
certificate program, assuming the translated and symmetric explicit-formula
representations.  No zero-divisor separation hypothesis remains. -/
theorem zetaSymmetricGaussianZeroSumNonnegative_iff_riemannHypothesis_proved
    (Q G : ℝ → ℝ → ℝ)
    (hQ : RepresentsZetaGaussianZeroSum
      analyticZetaZeroMultiplicity Q)
    (hG : RepresentsZetaSymmetricGaussianZeroSum
      analyticZetaZeroMultiplicity G) :
    ZetaSymmetricGaussianZeroSumNonnegative G ↔ RiemannHypothesis := by
  constructor
  · intro hnonnegative
    exact (zetaGaussianZeroSumNonnegative_iff_riemannHypothesis_proved
      Q hQ).1
        (zetaGaussianZeroSumNonnegative_of_symmetric
          Q G hQ hG hnonnegative)
  · exact zetaSymmetricGaussianZeroSumNonnegative_of_riemannHypothesis
      analyticZetaZeroMultiplicity G hG

/-! ## Canonical representation from an ordinate-tail condition -/

/-- The exact remaining zero-counting input needed merely to construct the
Gaussian zero sum: every positive Gaussian in the zero ordinate is summable,
with analytic multiplicity represented by occurrence slots.  A polynomial
Riemann--von Mangoldt bound would imply this condition. -/
def ZetaZeroGaussianOrdinateSummable : Prop :=
  ∀ (c : ℝ), 0 < c →
    Summable fun occurrence :
        NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
      Real.exp (-c * (zetaSpectralCoordinate occurrence.1.1).re ^ 2)

/-- The bounded critical strip and a Gaussian ordinate tail imply absolute
summability of every translated entire Gaussian. -/
theorem summable_zetaGaussianZeroSummand_of_ordinateSummable
    (hOrdinate : ZetaZeroGaussianOrdinateSummable)
    (ε t : ℝ) (hε : 0 < ε) :
    Summable (zetaGaussianZeroSummand
      analyticZetaZeroMultiplicity ε t) := by
  let c : ℝ := ε / 2
  have hc : 0 < c := div_pos hε two_pos
  have hbase := hOrdinate c hc
  let constant : ℝ := Real.exp (ε / 4 + ε * t ^ 2)
  have hdominating : Summable fun occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity =>
        constant * Real.exp
          (-c * (zetaSpectralCoordinate occurrence.1.1).re ^ 2) :=
    hbase.mul_left constant
  apply hdominating.of_norm_bounded
  intro occurrence
  let z := zetaSpectralCoordinate occurrence.1.1
  have habs :=
    NontrivialZetaZero.abs_spectralCoordinate_im_lt_half occurrence.1
  have himSq : z.im ^ 2 ≤ 1 / 4 := by
    have hsquare : z.im ^ 2 < (1 / 2 : ℝ) ^ 2 :=
      sq_lt_sq.mpr (by simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        using habs)
    norm_num at hsquare ⊢
    exact hsquare.le
  have hquadratic :
      ε * z.im ^ 2 - ε * (z.re - t) ^ 2 ≤
        ε / 4 + ε * t ^ 2 - (ε / 2) * z.re ^ 2 := by
    nlinarith [sq_nonneg (z.re - 2 * t)]
  rw [zetaGaussianZeroSummand, norm_complexTranslatedGaussian]
  calc
    Real.exp (ε * z.im ^ 2 - ε * (z.re - t) ^ 2) ≤
        Real.exp (ε / 4 + ε * t ^ 2 - (ε / 2) * z.re ^ 2) :=
      Real.exp_le_exp.mpr hquadratic
    _ = constant * Real.exp (-c * z.re ^ 2) := by
      unfold constant c
      rw [← Real.exp_add]
      congr 1
      ring

/-- Any convergent multiplicity-counted Gaussian zero sum is real.  The proof
regroups multiplicity slots, reindexes by critical-line reflection, and uses
uniqueness of unconditional sums. -/
theorem hasSum_zetaGaussianZeroSummand_im_eq_zero
    (ε t : ℝ) (S : ℂ)
    (hSum : HasSum
      (zetaGaussianZeroSummand analyticZetaZeroMultiplicity ε t) S) :
    S.im = 0 := by
  have hdistinct := hasSum_zetaGaussianDistinctZeroSummand
    analyticZetaZeroMultiplicity ε t S hSum
  have him := Complex.hasSum_im hdistinct
  have hreindexed :
      HasSum
        ((fun ρ : NontrivialZetaZero =>
          (zetaGaussianDistinctZeroSummand
            analyticZetaZeroMultiplicity ε t ρ).im) ∘
          NontrivialZetaZero.conjugatePartnerEquiv)
        S.im :=
    (NontrivialZetaZero.conjugatePartnerEquiv.hasSum_iff).2 him
  have hnegativeSameSum :
      HasSum
        (fun ρ : NontrivialZetaZero =>
          -(zetaGaussianDistinctZeroSummand
            analyticZetaZeroMultiplicity ε t ρ).im)
        S.im := by
    refine hreindexed.congr_fun fun ρ => ?_
    have hconj := congrArg Complex.im
      (zetaGaussianDistinctZeroSummand_conjugatePartner ε t ρ)
    simpa only [Function.comp_apply,
      NontrivialZetaZero.conjugatePartnerEquiv_apply,
      Complex.conj_im] using hconj.symm
  have hnegativeNegSum :
      HasSum
        (fun ρ : NontrivialZetaZero =>
          -(zetaGaussianDistinctZeroSummand
            analyticZetaZeroMultiplicity ε t ρ).im)
        (-S.im) := by
    simpa using him.neg
  have heq := hnegativeSameSum.unique hnegativeNegSum
  linarith

/-- Canonical real translated Gaussian zero sum. -/
noncomputable def canonicalZetaGaussianZeroSum (ε t : ℝ) : ℝ :=
  (∑' occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
    zetaGaussianZeroSummand analyticZetaZeroMultiplicity ε t occurrence).re

/-- Gaussian ordinate summability constructs the translated `HasSum`
representation canonically.  The still-separate explicit-formula task is to
identify this canonical function with the arithmetic expression. -/
theorem representsCanonicalZetaGaussianZeroSum
    (hOrdinate : ZetaZeroGaussianOrdinateSummable) :
    RepresentsZetaGaussianZeroSum analyticZetaZeroMultiplicity
      canonicalZetaGaussianZeroSum := by
  intro ε t hε
  have hsummable :=
    summable_zetaGaussianZeroSummand_of_ordinateSummable
      hOrdinate ε t hε
  let S : ℂ := ∑' occurrence :
      NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
    zetaGaussianZeroSummand analyticZetaZeroMultiplicity ε t occurrence
  have hSum : HasSum
      (zetaGaussianZeroSummand analyticZetaZeroMultiplicity ε t) S :=
    hsummable.hasSum
  have him : S.im = 0 :=
    hasSum_zetaGaussianZeroSummand_im_eq_zero ε t S hSum
  have hreal : S = (S.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [show (canonicalZetaGaussianZeroSum ε t : ℂ) = S by
    rw [canonicalZetaGaussianZeroSum]
    exact hreal.symm]
  exact hSum

/-- Canonical even normalization corresponding to the arithmetic certificate
family. -/
noncomputable def canonicalZetaSymmetricGaussianZeroSum
    (ε t : ℝ) : ℝ :=
  2 * canonicalZetaGaussianZeroSum ε t

theorem representsCanonicalZetaSymmetricGaussianZeroSum
    (hOrdinate : ZetaZeroGaussianOrdinateSummable) :
    RepresentsZetaSymmetricGaussianZeroSum analyticZetaZeroMultiplicity
      canonicalZetaSymmetricGaussianZeroSum := by
  have hQ := representsCanonicalZetaGaussianZeroSum hOrdinate
  intro ε t hε
  have hsum :=
    (representsZetaSymmetricGaussianZeroSum_of_translated
      analyticZetaZeroMultiplicity canonicalZetaGaussianZeroSum hQ)
      ε t hε
  have heven := representedZetaGaussianZeroSum_even
    canonicalZetaGaussianZeroSum hQ ε t hε
  simpa [canonicalZetaSymmetricGaussianZeroSum, heven, two_mul] using hsum

/-- Under the standard Gaussian ordinate-tail condition, positivity of the
canonical even zero sum is exactly RH. -/
theorem canonicalZetaSymmetricGaussianZeroSum_nonnegative_iff_riemannHypothesis
    (hOrdinate : ZetaZeroGaussianOrdinateSummable) :
    ZetaSymmetricGaussianZeroSumNonnegative
        canonicalZetaSymmetricGaussianZeroSum ↔
      RiemannHypothesis :=
  zetaSymmetricGaussianZeroSumNonnegative_iff_riemannHypothesis_proved
    canonicalZetaGaussianZeroSum canonicalZetaSymmetricGaussianZeroSum
    (representsCanonicalZetaGaussianZeroSum hOrdinate)
    (representsCanonicalZetaSymmetricGaussianZeroSum hOrdinate)

end

end RiemannGaussian
