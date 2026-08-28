import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Analytic.Order
import RiemannGaussian.GaussianEnvelopeSeparation

/-!
# The exact remaining Gaussian-to-zeta bridge

This file packages the logical interface between the entire spectral
Gaussians and Mathlib's `RiemannHypothesis` without assuming an explicit
formula or a convergence theorem.

`RepresentsZetaGaussianZeroSum multiplicity Q` says that a real function
`Q ε t` is the convergently interpreted sum of the translated Gaussian over
all nontrivial zeta zeros, counted with the supplied multiplicity.  Under RH,
every summand is positive, so any such `Q` is nonnegative.  The converse is isolated as
`ZetaGaussianZeroDivisorSeparation`: all-Gaussian nonnegativity must force the
entire infinite zero divisor onto the real spectral axis.

No axiom asserting the converse is introduced here.  It is proved downstream
in `GaussianZetaGeometry`, using absolute summability furnished by `HasSum`,
countable tie avoidance, and weighted dominated convergence.
-/

namespace RiemannGaussian

noncomputable section

lemma iteratedDeriv_conj_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n
        ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
  induction n with
  | zero => simp [iteratedDeriv_eq_iterate]
  | succ n ih =>
      rw [show n + 1 = n.succ by omega, iteratedDeriv_succ,
        iteratedDeriv_succ, ih, deriv_conj_conj]

lemma riemannZeta_eq_conj_comp_conj :
    riemannZeta = (starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ) := by
  funext s
  simp [Function.comp_apply]

theorem iteratedDeriv_riemannZeta_conj (n : ℕ) (s : ℂ) :
    iteratedDeriv n riemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (iteratedDeriv n riemannZeta s) := by
  have hiter := iteratedDeriv_conj_conj riemannZeta n
  rw [← riemannZeta_eq_conj_comp_conj] at hiter
  have h := congrFun hiter (starRingEnd ℂ s)
  simpa [Function.comp_apply] using h

/-- The predicate used by Mathlib's RH definition to exclude trivial zeta
zeros and the exceptional point `1`. -/
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
    (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1

/-- The set of distinct nontrivial zeros, before analytic multiplicities are
attached. -/
def nontrivialZetaZeroSet : Set ℂ :=
  {s | IsNontrivialZetaZero s}

theorem nontrivialZetaZeroSet_subset_riemannZetaZeros :
    nontrivialZetaZeroSet ⊆ riemannZetaZeros := by
  intro s hs
  exact hs.1

/-- Mathlib's discreteness theorem already settles the local part of the
zero-divisor problem: every compact region contains only finitely many
distinct nontrivial zeros.  What remains for Gaussian separation is uniform
control of the noncompact tail. -/
theorem IsCompact.inter_nontrivialZetaZeroSet_finite
    {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ nontrivialZetaZeroSet).Finite := by
  exact hS.inter_riemannZetaZeros_finite.subset
    (Set.inter_subset_inter_right S
      nontrivialZetaZeroSet_subset_riemannZetaZeros)

/-- Nontrivial zeta zeros as an indexing type. -/
abbrev NontrivialZetaZero := {s : ℂ // IsNontrivialZetaZero s}

namespace NontrivialZetaZero

/-- Complex conjugation preserves the set of distinct nontrivial zeta
zeros. -/
def conjugate (ρ : NontrivialZetaZero) : NontrivialZetaZero := by
  refine ⟨starRingEnd ℂ ρ.1, ?_⟩
  refine ⟨by simp [ρ.2.1], ?_, ?_⟩
  · rintro ⟨n, hn⟩
    apply ρ.2.2.1
    refine ⟨n, ?_⟩
    have h := congrArg (starRingEnd ℂ) hn
    have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
      apply Complex.ext <;> norm_num
    rw [map_mul, map_neg, htwo] at h
    simpa using h
  · intro hone
    apply ρ.2.2.2
    have h := congrArg (starRingEnd ℂ) hone
    simpa using h

@[simp]
theorem conjugate_coe (ρ : NontrivialZetaZero) :
    (conjugate ρ : ℂ) = starRingEnd ℂ ρ.1 := rfl

@[simp]
theorem conjugate_conjugate (ρ : NontrivialZetaZero) :
    conjugate (conjugate ρ) = ρ := by
  apply Subtype.ext
  simp

theorem spectralCoordinate_conjugate (ρ : NontrivialZetaZero) :
    zetaSpectralCoordinate (conjugate ρ).1 =
      -starRingEnd ℂ (zetaSpectralCoordinate ρ.1) := by
  simp

theorem coe_ne_zero (ρ : NontrivialZetaZero) : (ρ.1 : ℂ) ≠ 0 := by
  intro hzero
  have hzeta := ρ.2.1
  rw [hzero, riemannZeta_zero] at hzeta
  norm_num at hzeta

theorem GammaR_ne_zero (ρ : NontrivialZetaZero) :
    Complex.Gammaℝ ρ.1 ≠ 0 := by
  rw [ne_eq, Complex.Gammaℝ_eq_zero_iff, not_exists]
  intro n hn
  cases n with
  | zero =>
      apply coe_ne_zero ρ
      simpa using hn
  | succ n =>
      apply ρ.2.2.1
      refine ⟨n, ?_⟩
      simpa [Nat.cast_succ] using hn

/-- The completed zeta function vanishes at every nontrivial zeta zero. -/
theorem completedRiemannZeta_eq_zero (ρ : NontrivialZetaZero) :
    completedRiemannZeta ρ.1 = 0 := by
  have hzeta := ρ.2.1
  rw [riemannZeta_def_of_ne_zero (coe_ne_zero ρ)] at hzeta
  exact (div_eq_zero_iff.mp hzeta).resolve_right (GammaR_ne_zero ρ)

/-- The functional-equation partner `1 - ρ` is again a nontrivial zeta
zero. -/
def functionalPartner (ρ : NontrivialZetaZero) : NontrivialZetaZero := by
  refine ⟨1 - ρ.1, ?_⟩
  have hcompleted : completedRiemannZeta (1 - ρ.1) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact completedRiemannZeta_eq_zero ρ
  have hzero : riemannZeta (1 - ρ.1) = 0 := by
    rw [riemannZeta_def_of_ne_zero]
    · rw [hcompleted, zero_div]
    · exact sub_ne_zero.mpr ρ.2.2.2.symm
  refine ⟨hzero, ?_, ?_⟩
  · rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hRe : 1 ≤ ρ.1.re := by
      linarith
    exact riemannZeta_ne_zero_of_one_le_re hRe ρ.2.1
  · intro hone
    apply coe_ne_zero ρ
    exact sub_eq_self.mp hone

@[simp]
theorem functionalPartner_coe (ρ : NontrivialZetaZero) :
    (functionalPartner ρ : ℂ) = 1 - ρ.1 := rfl

@[simp]
theorem functionalPartner_functionalPartner (ρ : NontrivialZetaZero) :
    functionalPartner (functionalPartner ρ) = ρ := by
  apply Subtype.ext
  simp

theorem spectralCoordinate_functionalPartner (ρ : NontrivialZetaZero) :
    zetaSpectralCoordinate (functionalPartner ρ).1 =
      -zetaSpectralCoordinate ρ.1 := by
  simp

/-- Reflection across the critical line: `ρ ↦ 1 - conj ρ`.  In the
rotated spectral coordinate this is ordinary complex conjugation, so an
off-axis zero and its reflected partner form exactly the conjugate packet
used by the Gaussian separation argument. -/
def conjugatePartner (ρ : NontrivialZetaZero) : NontrivialZetaZero :=
  functionalPartner (conjugate ρ)

@[simp]
theorem conjugatePartner_coe (ρ : NontrivialZetaZero) :
    (conjugatePartner ρ : ℂ) = 1 - starRingEnd ℂ ρ.1 := rfl

@[simp]
theorem conjugatePartner_conjugatePartner (ρ : NontrivialZetaZero) :
    conjugatePartner (conjugatePartner ρ) = ρ := by
  apply Subtype.ext
  simp

theorem spectralCoordinate_conjugatePartner (ρ : NontrivialZetaZero) :
    zetaSpectralCoordinate (conjugatePartner ρ).1 =
      starRingEnd ℂ (zetaSpectralCoordinate ρ.1) := by
  simp [conjugatePartner]

end NontrivialZetaZero

/-- A multiplicity for each distinct nontrivial zero. -/
abbrev ZetaZeroMultiplicity := NontrivialZetaZero → ℕ

/-- The genuine analytic multiplicity: the order of vanishing of zeta at the
given nontrivial zero. -/
noncomputable def analyticZetaZeroMultiplicity : ZetaZeroMultiplicity :=
  fun ρ => analyticOrderNatAt riemannZeta ρ.1

lemma analyticAt_riemannZeta_nontrivialZero (ρ : NontrivialZetaZero) :
    AnalyticAt ℂ riemannZeta ρ.1 := by
  exact analyticOn_riemannZeta ρ.1 (by simpa using ρ.2.2.2)

lemma analyticAt_completedRiemannZeta_nontrivialZero
    (ρ : NontrivialZetaZero) :
    AnalyticAt ℂ completedRiemannZeta ρ.1 := by
  let U : Set ℂ := {0}ᶜ ∩ {1}ᶜ
  have hUopen : IsOpen U := isOpen_compl_singleton.inter isOpen_compl_singleton
  have hρU : ρ.1 ∈ U := by
    exact ⟨by simpa using NontrivialZetaZero.coe_ne_zero ρ,
      by simpa using ρ.2.2.2⟩
  apply DifferentiableOn.analyticAt (s := U) _ (hUopen.mem_nhds hρU)
  intro z hz
  exact (differentiableAt_completedZeta
    (by simpa [U] using hz.1) (by simpa [U] using hz.2)).differentiableWithinAt

/-- At a nontrivial zero, zeta and completed zeta have the same analytic
order because the inverse archimedean Gamma factor is analytic and nonzero. -/
theorem analyticOrderAt_riemannZeta_eq_completedRiemannZeta
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannZeta ρ.1 =
      analyticOrderAt completedRiemannZeta ρ.1 := by
  let inverseGamma : ℂ → ℂ := fun z => (Complex.Gammaℝ z)⁻¹
  have hinverseAnalytic : AnalyticAt ℂ inverseGamma ρ.1 := by
    exact Complex.differentiable_Gammaℝ_inv.analyticAt ρ.1
  have hinverseOrder : analyticOrderAt inverseGamma ρ.1 = 0 := by
    exact hinverseAnalytic.analyticOrderAt_eq_zero.mpr
      (inv_ne_zero (NontrivialZetaZero.GammaR_ne_zero ρ))
  have heq :
      riemannZeta =ᶠ[nhds ρ.1]
        fun z => completedRiemannZeta z * inverseGamma z := by
    filter_upwards [eventually_ne_nhds (NontrivialZetaZero.coe_ne_zero ρ)] with z hz
    rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
  calc
    analyticOrderAt riemannZeta ρ.1 =
        analyticOrderAt
          (fun z => completedRiemannZeta z * inverseGamma z) ρ.1 :=
      analyticOrderAt_congr heq
    _ = analyticOrderAt completedRiemannZeta ρ.1 +
        analyticOrderAt inverseGamma ρ.1 :=
      analyticOrderAt_mul
        (analyticAt_completedRiemannZeta_nontrivialZero ρ) hinverseAnalytic
    _ = analyticOrderAt completedRiemannZeta ρ.1 := by
      rw [hinverseOrder, add_zero]

/-- The functional equation preserves the analytic order of completed zeta
between `ρ` and `1 - ρ`. -/
theorem analyticOrderAt_completedRiemannZeta_functionalPartner
    (ρ : NontrivialZetaZero) :
    analyticOrderAt completedRiemannZeta
        (NontrivialZetaZero.functionalPartner ρ).1 =
      analyticOrderAt completedRiemannZeta ρ.1 := by
  let reflect : ℂ → ℂ := fun z => 1 - z
  have hreflectAnalytic : AnalyticAt ℂ reflect ρ.1 := by
    dsimp [reflect]
    fun_prop
  have hreflectDeriv : deriv reflect ρ.1 ≠ 0 := by
    have hderiv : deriv reflect ρ.1 = -1 := by
      simp [reflect]
    rw [hderiv]
    norm_num
  have horder := analyticOrderAt_comp_of_deriv_ne_zero
    (f := completedRiemannZeta) hreflectAnalytic hreflectDeriv
  have hfun : completedRiemannZeta ∘ reflect = completedRiemannZeta := by
    funext z
    exact completedRiemannZeta_one_sub z
  rw [hfun] at horder
  exact horder.symm

/-- Functional-equation partners have the same zeta-zero multiplicity. -/
theorem analyticOrderAt_riemannZeta_functionalPartner
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannZeta
        (NontrivialZetaZero.functionalPartner ρ).1 =
      analyticOrderAt riemannZeta ρ.1 := by
  rw [analyticOrderAt_riemannZeta_eq_completedRiemannZeta,
    analyticOrderAt_riemannZeta_eq_completedRiemannZeta,
    analyticOrderAt_completedRiemannZeta_functionalPartner]

/-- Conjugate zeta zeros have the same analytic order. -/
theorem analyticOrderAt_riemannZeta_conjugate
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannZeta (NontrivialZetaZero.conjugate ρ).1 =
      analyticOrderAt riemannZeta ρ.1 := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_riemannZeta_nontrivialZero
        (NontrivialZetaZero.conjugate ρ)),
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      (analyticAt_riemannZeta_nontrivialZero ρ)]
  simp [iteratedDeriv_riemannZeta_conj]

/-- Zeta is not locally identically zero at a nontrivial zero, so its
analytic order there is finite. -/
theorem analyticOrderAt_riemannZeta_nontrivialZero_ne_top
    (ρ : NontrivialZetaZero) :
    analyticOrderAt riemannZeta ρ.1 ≠ ⊤ := by
  intro htop
  have hlocal : riemannZeta =ᶠ[nhds ρ.1] (0 : ℂ → ℂ) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  have hpreconnected : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hglobal : Set.EqOn riemannZeta 0 ({1}ᶜ : Set ℂ) :=
    analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hpreconnected
        (by simpa using ρ.2.2.2) hlocal
  have hzetaTwo : riemannZeta (2 : ℂ) = 0 := by
    simpa using hglobal (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hzetaTwo

/-- Every distinct zero must occur at least once.  Without this condition a
zero of assigned multiplicity zero would be invisible to any separation
criterion. -/
def IsPositiveZetaZeroMultiplicity
    (multiplicity : ZetaZeroMultiplicity) : Prop :=
  ∀ ρ, 0 < multiplicity ρ

/-- Every nontrivial zeta zero has a finite, strictly positive analytic
multiplicity.  This removes any simplicity assumption from the zero-sum
interface. -/
theorem analyticZetaZeroMultiplicity_positive :
    IsPositiveZetaZeroMultiplicity analyticZetaZeroMultiplicity := by
  intro ρ
  change 0 < analyticOrderNatAt riemannZeta ρ.1
  have hfinite := analyticOrderAt_riemannZeta_nontrivialZero_ne_top ρ
  have horder : analyticOrderAt riemannZeta ρ.1 ≠ 0 :=
    analyticOrderAt_ne_zero.mpr
      ⟨analyticAt_riemannZeta_nontrivialZero ρ, ρ.2.1⟩
  apply Nat.pos_of_ne_zero
  intro hzero
  have hcast := Nat.cast_analyticOrderNatAt hfinite
  rw [hzero, Nat.cast_zero] at hcast
  exact horder hcast.symm

@[simp]
theorem analyticZetaZeroMultiplicity_conjugate
    (ρ : NontrivialZetaZero) :
    analyticZetaZeroMultiplicity (NontrivialZetaZero.conjugate ρ) =
      analyticZetaZeroMultiplicity ρ := by
  unfold analyticZetaZeroMultiplicity analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_conjugate]

@[simp]
theorem analyticZetaZeroMultiplicity_functionalPartner
    (ρ : NontrivialZetaZero) :
    analyticZetaZeroMultiplicity
        (NontrivialZetaZero.functionalPartner ρ) =
      analyticZetaZeroMultiplicity ρ := by
  unfold analyticZetaZeroMultiplicity analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_functionalPartner]

@[simp]
theorem analyticZetaZeroMultiplicity_conjugatePartner
    (ρ : NontrivialZetaZero) :
    analyticZetaZeroMultiplicity
        (NontrivialZetaZero.conjugatePartner ρ) =
      analyticZetaZeroMultiplicity ρ := by
  simp [NontrivialZetaZero.conjugatePartner]

/-- A zero together with one of its multiplicity slots.  Summing over this
type counts repeated zeros correctly without assuming that all zeta zeros
are simple. -/
abbrev NontrivialZetaZeroOccurrence
    (multiplicity : ZetaZeroMultiplicity) :=
  Σ ρ : NontrivialZetaZero, Fin (multiplicity ρ)

/-- One entire translated-Gaussian summand in the rotated spectral
coordinate. -/
def zetaGaussianZeroSummand
    (multiplicity : ZetaZeroMultiplicity) (ε t : ℝ)
    (occurrence : NontrivialZetaZeroOccurrence multiplicity) : ℂ :=
  complexTranslatedGaussian ε t
    (zetaSpectralCoordinate occurrence.1.1)

/-- The same zero-side term after its finite multiplicity fiber has been
summed.  This indexing by distinct zeros is convenient for separating one
critical-reflection packet from the rest of the divisor. -/
def zetaGaussianDistinctZeroSummand
    (multiplicity : ZetaZeroMultiplicity) (ε t : ℝ)
    (ρ : NontrivialZetaZero) : ℂ :=
  (multiplicity ρ : ℂ) *
    complexTranslatedGaussian ε t (zetaSpectralCoordinate ρ.1)

/-- Real part of a multiplicity-weighted distinct-zero summand. -/
theorem zetaGaussianDistinctZeroSummand_re
    (multiplicity : ZetaZeroMultiplicity) (ε t : ℝ)
    (ρ : NontrivialZetaZero) :
    (zetaGaussianDistinctZeroSummand multiplicity ε t ρ).re =
      (multiplicity ρ : ℝ) * offAxisSingleContribution ε t
        (zetaSpectralCoordinate ρ.1).re
        (zetaSpectralCoordinate ρ.1).im := by
  have hz : zetaSpectralCoordinate ρ.1 =
      ((zetaSpectralCoordinate ρ.1).re : ℂ) +
        ((zetaSpectralCoordinate ρ.1).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  unfold zetaGaussianDistinctZeroSummand
  rw [Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  rw [hz,
    complexTranslatedGaussian_re_eq_offAxisSingleContribution]
  simp

/-- Regroup a multiplicity-slot `HasSum` as a `HasSum` over distinct zeros
with natural-number weights. -/
theorem hasSum_zetaGaussianDistinctZeroSummand
    (multiplicity : ZetaZeroMultiplicity) (ε t : ℝ) (q : ℂ)
    (hSum : HasSum (zetaGaussianZeroSummand multiplicity ε t) q) :
    HasSum (zetaGaussianDistinctZeroSummand multiplicity ε t) q := by
  apply hSum.sigma
  intro ρ
  simpa [zetaGaussianZeroSummand, zetaGaussianDistinctZeroSummand,
    nsmul_eq_mul] using
      (hasSum_fintype
        (fun _ : Fin (multiplicity ρ) =>
          complexTranslatedGaussian ε t (zetaSpectralCoordinate ρ.1)))

/-- `Q` represents the Gaussian sum over all nontrivial zeta zeros.  Using
`HasSum`, rather than a bare `tsum`, prevents a nonsummable expression from
silently receiving Mathlib's default value zero. -/
def RepresentsZetaGaussianZeroSum
    (multiplicity : ZetaZeroMultiplicity) (Q : ℝ → ℝ → ℝ) : Prop :=
  ∀ (ε t : ℝ), 0 < ε →
    HasSum (zetaGaussianZeroSummand multiplicity ε t) (Q ε t : ℂ)

/-- A `HasSum` representation over `ℂ` automatically gives absolute
summability of the Gaussian envelopes.  This uses finite dimensionality of
`ℂ` over `ℝ`; it removes the need to import a separate zeta zero-counting
estimate merely to dominate the detector tail. -/
theorem summable_zetaGaussianZeroEnvelope_of_representation
    (multiplicity : ZetaZeroMultiplicity)
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum multiplicity Q)
    (ε t : ℝ) (hε : 0 < ε) :
    Summable fun occurrence : NontrivialZetaZeroOccurrence multiplicity =>
      Real.exp
        (ε * (zetaSpectralCoordinate occurrence.1.1).im ^ 2 -
          ε * ((zetaSpectralCoordinate occurrence.1.1).re - t) ^ 2) := by
  have hsummable := (hRep ε t hε).summable.norm
  simpa only [zetaGaussianZeroSummand,
    norm_complexTranslatedGaussian] using hsummable

/-- The same absolute convergence supplies exactly the relative-envelope
majorant required by fixed-center Gaussian separation, for any prospective
target packet. -/
theorem summable_fixedCenter_relativeEnvelope_of_representation
    (multiplicity : ZetaZeroMultiplicity)
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum multiplicity Q)
    (ε₀ t γ a : ℝ) (hε₀ : 0 < ε₀) :
    Summable fun occurrence : NontrivialZetaZeroOccurrence multiplicity =>
      Real.exp
        (-ε₀ * fixedCenterPacketGap t γ a
          (zetaSpectralCoordinate occurrence.1.1).re
          (zetaSpectralCoordinate occurrence.1.1).im) := by
  have henvelope :=
    summable_zetaGaussianZeroEnvelope_of_representation
      multiplicity Q hRep ε₀ t hε₀
  have hscaled := henvelope.mul_left
    (Real.exp (-ε₀ * offAxisEnvelopeExponent t γ a))
  refine hscaled.congr fun occurrence => ?_
  rw [← Real.exp_add]
  congr 1
  unfold fixedCenterPacketGap offAxisEnvelopeExponent
  ring

/-- Distinct-zero version of the relative-envelope majorant.  Analytic
multiplicity appears as a nonnegative real weight, exactly matching the
weighted individual-point detector. -/
theorem summable_weightedDistinct_fixedCenter_relativeEnvelope_of_representation
    (multiplicity : ZetaZeroMultiplicity)
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum multiplicity Q)
    (ε₀ t γ a : ℝ) (hε₀ : 0 < ε₀) :
    Summable fun ρ : NontrivialZetaZero =>
      (multiplicity ρ : ℝ) * Real.exp
        (-ε₀ * fixedCenterPacketGap t γ a
          (zetaSpectralCoordinate ρ.1).re
          (zetaSpectralCoordinate ρ.1).im) := by
  have hdistinct := hasSum_zetaGaussianDistinctZeroSummand
    multiplicity ε₀ t (Q ε₀ t) (hRep ε₀ t hε₀)
  have habsolute := hdistinct.summable.norm
  have henvelope : Summable fun ρ : NontrivialZetaZero =>
      (multiplicity ρ : ℝ) * Real.exp
        (ε₀ * (zetaSpectralCoordinate ρ.1).im ^ 2 -
          ε₀ * ((zetaSpectralCoordinate ρ.1).re - t) ^ 2) := by
    simpa only [zetaGaussianDistinctZeroSummand, Complex.norm_mul,
      Complex.norm_natCast, norm_complexTranslatedGaussian]
      using habsolute
  have hscaled := henvelope.mul_left
    (Real.exp (-ε₀ * offAxisEnvelopeExponent t γ a))
  refine hscaled.congr fun ρ => ?_
  rw [show -ε₀ * fixedCenterPacketGap t γ a
        (zetaSpectralCoordinate ρ.1).re
        (zetaSpectralCoordinate ρ.1).im =
      -ε₀ * offAxisEnvelopeExponent t γ a +
        (ε₀ * (zetaSpectralCoordinate ρ.1).im ^ 2 -
          ε₀ * ((zetaSpectralCoordinate ρ.1).re - t) ^ 2) by
      unfold fixedCenterPacketGap offAxisEnvelopeExponent
      ring,
    Real.exp_add]
  ring

/-- One summand for the even test
`H_(ε,t) + H_(ε,-t)` used in the exact arithmetic certificates. -/
def zetaSymmetricGaussianZeroSummand
    (multiplicity : ZetaZeroMultiplicity) (ε t : ℝ)
    (occurrence : NontrivialZetaZeroOccurrence multiplicity) : ℂ :=
  complexSymmetricGaussian ε t
    (zetaSpectralCoordinate occurrence.1.1)

/-- The symmetric Gaussian summand after its finite multiplicity fiber has
been summed, indexed by distinct nontrivial zeta zeros. -/
def zetaSymmetricGaussianDistinctZeroSummand
    (multiplicity : ZetaZeroMultiplicity) (ε t : ℝ)
    (ρ : NontrivialZetaZero) : ℂ :=
  (multiplicity ρ : ℂ) *
    complexSymmetricGaussian ε t (zetaSpectralCoordinate ρ.1)

/-- Regroup a multiplicity-slot symmetric Gaussian `HasSum` as a `HasSum`
over distinct zeros with natural-number weights. -/
theorem hasSum_zetaSymmetricGaussianDistinctZeroSummand
    (multiplicity : ZetaZeroMultiplicity) (ε t : ℝ) (q : ℂ)
    (hSum : HasSum
      (zetaSymmetricGaussianZeroSummand multiplicity ε t) q) :
    HasSum
      (zetaSymmetricGaussianDistinctZeroSummand multiplicity ε t) q := by
  apply hSum.sigma
  intro ρ
  simpa [zetaSymmetricGaussianZeroSummand,
    zetaSymmetricGaussianDistinctZeroSummand, nsmul_eq_mul] using
      (hasSum_fintype
        (fun _ : Fin (multiplicity ρ) =>
          complexSymmetricGaussian ε t (zetaSpectralCoordinate ρ.1)))

/-- `G` represents the multiplicity-counted zero sum for the symmetric
Gaussian family actually used by the certificate program. -/
def RepresentsZetaSymmetricGaussianZeroSum
    (multiplicity : ZetaZeroMultiplicity) (G : ℝ → ℝ → ℝ) : Prop :=
  ∀ (ε t : ℝ), 0 < ε →
    HasSum (zetaSymmetricGaussianZeroSummand multiplicity ε t) (G ε t : ℂ)

/-- Positivity for the certified symmetric Gaussian family. -/
def ZetaSymmetricGaussianZeroSumNonnegative
    (G : ℝ → ℝ → ℝ) : Prop :=
  ∀ (ε t : ℝ), 0 < ε → 0 ≤ G ε t

/-- A translated zero-sum representation gives the matching symmetric
representation by adding the values at `t` and `-t`. -/
theorem representsZetaSymmetricGaussianZeroSum_of_translated
    (multiplicity : ZetaZeroMultiplicity)
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum multiplicity Q) :
    RepresentsZetaSymmetricGaussianZeroSum multiplicity
      (fun ε t => Q ε t + Q ε (-t)) := by
  intro ε t hε
  have hsum := (hRep ε t hε).add (hRep ε (-t) hε)
  have hsum' :
      HasSum (zetaSymmetricGaussianZeroSummand multiplicity ε t)
        ((Q ε t : ℂ) + (Q ε (-t) : ℂ)) := by
    refine hsum.congr_fun fun occurrence => ?_
    rfl
  simpa only [Complex.ofReal_add] using hsum'

/-- Positivity for the complete translated-Gaussian family. -/
def ZetaGaussianZeroSumNonnegative (Q : ℝ → ℝ → ℝ) : Prop :=
  ∀ (ε t : ℝ), 0 < ε → 0 ≤ Q ε t

/-! ## The coherent-state kernel behind the scalar Gaussian values -/

/-- If `Q ε t` is the diagonal translated-Gaussian value, this is the
off-diagonal kernel obtained from half-Gaussian factors centered at `t` and
`s`. -/
def gaussianCoherentKernel (Q : ℝ → ℝ → ℝ) (ε t s : ℝ) : ℝ :=
  Real.exp (-ε * (t - s) ^ 2 / 4) * Q ε ((t + s) / 2)

@[simp]
theorem gaussianCoherentKernel_self (Q : ℝ → ℝ → ℝ) (ε t : ℝ) :
    gaussianCoherentKernel Q ε t t = Q ε t := by
  simp [gaussianCoherentKernel]

/-- Positive semidefiniteness on every finite span of half-Gaussian coherent
states.  This is strictly stronger on its face than nonnegativity of the
diagonal `Q ε t`. -/
def GaussianCoherentKernelPositiveSemidefinite
    (Q : ℝ → ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    ∀ (center coefficient : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j,
        coefficient i * coefficient j *
          gaussianCoherentKernel Q ε (center i) (center j)

theorem zetaGaussianZeroSumNonnegative_of_coherentKernelPositiveSemidefinite
    (Q : ℝ → ℝ → ℝ)
    (hPSD : GaussianCoherentKernelPositiveSemidefinite Q) :
    ZetaGaussianZeroSumNonnegative Q := by
  intro ε t hε
  have h := hPSD 1 ε hε (fun _ => t) (fun _ => 1)
  simpa using h

/-- A represented Gaussian diagonal also represents every half-Gaussian
cross term through the midpoint identity. -/
theorem hasSum_complexHalfGaussian_products
    (multiplicity : ZetaZeroMultiplicity)
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum multiplicity Q)
    (ε t s : ℝ) (hε : 0 < ε) :
    HasSum
      (fun occurrence : NontrivialZetaZeroOccurrence multiplicity =>
        complexHalfGaussian ε t
            (zetaSpectralCoordinate occurrence.1.1) *
          complexHalfGaussian ε s
            (zetaSpectralCoordinate occurrence.1.1))
      (gaussianCoherentKernel Q ε t s : ℂ) := by
  have h := (hRep ε ((t + s) / 2) hε).mul_left
    (Real.exp (-ε * (t - s) ^ 2 / 4) : ℂ)
  have h' :
      HasSum
        (fun occurrence : NontrivialZetaZeroOccurrence multiplicity =>
          complexHalfGaussian ε t
              (zetaSpectralCoordinate occurrence.1.1) *
            complexHalfGaussian ε s
              (zetaSpectralCoordinate occurrence.1.1))
        ((Real.exp (-ε * (t - s) ^ 2 / 4) : ℂ) *
          (Q ε ((t + s) / 2) : ℂ)) := by
    refine h.congr_fun fun occurrence => ?_
    rw [zetaGaussianZeroSummand]
    exact complexHalfGaussian_mul_complexHalfGaussian ε t s
      (zetaSpectralCoordinate occurrence.1.1)
  simpa only [gaussianCoherentKernel, Complex.ofReal_mul] using h'

lemma zetaSpectralCoordinate_real_of_riemannHypothesis
    (hRH : RiemannHypothesis) (ρ : NontrivialZetaZero) :
    zetaSpectralCoordinate ρ.1 = ((zetaSpectralCoordinate ρ.1).re : ℝ) := by
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    exact (zetaSpectralCoordinate_im_eq_zero_iff ρ.1).2
      (hRH ρ.1 ρ.2.1 ρ.2.2.1 ρ.2.2.2)

/-- The easy direction of the Gaussian criterion: RH makes every zero-side
Gaussian term positive. -/
theorem zetaGaussianZeroSumNonnegative_of_riemannHypothesis
    (multiplicity : ZetaZeroMultiplicity)
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum multiplicity Q)
    (hRH : RiemannHypothesis) :
    ZetaGaussianZeroSumNonnegative Q := by
  intro ε t hε
  have hsum := Complex.hasSum_re (hRep ε t hε)
  apply hsum.nonneg
  intro occurrence
  rw [zetaGaussianZeroSummand,
    zetaSpectralCoordinate_real_of_riemannHypothesis hRH occurrence.1,
    complexTranslatedGaussian_ofReal]
  exact (Real.exp_pos _).le

/-- RH also makes every summand of the symmetric Gaussian family positive.
This is the easy direction matching the exact arithmetic certificates. -/
theorem zetaSymmetricGaussianZeroSumNonnegative_of_riemannHypothesis
    (multiplicity : ZetaZeroMultiplicity)
    (G : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaSymmetricGaussianZeroSum multiplicity G)
    (hRH : RiemannHypothesis) :
    ZetaSymmetricGaussianZeroSumNonnegative G := by
  intro ε t hε
  have hsum := Complex.hasSum_re (hRep ε t hε)
  apply hsum.nonneg
  intro occurrence
  rw [zetaSymmetricGaussianZeroSummand,
    zetaSpectralCoordinate_real_of_riemannHypothesis hRH occurrence.1,
    complexSymmetricGaussian_ofReal]
  exact (symmetricGaussian_pos ε t _).le

/-- Under RH the full coherent-state kernel, not just its diagonal, is
positive semidefinite.  The proof expands a finite quadratic form as a sum of
real squares over the zero divisor. -/
theorem gaussianCoherentKernelPositiveSemidefinite_of_riemannHypothesis
    (multiplicity : ZetaZeroMultiplicity)
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum multiplicity Q)
    (hRH : RiemannHypothesis) :
    GaussianCoherentKernelPositiveSemidefinite Q := by
  intro n ε hε center coefficient
  have hpair (i j : Fin n) :
      HasSum
        (fun occurrence : NontrivialZetaZeroOccurrence multiplicity =>
          ((coefficient i * coefficient j : ℝ) : ℂ) *
            (complexHalfGaussian ε (center i)
                (zetaSpectralCoordinate occurrence.1.1) *
              complexHalfGaussian ε (center j)
                (zetaSpectralCoordinate occurrence.1.1)))
        ((coefficient i * coefficient j *
          gaussianCoherentKernel Q ε (center i) (center j) : ℝ) : ℂ) := by
    have h := (hasSum_complexHalfGaussian_products multiplicity Q hRep ε
      (center i) (center j) hε).mul_left
        ((coefficient i * coefficient j : ℝ) : ℂ)
    simpa only [Complex.ofReal_mul, mul_assoc] using h
  have htotal :
      HasSum
        (fun occurrence : NontrivialZetaZeroOccurrence multiplicity =>
          ∑ i, ∑ j,
            ((coefficient i * coefficient j : ℝ) : ℂ) *
              (complexHalfGaussian ε (center i)
                  (zetaSpectralCoordinate occurrence.1.1) *
                complexHalfGaussian ε (center j)
                  (zetaSpectralCoordinate occurrence.1.1)))
        ((∑ i, ∑ j,
          coefficient i * coefficient j *
            gaussianCoherentKernel Q ε (center i) (center j) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_sum] using
      (hasSum_sum (s := Finset.univ) fun i _ =>
        hasSum_sum (s := Finset.univ) fun j _ => hpair i j)
  have hre := Complex.hasSum_re htotal
  apply hre.nonneg
  intro occurrence
  rw [zetaSpectralCoordinate_real_of_riemannHypothesis hRH occurrence.1]
  simp only [complexHalfGaussian_ofReal, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  let v : Fin n → ℝ := fun i =>
    coefficient i * Real.exp (-(ε / 2) *
      ((zetaSpectralCoordinate occurrence.1.1).re - center i) ^ 2)
  calc
    0 ≤ (∑ i, v i) ^ 2 := sq_nonneg _
    _ = ∑ i, ∑ j,
        coefficient i * coefficient j *
          (Real.exp (-(ε / 2) *
            ((zetaSpectralCoordinate occurrence.1.1).re - center i) ^ 2) *
           Real.exp (-(ε / 2) *
            ((zetaSpectralCoordinate occurrence.1.1).re - center j) ^ 2)) := by
      rw [sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [v]
      ring

/-- The global separation interface.  Its content is that the complete
infinite zeta-zero divisor cannot mask every local off-axis Gaussian
detector.  `GaussianZetaGeometry` proves this proposition. -/
def ZetaGaussianZeroDivisorSeparation : Prop :=
  ∀ (Q : ℝ → ℝ → ℝ),
    RepresentsZetaGaussianZeroSum analyticZetaZeroMultiplicity Q →
    ZetaGaussianZeroSumNonnegative Q →
      ∀ ρ : NontrivialZetaZero, (zetaSpectralCoordinate ρ.1).im = 0

/-- The separation statement in exactly the symmetric normalization used by
the arithmetic certificate family. -/
def ZetaSymmetricGaussianZeroDivisorSeparation : Prop :=
  ∀ (G : ℝ → ℝ → ℝ),
    RepresentsZetaSymmetricGaussianZeroSum analyticZetaZeroMultiplicity G →
    ZetaSymmetricGaussianZeroSumNonnegative G →
      ∀ ρ : NontrivialZetaZero, (zetaSpectralCoordinate ρ.1).im = 0

/-- The analogous, stronger-data separation statement using positivity of
every finite coherent-state Gram matrix.  This is the Gaussian-span version
closest to Weil's quadratic criterion. -/
def ZetaGaussianCoherentKernelSeparation : Prop :=
  ∀ (Q : ℝ → ℝ → ℝ),
    RepresentsZetaGaussianZeroSum analyticZetaZeroMultiplicity Q →
    GaussianCoherentKernelPositiveSemidefinite Q →
      ∀ ρ : NontrivialZetaZero, (zetaSpectralCoordinate ρ.1).im = 0

theorem zetaGaussianCoherentKernelSeparation_of_zeroDivisorSeparation
    (hSeparate : ZetaGaussianZeroDivisorSeparation) :
    ZetaGaussianCoherentKernelSeparation := by
  intro Q hRep hPSD
  exact hSeparate Q hRep
    (zetaGaussianZeroSumNonnegative_of_coherentKernelPositiveSemidefinite Q hPSD)

/-- Once the global separation theorem and the zero-sum representation are
proved, all-Gaussian positivity implies Mathlib's RH. -/
theorem riemannHypothesis_of_zetaGaussianZeroSumNonnegative
    (hSeparate : ZetaGaussianZeroDivisorSeparation)
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum analyticZetaZeroMultiplicity Q)
    (hPos : ZetaGaussianZeroSumNonnegative Q) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_spectralCoordinate_real]
  intro s hs hnontrivial hone
  let ρ : NontrivialZetaZero :=
    ⟨s, hs, hnontrivial, hone⟩
  exact hSeparate Q hRep hPos ρ

/-- Once symmetric zero-divisor separation and the symmetric `HasSum`
representation are proved, the certified all-epsilon inequality implies
Mathlib's RH. -/
theorem riemannHypothesis_of_zetaSymmetricGaussianZeroSumNonnegative
    (hSeparate : ZetaSymmetricGaussianZeroDivisorSeparation)
    (G : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaSymmetricGaussianZeroSum
      analyticZetaZeroMultiplicity G)
    (hPos : ZetaSymmetricGaussianZeroSumNonnegative G) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_spectralCoordinate_real]
  intro s hs hnontrivial hone
  let ρ : NontrivialZetaZero :=
    ⟨s, hs, hnontrivial, hone⟩
  exact hSeparate G hRep hPos ρ

/-- With a represented Gaussian zero sum and the global separation theorem,
Gaussian nonnegativity is equivalent to RH. -/
theorem zetaGaussianZeroSumNonnegative_iff_riemannHypothesis
    (hSeparate : ZetaGaussianZeroDivisorSeparation)
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum analyticZetaZeroMultiplicity Q) :
    ZetaGaussianZeroSumNonnegative Q ↔ RiemannHypothesis := by
  exact ⟨riemannHypothesis_of_zetaGaussianZeroSumNonnegative hSeparate Q hRep,
    zetaGaussianZeroSumNonnegative_of_riemannHypothesis
      analyticZetaZeroMultiplicity Q hRep⟩

/-- Conditional RH equivalence for the symmetric Gaussian values that the
Python and finite Lean certificates target. -/
theorem zetaSymmetricGaussianZeroSumNonnegative_iff_riemannHypothesis
    (hSeparate : ZetaSymmetricGaussianZeroDivisorSeparation)
    (G : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaSymmetricGaussianZeroSum
      analyticZetaZeroMultiplicity G) :
    ZetaSymmetricGaussianZeroSumNonnegative G ↔ RiemannHypothesis := by
  exact ⟨riemannHypothesis_of_zetaSymmetricGaussianZeroSumNonnegative
      hSeparate G hRep,
    zetaSymmetricGaussianZeroSumNonnegative_of_riemannHypothesis
      analyticZetaZeroMultiplicity G hRep⟩

/-- Under coherent-kernel separation, positive semidefiniteness on all finite
Gaussian spans is equivalent to RH. -/
theorem gaussianCoherentKernelPositiveSemidefinite_iff_riemannHypothesis
    (hSeparate : ZetaGaussianCoherentKernelSeparation)
    (Q : ℝ → ℝ → ℝ)
    (hRep : RepresentsZetaGaussianZeroSum analyticZetaZeroMultiplicity Q) :
    GaussianCoherentKernelPositiveSemidefinite Q ↔ RiemannHypothesis := by
  constructor
  · intro hPSD
    rw [riemannHypothesis_iff_spectralCoordinate_real]
    intro s hs hnontrivial hone
    let ρ : NontrivialZetaZero :=
      ⟨s, hs, hnontrivial, hone⟩
    exact hSeparate Q hRep hPSD ρ
  · exact gaussianCoherentKernelPositiveSemidefinite_of_riemannHypothesis
      analyticZetaZeroMultiplicity Q hRep

end

end RiemannGaussian
