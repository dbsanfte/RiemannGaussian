import RiemannGaussian.RiemannXiSuzukiCoefficientWindow

/-!
# The exact bounded-synthesis frontier for Suzuki's zero functions

This file isolates the one uniform Hilbert-space estimate needed to transport
the already proved coefficient-window convergence into boundary `L²`.
Finite coefficient families are represented by `Finsupp`; their synthesis by
the normalized xi-zero functions and their canonical embedding into `ℓ²` are
both honest linear maps.

The Bessel bound below is a proposition, not an assumption or an axiom.  Lean
proves that it is equivalent to the corresponding uniform finite Gram bound
and that any witness forces the genuine Suzuki spectral windows to converge
in boundary `L²`.  Proving that a witness exists remains the mathematical
frontier.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Synthesis of an arbitrary finitely supported scalar family by Suzuki's
normalized real-axis xi-zero functions. -/
def suzukiXiZeroFunctionFiniteSynthesis :
    (NontrivialZetaZero →₀ ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  Finsupp.linearCombination ℂ suzukiRealAxisZeroFunctionLp

/-- The canonical coordinate embedding of a finitely supported family into
the ambient coefficient space `ℓ²`. -/
def suzukiXiFiniteCoefficientEmbedding :
    (NontrivialZetaZero →₀ ℂ) →ₗ[ℂ] ℓ²(NontrivialZetaZero, ℂ) :=
  Finsupp.lsum ℕ (fun rho ↦
    lp.lsingle (𝕜 := ℂ) (E := fun _ : NontrivialZetaZero ↦ ℂ) 2 rho)

/-- The synthesis linear map is the expected finite sum over the support. -/
theorem suzukiXiZeroFunctionFiniteSynthesis_apply
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiZeroFunctionFiniteSynthesis c =
      ∑ rho ∈ c.support, c rho • suzukiRealAxisZeroFunctionLp rho := by
  rfl

/-- The coefficient embedding is the expected finite sum of coordinate
vectors. -/
theorem suzukiXiFiniteCoefficientEmbedding_apply
    (c : NontrivialZetaZero →₀ ℂ) :
    suzukiXiFiniteCoefficientEmbedding c =
      ∑ rho ∈ c.support, lp.single 2 rho (c rho) := by
  rfl

/-- The exact squared norm of the canonical embedding of a finitely supported
coefficient family. -/
theorem norm_sq_suzukiXiFiniteCoefficientEmbedding
    (c : NontrivialZetaZero →₀ ℂ) :
    ‖suzukiXiFiniteCoefficientEmbedding c‖ ^ 2 =
      ∑ rho ∈ c.support, ‖c rho‖ ^ 2 := by
  rw [suzukiXiFiniteCoefficientEmbedding_apply]
  have hnorm := lp.norm_sum_single
    (p := (2 : ℝ≥0∞)) (by norm_num)
    (fun rho ↦ c rho) c.support
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hnorm

/-- The Gram quadratic for an arbitrary finitely supported coefficient
family of normalized xi-zero functions. -/
def suzukiXiZeroFunctionFinsuppGramQuadratic
    (c : NontrivialZetaZero →₀ ℂ) : ℂ :=
  ∑ rho ∈ c.support,
    ∑ sigma ∈ c.support,
      starRingEnd ℂ (c rho) * c sigma *
        suzukiXiZeroFunctionGramEntry rho sigma

/-- The finitely supported Gram quadratic is exactly the inner square of its
boundary `L²` synthesis. -/
theorem inner_suzukiXiZeroFunctionFiniteSynthesis_eq_gramQuadratic
    (c : NontrivialZetaZero →₀ ℂ) :
    inner ℂ (suzukiXiZeroFunctionFiniteSynthesis c)
        (suzukiXiZeroFunctionFiniteSynthesis c) =
      suzukiXiZeroFunctionFinsuppGramQuadratic c := by
  rw [suzukiXiZeroFunctionFiniteSynthesis_apply]
  unfold suzukiXiZeroFunctionFinsuppGramQuadratic
    suzukiXiZeroFunctionGramEntry
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  ring

/-- The real part of the finitely supported Gram quadratic is exactly the
squared boundary norm. -/
theorem suzukiXiZeroFunctionFinsuppGramQuadratic_re
    (c : NontrivialZetaZero →₀ ℂ) :
    (suzukiXiZeroFunctionFinsuppGramQuadratic c).re =
      ‖suzukiXiZeroFunctionFiniteSynthesis c‖ ^ 2 := by
  rw [← inner_suzukiXiZeroFunctionFiniteSynthesis_eq_gramQuadratic]
  exact inner_self_eq_norm_sq (𝕜 := ℂ)
    (suzukiXiZeroFunctionFiniteSynthesis c)

/-- A uniform Bessel bound for Suzuki's normalized xi-zero functions.  This
is the precise open estimate: the declaration merely defines the proposition
and does not assert that it holds. -/
def SuzukiXiZeroFunctionBesselBound (C : ℝ) : Prop :=
  0 < C ∧ ∀ c : NontrivialZetaZero →₀ ℂ,
    ‖suzukiXiZeroFunctionFiniteSynthesis c‖ ≤
      C * ‖suzukiXiFiniteCoefficientEmbedding c‖

/-- The Bessel bound is exactly the corresponding uniform finite Gram
quadratic bound. -/
theorem suzukiXiZeroFunctionBesselBound_iff_gram
    (C : ℝ) :
    SuzukiXiZeroFunctionBesselBound C ↔
      0 < C ∧ ∀ c : NontrivialZetaZero →₀ ℂ,
        (suzukiXiZeroFunctionFinsuppGramQuadratic c).re ≤
          C ^ 2 * ∑ rho ∈ c.support, ‖c rho‖ ^ 2 := by
  constructor
  · rintro ⟨hC, hbound⟩
    refine ⟨hC, ?_⟩
    intro c
    rw [suzukiXiZeroFunctionFinsuppGramQuadratic_re,
      ← norm_sq_suzukiXiFiniteCoefficientEmbedding]
    calc
      ‖suzukiXiZeroFunctionFiniteSynthesis c‖ ^ 2 ≤
          (C * ‖suzukiXiFiniteCoefficientEmbedding c‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg hC.le (norm_nonneg _))).2 (hbound c)
      _ = C ^ 2 * ‖suzukiXiFiniteCoefficientEmbedding c‖ ^ 2 := by
        ring
  · rintro ⟨hC, hgram⟩
    refine ⟨hC, ?_⟩
    intro c
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hC.le (norm_nonneg _))).1
    calc
      ‖suzukiXiZeroFunctionFiniteSynthesis c‖ ^ 2 =
          (suzukiXiZeroFunctionFinsuppGramQuadratic c).re :=
        (suzukiXiZeroFunctionFinsuppGramQuadratic_re c).symm
      _ ≤ C ^ 2 * ∑ rho ∈ c.support, ‖c rho‖ ^ 2 := hgram c
      _ = (C * ‖suzukiXiFiniteCoefficientEmbedding c‖) ^ 2 := by
        rw [← norm_sq_suzukiXiFiniteCoefficientEmbedding]
        ring

/-- A Bessel bound makes finite synthesis Lipschitz with respect to the
canonical `ℓ²` coordinate embedding. -/
theorem norm_sub_suzukiXiZeroFunctionFiniteSynthesis_le
    {C : ℝ} (hC : SuzukiXiZeroFunctionBesselBound C)
    (c d : NontrivialZetaZero →₀ ℂ) :
    ‖suzukiXiZeroFunctionFiniteSynthesis c -
        suzukiXiZeroFunctionFiniteSynthesis d‖ ≤
      C * ‖suzukiXiFiniteCoefficientEmbedding c -
        suzukiXiFiniteCoefficientEmbedding d‖ := by
  simpa only [map_sub] using hC.2 (c - d)

/-- The finitely supported Suzuki coefficient family cut out by one genuine
symmetric spectral window. -/
def riemannXiSuzukiSpectralCoefficientWindowFinsupp
    (t T : ℝ) : NontrivialZetaZero →₀ ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    Finsupp.single rho (zetaSuzukiSpectralCoefficientFeature t rho)

/-- The coefficient embedding of the finitely supported window is literally
the previously constructed `ℓ²` coefficient window. -/
theorem suzukiXiFiniteCoefficientEmbedding_window
    (t T : ℝ) :
    suzukiXiFiniteCoefficientEmbedding
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) =
      riemannXiSuzukiSpectralCoefficientWindowVector t T := by
  simp [riemannXiSuzukiSpectralCoefficientWindowFinsupp,
    suzukiXiFiniteCoefficientEmbedding,
    riemannXiSuzukiSpectralCoefficientWindowVector]

/-- The finite normalized zero-function synthesis whose coefficients are
exactly the coordinates of Suzuki's complete coefficient vector. -/
def suzukiRealAxisNormalizedSignalWindowSynthesisLp
    (t T : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    zetaSuzukiSpectralCoefficientFeature t rho •
      suzukiRealAxisZeroFunctionLp rho

/-- Applying finite synthesis to the window coefficient family gives its
normalized boundary signal. -/
theorem suzukiXiZeroFunctionFiniteSynthesis_window
    (t T : ℝ) :
    suzukiXiZeroFunctionFiniteSynthesis
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) =
      suzukiRealAxisNormalizedSignalWindowSynthesisLp t T := by
  simp [riemannXiSuzukiSpectralCoefficientWindowFinsupp,
    suzukiXiZeroFunctionFiniteSynthesis,
    suzukiRealAxisNormalizedSignalWindowSynthesisLp]

/-- Suzuki's published finite synthesis is the normalized synthesis scaled
by its universal `sqrt(pi)` factor. -/
theorem suzukiRealAxisSignalWindowSynthesisLp_eq_sqrtPi_smul_normalized
    (t T : ℝ) :
    suzukiRealAxisSignalWindowSynthesisLp t T =
      (Real.sqrt Real.pi : ℂ) •
        suzukiRealAxisNormalizedSignalWindowSynthesisLp t T := by
  unfold suzukiRealAxisSignalWindowSynthesisLp
    suzukiRealAxisNormalizedSignalWindowSynthesisLp
  simp_rw [suzukiXiZeroSynthesisCoefficient_eq_sqrtPi_mul_feature,
    Finset.smul_sum, smul_smul]

/-- The literal finite real-axis signal has the same universal scaling from
the normalized coefficient synthesis. -/
theorem suzukiRealAxisSignalWindowLp_eq_sqrtPi_smul_normalized
    (t T : ℝ) :
    suzukiRealAxisSignalWindowLp t T =
      (Real.sqrt Real.pi : ℂ) •
        suzukiRealAxisNormalizedSignalWindowSynthesisLp t T := by
  rw [suzukiRealAxisSignalWindowLp_eq_synthesis,
    suzukiRealAxisSignalWindowSynthesisLp_eq_sqrtPi_smul_normalized]

/-- Under a Bessel bound, differences of normalized genuine spectral windows
are controlled by the already convergent coefficient windows. -/
theorem norm_sub_suzukiRealAxisNormalizedSignalWindowSynthesisLp_le
    {C : ℝ} (hC : SuzukiXiZeroFunctionBesselBound C)
    (t T U : ℝ) :
    ‖suzukiRealAxisNormalizedSignalWindowSynthesisLp t T -
        suzukiRealAxisNormalizedSignalWindowSynthesisLp t U‖ ≤
      C * ‖riemannXiSuzukiSpectralCoefficientWindowVector t T -
        riemannXiSuzukiSpectralCoefficientWindowVector t U‖ := by
  simpa only [suzukiXiZeroFunctionFiniteSynthesis_window,
    suzukiXiFiniteCoefficientEmbedding_window] using
      norm_sub_suzukiXiZeroFunctionFiniteSynthesis_le hC
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T)
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t U)

/-- A Bessel bound makes the normalized genuine Suzuki windows a Cauchy net
in boundary `L²`. -/
theorem cauchySeq_suzukiRealAxisNormalizedSignalWindowSynthesisLp
    {C : ℝ} (hC : SuzukiXiZeroFunctionBesselBound C)
    (t : ℝ) :
    CauchySeq (fun T : ℝ ↦
      suzukiRealAxisNormalizedSignalWindowSynthesisLp t T) := by
  have hcoeff : CauchySeq (fun T : ℝ ↦
      riemannXiSuzukiSpectralCoefficientWindowVector t T) :=
    (tendsto_riemannXiSuzukiSpectralCoefficientWindowVector t).cauchySeq
  rw [Metric.cauchySeq_iff] at hcoeff ⊢
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hcoeff (epsilon / C) (div_pos hepsilon hC.1)
  refine ⟨N, ?_⟩
  intro T hT U hU
  rw [dist_eq_norm]
  have hdist := hN T hT U hU
  rw [dist_eq_norm] at hdist
  calc
    ‖suzukiRealAxisNormalizedSignalWindowSynthesisLp t T -
        suzukiRealAxisNormalizedSignalWindowSynthesisLp t U‖ ≤
        C * ‖riemannXiSuzukiSpectralCoefficientWindowVector t T -
          riemannXiSuzukiSpectralCoefficientWindowVector t U‖ :=
      norm_sub_suzukiRealAxisNormalizedSignalWindowSynthesisLp_le hC t T U
    _ < C * (epsilon / C) := mul_lt_mul_of_pos_left hdist hC.1
    _ = epsilon := by field_simp [ne_of_gt hC.1]

/-- The exact bounded-synthesis estimate therefore gives a boundary `L²`
limit for the normalized genuine Suzuki windows. -/
theorem exists_tendsto_suzukiRealAxisNormalizedSignalWindowSynthesisLp
    {C : ℝ} (hC : SuzukiXiZeroFunctionBesselBound C)
    (t : ℝ) :
    ∃ signal : Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (fun T : ℝ ↦
        suzukiRealAxisNormalizedSignalWindowSynthesisLp t T) atTop
          (nhds signal) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_suzukiRealAxisNormalizedSignalWindowSynthesisLp hC t)

/-- Every normalized boundary limit supplied by the Bessel estimate inherits
the sharp bound by `C` times the norm of Suzuki's complete coefficient
vector. -/
theorem norm_suzukiRealAxisNormalizedSignal_limit_le
    {C : ℝ} (hC : SuzukiXiZeroFunctionBesselBound C)
    {t : ℝ} {signal : Lp ℂ 2 (volume : Measure ℝ)}
    (hsignal : Tendsto (fun T : ℝ ↦
      suzukiRealAxisNormalizedSignalWindowSynthesisLp t T) atTop
        (nhds signal)) :
    ‖signal‖ ≤ C * ‖riemannXiSuzukiSpectralCoefficientVector t‖ := by
  apply le_of_tendsto_of_tendsto hsignal.norm
    ((tendsto_riemannXiSuzukiSpectralCoefficientWindowVector t).norm.const_mul C)
  exact Eventually.of_forall fun T ↦ by
    simpa only [suzukiXiZeroFunctionFiniteSynthesis_window,
      suzukiXiFiniteCoefficientEmbedding_window] using
        hC.2 (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T)

/-- The same bound gives a boundary `L²` limit for Suzuki's literal published
finite spectral signals. -/
theorem exists_tendsto_suzukiRealAxisSignalWindowLp_of_besselBound
    {C : ℝ} (hC : SuzukiXiZeroFunctionBesselBound C)
    (t : ℝ) :
    ∃ signal : Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (fun T : ℝ ↦ suzukiRealAxisSignalWindowLp t T) atTop
        (nhds signal) := by
  obtain ⟨signal, hsignal⟩ :=
    exists_tendsto_suzukiRealAxisNormalizedSignalWindowSynthesisLp hC t
  refine ⟨(Real.sqrt Real.pi : ℂ) • signal, ?_⟩
  have hscaled :
      Tendsto (fun T : ℝ ↦
        (Real.sqrt Real.pi : ℂ) •
          suzukiRealAxisNormalizedSignalWindowSynthesisLp t T) atTop
        (nhds ((Real.sqrt Real.pi : ℂ) • signal)) :=
    tendsto_const_nhds.smul hsignal
  simpa only [← suzukiRealAxisSignalWindowLp_eq_sqrtPi_smul_normalized]
    using hscaled

/-- The convergent published signal can be chosen with the corresponding
quantitative norm bound, including Suzuki's universal `sqrt(pi)` factor. -/
theorem exists_tendsto_suzukiRealAxisSignalWindowLp_and_norm_le_of_besselBound
    {C : ℝ} (hC : SuzukiXiZeroFunctionBesselBound C)
    (t : ℝ) :
    ∃ signal : Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (fun T : ℝ ↦ suzukiRealAxisSignalWindowLp t T) atTop
          (nhds signal) ∧
        ‖signal‖ ≤ Real.sqrt Real.pi * C *
          ‖riemannXiSuzukiSpectralCoefficientVector t‖ := by
  obtain ⟨normalized, hnormalized⟩ :=
    exists_tendsto_suzukiRealAxisNormalizedSignalWindowSynthesisLp hC t
  refine ⟨(Real.sqrt Real.pi : ℂ) • normalized, ?_, ?_⟩
  · have hscaled :
        Tendsto (fun T : ℝ ↦
          (Real.sqrt Real.pi : ℂ) •
            suzukiRealAxisNormalizedSignalWindowSynthesisLp t T) atTop
          (nhds ((Real.sqrt Real.pi : ℂ) • normalized)) :=
      tendsto_const_nhds.smul hnormalized
    simpa only [← suzukiRealAxisSignalWindowLp_eq_sqrtPi_smul_normalized]
      using hscaled
  · have hnorm :=
      norm_suzukiRealAxisNormalizedSignal_limit_le hC hnormalized
    calc
      ‖(Real.sqrt Real.pi : ℂ) • normalized‖ =
          Real.sqrt Real.pi * ‖normalized‖ := by
        rw [norm_smul]
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt Real.pi *
          (C * ‖riemannXiSuzukiSpectralCoefficientVector t‖) :=
        mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
      _ = Real.sqrt Real.pi * C *
          ‖riemannXiSuzukiSpectralCoefficientVector t‖ := by ring

end

end RiemannGaussian
