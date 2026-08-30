import RiemannGaussian.EtaEnergyFiniteWindowInertia

/-!
# Trace and Frobenius identities for finite eta zero windows

This module translates the finite eta matrix into the scalar quantities used
by rank--trace arguments.  It defines real trace and squared Frobenius mass,
proves the entrywise Frobenius identity, and evaluates the real traces of the
literal on-line, off-line-real, and off-line-imaginary eta blocks.

The on-line trace is a multiplicity-weighted sum of squared feature norms.
The off-line trace is the difference between the corresponding squared real
and imaginary feature coordinates.  The Frobenius mass of the complete
window is an explicit finite sum of squared norms of coherent zero sums.  All
identities retain the actual eta features, genuine spectral windows, and
analytic zero multiplicities; no arithmetic estimate is asserted here.
-/

open Complex
open Matrix Finset
open scoped Classical ComplexConjugate ComplexOrder Matrix

namespace RiemannGaussian

noncomputable section

namespace HermitianInertia

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n]

/-- The real part of the trace of a square matrix. -/
def rtrace (A : Matrix n n 𝕜) : ℝ :=
  RCLike.re A.trace

/-- The squared Frobenius mass `Re tr(Aᴴ A)` of a square matrix. -/
def frobSq (A : Matrix n n 𝕜) : ℝ :=
  RCLike.re (Aᴴ * A).trace

/-- Squared Frobenius mass is the sum of squared entry norms. -/
theorem frobSq_eq_sum_norm_sq_entries (A : Matrix n n 𝕜) :
    frobSq A = ∑ i, ∑ j, ‖A j i‖ ^ 2 := by
  unfold frobSq Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow,
    RCLike.ofReal_re]

/-- Squared Frobenius mass is nonnegative. -/
theorem frobSq_nonneg (A : Matrix n n 𝕜) :
    0 ≤ frobSq A := by
  rw [frobSq_eq_sum_norm_sq_entries]
  positivity

/-- Real trace is additive. -/
theorem rtrace_add (A B : Matrix n n 𝕜) :
    rtrace (A + B) = rtrace A + rtrace B := by
  simp [rtrace, map_add]

/-- Real trace respects subtraction. -/
theorem rtrace_sub (A B : Matrix n n 𝕜) :
    rtrace (A - B) = rtrace A - rtrace B := by
  simp [rtrace, map_sub]

end HermitianInertia

private theorem rtrace_real_smul_vecMulVec
    {n : Type*} [Fintype n] (c : ℝ) (v : n → ℂ)
    (hv : star v = v) :
    HermitianInertia.rtrace
        ((c : ℂ) • Matrix.vecMulVec v v) =
      c * ∑ j, ‖v j‖ ^ 2 := by
  have hdot : v ⬝ᵥ v = ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ) := by
    unfold dotProduct
    push_cast
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hj : starRingEnd ℂ (v j) = v j := by
      have := congrFun hv j
      simpa only [Pi.star_apply, RCLike.star_def] using this
    calc
      v j * v j = starRingEnd ℂ (v j) * v j := by rw [hj]
      _ = (‖v j‖ : ℂ) ^ 2 := by
        rw [RCLike.conj_mul, RCLike.ofReal_eq_complex_ofReal]
  unfold HermitianInertia.rtrace
  rw [Matrix.trace_smul, Matrix.trace_vecMulVec, hdot]
  change ((c : ℂ) * ((∑ j, ‖v j‖ ^ 2 : ℝ) : ℂ)).re = _
  rw [Complex.re_ofReal_mul, Complex.ofReal_re]

private theorem rtrace_finsetSum
    {n α : Type*} [Fintype n] (s : Finset α)
    (f : α → Matrix n n ℂ) :
    HermitianInertia.rtrace (∑ a ∈ s, f a) =
      ∑ a ∈ s, HermitianInertia.rtrace (f a) := by
  simp [HermitianInertia.rtrace, map_sum]

/-! ## Exact traces of the three eta blocks -/

/-- The critical-line eta trace is a multiplicity-weighted sum of squared
norms of the packed eta features. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_eq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T) =
      ∑ rho ∈ spectralCriticalZetaZeroWindow T,
        (analyticZetaZeroMultiplicity rho : ℝ) *
          ∑ j, ‖pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho j‖ ^ 2 := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOnLineBlock
  rw [rtrace_finsetSum]
  refine Finset.sum_congr rfl fun rho hrho ↦ ?_
  have hre : rho.1.re = 1 / 2 :=
    (zetaSpectralCoordinate_im_eq_zero_iff rho.1).1
      (mem_spectralCriticalZetaZeroWindow.mp hrho).2
  have hpartner : NontrivialZetaZero.conjugatePartner rho = rho :=
    conjugatePartner_eq_self_of_re_eq_half rho hre
  have hstar :
      star (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) =
        pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho := by
    rw [← topPrefixFiniteCutoffFamilyFeature_conjugatePartner, hpartner]
  exact rtrace_real_smul_vecMulVec
    (analyticZetaZeroMultiplicity rho : ℝ)
    (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) hstar

/-- The critical-line eta trace is nonnegative. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_nonneg
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    0 ≤ HermitianInertia.rtrace
      (pairedEtaTopPrefixFiniteZeroWindowOnLineBlock cutoff T) := by
  rw [pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_eq]
  positivity

/-- The positive off-line-real eta trace is twice the
multiplicity-weighted squared norm of the real feature coordinates. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_rtrace_eq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T) =
      ∑ rho ∈ spectralUpperZetaZeroWindow T,
        (2 * analyticZetaZeroMultiplicity rho : ℝ) *
          ∑ j, ‖complexVectorReal
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) j‖ ^ 2 := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock
  rw [rtrace_finsetSum]
  refine Finset.sum_congr rfl fun rho _hrho ↦ ?_
  have hscalar :
      (analyticZetaZeroMultiplicity rho : ℂ) * 2 =
        ((2 * analyticZetaZeroMultiplicity rho : ℝ) : ℂ) := by
    norm_cast
    ring
  rw [smul_smul, hscalar]
  exact rtrace_real_smul_vecMulVec
    (2 * analyticZetaZeroMultiplicity rho : ℝ)
    (complexVectorReal
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
    (star_complexVectorReal
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))

/-- The off-line-real eta trace is nonnegative. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_rtrace_nonneg
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    0 ≤ HermitianInertia.rtrace
      (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T) := by
  rw [pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_rtrace_eq]
  positivity

/-- The positive off-line-imaginary eta trace is twice the
multiplicity-weighted squared norm of the imaginary feature coordinates. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_rtrace_eq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T) =
      ∑ rho ∈ spectralUpperZetaZeroWindow T,
        (2 * analyticZetaZeroMultiplicity rho : ℝ) *
          ∑ j, ‖complexVectorImag
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) j‖ ^ 2 := by
  unfold pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock
  rw [rtrace_finsetSum]
  refine Finset.sum_congr rfl fun rho _hrho ↦ ?_
  have hscalar :
      (analyticZetaZeroMultiplicity rho : ℂ) * 2 =
        ((2 * analyticZetaZeroMultiplicity rho : ℝ) : ℂ) := by
    norm_cast
    ring
  rw [smul_smul, hscalar]
  exact rtrace_real_smul_vecMulVec
    (2 * analyticZetaZeroMultiplicity rho : ℝ)
    (complexVectorImag
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))
    (star_complexVectorImag
      (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho))

/-- The off-line-imaginary eta trace is nonnegative. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_rtrace_nonneg
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    0 ≤ HermitianInertia.rtrace
      (pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T) := by
  rw [pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_rtrace_eq]
  positivity

/-- The real trace of the off-line hyperbolic difference is the difference
between its explicit real- and imaginary-coordinate masses. -/
theorem pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_rtrace_eq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock cutoff T -
          pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock cutoff T) =
      (∑ rho ∈ spectralUpperZetaZeroWindow T,
        (2 * analyticZetaZeroMultiplicity rho : ℝ) *
          ∑ j, ‖complexVectorReal
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) j‖ ^ 2) -
      ∑ rho ∈ spectralUpperZetaZeroWindow T,
        (2 * analyticZetaZeroMultiplicity rho : ℝ) *
          ∑ j, ‖complexVectorImag
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) j‖ ^ 2 := by
  rw [HermitianInertia.rtrace_sub,
    pairedEtaTopPrefixFiniteZeroWindowOffLineRealBlock_rtrace_eq,
    pairedEtaTopPrefixFiniteZeroWindowOffLineImagBlock_rtrace_eq]

/-- The complete eta-window trace is the critical-line norm mass plus the
explicit real-minus-imaginary off-line mass. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_rtrace_eq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    HermitianInertia.rtrace
        (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) =
      (∑ rho ∈ spectralCriticalZetaZeroWindow T,
        (analyticZetaZeroMultiplicity rho : ℝ) *
          ∑ j, ‖pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho j‖ ^ 2) +
      ((∑ rho ∈ spectralUpperZetaZeroWindow T,
        (2 * analyticZetaZeroMultiplicity rho : ℝ) *
          ∑ j, ‖complexVectorReal
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) j‖ ^ 2) -
      ∑ rho ∈ spectralUpperZetaZeroWindow T,
        (2 * analyticZetaZeroMultiplicity rho : ℝ) *
          ∑ j, ‖complexVectorImag
            (pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho) j‖ ^ 2) := by
  rw [pairedEtaTopPrefixFiniteZeroWindowBlock_eq_onLine_add_offLineReal_sub_imag
      cutoff hT,
    HermitianInertia.rtrace_add,
    pairedEtaTopPrefixFiniteZeroWindowOnLineBlock_rtrace_eq,
    pairedEtaTopPrefixFiniteZeroWindowOffLineDifference_rtrace_eq]

/-! ## Literal Frobenius mass -/

/-- The complete eta-window Frobenius mass is the entrywise squared norm of
the coherent multiplicity-weighted spectral feature sum. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_eq
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    HermitianInertia.frobSq
        (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) =
      ∑ i, ∑ j, ‖∑ rho ∈ spectralZetaZeroWindow T,
        (analyticZetaZeroMultiplicity rho : ℂ) *
          pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho j *
          pairedEtaTopPrefixFiniteCutoffFamilyFeature cutoff rho i‖ ^ 2 := by
  rw [HermitianInertia.frobSq_eq_sum_norm_sq_entries]
  congr 1
  funext i
  congr 1
  funext j
  congr 1
  unfold pairedEtaTopPrefixFiniteZeroWindowBlock
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    smul_eq_mul, mul_assoc]

/-- The complete finite eta-window Frobenius mass is nonnegative. -/
theorem pairedEtaTopPrefixFiniteZeroWindowBlock_frobSq_nonneg
    {d : Type*} [Fintype d] (cutoff : d → ℕ) (T : ℝ) :
    0 ≤ HermitianInertia.frobSq
      (pairedEtaTopPrefixFiniteZeroWindowBlock cutoff T) :=
  HermitianInertia.frobSq_nonneg _

end

end RiemannGaussian
