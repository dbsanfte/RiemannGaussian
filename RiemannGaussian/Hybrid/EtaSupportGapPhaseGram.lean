import RiemannGaussian.EtaSupportGapGaussian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Mixed phase Gram matrices on the actual eta support and gaps

The entries retain the complex two-time phase products before identifying
their integrals with the real continuous eta heat transfer. Positivity comes
from the literal nonnegative support/gap weight, with all entries integrable.
-/

open Complex Filter MeasureTheory Set Topology Matrix
open scoped Classical ENNReal BigOperators ComplexOrder

namespace RiemannGaussian

noncomputable section

/-- The unit complex phase attached to an ordered pair of times. -/
def pairedEtaHeatPhaseUnit (phi : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  Complex.exp (((phi p.2 - phi p.1 : ℝ) : ℂ) * Complex.I)

/-- Every real phase has unit modulus on each ordered time pair. -/
theorem norm_pairedEtaHeatPhaseUnit (phi : ℝ → ℝ) (p : ℝ × ℝ) :
    ‖pairedEtaHeatPhaseUnit phi p‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- Measurability of the ordered unit phase for a measurable real phase. -/
theorem measurable_pairedEtaHeatPhaseUnit {phi : ℝ → ℝ} (hphi : Measurable phi) :
    Measurable (pairedEtaHeatPhaseUnit phi) := by
  exact Complex.continuous_exp.measurable.comp
    (((hphi.comp measurable_snd).sub (hphi.comp measurable_fst)).complex_ofReal.mul_const Complex.I)

/-- Swapping the two times conjugates the phase instead of discarding it. -/
theorem pairedEtaHeatPhaseUnit_swap (phi : ℝ → ℝ) (p : ℝ × ℝ) :
    pairedEtaHeatPhaseUnit phi p.swap = star (pairedEtaHeatPhaseUnit phi p) := by
  rcases p with ⟨t, u⟩
  simp only [pairedEtaHeatPhaseUnit, Complex.star_def, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  simp only [Complex.ofReal_sub, Prod.swap_prod_mk]
  ring

/-- The mixed phase product is exactly the unit phase of the difference. -/
theorem pairedEtaHeatPhaseUnit_mixed (phi psi : ℝ → ℝ) (p : ℝ × ℝ) :
    star (pairedEtaHeatPhaseUnit phi p) * pairedEtaHeatPhaseUnit psi p =
      pairedEtaHeatPhaseUnit (fun t ↦ psi t - phi t) p := by
  simp only [pairedEtaHeatPhaseUnit, Complex.star_def, ← Complex.exp_conj,
    map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_sub]
  ring

/-- The positive heat weight is integrable at every positive tilt and width. -/
theorem integrable_pairedEtaSupportGapHeatWeight {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) :
    Integrable (pairedEtaSupportGapHeatWeight sigma h)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hfun : pairedEtaSupportGapHeatKernel sigma h (fun _ ↦ 0) =
      pairedEtaSupportGapHeatWeight sigma h := by
    funext p
    simp [pairedEtaSupportGapHeatKernel]
  rw [← hfun]
  exact integrable_pairedEtaSupportGapHeatKernel hsigma hh measurable_const

/-- The full ordered mixed kernel, before integration or taking a real part. -/
def pairedEtaSupportGapComplexKernel (sigma h : ℝ) (phi psi : ℝ → ℝ)
    (p : ℝ × ℝ) : ℂ :=
  (pairedEtaSupportGapHeatWeight sigma h p : ℂ) *
    star (pairedEtaHeatPhaseUnit phi p) * pairedEtaHeatPhaseUnit psi p

/-- The norm of each mixed kernel is exactly the common positive weight. -/
theorem norm_pairedEtaSupportGapComplexKernel {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (phi psi : ℝ → ℝ) (p : ℝ × ℝ) :
    ‖pairedEtaSupportGapComplexKernel sigma h phi psi p‖ =
      pairedEtaSupportGapHeatWeight sigma h p := by
  simp only [pairedEtaSupportGapComplexKernel, norm_mul, norm_star,
    norm_pairedEtaHeatPhaseUnit, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pairedEtaSupportGapHeatWeight_nonneg hh sigma p)]

/-- Every mixed entry is genuinely integrable, without bounds on the real phases. -/
theorem integrable_pairedEtaSupportGapComplexKernel {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) {phi psi : ℝ → ℝ}
    (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (pairedEtaSupportGapComplexKernel sigma h phi psi)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  apply (integrable_pairedEtaSupportGapHeatWeight hsigma hh).mono'
  · exact (((measurable_pairedEtaSupportGapHeatWeight sigma h).complex_ofReal.mul
      (Complex.continuous_conj.measurable.comp (measurable_pairedEtaHeatPhaseUnit hphi))).mul
      (measurable_pairedEtaHeatPhaseUnit hpsi)).aestronglyMeasurable
  · exact Eventually.of_forall fun p ↦
      (norm_pairedEtaSupportGapComplexKernel hh sigma phi psi p).le

/-- The real part of the ordered mixed kernel is the exact difference-phase
kernel, with the support/gap indicator unchanged. -/
theorem pairedEtaSupportGapComplexKernel_re (sigma h : ℝ) (phi psi : ℝ → ℝ)
    (p : ℝ × ℝ) :
    (pairedEtaSupportGapComplexKernel sigma h phi psi p).re =
      pairedEtaSupportGapHeatKernel sigma h (fun t ↦ psi t - phi t) p := by
  rw [pairedEtaSupportGapComplexKernel, mul_assoc, pairedEtaHeatPhaseUnit_mixed]
  simp only [pairedEtaHeatPhaseUnit, pairedEtaSupportGapHeatKernel, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.exp_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
    mul_one, Real.exp_zero, one_mul]

/-- Time reversal conjugates the complete mixed kernel. -/
theorem pairedEtaSupportGapComplexKernel_swap (sigma h : ℝ) (phi psi : ℝ → ℝ)
    (p : ℝ × ℝ) :
    pairedEtaSupportGapComplexKernel sigma h phi psi p.swap =
      star (pairedEtaSupportGapComplexKernel sigma h phi psi p) := by
  unfold pairedEtaSupportGapComplexKernel
  rw [pairedEtaHeatPhaseUnit_swap, pairedEtaHeatPhaseUnit_swap]
  have hw : pairedEtaSupportGapHeatWeight sigma h p.swap =
      pairedEtaSupportGapHeatWeight sigma h p :=
    pairedEtaSupportGapHeatWeight_swap sigma h p.2 p.1
  rw [hw]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

/-- The complex mixed integral is real by time reversal, and equals the
literal difference-phase support/gap heat transfer. -/
theorem integral_pairedEtaSupportGapComplexKernel {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) {phi psi : ℝ → ℝ}
    (hphi : Measurable phi) (hpsi : Measurable psi) :
    (∫ p, pairedEtaSupportGapComplexKernel sigma h phi psi p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      (pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ psi t - phi t) : ℂ) := by
  let F := pairedEtaSupportGapComplexKernel sigma h phi psi
  let mu : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))
  have hi : Integrable F mu := integrable_pairedEtaSupportGapComplexKernel hsigma hh hphi hpsi
  have hs : star (∫ p, F p ∂mu) = ∫ p, F p ∂mu := by
    rw [Complex.star_def, ← integral_conj]
    have hswap : (fun p ↦ star (F p)) = (fun p ↦ F p.swap) := by
      funext p
      exact (pairedEtaSupportGapComplexKernel_swap sigma h phi psi p).symm
    change (∫ p, star (F p) ∂mu) = _
    rw [hswap]
    exact integral_prod_swap F
  apply Complex.ext
  · have hre : (∫ p, F p ∂mu).re = ∫ p, (F p).re ∂mu := (integral_re hi).symm
    change (∫ p, F p ∂mu).re = _
    rw [hre]
    simp only [F, pairedEtaSupportGapComplexKernel_re, Complex.ofReal_re]
    rfl
  · have him := congrArg Complex.im hs
    simp only [Complex.star_def, Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

/-- The literal mixed phase matrix on any finite family of real phases. -/
def pairedEtaSupportGapPhaseGram {ι : Type*} (sigma h : ℝ) (phi : ι → ℝ → ℝ) :
    Matrix ι ι ℝ :=
  fun i j ↦ pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ phi j t - phi i t)

/-- The real cosine Gram quadratic form at one collection of phases. -/
def finiteCosinePhaseEnergy {ι : Type*} [Fintype ι] (theta c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * Real.cos (theta j - theta i)

/-- The cosine quadratic form retains both its cosine and sine squares. -/
theorem finiteCosinePhaseEnergy_eq_squares {ι : Type*} [Fintype ι] (theta c : ι → ℝ) :
    finiteCosinePhaseEnergy theta c =
      (∑ i, c i * Real.cos (theta i)) ^ 2 + (∑ i, c i * Real.sin (theta i)) ^ 2 := by
  simp only [finiteCosinePhaseEnergy, Real.cos_sub, mul_add, Finset.sum_add_distrib,
    pow_two, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    apply Finset.sum_congr rfl <;> intro j hj <;> ring

/-- A cosine phase Gram is nonnegative for every real coefficient vector. -/
theorem finiteCosinePhaseEnergy_nonneg {ι : Type*} [Fintype ι] (theta c : ι → ℝ) :
    0 ≤ finiteCosinePhaseEnergy theta c := by
  rw [finiteCosinePhaseEnergy_eq_squares]
  positivity

/-- The real quadratic form of a finite matrix, with both indices explicit. -/
def finiteRealMatrixEnergy {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (c : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * M i j

/-- Identification with the standard matrix quadratic form. -/
theorem finiteRealMatrixEnergy_eq_dotProduct {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (c : ι → ℝ) :
    finiteRealMatrixEnergy M c = star c ⬝ᵥ (M *ᵥ c) := by
  simp only [finiteRealMatrixEnergy, dotProduct, mulVec, Pi.star_apply, star_trivial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual mixed phase matrix is symmetric. No phase averaging is used. -/
theorem pairedEtaSupportGapPhaseGram_isHermitian {ι : Type*}
    (sigma h : ℝ) (phi : ι → ℝ → ℝ) :
    (pairedEtaSupportGapPhaseGram sigma h phi).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  simp only [star_trivial, pairedEtaSupportGapPhaseGram,
    pairedEtaSupportGapGaussianLeakage, pairedEtaSupportGapHeatKernel]
  apply integral_congr_ae
  filter_upwards with p
  rw [show phi i p.2 - phi j p.2 - (phi i p.1 - phi j p.1) =
      -(phi j p.2 - phi i p.2 - (phi j p.1 - phi i p.1)) by ring,
    Real.cos_neg]

/-- The finite mixed quadratic form is the integral of the full positive
phase energy against the literal eta support/gap heat weight. -/
theorem pairedEtaSupportGapPhaseGram_energy_eq_integral {ι : Type*} [Fintype ι]
    {sigma h : ℝ} (hsigma : 0 < sigma) (hh : 0 < h)
    {phi : ι → ℝ → ℝ} (hphi : ∀ i, Measurable (phi i)) (c : ι → ℝ) :
    finiteRealMatrixEnergy (pairedEtaSupportGapPhaseGram sigma h phi) c =
      ∫ p, pairedEtaSupportGapHeatWeight sigma h p *
        finiteCosinePhaseEnergy (fun i ↦ phi i p.2 - phi i p.1) c
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let mu : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))
  let F : ι → ι → ℝ × ℝ → ℝ := fun i j p ↦
    (c i * c j) * pairedEtaSupportGapHeatKernel sigma h (fun t ↦ phi j t - phi i t) p
  have hi : ∀ i j, Integrable (F i j) mu := fun i j ↦
    (integrable_pairedEtaSupportGapHeatKernel hsigma hh ((hphi j).sub (hphi i))).const_mul _
  have hint : (∫ p, ∑ i, ∑ j, F i j p ∂mu) =
      ∑ i, ∑ j, ∫ p, F i j p ∂mu := by
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j)]
    apply Finset.sum_congr rfl
    intro i hi'
    exact integral_finsetSum _ (fun j _ ↦ hi i j)
  calc
    finiteRealMatrixEnergy (pairedEtaSupportGapPhaseGram sigma h phi) c =
        ∑ i, ∑ j, ∫ p, F i j p ∂mu := by
      simp only [F, integral_const_mul]
      rfl
    _ = ∫ p, ∑ i, ∑ j, F i j p ∂mu := hint.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      simp only [F, pairedEtaSupportGapHeatKernel, finiteCosinePhaseEnergy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi'
      apply Finset.sum_congr rfl
      intro j hj'
      rw [show phi j p.2 - phi i p.2 - (phi j p.1 - phi i p.1) =
          (phi j p.2 - phi j p.1) - (phi i p.2 - phi i p.1) by ring]
      ring

/-- Positive semidefiniteness of the finite Gram on the actual continuous
eta support, for arbitrary measurable real phases. -/
theorem pairedEtaSupportGapPhaseGram_posSemidef {ι : Type*} [Fintype ι]
    {sigma h : ℝ} (hsigma : 0 < sigma) (hh : 0 < h)
    {phi : ι → ℝ → ℝ} (hphi : ∀ i, Measurable (phi i)) :
    (pairedEtaSupportGapPhaseGram sigma h phi).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (pairedEtaSupportGapPhaseGram_isHermitian sigma h phi)
  intro c
  rw [← finiteRealMatrixEnergy_eq_dotProduct,
    pairedEtaSupportGapPhaseGram_energy_eq_integral hsigma hh hphi]
  exact integral_nonneg fun p ↦ mul_nonneg (pairedEtaSupportGapHeatWeight_nonneg hh sigma p)
    (finiteCosinePhaseEnergy_nonneg _ c)

/-- For a real matrix, the real part of the complex quadratic form is the
sum of the energies of the real and imaginary coefficient vectors. -/
theorem finiteRealMatrixEnergy_complex_re {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (c : ι → ℂ) :
    (star c ⬝ᵥ (M.map Complex.ofReal *ᵥ c)).re =
      finiteRealMatrixEnergy M (fun i ↦ (c i).re) +
      finiteRealMatrixEnergy M (fun i ↦ (c i).im) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum,
    Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Matrix.map_apply, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, sub_neg_eq_add, neg_mul,
    finiteRealMatrixEnergy, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A real positive semidefinite matrix remains positive semidefinite on
complex coefficient vectors under the literal real-to-complex embedding. -/
theorem posSemidef_complex_ofReal {ι : Type*} [Fintype ι]
    {M : Matrix ι ι ℝ} (hM : M.PosSemidef) : (M.map Complex.ofReal).PosSemidef := by
  have hH : (M.map Complex.ofReal).IsHermitian := hM.isHermitian.map _ (by
    intro x
    simp only [star_trivial, Complex.star_def, Complex.conj_ofReal])
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro c
  apply RCLike.nonneg_iff.mpr
  constructor
  · change 0 ≤ (star c ⬝ᵥ (M.map Complex.ofReal *ᵥ c)).re
    rw [finiteRealMatrixEnergy_complex_re, finiteRealMatrixEnergy_eq_dotProduct,
      finiteRealMatrixEnergy_eq_dotProduct]
    exact add_nonneg (hM.dotProduct_mulVec_nonneg _) (hM.dotProduct_mulVec_nonneg _)
  · exact hH.im_star_dotProduct_mulVec_self c

/-- The complex finite matrix is positive semidefinite for the full family
of measurable phase probes. -/
theorem pairedEtaSupportGapPhaseGram_complex_posSemidef {ι : Type*} [Fintype ι]
    {sigma h : ℝ} (hsigma : 0 < sigma) (hh : 0 < h)
    {phi : ι → ℝ → ℝ} (hphi : ∀ i, Measurable (phi i)) :
    ((pairedEtaSupportGapPhaseGram sigma h phi).map Complex.ofReal).PosSemidef :=
  posSemidef_complex_ofReal (pairedEtaSupportGapPhaseGram_posSemidef hsigma hh hphi)

/-- The entire complex quadratic form is the integral of an absolute
square, retaining all mixed products of the ordered phase features. -/
theorem pairedEtaSupportGapPhaseGram_complex_energy_eq_integral {ι : Type*} [Fintype ι]
    {sigma h : ℝ} (hsigma : 0 < sigma) (hh : 0 < h)
    {phi : ι → ℝ → ℝ} (hphi : ∀ i, Measurable (phi i)) (c : ι → ℂ) :
    star c ⬝ᵥ ((pairedEtaSupportGapPhaseGram sigma h phi).map Complex.ofReal *ᵥ c) =
      ((∫ p, pairedEtaSupportGapHeatWeight sigma h p *
        Complex.normSq (∑ i, c i * pairedEtaHeatPhaseUnit (phi i) p)
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) : ℝ) := by
  let mu : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))
  let F : ι → ι → ℝ × ℝ → ℂ := fun i j p ↦
    star (c i) * pairedEtaSupportGapComplexKernel sigma h (phi i) (phi j) p * c j
  have hi : ∀ i j, Integrable (F i j) mu := fun i j ↦
    ((integrable_pairedEtaSupportGapComplexKernel hsigma hh (hphi i) (hphi j)).const_mul _).mul_const _
  have hent : ∀ i j, (∫ p, F i j p ∂mu) =
      star (c i) * (pairedEtaSupportGapPhaseGram sigma h phi i j : ℂ) * c j := by
    intro i j
    dsimp [F]
    rw [integral_mul_const, integral_const_mul,
      integral_pairedEtaSupportGapComplexKernel hsigma hh (hphi i) (hphi j)]
    rfl
  have hsum : (∫ p, ∑ i, ∑ j, F i j p ∂mu) = ∑ i, ∑ j, ∫ p, F i j p ∂mu := by
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j)]
    apply Finset.sum_congr rfl
    intro i hi'
    exact integral_finsetSum _ (fun j _ ↦ hi i j)
  calc
    star c ⬝ᵥ ((pairedEtaSupportGapPhaseGram sigma h phi).map Complex.ofReal *ᵥ c) =
        ∑ i, ∑ j, ∫ p, F i j p ∂mu := by
      simp only [dotProduct, mulVec, Pi.star_apply, Matrix.map_apply, Finset.mul_sum, hent]
      apply Finset.sum_congr rfl
      intro i hi'
      apply Finset.sum_congr rfl
      intro j hj'
      ring
    _ = ∫ p, ∑ i, ∑ j, F i j p ∂mu := hsum.symm
    _ = ∫ p, ((pairedEtaSupportGapHeatWeight sigma h p *
        Complex.normSq (∑ i, c i * pairedEtaHeatPhaseUnit (phi i) p) : ℝ) : ℂ) ∂mu := by
      apply integral_congr_ae
      filter_upwards with p
      rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
      simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, F,
        pairedEtaSupportGapComplexKernel, Complex.star_def]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi'
      apply Finset.sum_congr rfl
      intro j hj'
      ring
    _ = _ := integral_complex_ofReal

end

end RiemannGaussian
