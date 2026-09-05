import RiemannGaussian.Hybrid.EtaSupportGapPhaseGram
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Quantitative coercivity of the actual eta phase heat matrix

Integer phase probes have exact Fourier orthogonality on `[1,2]`. The
Gaussian phase profile therefore has a uniform positive lower bound as a
matrix. The actual eta kernel inherits a dimension-dependent bound through
the ordinate-uniform critical error estimate.
-/

open Complex Filter MeasureTheory Set Topology Matrix
open scoped Classical ENNReal BigOperators Interval ComplexOrder

namespace RiemannGaussian

noncomputable section

/-- Exact integer Fourier orthogonality on the unit interval `[1,2]`. -/
theorem integral_Icc_cos_integer_heatPhase (k : ℤ) :
    (∫ v : ℝ in Icc 1 2, Real.cos ((2 * Real.pi * (k : ℝ)) * v)) =
      if k = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  by_cases hk : k = 0
  · norm_num [hk]
  · rw [if_neg hk, intervalIntegral.integral_comp_mul_left Real.cos (by
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by exact_mod_cast hk)),
      integral_cos]
    rw [show (2 * Real.pi * (k : ℝ)) * 2 = ((4 * k : ℤ) : ℝ) * Real.pi by push_cast; ring,
      show (2 * Real.pi * (k : ℝ)) * 1 = ((2 * k : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi, Real.sin_int_mul_pi]
    simp

/-- The leading critical phase-profile matrix at a finite family of real frequencies. -/
def pairedEtaHeatProfileGram {ι : Type*} (kappa : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j ↦ pairedEtaHeatPhaseProfile (kappa j - kappa i)

/-- The positive constant supplied by one unit interval of Fourier orthogonality. -/
def pairedEtaHeatProfileCoercivity : ℝ := Real.exp (-1) / Real.sqrt Real.pi

/-- The explicit profile coercivity constant is strictly positive. -/
theorem pairedEtaHeatProfileCoercivity_pos : 0 < pairedEtaHeatProfileCoercivity := by
  unfold pairedEtaHeatProfileCoercivity
  positivity

/-- The weighted finite cosine energy is integrable over the positive half-line. -/
theorem integrableOn_weighted_finiteCosinePhaseEnergy {ι : Type*} [Fintype ι]
    (kappa c : ι → ℝ) :
    IntegrableOn (fun v ↦ (v * Real.exp (-(1 / 4) * v ^ 2)) *
      finiteCosinePhaseEnergy (fun i ↦ kappa i * v) c) (Ioi 0) := by
  have hfun : (fun v : ℝ ↦ (v * Real.exp (-(1 / 4) * v ^ 2)) *
      finiteCosinePhaseEnergy (fun i ↦ kappa i * v) c) =
      (fun v ↦ ∑ i, ∑ j, (c i * c j) *
        (v * Real.exp (-(1 / 4) * v ^ 2) * Real.cos ((kappa j - kappa i) * v))) := by
    funext v
    simp only [finiteCosinePhaseEnergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [sub_mul]
    ring
  rw [hfun]
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    (integrableOn_pairedEtaHeatPhaseProfile_kernel (kappa j - kappa i)).const_mul (c i * c j)

/-- The full profile-matrix quadratic form is its weighted finite cosine energy. -/
theorem pairedEtaHeatProfileGram_energy_eq_integral {ι : Type*} [Fintype ι]
    (kappa c : ι → ℝ) :
    finiteRealMatrixEnergy (pairedEtaHeatProfileGram kappa) c =
      (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0,
        (v * Real.exp (-(1 / 4) * v ^ 2)) * finiteCosinePhaseEnergy (fun i ↦ kappa i * v) c := by
  let F : ι → ι → ℝ → ℝ := fun i j v ↦ (c i * c j) *
    (v * Real.exp (-(1 / 4) * v ^ 2) * Real.cos ((kappa j - kappa i) * v))
  have hi : ∀ i j, IntegrableOn (F i j) (Ioi 0) := fun i j ↦
    (integrableOn_pairedEtaHeatPhaseProfile_kernel (kappa j - kappa i)).const_mul _
  have hfun : (fun v : ℝ ↦ (v * Real.exp (-(1 / 4) * v ^ 2)) *
      finiteCosinePhaseEnergy (fun i ↦ kappa i * v) c) =
      (fun v ↦ ∑ i, ∑ j, F i j v) := by
    funext v
    simp only [finiteCosinePhaseEnergy, Finset.mul_sum, F]
    apply Finset.sum_congr rfl
    intro i hi'
    apply Finset.sum_congr rfl
    intro j hj'
    rw [sub_mul]
    ring
  rw [hfun, integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hi _ j), F, integral_const_mul]
  simp only [finiteRealMatrixEnergy, pairedEtaHeatProfileGram, pairedEtaHeatPhaseProfile,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi'
  apply Finset.sum_congr rfl
  intro j hj'
  ring

/-- Distinct integer probes have unit-interval energy equal to the full
coefficient square sum. -/
theorem integral_Icc_finiteCosinePhaseEnergy_integer {ι : Type*} [Fintype ι]
    {k : ι → ℤ} (hk : Function.Injective k) (c : ι → ℝ) :
    (∫ v : ℝ in Icc 1 2,
      finiteCosinePhaseEnergy (fun i ↦ (2 * Real.pi * (k i : ℝ)) * v) c) = ∑ i, c i ^ 2 := by
  have hi : ∀ i j, IntegrableOn (fun v : ℝ ↦ c i * c j *
      Real.cos (((2 * Real.pi * (k j : ℝ)) * v) - ((2 * Real.pi * (k i : ℝ)) * v))) (Icc 1 2) :=
    fun i j ↦ (by fun_prop : Continuous (fun v : ℝ ↦ c i * c j *
      Real.cos (((2 * Real.pi * (k j : ℝ)) * v) - ((2 * Real.pi * (k i : ℝ)) * v)))).integrableOn_Icc
  unfold finiteCosinePhaseEnergy
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j)]
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ ↦ hi i j)]
  have hent : ∀ j,
      (∫ v : ℝ in Icc 1 2, c i * c j *
        Real.cos ((2 * Real.pi * (k j : ℝ)) * v - (2 * Real.pi * (k i : ℝ)) * v)) =
        if j = i then c i ^ 2 else 0 := by
    intro j
    rw [integral_const_mul]
    have hfun : (fun v : ℝ ↦ Real.cos ((2 * Real.pi * (k j : ℝ)) * v -
        (2 * Real.pi * (k i : ℝ)) * v)) =
        (fun v ↦ Real.cos ((2 * Real.pi * ((k j - k i : ℤ) : ℝ)) * v)) := by
      funext v
      congr 1
      push_cast
      ring
    rw [hfun, integral_Icc_cos_integer_heatPhase]
    by_cases hji : j = i
    · subst j
      simp [sq]
    · have hn : k j - k i ≠ 0 := sub_ne_zero.mpr (fun h ↦ hji (hk h))
      simp [hn, hji]
  simp_rw [hent]
  simp

/-- The exact Fourier interval carries a fixed positive amount of Gaussian weight. -/
theorem etaHeatProfileWeight_lower_on_Icc {v : ℝ} (hv : v ∈ Icc 1 2) :
    Real.exp (-1) ≤ v * Real.exp (-(1 / 4) * v ^ 2) := by
  have he : Real.exp (-1) ≤ Real.exp (-(1 / 4) * v ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [hv.1, hv.2])
  exact he.trans (le_mul_of_one_le_left (Real.exp_pos _).le hv.1)

/-- Uniform coercivity of the entire profile matrix for distinct integer
probes, with the explicit constant `exp(-1) / sqrt pi`. -/
theorem pairedEtaHeatProfileGram_integer_energy_lower {ι : Type*} [Fintype ι]
    {k : ι → ℤ} (hk : Function.Injective k) (c : ι → ℝ) :
    pairedEtaHeatProfileCoercivity * (∑ i, c i ^ 2) ≤
      finiteRealMatrixEnergy (pairedEtaHeatProfileGram (fun i ↦ 2 * Real.pi * (k i : ℝ))) c := by
  let theta : ι → ℝ := fun i ↦ 2 * Real.pi * (k i : ℝ)
  let E : ℝ → ℝ := fun v ↦ finiteCosinePhaseEnergy (fun i ↦ theta i * v) c
  let w : ℝ → ℝ := fun v ↦ v * Real.exp (-(1 / 4) * v ^ 2)
  have hE : Continuous E := by unfold E finiteCosinePhaseEnergy; fun_prop
  have hi : IntegrableOn (fun v ↦ w v * E v) (Ioi 0) :=
    integrableOn_weighted_finiteCosinePhaseEnergy theta c
  have hsub : Icc (1 : ℝ) 2 ⊆ Ioi 0 := fun v hv ↦ by have := hv.1; simp only [mem_Ioi]; linarith
  have hpos : ∀ᵐ v ∂volume.restrict (Ioi 0), 0 ≤ w v * E v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact mul_nonneg (mul_nonneg (le_of_lt hv) (Real.exp_pos _).le)
      (finiteCosinePhaseEnergy_nonneg _ c)
  have hrestrict := setIntegral_mono_set hi hpos (Eventually.of_forall hsub)
  have hinterval : Real.exp (-1) * (∫ v in Icc 1 2, E v) ≤ ∫ v in Icc 1 2, w v * E v := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hE.integrableOn_Icc.const_mul _) (hi.mono_set hsub) measurableSet_Icc
    intro v hv
    exact mul_le_mul_of_nonneg_right (etaHeatProfileWeight_lower_on_Icc hv)
      (finiteCosinePhaseEnergy_nonneg _ c)
  have horth : (∫ v in Icc 1 2, E v) = ∑ i, c i ^ 2 :=
    integral_Icc_finiteCosinePhaseEnergy_integer hk c
  rw [horth] at hinterval
  have hbound := mul_le_mul_of_nonneg_left (hinterval.trans hrestrict)
    (show 0 ≤ 1 / Real.sqrt Real.pi by positivity)
  rw [pairedEtaHeatProfileGram_energy_eq_integral]
  change pairedEtaHeatProfileCoercivity * (∑ i, c i ^ 2) ≤
    (1 / Real.sqrt Real.pi) * ∫ v in Ioi 0, w v * E v
  simpa only [pairedEtaHeatProfileCoercivity, div_eq_mul_inv, one_mul, mul_assoc, mul_left_comm] using hbound

/-- Scalar multiplication of a real matrix scales its full quadratic form. -/
theorem finiteRealMatrixEnergy_smul {ι : Type*} [Fintype ι]
    (a : ℝ) (M : Matrix ι ι ℝ) (c : ι → ℝ) :
    finiteRealMatrixEnergy (a • M) c = a * finiteRealMatrixEnergy M c := by
  simp only [finiteRealMatrixEnergy, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Matrix subtraction retains the signed difference of the two energies. -/
theorem finiteRealMatrixEnergy_sub {ι : Type*} [Fintype ι]
    (M N : Matrix ι ι ℝ) (c : ι → ℝ) :
    finiteRealMatrixEnergy (M - N) c = finiteRealMatrixEnergy M c - finiteRealMatrixEnergy N c := by
  simp only [finiteRealMatrixEnergy, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The identity matrix has the exact coefficient square sum as its energy. -/
theorem finiteRealMatrixEnergy_one {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) :
    finiteRealMatrixEnergy (1 : Matrix ι ι ℝ) c = ∑ i, c i ^ 2 := by
  simp [finiteRealMatrixEnergy, Matrix.one_apply, sq]

/-- An entrywise error gives a quadratic-form error with an explicit finite
dimension cost; no uniformity in growing matrix size is asserted. -/
theorem finiteRealMatrixEnergy_sub_abs_le_card {ι : Type*} [Fintype ι]
    {M N : Matrix ι ι ℝ} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hMN : ∀ i j, |M i j - N i j| ≤ delta) (c : ι → ℝ) :
    |finiteRealMatrixEnergy M c - finiteRealMatrixEnergy N c| ≤
      delta * (Fintype.card ι : ℝ) * (∑ i, c i ^ 2) := by
  rw [← finiteRealMatrixEnergy_sub]
  have hcs : (∑ i, |c i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, c i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i ↦ |c i|) (fun _ ↦ (1 : ℝ))
    simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, sq_abs, mul_comm] using h
  calc
    |finiteRealMatrixEnergy (M - N) c| = |∑ i, ∑ j, c i * c j * (M i j - N i j)| := rfl
    _ ≤ ∑ i, ∑ j, |c i| * |c j| * delta := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hMN i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = delta * (∑ i, |c i|) ^ 2 := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ delta * ((Fintype.card ι : ℝ) * (∑ i, c i ^ 2)) :=
      mul_le_mul_of_nonneg_left hcs hdelta
    _ = _ := by ring

/-- The actual critical eta matrix at frequencies scaled with the heat width. -/
def pairedEtaSupportGapScaledPhaseGram {ι : Type*} (h : ℝ) (kappa : ι → ℝ) : Matrix ι ι ℝ :=
  pairedEtaSupportGapPhaseGram (1 / 2) h (fun i t ↦ (kappa i / h) * t)

/-- The error in each actual mixed entry is at most `32h`, independently
of both chosen frequencies. -/
theorem pairedEtaSupportGapScaledPhaseGram_entry_error {ι : Type*}
    {h : ℝ} (hh : 0 < h) (hhone : h ≤ 1) (kappa : ι → ℝ) (i j : ι) :
    |pairedEtaSupportGapScaledPhaseGram h kappa i j -
      (h * Real.log (1 / h)) * pairedEtaHeatProfileGram kappa i j| ≤ 32 * h := by
  have hphase : (fun t : ℝ ↦ kappa j / h * t - kappa i / h * t) =
      (fun t ↦ ((kappa j - kappa i) / h) * t) := by funext t; ring
  unfold pairedEtaSupportGapScaledPhaseGram pairedEtaSupportGapPhaseGram pairedEtaHeatProfileGram
  rw [hphase]
  have hb := pairedEtaSupportGapGaussianLeakage_uniform_error_le hh hhone ((kappa j - kappa i) / h)
  have hcancel : h * ((kappa j - kappa i) / h) = kappa j - kappa i := by field_simp
  simpa only [hcancel] using hb

/-- Quantitative coercivity of the actual continuous eta heat matrix for
distinct integer probes, with the dimension cost `32 * card ι`. -/
theorem pairedEtaSupportGapScaledPhaseGram_integer_energy_lower {ι : Type*} [Fintype ι]
    {h : ℝ} (hh : 0 < h) (hhone : h ≤ 1) {k : ι → ℤ}
    (hk : Function.Injective k) (c : ι → ℝ) :
    h * (pairedEtaHeatProfileCoercivity * Real.log (1 / h) - (Fintype.card ι : ℝ) * 32) *
      (∑ i, c i ^ 2) ≤
      finiteRealMatrixEnergy (pairedEtaSupportGapScaledPhaseGram h
        (fun i ↦ 2 * Real.pi * (k i : ℝ))) c := by
  let kappa : ι → ℝ := fun i ↦ 2 * Real.pi * (k i : ℝ)
  let a := h * Real.log (1 / h)
  have hlog : 0 ≤ Real.log (1 / h) := Real.log_nonneg ((le_div_iff₀ hh).2 (by linarith))
  have ha : 0 ≤ a := mul_nonneg hh.le hlog
  have he := finiteRealMatrixEnergy_sub_abs_le_card
    (M := pairedEtaSupportGapScaledPhaseGram h kappa)
    (N := a • pairedEtaHeatProfileGram kappa) (delta := 32 * h) (by positivity)
    (fun i j ↦ pairedEtaSupportGapScaledPhaseGram_entry_error hh hhone kappa i j) c
  rw [finiteRealMatrixEnergy_smul] at he
  have hb := mul_le_mul_of_nonneg_left (pairedEtaHeatProfileGram_integer_energy_lower hk c) ha
  have hlo := (abs_le.mp he).1
  dsimp [a, kappa] at hb hlo
  nlinarith

/-- Loewner-form version of the actual eta matrix lower bound, including
the complete finite matrix instead of only diagonal or trace information. -/
theorem pairedEtaSupportGapScaledPhaseGram_integer_coercive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {h : ℝ} (hh : 0 < h) (hhone : h ≤ 1) {k : ι → ℤ} (hk : Function.Injective k) :
    (pairedEtaSupportGapScaledPhaseGram h (fun i ↦ 2 * Real.pi * (k i : ℝ)) -
      (h * (pairedEtaHeatProfileCoercivity * Real.log (1 / h) - (Fintype.card ι : ℝ) * 32)) •
        (1 : Matrix ι ι ℝ)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (pairedEtaSupportGapPhaseGram_isHermitian _ _ _).sub
      (Matrix.isHermitian_one.smul (by apply IsSelfAdjoint.all))
  · intro c
    rw [← finiteRealMatrixEnergy_eq_dotProduct, finiteRealMatrixEnergy_sub,
      finiteRealMatrixEnergy_smul, finiteRealMatrixEnergy_one]
    exact sub_nonneg.mpr (pairedEtaSupportGapScaledPhaseGram_integer_energy_lower hh hhone hk c)

/-- A fully explicit logarithmic threshold gives half the leading
coercivity, with dependence on the number of probes retained. -/
theorem pairedEtaSupportGapScaledPhaseGram_integer_small_width {ι : Type*} [Fintype ι]
    {h : ℝ} (hh : 0 < h) (hhone : h ≤ 1) {k : ι → ℤ} (hk : Function.Injective k)
    (hsmall : 64 * (Fintype.card ι : ℝ) / pairedEtaHeatProfileCoercivity ≤ Real.log (1 / h))
    (c : ι → ℝ) :
    (pairedEtaHeatProfileCoercivity / 2) * h * Real.log (1 / h) * (∑ i, c i ^ 2) ≤
      finiteRealMatrixEnergy (pairedEtaSupportGapScaledPhaseGram h
        (fun i ↦ 2 * Real.pi * (k i : ℝ))) c := by
  apply le_trans _ (pairedEtaSupportGapScaledPhaseGram_integer_energy_lower hh hhone hk c)
  have hb := (div_le_iff₀ pairedEtaHeatProfileCoercivity_pos).mp hsmall
  have hs : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg (c i)
  have hscalar : (pairedEtaHeatProfileCoercivity / 2) * Real.log (1 / h) ≤
      pairedEtaHeatProfileCoercivity * Real.log (1 / h) - (Fintype.card ι : ℝ) * 32 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscalar hh.le) hs
  nlinarith

/-- The profile preserves the sign reversal of its frequency as an exact equality. -/
theorem pairedEtaHeatPhaseProfile_neg (kappa : ℝ) :
    pairedEtaHeatPhaseProfile (-kappa) = pairedEtaHeatPhaseProfile kappa := by
  simp only [pairedEtaHeatPhaseProfile, neg_mul, Real.cos_neg]

/-- Hermitian symmetry of the complete real profile matrix. -/
theorem pairedEtaHeatProfileGram_isHermitian {ι : Type*} (kappa : ι → ℝ) :
    (pairedEtaHeatProfileGram kappa).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  simp only [star_trivial, pairedEtaHeatProfileGram]
  rw [show kappa i - kappa j = -(kappa j - kappa i) by ring, pairedEtaHeatPhaseProfile_neg]

/-- The explicit lower bound for the entire profile matrix in Loewner form. -/
theorem pairedEtaHeatProfileGram_integer_coercive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ι → ℤ} (hk : Function.Injective k) :
    (pairedEtaHeatProfileGram (fun i ↦ 2 * Real.pi * (k i : ℝ)) -
      pairedEtaHeatProfileCoercivity • (1 : Matrix ι ι ℝ)).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (pairedEtaHeatProfileGram_isHermitian _).sub
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  · intro c
    rw [← finiteRealMatrixEnergy_eq_dotProduct, finiteRealMatrixEnergy_sub,
      finiteRealMatrixEnergy_smul, finiteRealMatrixEnergy_one]
    exact sub_nonneg.mpr (pairedEtaHeatProfileGram_integer_energy_lower hk c)

/-- A real matrix lower bound extends to the full complex coefficient space
with the same constant and the usual coefficient norm square. -/
theorem finiteRealMatrixEnergy_complex_lower {ι : Type*} [Fintype ι]
    {M : Matrix ι ι ℝ} {a : ℝ}
    (hM : ∀ c : ι → ℝ, a * (∑ i, c i ^ 2) ≤ finiteRealMatrixEnergy M c) (c : ι → ℂ) :
    a * (∑ i, Complex.normSq (c i)) ≤ (star c ⬝ᵥ (M.map Complex.ofReal *ᵥ c)).re := by
  rw [finiteRealMatrixEnergy_complex_re]
  have hs : (∑ i, Complex.normSq (c i)) =
      (∑ i, (c i).re ^ 2) + ∑ i, (c i).im ^ 2 := by
    simp only [Complex.normSq_apply, pow_two, Finset.sum_add_distrib]
  rw [hs, mul_add]
  exact add_le_add (hM _) (hM _)

/-- The arithmetic matrix coercivity holds for every complex coefficient
vector, including interference between distinct phase probes. -/
theorem pairedEtaSupportGapScaledPhaseGram_integer_complex_energy_lower {ι : Type*} [Fintype ι]
    {h : ℝ} (hh : 0 < h) (hhone : h ≤ 1) {k : ι → ℤ}
    (hk : Function.Injective k) (c : ι → ℂ) :
    h * (pairedEtaHeatProfileCoercivity * Real.log (1 / h) - (Fintype.card ι : ℝ) * 32) *
      (∑ i, Complex.normSq (c i)) ≤
      (star c ⬝ᵥ ((pairedEtaSupportGapScaledPhaseGram h
        (fun i ↦ 2 * Real.pi * (k i : ℝ))).map Complex.ofReal *ᵥ c)).re :=
  finiteRealMatrixEnergy_complex_lower
    (pairedEtaSupportGapScaledPhaseGram_integer_energy_lower hh hhone hk) c

/-- The full complex Loewner lower bound has the same exact dimension cost. -/
theorem pairedEtaSupportGapScaledPhaseGram_integer_complex_coercive
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℝ} (hh : 0 < h) (hhone : h ≤ 1)
    {k : ι → ℤ} (hk : Function.Injective k) :
    ((pairedEtaSupportGapScaledPhaseGram h (fun i ↦ 2 * Real.pi * (k i : ℝ)) -
      (h * (pairedEtaHeatProfileCoercivity * Real.log (1 / h) - (Fintype.card ι : ℝ) * 32)) •
        (1 : Matrix ι ι ℝ)).map Complex.ofReal).PosSemidef :=
  posSemidef_complex_ofReal (pairedEtaSupportGapScaledPhaseGram_integer_coercive hh hhone hk)

end

end RiemannGaussian
