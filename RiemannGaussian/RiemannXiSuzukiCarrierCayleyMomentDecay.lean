import RiemannGaussian.RiemannXiSuzukiCarrierCayleyMoments
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Square summability and decay of the Cayley moments

The Cayley moments of the finite xi-energy carrier measure are Fourier
coefficients after the exact global change of variables `y = arctan x`.
This file carries out that change of variables in Lean.  The transformed
density is bounded by one on an interval of length `pi`, hence belongs to
`L²`; Parseval then makes all bilateral Cayley moments square summable and,
in particular, forces the positive moments in the Hardy Hankel block to
vanish at infinity.

No quantitative decay rate, compactness conclusion beyond entrywise decay,
or RH conclusion is asserted here.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- The arithmetic carrier density in the angular coordinate
`y = arctan x`. -/
def suzukiXiCarrierAngularDensity (y : ℝ) : ℂ :=
  suzukiXiRealAxisArithmeticCarrierDensity (Real.tan y)

/-- The angular carrier density is Borel measurable. -/
theorem measurable_suzukiXiCarrierAngularDensity :
    Measurable suzukiXiCarrierAngularDensity := by
  unfold suzukiXiCarrierAngularDensity
  have htan : Measurable Real.tan := by
    rw [show Real.tan = Real.sin / Real.cos by
      funext x
      exact Real.tan_eq_sin_div_cos x]
    exact Real.measurable_sin.div Real.measurable_cos
  exact Complex.measurable_ofReal.comp
    (measurable_suzukiXiRealAxisArithmeticCarrierDensity.comp
      htan)

/-- The angular carrier density has norm at most one everywhere, including
the totalized endpoint values of `tan`. -/
theorem norm_suzukiXiCarrierAngularDensity_le_one (y : ℝ) :
    ‖suzukiXiCarrierAngularDensity y‖ ≤ 1 := by
  unfold suzukiXiCarrierAngularDensity
  rw [Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (suzukiXiRealAxisArithmeticCarrierDensity_nonneg (Real.tan y))]
  exact suzukiXiRealAxisArithmeticCarrierDensity_le_one (Real.tan y)

/-- The bounded angular carrier density belongs to `L²` on the canonical
interval of length `pi`. -/
theorem memLp_two_suzukiXiCarrierAngularDensity :
    MemLp suzukiXiCarrierAngularDensity 2
      (volume.restrict (Ioc (-(Real.pi / 2)) (Real.pi / 2))) := by
  apply MemLp.of_bound
    measurable_suzukiXiCarrierAngularDensity.aestronglyMeasurable 1
  exact Eventually.of_forall norm_suzukiXiCarrierAngularDensity_le_one

/-- The same angular density shifted onto the interval `(0, pi)`.  This
half-period shift removes the minus sign in the Cayley character. -/
def suzukiXiCarrierShiftedAngularDensity (theta : ℝ) : ℂ :=
  suzukiXiRealAxisArithmeticCarrierDensity
    (Real.tan (theta - Real.pi / 2))

/-- The shifted angular carrier density is Borel measurable. -/
theorem measurable_suzukiXiCarrierShiftedAngularDensity :
    Measurable suzukiXiCarrierShiftedAngularDensity := by
  unfold suzukiXiCarrierShiftedAngularDensity
  have htan : Measurable Real.tan := by
    rw [show Real.tan = Real.sin / Real.cos by
      funext x
      exact Real.tan_eq_sin_div_cos x]
    exact Real.measurable_sin.div Real.measurable_cos
  exact Complex.measurable_ofReal.comp
    (measurable_suzukiXiRealAxisArithmeticCarrierDensity.comp
      (htan.comp (measurable_id.sub measurable_const)))

/-- The shifted angular carrier density is still bounded by one. -/
theorem norm_suzukiXiCarrierShiftedAngularDensity_le_one (theta : ℝ) :
    ‖suzukiXiCarrierShiftedAngularDensity theta‖ ≤ 1 := by
  unfold suzukiXiCarrierShiftedAngularDensity
  rw [Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_nonneg
      (suzukiXiRealAxisArithmeticCarrierDensity_nonneg
        (Real.tan (theta - Real.pi / 2)))]
  exact suzukiXiRealAxisArithmeticCarrierDensity_le_one
    (Real.tan (theta - Real.pi / 2))

/-- The shifted density belongs to `L²` on `(0, pi]`. -/
theorem memLp_two_suzukiXiCarrierShiftedAngularDensity :
    MemLp suzukiXiCarrierShiftedAngularDensity 2
      (volume.restrict (Ioc 0 Real.pi)) := by
  apply MemLp.of_bound
    measurable_suzukiXiCarrierShiftedAngularDensity.aestronglyMeasurable 1
  exact Eventually.of_forall
    norm_suzukiXiCarrierShiftedAngularDensity_le_one

/-- The shifted density, periodically packaged on the additive circle of
length `pi`. -/
def suzukiXiCarrierShiftedAngularCircleDensity :
    AddCircle Real.pi → ℂ :=
  AddCircle.liftIoc Real.pi 0 suzukiXiCarrierShiftedAngularDensity

/-- The periodic shifted density belongs to `L²` for normalized Haar
measure on the additive circle. -/
theorem memLp_two_suzukiXiCarrierShiftedAngularCircleDensity :
    MemLp suzukiXiCarrierShiftedAngularCircleDensity 2
      AddCircle.haarAddCircle := by
  have hbase : MemLp suzukiXiCarrierShiftedAngularDensity 2
      (volume.restrict (Ioc 0 (0 + Real.pi))) := by
    simpa only [zero_add] using
      memLp_two_suzukiXiCarrierShiftedAngularDensity
  exact hbase.memLp_liftIoc.haarAddCircle

/-- The shifted angular density as a literal vector in circle `L²`. -/
def suzukiXiCarrierShiftedAngularDensityLp :
    Lp ℂ 2 (@AddCircle.haarAddCircle Real.pi inferInstance) :=
  memLp_two_suzukiXiCarrierShiftedAngularCircleDensity.toLp
    suzukiXiCarrierShiftedAngularCircleDensity

/-- The packaged circle `L²` density agrees almost everywhere with its
literal representative. -/
theorem suzukiXiCarrierShiftedAngularDensityLp_ae :
    suzukiXiCarrierShiftedAngularDensityLp =ᵐ[
      @AddCircle.haarAddCircle Real.pi inferInstance]
        suzukiXiCarrierShiftedAngularCircleDensity := by
  unfold suzukiXiCarrierShiftedAngularDensityLp
  exact MemLp.coeFn_toLp
    memLp_two_suzukiXiCarrierShiftedAngularCircleDensity

/-! ## Exact angular Cayley character -/

/-- On the open arctangent interval, the boundary Cayley coordinate is the
negative fundamental Fourier character of the additive circle of length
`pi`. -/
theorem suzukiXiCarrierCayleyBoundaryCoordinate_tan_eq_neg_fourier
    {y : ℝ} (hy : y ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    suzukiXiCarrierCayleyBoundaryCoordinate (Real.tan y) =
      -(@fourier Real.pi 1 (y : AddCircle Real.pi)) := by
  have hcos : Real.cos y ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo hy).ne'
  have hcosComplex : Complex.cos (y : ℂ) ≠ 0 := by
    exact_mod_cast hcos
  rw [fourier_coe_apply]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  norm_num only [Int.cast_one, mul_one]
  have hexponent :
      2 * (Real.pi : ℂ) * Complex.I * (y : ℂ) /
          (Real.pi : ℂ) =
        2 * (y : ℂ) * Complex.I := by
    field_simp [hpi]
  rw [hexponent, Complex.exp_mul_I]
  have hden : ((Real.tan y : ℝ) : ℂ) + Complex.I ≠ 0 := by
    simpa [sub_eq_add_neg] using
      (ofReal_sub_ne_zero_of_im_ne_zero
        (z := -Complex.I) (by simp) (Real.tan y))
  unfold suzukiXiCarrierCayleyBoundaryCoordinate
  rw [div_eq_iff hden]
  rw [Real.tan_eq_sin_div_cos]
  push_cast
  field_simp [hcos, hcosComplex]
  rw [Complex.cos_two_mul, Complex.sin_two_mul]
  have htrig := Complex.sin_sq_add_cos_sq (y : ℂ)
  ring_nf at htrig
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  have hsin : Complex.sin (y : ℂ) ^ 2 =
      1 - Complex.cos (y : ℂ) ^ 2 :=
    eq_sub_of_add_eq htrig
  rw [hsin]
  ring

/-- Integer powers of the fundamental Fourier character are exactly the
integer-indexed Fourier characters. -/
theorem fourier_one_zpow_eq_fourier (k : ℤ)
    (theta : AddCircle Real.pi) :
    (@fourier Real.pi 1 theta) ^ k = @fourier Real.pi k theta := by
  rw [fourier_one, fourier_apply, ← Circle.coe_zpow,
    ← AddCircle.toCircle_zsmul]

/-- After shifting `arctan x` by half the angular period, the boundary
Cayley coordinate is exactly (without a residual sign) the fundamental
Fourier character. -/
theorem suzukiXiCarrierCayleyBoundaryCoordinate_eq_shifted_fourier
    (x : ℝ) :
    suzukiXiCarrierCayleyBoundaryCoordinate x =
      @fourier Real.pi 1
        ((Real.arctan x + Real.pi / 2 : ℝ) : AddCircle Real.pi) := by
  have hbase :=
    suzukiXiCarrierCayleyBoundaryCoordinate_tan_eq_neg_fourier
      (Real.arctan_mem_Ioo x)
  rw [Real.tan_arctan] at hbase
  have hshift := @fourier_add_half_inv_index Real.pi 1
    (by norm_num) Real.pi_pos
    ((Real.arctan x : ℝ) : AddCircle Real.pi)
  simpa only [Int.cast_one, div_one, ← QuotientAddGroup.mk_add] using
    hbase.trans hshift.symm

/-- Every integer Cayley character becomes the corresponding shifted
Fourier character in the arctangent coordinate. -/
theorem suzukiXiCarrierCayleyBoundaryZPower_eq_shifted_fourier
    (k : ℤ) (x : ℝ) :
    suzukiXiCarrierCayleyBoundaryZPower k x =
      @fourier Real.pi k
        ((Real.arctan x + Real.pi / 2 : ℝ) : AddCircle Real.pi) := by
  unfold suzukiXiCarrierCayleyBoundaryZPower
  rw [suzukiXiCarrierCayleyBoundaryCoordinate_eq_shifted_fourier,
    fourier_one_zpow_eq_fourier]

/-! ## The exact arctangent Jacobian -/

/-- The shifted arctangent maps the whole real line exactly onto `(0, pi)`. -/
theorem image_shifted_arctan_univ :
    (fun x : ℝ ↦ Real.arctan x + Real.pi / 2) '' univ =
      Ioo 0 Real.pi := by
  ext theta
  constructor
  · rintro ⟨x, -, rfl⟩
    constructor
    · linarith [Real.neg_pi_div_two_lt_arctan x]
    · linarith [Real.arctan_lt_pi_div_two x]
  · intro htheta
    rcases htheta with ⟨htheta0, hthetaPi⟩
    have hdiff : theta - Real.pi / 2 ∈
        Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    refine ⟨Real.tan (theta - Real.pi / 2), mem_univ _, ?_⟩
    change Real.arctan (Real.tan (theta - Real.pi / 2)) +
      Real.pi / 2 = theta
    rw [Real.arctan_tan hdiff.1 hdiff.2]
    ring

/-- The exact global Jacobian formula for the shifted arctangent coordinate. -/
theorem integral_shiftedAngular_eq_arctan_jacobian
    (g : ℝ → ℂ) :
    ∫ theta in Ioo 0 Real.pi, g theta =
      ∫ x : ℝ, (1 / (1 + x ^ 2)) •
        g (Real.arctan x + Real.pi / 2) := by
  have hchange :=
    integral_image_eq_integral_deriv_smul_of_monotoneOn
      (s := univ) (f := fun x : ℝ ↦ Real.arctan x + Real.pi / 2)
      (f' := fun x : ℝ ↦ 1 / (1 + x ^ 2)) MeasurableSet.univ
      (fun x _ ↦ (Real.hasDerivAt_arctan x).add_const
        (Real.pi / 2) |>.hasDerivWithinAt)
      (fun _ _ _ _ hxy ↦ by
        simpa [add_comm] using
          add_le_add_left (Real.arctan_mono hxy) (Real.pi / 2))
      g
  rw [image_shifted_arctan_univ, setIntegral_univ] at hchange
  exact hchange

/-- A Cayley moment is exactly the ordinary angular integral of the shifted
carrier density against the corresponding Fourier character. -/
theorem suzukiXiCarrierCayleyMoment_eq_shiftedAngular_integral
    (k : ℤ) :
    suzukiXiCarrierCayleyMoment k =
      ∫ theta in (0 : ℝ)..Real.pi,
        @fourier Real.pi k
            (theta : AddCircle Real.pi) *
          suzukiXiCarrierShiftedAngularDensity theta := by
  rw [suzukiXiCarrierCayleyMoment_eq_xiEnergy_integral]
  have hchange := integral_shiftedAngular_eq_arctan_jacobian
    (fun theta : ℝ ↦
      @fourier Real.pi k (theta : AddCircle Real.pi) *
        suzukiXiCarrierShiftedAngularDensity theta)
  rw [intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Ioc_eq_integral_Ioo]
  rw [hchange]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    change suzukiXiCarrierNevanlinnaWeight x •
        suzukiXiCarrierCayleyBoundaryZPower k x =
      (1 / (1 + x ^ 2)) •
        (@fourier Real.pi k
            ((Real.arctan x + Real.pi / 2 : ℝ) : AddCircle Real.pi) *
          suzukiXiCarrierShiftedAngularDensity
            (Real.arctan x + Real.pi / 2))
    rw [suzukiXiCarrierCayleyBoundaryZPower_eq_shifted_fourier]
    unfold suzukiXiCarrierNevanlinnaWeight
      suzukiXiCarrierShiftedAngularDensity
    rw [show Real.arctan x + Real.pi / 2 - Real.pi / 2 =
        Real.arctan x by ring,
      Real.tan_arctan]
    simp only [Complex.real_smul]
    push_cast
    field_simp

/-! ## Parseval and moment decay -/

/-- With the normalized Fourier convention used by Mathlib, a Cayley moment
is `pi` times the corresponding Fourier coefficient on the additive
circle. -/
theorem suzukiXiCarrierCayleyMoment_eq_pi_mul_fourierCoeff
    (k : ℤ) :
    suzukiXiCarrierCayleyMoment k =
      (Real.pi : ℂ) *
        fourierCoeff suzukiXiCarrierShiftedAngularCircleDensity (-k) := by
  rw [suzukiXiCarrierCayleyMoment_eq_shiftedAngular_integral]
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, neg_neg]
  have hintegral :
      (∫ theta in (0 : ℝ)..Real.pi,
        @fourier Real.pi k (theta : AddCircle Real.pi) •
          suzukiXiCarrierShiftedAngularCircleDensity
            (theta : AddCircle Real.pi)) =
        ∫ theta in (0 : ℝ)..Real.pi,
          @fourier Real.pi k (theta : AddCircle Real.pi) *
            suzukiXiCarrierShiftedAngularDensity theta := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro theta htheta
    unfold suzukiXiCarrierShiftedAngularCircleDensity
    change @fourier Real.pi k (theta : AddCircle Real.pi) •
        AddCircle.liftIoc Real.pi 0
          suzukiXiCarrierShiftedAngularDensity
          (theta : AddCircle Real.pi) =
      @fourier Real.pi k (theta : AddCircle Real.pi) *
        suzukiXiCarrierShiftedAngularDensity theta
    rw [AddCircle.liftIoc_coe_apply
      (p := Real.pi) (a := 0) (f := suzukiXiCarrierShiftedAngularDensity)
      (by simpa only [zero_add] using htheta)]
    exact smul_eq_mul _ _
  rw [hintegral]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  rw [Complex.real_smul]
  push_cast
  field_simp [hpi]

/-- The squared norm of each moment is the correspondingly rescaled squared
Fourier-coefficient norm. -/
theorem norm_sq_suzukiXiCarrierCayleyMoment_eq_fourierCoeff
    (k : ℤ) :
    ‖suzukiXiCarrierCayleyMoment k‖ ^ 2 =
      Real.pi ^ 2 *
        ‖fourierCoeff suzukiXiCarrierShiftedAngularCircleDensity (-k)‖ ^ 2 := by
  rw [suzukiXiCarrierCayleyMoment_eq_pi_mul_fourierCoeff,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_pow]

/-- Parseval implies unconditional bilateral square summability of all
Cayley moments of the xi-energy carrier measure. -/
theorem summable_norm_sq_suzukiXiCarrierCayleyMoment :
    Summable (fun k : ℤ ↦ ‖suzukiXiCarrierCayleyMoment k‖ ^ 2) := by
  have hcoeff : Summable (fun k : ℤ ↦
      ‖fourierCoeff suzukiXiCarrierShiftedAngularCircleDensity k‖ ^ 2) := by
    have hparseval :=
      (hasSum_sq_fourierCoeff
        suzukiXiCarrierShiftedAngularDensityLp).summable
    apply hparseval.congr
    intro k
    rw [fourierCoeff_congr_ae
      suzukiXiCarrierShiftedAngularDensityLp_ae]
  have hneg := hcoeff.comp_injective neg_injective
  have hscaled := hneg.mul_left (Real.pi ^ 2)
  refine hscaled.congr fun k ↦ ?_
  simpa only [Function.comp_apply] using
    (norm_sq_suzukiXiCarrierCayleyMoment_eq_fourierCoeff k).symm

/-- The nonnegative-index half of the moment sequence is square summable. -/
theorem summable_norm_sq_suzukiXiCarrierCayleyMoment_nat :
    Summable (fun n : ℕ ↦
      ‖suzukiXiCarrierCayleyMoment (n : ℤ)‖ ^ 2) := by
  change Summable ((fun k : ℤ ↦
    ‖suzukiXiCarrierCayleyMoment k‖ ^ 2) ∘ Int.ofNat)
  exact summable_norm_sq_suzukiXiCarrierCayleyMoment.comp_injective
    Int.ofNat_injective

/-- The positive Cayley moments tend to zero.  This is the
Riemann--Lebesgue conclusion needed for the exposed Hardy Hankel block. -/
theorem tendsto_suzukiXiCarrierCayleyMoment_nat_atTop_zero :
    Tendsto (fun n : ℕ ↦ suzukiXiCarrierCayleyMoment (n : ℤ))
      atTop (nhds 0) := by
  have hsquares : Tendsto (fun n : ℕ ↦
      ‖suzukiXiCarrierCayleyMoment (n : ℤ)‖ ^ 2) atTop (nhds 0) :=
    summable_norm_sq_suzukiXiCarrierCayleyMoment_nat.tendsto_atTop_zero
  have hsqrtContinuity :
      Tendsto (fun x : ℝ ↦ √x) (nhds 0) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ ↦ √x) 0 :=
      Real.continuous_sqrt.continuousAt
    simpa only [ContinuousAt, Real.sqrt_zero] using hc
  have hsqrt := hsqrtContinuity.comp hsquares
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsqrt' : Tendsto (fun n : ℕ ↦
      √(‖suzukiXiCarrierCayleyMoment (n : ℤ)‖ ^ 2))
      atTop (nhds 0) := by
    simpa only [Function.comp_def] using hsqrt
  have hpoint :
      (fun n : ℕ ↦ √(‖suzukiXiCarrierCayleyMoment (n : ℤ)‖ ^ 2)) =
        fun n : ℕ ↦ ‖suzukiXiCarrierCayleyMoment (n : ℤ)‖ := by
    funext n
    rw [Real.sqrt_sq (norm_nonneg _)]
  rw [← hpoint]
  exact hsqrt'

/-- Every fixed row of the Hardy cross-Hankel kernel tends entrywise to
zero. -/
theorem tendsto_suzukiXiCarrierCayleyHardyHankelKernel_row
    (m : ℕ) :
    Tendsto (fun n : ℕ ↦
      suzukiXiCarrierCayleyHardyHankelKernel m n)
      atTop (nhds 0) := by
  have h := tendsto_suzukiXiCarrierCayleyMoment_nat_atTop_zero.comp
    (tendsto_add_atTop_nat (m + 1))
  have heq :
      ((fun n : ℕ ↦ suzukiXiCarrierCayleyMoment (n : ℤ)) ∘
          fun n : ℕ ↦ n + (m + 1)) =
        fun n : ℕ ↦ suzukiXiCarrierCayleyHardyHankelKernel m n := by
    funext n
    unfold suzukiXiCarrierCayleyHardyHankelKernel
    change suzukiXiCarrierCayleyMoment ((n + (m + 1) : ℕ) : ℤ) =
      suzukiXiCarrierCayleyMoment ((m + n + 1 : ℕ) : ℤ)
    congr 1
    omega
  rw [← heq]
  exact h

/-- Every fixed column of the Hardy cross-Hankel kernel tends entrywise to
zero. -/
theorem tendsto_suzukiXiCarrierCayleyHardyHankelKernel_column
    (n : ℕ) :
    Tendsto (fun m : ℕ ↦
      suzukiXiCarrierCayleyHardyHankelKernel m n)
      atTop (nhds 0) := by
  simpa only [suzukiXiCarrierCayleyHardyHankelKernel, add_comm] using
    tendsto_suzukiXiCarrierCayleyHardyHankelKernel_row n

end

end RiemannGaussian
