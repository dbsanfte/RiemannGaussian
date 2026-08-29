import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevCumulative

/-!
# Two-sided localization of the Suzuki Chebyshev center

The cumulative-error frontier still contains an endpoint term whose centered
kernel coefficient depends on the canonical Legendre point.  The preceding
lower localization controls one side of that coefficient.  This file proves
the complementary upper localization unconditionally.

The argument combines a proportional lower bound for Suzuki's exact smooth
curvature with an elementary upper bound for the weighted Chebyshev prefix
mass.  At the exact slope-matching point these estimates trap every canonical
center in a fixed-width logarithmic strip.  In particular, the remaining
endpoint kernel coefficient has a uniform inverse-square-root envelope.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## A proportional curvature lower bound -/

/-- Beyond the first event, Suzuki's missing curvature is at most one sixth
of the leading exponential curvature. -/
theorem suzukiMissingCurvature_le_one_sixth_exp_half_of_logTwo_le
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    suzukiMissingCurvature t ≤ (1 / 6 : ℝ) * Real.exp (t / 2) := by
  have htpos : 0 < t :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le ht
  have hden : 0 < 1 - Real.exp (-2 * t) :=
    one_sub_exp_neg_two_mul_pos htpos
  have hexpNegLogTwo :
      Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hexpNegTwoLogTwo :
      Real.exp (-2 * Real.log 2) = (1 / 4 : ℝ) := by
    calc
      Real.exp (-2 * Real.log 2) =
          Real.exp (((2 : ℕ) : ℝ) * (-Real.log 2)) := by
            congr 1
            norm_num
      _ = Real.exp (-Real.log 2) ^ (2 : ℕ) :=
        Real.exp_nat_mul (-Real.log 2) 2
      _ = (1 / 4 : ℝ) := by rw [hexpNegLogTwo]; norm_num
  have hexpNegThreeLogTwo :
      Real.exp (-3 * Real.log 2) = (1 / 8 : ℝ) := by
    calc
      Real.exp (-3 * Real.log 2) =
          Real.exp (((3 : ℕ) : ℝ) * (-Real.log 2)) := by
            congr 1
            norm_num
      _ = Real.exp (-Real.log 2) ^ (3 : ℕ) :=
        Real.exp_nat_mul (-Real.log 2) 3
      _ = (1 / 8 : ℝ) := by rw [hexpNegLogTwo]; norm_num
  have hnegativeTwo : Real.exp (-2 * t) ≤ (1 / 4 : ℝ) := by
    rw [← hexpNegTwoLogTwo]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hnegativeThree : Real.exp (-3 * t) ≤ (1 / 8 : ℝ) := by
    rw [← hexpNegThreeLogTwo]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hdenLower : (3 / 4 : ℝ) ≤ 1 - Real.exp (-2 * t) := by
    linarith
  have hratio :
      Real.exp (-3 * t) / (1 - Real.exp (-2 * t)) ≤ (1 / 6 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hidentity :
      suzukiMissingCurvature t =
        Real.exp (t / 2) *
          (Real.exp (-3 * t) / (1 - Real.exp (-2 * t))) := by
    unfold suzukiMissingCurvature
    field_simp [hden.ne']
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [hidentity]
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left hratio (Real.exp_pos (t / 2)).le)

/-- The exact smooth curvature retains at least five sixths of its leading
pure exponential throughout the first tail. -/
theorem five_sixths_exp_half_le_suzukiSmoothCurvature_of_logTwo_le
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    (5 / 6 : ℝ) * Real.exp (t / 2) ≤ suzukiSmoothCurvature t := by
  have hmissing :=
    suzukiMissingCurvature_le_one_sixth_exp_half_of_logTwo_le ht
  unfold suzukiSmoothCurvature
  linarith

private theorem exp_logTwo_half_le_three_halves :
    Real.exp (Real.log 2 / 2) ≤ (3 / 2 : ℝ) := by
  rw [Real.exp_half, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  nlinarith

/-- Integrating the proportional curvature estimate gives an explicit lower
bound for the source-exact Archimedean slope. -/
theorem five_thirds_exp_half_sub_fourteen_fifths_lt_archimedeanSlope
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    (5 / 3 : ℝ) * Real.exp (t / 2) - 14 / 5 <
      suzukiPointwiseArchimedeanSlope t := by
  have hlogPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have htpos : 0 < t := hlogPos.trans_le ht
  have hprefixMass :
      0 ≤ screwPrefixMass suzukiPrimeWeight 1 :=
    screwPrefixMass_nonnegative suzukiPrimeWeight_nonnegative 1
  have hbaseSlope :
      (-3 / 10 : ℝ) <
        suzukiPointwiseArchimedeanSlope (Real.log 2) := by
    have hfrozen :=
      neg_three_tenths_lt_suzukiPointwiseFrozenBaseSlope_logTwo_one
    unfold suzukiPointwiseFrozenBaseSlope at hfrozen
    linarith
  have hcurvatureContinuous : ContinuousOn suzukiSmoothCurvature
      (Set.Icc (Real.log 2) t) := by
    apply continuousOn_suzukiSmoothCurvature_Ioi.mono
    intro x hx
    exact hlogPos.trans_le hx.1
  have hlowerContinuous : ContinuousOn
      (fun x : ℝ => (5 / 6 : ℝ) * Real.exp (x / 2))
      (Set.Icc (Real.log 2) t) := by
    fun_prop
  have hlowerIntegral :
      (∫ x in Real.log 2..t,
          (5 / 6 : ℝ) * Real.exp (x / 2)) ≤
        ∫ x in Real.log 2..t, suzukiSmoothCurvature x := by
    apply intervalIntegral.integral_mono_on ht
      (hlowerContinuous.intervalIntegrable_of_Icc ht)
      (hcurvatureContinuous.intervalIntegrable_of_Icc ht)
    intro x hx
    exact
      five_sixths_exp_half_le_suzukiSmoothCurvature_of_logTwo_le hx.1
  have hexponentialIntegral :
      (∫ x in Real.log 2..t,
          (5 / 6 : ℝ) * Real.exp (x / 2)) =
        (5 / 3 : ℝ) *
          (Real.exp (t / 2) - Real.exp (Real.log 2 / 2)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_div Real.exp
        (by norm_num : (2 : ℝ) ≠ 0), integral_exp]
    norm_num only [smul_eq_mul]
    ring
  rw [hexponentialIntegral] at hlowerIntegral
  rw [suzukiPointwiseArchimedeanSlope_eq_integrated hlogPos htpos]
  unfold suzukiPointwiseIntegratedArchimedeanSlope
    transportCurvatureMass
  nlinarith [exp_logTwo_half_le_three_halves]

/-! ## An upper Chebyshev mass bound -/

/-- The elementary Mathlib Chebyshev estimate gives the convenient linear
upper bound `psi(x) <= 6x` on the complete multiplicative range used here. -/
theorem chebyshevPsi_le_six_mul_self_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x ≤ 6 * x := by
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hconstant : Real.log (4 : ℝ) + 4 ≤ 6 := by
    rw [hlogFour]
    linarith [Real.log_two_lt_d9]
  exact (Chebyshev.psi_le_const_mul_self (zero_le_one.trans hx)).trans
    (mul_le_mul_of_nonneg_right hconstant (zero_le_one.trans hx))

private theorem integrableOn_suzukiChebyshevMassUpperIntegrand_Icc
    {b : ℝ} :
    IntegrableOn
      (fun x : ℝ => x ^ (-3 / 2 : ℝ) * Chebyshev.psi x)
      (Set.Icc 1 b) := by
  have hpower : IntegrableOn (fun x : ℝ => x ^ (-3 / 2 : ℝ))
      (Set.Icc 1 b) := by
    apply ContinuousOn.integrableOn_Icc
    intro x hx
    exact (Real.continuousAt_rpow_const x (-3 / 2 : ℝ)
      (Or.inl (zero_lt_one.trans_le hx.1).ne')).continuousWithinAt
  have hpsi := integrableOn_mul_sum_Icc
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (a := (1 : ℝ)) (b := b) (m := 0) (by norm_num) hpower
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at hpsi
  exact hpsi

/-- Every weighted von-Mangoldt prefix mass is at most twelve times the
square root of its endpoint. -/
theorem suzukiChebyshevWeightedMass_le_twelve_sqrt
    {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevWeightedMass b ≤ 12 * Real.sqrt b := by
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hpowerMul :
      b ^ (-1 / 2 : ℝ) * b = b ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hbpos.ne' (-1 / 2 : ℝ)]
    congr 1
    ring_nf
  have hboundary :
      b ^ (-1 / 2 : ℝ) * Chebyshev.psi b ≤
        6 * Real.sqrt b := by
    rw [Real.sqrt_eq_rpow]
    calc
      b ^ (-1 / 2 : ℝ) * Chebyshev.psi b ≤
          b ^ (-1 / 2 : ℝ) * (6 * b) :=
        mul_le_mul_of_nonneg_left
          (chebyshevPsi_le_six_mul_self_of_one_le hb)
          (Real.rpow_nonneg hbpos.le _)
      _ = 6 * b ^ (1 / 2 : ℝ) := by
        rw [← hpowerMul]
        ring_nf
  let f : ℝ → ℝ := fun x =>
    x ^ (-3 / 2 : ℝ) * Chebyshev.psi x
  let g : ℝ → ℝ := fun x =>
    6 * x ^ (-1 / 2 : ℝ)
  have hf : IntegrableOn f (Set.Ioc (1 : ℝ) b) :=
    (integrableOn_suzukiChebyshevMassUpperIntegrand_Icc (b := b)).mono_set
      Set.Ioc_subset_Icc_self
  have hg : IntegrableOn g (Set.Ioc (1 : ℝ) b) := by
    have hgIcc : IntegrableOn g (Set.Icc (1 : ℝ) b) := by
      apply ContinuousOn.integrableOn_Icc
      intro x hx
      unfold g
      exact continuousAt_const.mul
        (Real.continuousAt_rpow_const x (-1 / 2 : ℝ)
          (Or.inl (zero_lt_one.trans_le hx.1).ne')) |>.continuousWithinAt
    exact hgIcc.mono_set Set.Ioc_subset_Icc_self
  have hpointwise : ∀ x ∈ Set.Ioc (1 : ℝ) b, f x ≤ g x := by
    intro x hx
    have hxpos : 0 < x := zero_lt_one.trans hx.1
    have hpowerMulX :
        x ^ (-3 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hxpos.ne' (-3 / 2 : ℝ)]
      congr 1
      ring_nf
    unfold f g
    calc
      x ^ (-3 / 2 : ℝ) * Chebyshev.psi x ≤
          x ^ (-3 / 2 : ℝ) * (6 * x) :=
        mul_le_mul_of_nonneg_left
          (chebyshevPsi_le_six_mul_self_of_one_le hx.1.le)
          (Real.rpow_nonneg hxpos.le _)
      _ = 6 * x ^ (-1 / 2 : ℝ) := by
        rw [← hpowerMulX]
        ring_nf
  have hintegralMono :
      (∫ x in Set.Ioc (1 : ℝ) b, f x) ≤
        ∫ x in Set.Ioc (1 : ℝ) b, g x :=
    setIntegral_mono_on hf hg measurableSet_Ioc hpointwise
  have hpure :
      (∫ x in Set.Ioc (1 : ℝ) b, g x) =
        12 * (Real.sqrt b - 1) := by
    unfold g
    rw [MeasureTheory.integral_const_mul,
      ← intervalIntegral.integral_of_le hb,
      integral_rpow
        (r := (-1 / 2 : ℝ)) (Or.inl (by norm_num))]
    rw [Real.sqrt_eq_rpow]
    ring_nf
  rw [suzukiChebyshevWeightedMass_eq_explicit]
  change b ^ (-1 / 2 : ℝ) * Chebyshev.psi b +
      (1 / 2 : ℝ) * (∫ x in Set.Ioc (1 : ℝ) b, f x) ≤ _
  rw [hpure] at hintegralMono
  nlinarith

/-! ## Two-sided localization and the endpoint envelope -/

private theorem nine_lt_exp_five_halves :
    (9 : ℝ) < Real.exp (5 / 2 : ℝ) := by
  have hsum :
      (∑ i ∈ Finset.range 6,
          (5 / 2 : ℝ) ^ i / i.factorial) ≤
        Real.exp (5 / 2 : ℝ) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 6
  have hnine :
      (9 : ℝ) < ∑ i ∈ Finset.range 6,
          (5 / 2 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hnine.trans_le hsum

/-- Every canonical slope-matching center lies less than five logarithmic
units above its integer endpoint.  This is the unconditional upper half of
the fixed-width localization strip. -/
theorem suzukiFirstTailChebyshevCenter_lt_log_endpoint_add_five
    (count : ℕ) :
    suzukiFirstTailChebyshevCenter count <
      Real.log (((count + 2 : ℕ) : ℝ)) + 5 := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  change r < Real.log b + 5
  have hb1 : 1 ≤ b := by
    dsimp only [b]
    exact_mod_cast (show 1 ≤ count + 2 by omega)
  have hbpos : 0 < b := zero_lt_one.trans_le hb1
  have hrbase : Real.log 2 ≤ r := by
    dsimp only [r]
    exact log_two_le_suzukiFirstTailChebyshevCenter count
  have hmassUpper :
      suzukiChebyshevWeightedMass b ≤ 12 * Real.sqrt b :=
    suzukiChebyshevWeightedMass_le_twelve_sqrt hb1
  have hslopeLower :
      (5 / 3 : ℝ) * Real.exp (r / 2) - 14 / 5 <
        suzukiPointwiseArchimedeanSlope r :=
    five_thirds_exp_half_sub_fourteen_fifths_lt_archimedeanSlope hrbase
  have hmatch :
      suzukiPointwiseArchimedeanSlope r =
        suzukiChebyshevWeightedMass b := by
    dsimp only [r, b]
    exact
      suzukiPointwiseArchimedeanSlope_firstTailChebyshevCenter_eq_mass
        count
  rw [hmatch] at hslopeLower
  have hsqrtNonneg : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hsqrtSq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hbpos.le
  have hsqrtOne : 1 ≤ Real.sqrt b := by
    nlinarith
  have hexpUpper :
      Real.exp (r / 2) < 9 * Real.sqrt b := by
    nlinarith
  by_contra hcenter
  have hrge : Real.log b + 5 ≤ r := le_of_not_gt hcenter
  have hhalf :
      Real.log b / 2 + 5 / 2 ≤ r / 2 := by
    linarith
  have hexpLower :
      Real.exp (Real.log b / 2 + 5 / 2) ≤
        Real.exp (r / 2) :=
    Real.exp_le_exp.mpr hhalf
  have hexpEndpoint :
      Real.exp (Real.log b / 2 + 5 / 2) =
        Real.sqrt b * Real.exp (5 / 2 : ℝ) := by
    rw [Real.exp_add, Real.exp_half, Real.exp_log hbpos]
  rw [hexpEndpoint] at hexpLower
  have hproduct :
      9 * Real.sqrt b <
        Real.sqrt b * Real.exp (5 / 2 : ℝ) := by
    rw [mul_comm (9 : ℝ)]
    exact mul_lt_mul_of_pos_left nine_lt_exp_five_halves
      (Real.sqrt_pos.2 hbpos)
  linarith

/-- At a canonical endpoint the coefficient left outside the cumulative PNT
error moment is uniformly bounded by `5 * endpoint^(-1/2)`. -/
theorem abs_suzukiChebyshevCenteredKernel_firstTailEndpoint_le
    (count : ℕ) :
    |suzukiChebyshevCenteredKernel
        (suzukiFirstTailChebyshevCenter count)
        (((count + 2 : ℕ) : ℝ))| ≤
      5 * (((count + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  have hbpos : 0 < b := by
    dsimp only [b]
    exact_mod_cast (show 0 < count + 2 by omega)
  have hlower : Real.log b - 2 ≤ r := by
    dsimp only [r, b]
    exact
      log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter count
  have hupper : r < Real.log b + 5 := by
    dsimp only [r, b]
    exact
      suzukiFirstTailChebyshevCenter_lt_log_endpoint_add_five count
  have habs : |Real.log b - r| ≤ 5 := by
    rw [abs_le]
    constructor <;> linarith
  change |(Real.log b - r) * b ^ (-1 / 2 : ℝ)| ≤
    5 * b ^ (-1 / 2 : ℝ)
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hbpos.le _)]
  exact mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg hbpos.le _)

end

end RiemannGaussian
