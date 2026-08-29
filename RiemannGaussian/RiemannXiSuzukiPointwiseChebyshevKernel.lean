import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevError

/-!
# Large-prefix localization of the Suzuki Chebyshev kernel

The exact PNT-error frontier has a centered Abel kernel whose derivative
changes sign only when `log x - center` exceeds two.  This file proves that
the sign change lies beyond every sufficiently large canonical prefix.

The argument is unconditional.  A checked Chebyshev lower bound gives
`psi(x) >= x / 2` for `x >= 5`, hence a quantitative lower bound for the
weighted von-Mangoldt prefix mass.  The source-exact Archimedean slope is
strictly smaller than its leading exponential.  Comparing both quantities at
the canonical slope-matching point locates that point at least at
`log N - 2` for every integer endpoint.  Consequently the centered kernel is
monotone throughout the complete unresolved prefix family.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## An explicit Chebyshev lower bound -/

/-- A rational upper bound for `log 22`, checked through a finite lower
Taylor bound for the exponential. -/
private theorem log_twentyTwo_lt_31_over_10 :
    Real.log 22 < (31 / 10 : ℝ) := by
  have hexponential :=
    Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 31 / 10) 10
  have htwentyTwoExp : (22 : ℝ) < Real.exp (31 / 10) := by
    calc
      (22 : ℝ) < ∑ i ∈ Finset.range 10,
          (31 / 10 : ℝ) ^ i / i.factorial := by
            norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (31 / 10) := hexponential
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 22)).2
    htwentyTwoExp

/-- On the elementary Chebyshev range beginning at twenty, `psi` is at
least one half of its argument. -/
theorem half_self_le_chebyshevPsi_of_twenty_le
    {x : ℝ} (hx : 20 ≤ x) :
    x / 2 ≤ Chebyshev.psi x := by
  have hxpos : 0 < x := by linarith
  have hxplus : 0 < x + 2 := by linarith
  have hratio : 0 < (x + 2) / 22 := by positivity
  have hlogRatio := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div hxplus.ne' (by norm_num : (22 : ℝ) ≠ 0)] at hlogRatio
  have hlogUpper :
      Real.log (x + 2) < (31 / 10 : ℝ) + (x + 2) / 22 - 1 := by
    linarith [log_twentyTwo_lt_31_over_10]
  have hlower :
      x / 2 ≤ (x - 1) * Real.log 2 - Real.log (x + 2) := by
    nlinarith [Real.log_two_gt_d9]
  exact hlower.trans (Chebyshev.psi_ge' hxpos.le)

private theorem exp_nat_lt_eleven_four_pow (n : ℕ) (hn : n ≠ 0) :
    Real.exp (n : ℝ) < (11 / 4 : ℝ) ^ n := by
  calc
    Real.exp (n : ℝ) = Real.exp 1 ^ n := by
      rw [← Real.exp_nat_mul]
      norm_num
    _ < (11 / 4 : ℝ) ^ n := by
      apply pow_lt_pow_left₀
      · exact Real.exp_one_lt_d9.trans (by norm_num)
      · exact (Real.exp_pos 1).le
      · exact hn

private theorem four_lt_log_sixty : (4 : ℝ) < Real.log 60 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 60)).2
  exact (exp_nat_lt_eleven_four_pow 4 (by norm_num)).trans (by norm_num)

private theorem six_lt_log_eightForty : (6 : ℝ) < Real.log 840 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 840)).2
  exact (exp_nat_lt_eleven_four_pow 6 (by norm_num)).trans (by norm_num)

private theorem nine_lt_log_twentySevenSevenTwenty :
    (9 : ℝ) < Real.log 27720 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 27720)).2
  exact (exp_nat_lt_eleven_four_pow 9 (by norm_num)).trans (by norm_num)

private theorem ten_lt_log_twelveMillion :
    (10 : ℝ) < Real.log 12252240 := by
  apply (Real.lt_log_iff_exp_lt
    (by norm_num : (0 : ℝ) < 12252240)).2
  exact (exp_nat_lt_eleven_four_pow 10 (by norm_num)).trans (by norm_num)

private theorem four_lt_chebyshevPsi_five :
    (4 : ℝ) < Chebyshev.psi (5 : ℕ) := by
  rw [Chebyshev.psi_eq_log_lcmUpto,
    show Nat.lcmUpto 5 = 60 by decide]
  norm_num only [Nat.cast_ofNat]
  exact four_lt_log_sixty

private theorem six_lt_chebyshevPsi_eight :
    (6 : ℝ) < Chebyshev.psi (8 : ℕ) := by
  rw [Chebyshev.psi_eq_log_lcmUpto,
    show Nat.lcmUpto 8 = 840 by decide]
  norm_num only [Nat.cast_ofNat]
  exact six_lt_log_eightForty

private theorem nine_lt_chebyshevPsi_twelve :
    (9 : ℝ) < Chebyshev.psi (12 : ℕ) := by
  rw [Chebyshev.psi_eq_log_lcmUpto,
    show Nat.lcmUpto 12 = 27720 by decide]
  norm_num only [Nat.cast_ofNat]
  exact nine_lt_log_twentySevenSevenTwenty

private theorem ten_lt_chebyshevPsi_eighteen :
    (10 : ℝ) < Chebyshev.psi (18 : ℕ) := by
  rw [Chebyshev.psi_eq_log_lcmUpto,
    show Nat.lcmUpto 18 = 12252240 by decide]
  norm_num only [Nat.cast_ofNat]
  exact ten_lt_log_twelveMillion

/-- The half-linear Chebyshev bound in fact begins at five; the short range
is discharged by four exact lcm anchors, and the infinite range by the
preceding analytic estimate. -/
theorem half_self_le_chebyshevPsi_of_five_le
    {x : ℝ} (hx : 5 ≤ x) :
    x / 2 ≤ Chebyshev.psi x := by
  by_cases htwenty : 20 ≤ x
  · exact half_self_le_chebyshevPsi_of_twenty_le htwenty
  have hxTwenty : x < 20 := lt_of_not_ge htwenty
  by_cases height : x ≤ 8
  · have hpsi := Chebyshev.psi_mono hx
    have hanchor : (4 : ℝ) < Chebyshev.psi (5 : ℝ) := by
      simpa only [Nat.cast_ofNat] using four_lt_chebyshevPsi_five
    linarith
  by_cases htwelve : x ≤ 12
  · have hpsi := Chebyshev.psi_mono (show (8 : ℝ) ≤ x by linarith)
    have hanchor : (6 : ℝ) < Chebyshev.psi (8 : ℝ) := by
      simpa only [Nat.cast_ofNat] using six_lt_chebyshevPsi_eight
    linarith
  by_cases heighteen : x ≤ 18
  · have hpsi := Chebyshev.psi_mono (show (12 : ℝ) ≤ x by linarith)
    have hanchor : (9 : ℝ) < Chebyshev.psi (12 : ℝ) := by
      simpa only [Nat.cast_ofNat] using nine_lt_chebyshevPsi_twelve
    linarith
  · have hpsi := Chebyshev.psi_mono (show (18 : ℝ) ≤ x by linarith)
    have hanchor : (10 : ℝ) < Chebyshev.psi (18 : ℝ) := by
      simpa only [Nat.cast_ofNat] using ten_lt_chebyshevPsi_eighteen
    linarith

/-! ## A lower bound for weighted von-Mangoldt mass -/

/-- Explicit derivative of Suzuki's weighted-mass Abel kernel. -/
theorem deriv_suzukiChebyshevMassKernel
    {x : ℝ} (hx : 0 < x) :
    deriv suzukiChebyshevMassKernel x =
      (-1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ) := by
  have hpower : HasDerivAt (fun y : ℝ => y ^ (-1 / 2 : ℝ))
      ((-1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ)) x := by
    convert Real.hasDerivAt_rpow_const
      (x := x) (p := (-1 / 2 : ℝ)) (Or.inl hx.ne') using 1
    ring_nf
  change deriv (fun y : ℝ => y ^ (-1 / 2 : ℝ)) x = _
  exact hpower.deriv

/-- The weighted-mass Abel functional with its derivative evaluated. -/
theorem suzukiChebyshevWeightedMass_eq_explicit (b : ℝ) :
    suzukiChebyshevWeightedMass b =
      b ^ (-1 / 2 : ℝ) * Chebyshev.psi b +
        (1 / 2 : ℝ) *
          ∫ x in Set.Ioc (1 : ℝ) b,
            x ^ (-3 / 2 : ℝ) * Chebyshev.psi x := by
  have hintegral :
      (∫ x in Set.Ioc (1 : ℝ) b,
          deriv suzukiChebyshevMassKernel x * Chebyshev.psi x) =
        (-1 / 2 : ℝ) *
          ∫ x in Set.Ioc (1 : ℝ) b,
            x ^ (-3 / 2 : ℝ) * Chebyshev.psi x := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [deriv_suzukiChebyshevMassKernel (zero_lt_one.trans hx.1)]
    ring
  unfold suzukiChebyshevWeightedMass
  rw [show suzukiChebyshevMassKernel b =
      b ^ (-1 / 2 : ℝ) by rfl,
    hintegral]
  ring

private theorem integrableOn_suzukiChebyshevMassLowerIntegrand_Icc
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

/-- For every real endpoint at least five, the weighted von-Mangoldt mass
has the unconditional lower bound `sqrt b - sqrt 5 / 2`. -/
theorem sqrt_sub_half_sqrt_five_le_suzukiChebyshevWeightedMass
    {b : ℝ} (hb : 5 ≤ b) :
    Real.sqrt b - Real.sqrt 5 / 2 ≤
      suzukiChebyshevWeightedMass b := by
  have hbpos : 0 < b := by linarith
  have hbOne : (1 : ℝ) ≤ b := by linarith
  have hpowerMul :
      b ^ (-1 / 2 : ℝ) * b = b ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one hbpos.ne' (-1 / 2 : ℝ)]
    congr 1
    ring_nf
  have hboundary :
      Real.sqrt b / 2 ≤
        b ^ (-1 / 2 : ℝ) * Chebyshev.psi b := by
    rw [Real.sqrt_eq_rpow]
    calc
      b ^ (1 / 2 : ℝ) / 2 =
          b ^ (-1 / 2 : ℝ) * (b / 2) := by
            rw [← hpowerMul]
            ring
      _ ≤ b ^ (-1 / 2 : ℝ) * Chebyshev.psi b :=
        mul_le_mul_of_nonneg_left
          (half_self_le_chebyshevPsi_of_five_le hb)
          (Real.rpow_nonneg hbpos.le _)
  let f : ℝ → ℝ := fun x =>
    x ^ (-3 / 2 : ℝ) * Chebyshev.psi x
  let g : ℝ → ℝ := fun x =>
    (1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ)
  have hfIoc : IntegrableOn f (Set.Ioc (1 : ℝ) b) :=
    (integrableOn_suzukiChebyshevMassLowerIntegrand_Icc (b := b)).mono_set
      Set.Ioc_subset_Icc_self
  have hfFive : IntegrableOn f (Set.Ioc (5 : ℝ) b) :=
    hfIoc.mono_set (by
      intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩)
  have hgFive : IntegrableOn g (Set.Ioc (5 : ℝ) b) := by
    have hgIcc : IntegrableOn g (Set.Icc (5 : ℝ) b) := by
      apply ContinuousOn.integrableOn_Icc
      intro x hx
      unfold g
      exact continuousAt_const.mul
        (Real.continuousAt_rpow_const x (-1 / 2 : ℝ)
          (Or.inl (by linarith [hx.1] : x ≠ 0))) |>.continuousWithinAt
    exact hgIcc.mono_set Set.Ioc_subset_Icc_self
  have hpointwise : ∀ x ∈ Set.Ioc (5 : ℝ) b, g x ≤ f x := by
    intro x hx
    have hxpos : 0 < x := by linarith [hx.1]
    have hpowerMulX :
        x ^ (-3 / 2 : ℝ) * x = x ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hxpos.ne' (-3 / 2 : ℝ)]
      congr 1
      ring_nf
    unfold f g
    calc
      (1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) =
          x ^ (-3 / 2 : ℝ) * (x / 2) := by
            rw [← hpowerMulX]
            ring
      _ ≤ x ^ (-3 / 2 : ℝ) * Chebyshev.psi x :=
        mul_le_mul_of_nonneg_left
          (half_self_le_chebyshevPsi_of_five_le hx.1.le)
          (Real.rpow_nonneg hxpos.le _)
  have hmonoFive :
      (∫ x in Set.Ioc (5 : ℝ) b, g x) ≤
        ∫ x in Set.Ioc (5 : ℝ) b, f x :=
    setIntegral_mono_on hgFive hfFive measurableSet_Ioc hpointwise
  have hsubset : Set.Ioc (5 : ℝ) b ⊆ Set.Ioc (1 : ℝ) b := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  have hmonoSet :
      (∫ x in Set.Ioc (5 : ℝ) b, f x) ≤
        ∫ x in Set.Ioc (1 : ℝ) b, f x :=
    setIntegral_mono_set hfIoc
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        unfold f
        exact mul_nonneg (Real.rpow_nonneg (by linarith [hx.1]) _)
          (Chebyshev.psi_nonneg x))
      hsubset.eventuallyLE
  have hpure :
      (∫ x in Set.Ioc (5 : ℝ) b, g x) =
        Real.sqrt b - Real.sqrt 5 := by
    unfold g
    rw [MeasureTheory.integral_const_mul,
      ← intervalIntegral.integral_of_le hb,
      integral_rpow
        (r := (-1 / 2 : ℝ)) (Or.inl (by norm_num))]
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    ring_nf
  have hintegral :
      Real.sqrt b - Real.sqrt 5 ≤
        ∫ x in Set.Ioc (1 : ℝ) b,
          x ^ (-3 / 2 : ℝ) * Chebyshev.psi x := by
    change Real.sqrt b - Real.sqrt 5 ≤
      ∫ x in Set.Ioc (1 : ℝ) b, f x
    rw [← hpure]
    exact hmonoFive.trans hmonoSet
  rw [suzukiChebyshevWeightedMass_eq_explicit]
  nlinarith

/-! ## Localization of the canonical Legendre point -/

/-- Beyond the first prime event, the source-exact Archimedean slope remains
at least one unit below the leading pure-exponential slope. -/
theorem suzukiPointwiseArchimedeanSlope_lt_two_mul_exp_half_sub_one
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    suzukiPointwiseArchimedeanSlope t < 2 * Real.exp (t / 2) - 1 := by
  have hlogPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have htpos : 0 < t := hlogPos.trans_le ht
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtSquare : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith
  have hsqrtPos : 0 < Real.sqrt 2 := lt_of_lt_of_le zero_lt_one hsqrtOne
  have hfirstMass :
      screwPrefixMass suzukiPrimeWeight 1 =
        Real.log 2 / Real.sqrt 2 := by
    simp [screwPrefixMass, suzukiPrimeWeight,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hfirstMassLt : screwPrefixMass suzukiPrimeWeight 1 < 1 := by
    rw [hfirstMass, div_lt_one hsqrtPos]
    nlinarith [Real.log_two_lt_d9]
  have htwoLt : (2 : ℝ) <
      2 * Real.exp (Real.log 2 / 2) := by
    have hexp : 1 < Real.exp (Real.log 2 / 2) :=
      Real.one_lt_exp_iff.mpr (by linarith)
    nlinarith
  have hbaseSlopeOne :
      suzukiPointwiseArchimedeanSlope (Real.log 2) < 1 := by
    have hfrozen :=
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive
    unfold suzukiPointwiseFrozenBaseSlope at hfrozen
    linarith
  have hcurvatureContinuous : ContinuousOn suzukiSmoothCurvature
      (Set.Icc (Real.log 2) t) := by
    apply continuousOn_suzukiSmoothCurvature_Ioi.mono
    intro x hx
    exact hlogPos.trans_le hx.1
  have hexponentialContinuous : ContinuousOn
      (fun x : ℝ => Real.exp (x / 2))
      (Set.Icc (Real.log 2) t) := by fun_prop
  have hcurvatureIntegral :
      (∫ x in Real.log 2..t, suzukiSmoothCurvature x) ≤
        ∫ x in Real.log 2..t, Real.exp (x / 2) := by
    apply intervalIntegral.integral_mono_on ht
      (hcurvatureContinuous.intervalIntegrable_of_Icc ht)
      (hexponentialContinuous.intervalIntegrable_of_Icc ht)
    intro x hx
    exact (suzukiSmoothCurvature_lt_pureExponential
      (hlogPos.trans_le hx.1)).le
  have hexponentialIntegral :
      (∫ x in Real.log 2..t, Real.exp (x / 2)) =
        2 * Real.exp (t / 2) -
          2 * Real.exp (Real.log 2 / 2) := by
    rw [intervalIntegral.integral_comp_div Real.exp
      (by norm_num : (2 : ℝ) ≠ 0), integral_exp]
    norm_num only [smul_eq_mul]
    ring
  rw [suzukiPointwiseArchimedeanSlope_eq_integrated hlogPos htpos]
  unfold suzukiPointwiseIntegratedArchimedeanSlope
    transportCurvatureMass
  rw [hexponentialIntegral] at hcurvatureIntegral
  linarith

/-- In particular, the Archimedean slope is below its leading exponential. -/
theorem suzukiPointwiseArchimedeanSlope_lt_two_mul_exp_half
    {t : ℝ} (ht : Real.log 2 ≤ t) :
    suzukiPointwiseArchimedeanSlope t < 2 * Real.exp (t / 2) := by
  linarith [
    suzukiPointwiseArchimedeanSlope_lt_two_mul_exp_half_sub_one ht]

/-- Every canonical first-tail Chebyshev center remains beyond the original
tail base `log 2`. -/
theorem log_two_le_suzukiFirstTailChebyshevCenter (count : ℕ) :
    Real.log 2 ≤ suzukiFirstTailChebyshevCenter count := by
  unfold suzukiFirstTailChebyshevCenter
  exact base_le_suzukiResetTransportMassPoint
    (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
    (count + 1)

/-- The canonical center is the literal Archimedean slope-matching point for
the weighted Chebyshev mass at endpoint `count + 2`. -/
theorem suzukiPointwiseArchimedeanSlope_firstTailChebyshevCenter_eq_mass
    (count : ℕ) :
    suzukiPointwiseArchimedeanSlope
        (suzukiFirstTailChebyshevCenter count) =
      suzukiChebyshevWeightedMass ((count + 2 : ℕ) : ℝ) := by
  calc
    suzukiPointwiseArchimedeanSlope
        (suzukiFirstTailChebyshevCenter count) =
        screwPrefixMass suzukiPrimeWeight (count + 1) := by
          simpa [suzukiFirstTailChebyshevCenter] using
            suzukiPointwiseArchimedeanSlope_firstTailResetMassPoint_succ_eq
              count
    _ = suzukiChebyshevWeightedMass
          (((count + 1) + 1 : ℕ) : ℝ) :=
      screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass
        (count + 1)
    _ = suzukiChebyshevWeightedMass ((count + 2 : ℕ) : ℝ) := by
      congr 2

/-- At every integer endpoint at least five, the canonical Legendre center
lies no more than two logarithmic units below the endpoint. -/
theorem log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter_of_five_le
    (count : ℕ) (hendpoint : 5 ≤ count + 2) :
    Real.log ((count + 2 : ℕ) : ℝ) - 2 ≤
      suzukiFirstTailChebyshevCenter count := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  have hb5 : (5 : ℝ) ≤ b := by
    dsimp only [b]
    exact_mod_cast hendpoint
  have hbpos : 0 < b := by linarith
  have hrbase : Real.log 2 ≤ r := by
    dsimp only [r]
    exact log_two_le_suzukiFirstTailChebyshevCenter count
  have hmassLower :=
    sqrt_sub_half_sqrt_five_le_suzukiChebyshevWeightedMass hb5
  have hsqrtBNonneg : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hsqrtFiveNonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrtBSquare : Real.sqrt b ^ 2 = b :=
    Real.sq_sqrt hbpos.le
  have hsqrtFiveSquare : Real.sqrt 5 ^ 2 = 5 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtFiveLeB : Real.sqrt 5 ≤ Real.sqrt b :=
    Real.sqrt_le_sqrt hb5
  have hsqrtFiveLtThree : Real.sqrt 5 < 3 := by
    nlinarith
  have hmassNinetyTwoOneTwentyFive :
      (92 / 125 : ℝ) * Real.sqrt b - 1 ≤
        suzukiChebyshevWeightedMass b := by
    nlinarith
  by_contra hcenter
  have hrlt : r < Real.log b - 2 := by
    dsimp only [r, b] at hcenter ⊢
    exact lt_of_not_ge hcenter
  have hhalf : r / 2 < Real.log b / 2 - 1 := by linarith
  have hexpLt := Real.exp_lt_exp.mpr hhalf
  have hexpEndpoint :
      Real.exp (Real.log b / 2 - 1) =
        Real.sqrt b * Real.exp (-1) := by
    rw [show Real.log b / 2 - 1 =
        Real.log b / 2 + (-1) by ring,
      Real.exp_add, Real.exp_half, Real.exp_log hbpos]
  rw [hexpEndpoint] at hexpLt
  have hnegOne : Real.exp (-1) < (46 / 125 : ℝ) :=
    Real.exp_neg_one_lt_d9.trans (by norm_num)
  have hscaledNegOne :
      Real.sqrt b * Real.exp (-1) <
        Real.sqrt b * (46 / 125 : ℝ) :=
    mul_lt_mul_of_pos_left hnegOne (Real.sqrt_pos.2 hbpos)
  have hexpUpper :
      2 * Real.exp (r / 2) < (92 / 125 : ℝ) * Real.sqrt b := by
    nlinarith
  have harchUpper :=
    suzukiPointwiseArchimedeanSlope_lt_two_mul_exp_half_sub_one hrbase
  have hmatch :=
    suzukiPointwiseArchimedeanSlope_firstTailChebyshevCenter_eq_mass
      count
  dsimp only [r, b] at harchUpper hmatch ⊢
  rw [hmatch] at harchUpper
  nlinarith

/-- The remaining endpoints below five are covered directly by the base
location, so the same two-unit localization holds for every canonical
prefix. -/
theorem log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter
    (count : ℕ) :
    Real.log ((count + 2 : ℕ) : ℝ) - 2 ≤
      suzukiFirstTailChebyshevCenter count := by
  by_cases hfive : 5 ≤ count + 2
  · exact
      log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter_of_five_le
        count hfive
  have hfour : count + 2 ≤ 4 := by omega
  have hcast : ((count + 2 : ℕ) : ℝ) ≤ 4 := by
    exact_mod_cast hfour
  have hendPos : (0 : ℝ) < ((count + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < count + 2 by omega)
  have hlogEndpoint :
      Real.log ((count + 2 : ℕ) : ℝ) ≤ Real.log 4 :=
    Real.log_le_log hendPos hcast
  have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlogFour] at hlogEndpoint
  have hsmall :
      Real.log ((count + 2 : ℕ) : ℝ) - 2 ≤ Real.log 2 := by
    nlinarith [Real.log_two_lt_d9]
  exact hsmall.trans (log_two_le_suzukiFirstTailChebyshevCenter count)

/-! ## The large-prefix kernel regime -/

/-- On every canonical prefix, the explicit centered Abel derivative is
nonnegative throughout the complete prefix interval. -/
theorem deriv_suzukiChebyshevCenteredKernel_nonneg_on_firstTailPrefix
    (count : ℕ) {x : ℝ} (hxone : 1 ≤ x)
    (hxend : x ≤ ((count + 2 : ℕ) : ℝ)) :
    0 ≤ deriv
      (suzukiChebyshevCenteredKernel
        (suzukiFirstTailChebyshevCenter count)) x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hlog := Real.log_le_log hxpos hxend
  have hcenter :=
    log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter
      count
  rw [deriv_suzukiChebyshevCenteredKernel
    (suzukiFirstTailChebyshevCenter count) hxpos]
  apply mul_nonneg (Real.rpow_nonneg hxpos.le _)
  nlinarith

/-- Thus the centered Abel kernel itself is monotone on every canonical
integer prefix interval. -/
theorem monotoneOn_suzukiChebyshevCenteredKernel_firstTailPrefix
    (count : ℕ) :
    MonotoneOn
      (suzukiChebyshevCenteredKernel
        (suzukiFirstTailChebyshevCenter count))
      (Set.Icc 1 (((count + 2 : ℕ) : ℝ))) := by
  let r := suzukiFirstTailChebyshevCenter count
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  apply monotoneOn_of_deriv_nonneg (convex_Icc (1 : ℝ) b)
  · intro x hx
    unfold suzukiChebyshevCenteredKernel suzukiChebyshevMassKernel
    exact ((Real.continuousAt_log
      (zero_lt_one.trans_le hx.1).ne').sub continuousAt_const).mul
        (Real.continuousAt_rpow_const x (-1 / 2 : ℝ)
          (Or.inl (zero_lt_one.trans_le hx.1).ne')) |>.continuousWithinAt
  · intro x hx
    have hxIoo : x ∈ Set.Ioo (1 : ℝ) b := by
      simpa only [interior_Icc] using hx
    unfold suzukiChebyshevCenteredKernel suzukiChebyshevMassKernel
    exact ((Real.differentiableAt_log
      (zero_lt_one.trans hxIoo.1).ne').sub_const r).mul
        (Real.differentiableAt_rpow_const_of_ne _
          (zero_lt_one.trans hxIoo.1).ne') |>.differentiableWithinAt
  · intro x hx
    have hxIoo : x ∈ Set.Ioo (1 : ℝ) b := by
      simpa only [interior_Icc] using hx
    exact deriv_suzukiChebyshevCenteredKernel_nonneg_on_firstTailPrefix
      count hxIoo.1.le hxIoo.2.le

/-- Positive-kernel moment form of the direct arithmetic frontier.  Because
the derivative in the integral is nonnegative by
`deriv_suzukiChebyshevCenteredKernel_nonneg_on_firstTailPrefix`, tail
positivity is now exactly a one-sided upper bound on the PNT error, rather
than an estimate against a sign-indefinite test function. -/
theorem
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_chebyshevPNTPositiveKernelMoment :
    (∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ count : ℕ, 1 ≤ count →
        (∫ x in Set.Ioc (1 : ℝ) ((count + 2 : ℕ) : ℝ),
            deriv
                (suzukiChebyshevCenteredKernel
                  (suzukiFirstTailChebyshevCenter count)) x *
              (Chebyshev.psi x - x)) ≤
          suzukiChebyshevCenteredKernel
              (suzukiFirstTailChebyshevCenter count)
              ((count + 2 : ℕ) : ℝ) *
            (Chebyshev.psi ((count + 2 : ℕ) : ℝ) -
              ((count + 2 : ℕ) : ℝ)) +
          suzukiPointwiseArchimedean
              (suzukiFirstTailChebyshevCenter count) +
          2 * ((((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
            (Real.log ((count + 2 : ℕ) : ℝ) -
              suzukiFirstTailChebyshevCenter count - 2)) +
          suzukiFirstTailChebyshevCenter count + 4 := by
  rw [
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_chebyshevPNTErrorLowerBound]
  constructor
  · intro hlower count hcount
    have hbound := hlower count hcount
    unfold suzukiChebyshevCenteredPNTError at hbound
    linarith
  · intro hmoments count hcount
    have hmoment := hmoments count hcount
    unfold suzukiChebyshevCenteredPNTError
    linarith

end

end RiemannGaussian
