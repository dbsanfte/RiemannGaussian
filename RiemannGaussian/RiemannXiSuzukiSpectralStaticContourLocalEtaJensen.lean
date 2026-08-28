import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourCriticalZetaUpper
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Moving local Jensen disks for the paired eta function

The radial entire-function argument loses a full factor of the height because
it counts every xi zero below the endpoint.  This module replaces that global
geometry by a fixed disk translated with the endpoint.  We apply Jensen's
inequality to the paired Dirichlet eta function, rather than to xi itself.

This removes the common archimedean decay before estimating anything.  The
paired eta series is analytic and grows only linearly on the translated disk;
at its safe center `3 / 2 + I*T`, its eta factor and zeta value both have a
uniform positive lower bound.  Consequently the multiplicity-weighted number
of eta zeros in the fixed inner disk is `O(log (T + 4))`.
-/

open Complex Filter MeasureTheory MeromorphicOn Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Radius of the disk whose eta zeros will be retained in the local
canonical decomposition.  It strictly contains the critical endpoint, which
is one unit left of the safe center. -/
def staticContourLocalEtaInnerRadius : ℝ := 9 / 8

/-- Radius of the larger Jensen disk.  It leaves the entire translated disk
inside `0 < re s`. -/
def staticContourLocalEtaOuterRadius : ℝ := 5 / 4

lemma staticContourLocalEtaInnerRadius_pos :
    0 < staticContourLocalEtaInnerRadius := by
  norm_num [staticContourLocalEtaInnerRadius]

lemma staticContourLocalEtaInnerRadius_lt_outer :
    staticContourLocalEtaInnerRadius < staticContourLocalEtaOuterRadius := by
  norm_num [staticContourLocalEtaInnerRadius,
    staticContourLocalEtaOuterRadius]

/-- The paired eta function translated so that the safe endpoint is the
origin. -/
def staticContourLocalEta (T : ℝ) (z : ℂ) : ℂ :=
  pairedEtaCore (staticContourSafeEndpoint T + z)

/-- Fixed summable mass which majorizes paired eta throughout the translated
outer disk. -/
def staticContourLocalEtaMass : ℝ :=
  ∑' n : ℕ, ((((2 * n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹

lemma summable_staticContourLocalEtaMass :
    Summable (fun n : ℕ =>
      ((((2 * n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹) := by
  have hfull : Summable
      (fun m : ℕ => ((((m : ℝ) + 1) ^ (5 / 4 : ℝ)))⁻¹) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow 1 (5 / 4 : ℝ)).mpr (by norm_num)
    apply h.congr
    intro m
    rw [abs_of_nonneg (by positivity)]
    simp only [one_div]
  simpa [Function.comp_def] using
    hfull.comp_injective (i := fun n : ℕ => 2 * n) (by
      intro n m h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)

lemma one_le_staticContourLocalEtaMass :
    1 ≤ staticContourLocalEtaMass := by
  unfold staticContourLocalEtaMass
  have hone : ((((2 * 0 + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹ = 1 := by
    norm_num
  rw [← hone]
  apply summable_staticContourLocalEtaMass.le_tsum 0
  intro n _hn
  positivity

/-- The paired eta series has a uniform linear-in-`s` bound on the half-strip
`1 / 4 ≤ re s`. -/
lemma norm_pairedEtaCore_le_localStrip
    {s : ℂ} (hs : 1 / 4 ≤ s.re) :
    ‖pairedEtaCore s‖ ≤ ‖s‖ * staticContourLocalEtaMass := by
  have hspos : 0 < s.re := by linarith
  have heta := summable_pairedEtaCoreSummand hspos
  have hetanorm : Summable (fun n => ‖pairedEtaCoreSummand s n‖) :=
    summable_norm_iff.mpr heta
  have hmajor : Summable (fun n : ℕ => ‖s‖ *
      ((((2 * n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹) :=
    summable_staticContourLocalEtaMass.mul_left ‖s‖
  unfold pairedEtaCore
  calc
    ‖∑' n : ℕ, pairedEtaCoreSummand s n‖ ≤
        ∑' n : ℕ, ‖pairedEtaCoreSummand s n‖ :=
      norm_tsum_le_tsum_norm hetanorm
    _ ≤ ∑' n : ℕ, ‖s‖ *
        ((((2 * n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹ := by
      apply hetanorm.tsum_le_tsum _ hmajor
      intro n
      have hraw := norm_pairedEtaCoreSummand_le hspos n
      let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
      have ha1 : 1 ≤ a := by
        dsimp [a]
        exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
      have ha0 : 0 ≤ a := zero_le_one.trans ha1
      have hpow : a ^ (-(s.re + 1)) ≤ a ^ (-(5 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
      calc
        ‖pairedEtaCoreSummand s n‖ ≤
            ‖s‖ * (a ^ (s.re + 1))⁻¹ := by
          simpa [a] using hraw
        _ = ‖s‖ * a ^ (-(s.re + 1)) := by
          rw [Real.rpow_neg ha0]
        _ ≤ ‖s‖ * a ^ (-(5 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg s)
        _ = ‖s‖ * (a ^ (5 / 4 : ℝ))⁻¹ := by
          rw [Real.rpow_neg ha0]
        _ = ‖s‖ *
            ((((2 * n + 1 : ℕ) : ℝ) ^ (5 / 4 : ℝ)))⁻¹ := rfl
    _ = ‖s‖ * staticContourLocalEtaMass := by
      unfold staticContourLocalEtaMass
      exact summable_staticContourLocalEtaMass.tsum_mul_left ‖s‖

/-- The translated eta function is analytic on the larger Jensen disk. -/
lemma analyticOnNhd_staticContourLocalEta_closedBall
    (T : ℝ) :
    AnalyticOnNhd ℂ (staticContourLocalEta T)
      (closedBall 0 staticContourLocalEtaOuterRadius) := by
  intro z hz
  have hznorm : ‖z‖ ≤ staticContourLocalEtaOuterRadius := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hzre : -‖z‖ ≤ z.re := by
    exact (abs_le.mp (Complex.abs_re_le_norm z)).1
  have hre : 0 < (staticContourSafeEndpoint T + z).re := by
    simp only [staticContourSafeEndpoint, add_re, ofReal_re, mul_re,
      ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [staticContourLocalEtaOuterRadius] at hznorm
    linarith
  unfold staticContourLocalEta
  exact (analyticOnNhd_pairedEtaCore
    (staticContourSafeEndpoint T + z) hre).comp
      (analyticAt_const.add analyticAt_id)

/-- On the outer Jensen disk, translated eta is bounded by a fixed mass
times `T + 4`. -/
lemma norm_staticContourLocalEta_le
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ closedBall 0 staticContourLocalEtaOuterRadius) :
    ‖staticContourLocalEta T z‖ ≤
      staticContourLocalEtaMass * (T + 4) := by
  have hznorm : ‖z‖ ≤ staticContourLocalEtaOuterRadius := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hzre : -‖z‖ ≤ z.re := by
    exact (abs_le.mp (Complex.abs_re_le_norm z)).1
  have hre : 1 / 4 ≤ (staticContourSafeEndpoint T + z).re := by
    simp only [staticContourSafeEndpoint, add_re, ofReal_re, mul_re,
      ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [staticContourLocalEtaOuterRadius] at hznorm
    linarith
  have hsafe : ‖staticContourSafeEndpoint T‖ ≤ T + 3 / 2 := by
    unfold staticContourSafeEndpoint
    calc
      ‖((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I‖ ≤
          ‖((3 / 2 : ℝ) : ℂ)‖ + ‖(T : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = 3 / 2 + T := by simp [abs_of_nonneg hT]
      _ = T + 3 / 2 := by ring
  have harg : ‖staticContourSafeEndpoint T + z‖ ≤ T + 4 := by
    calc
      ‖staticContourSafeEndpoint T + z‖ ≤
          ‖staticContourSafeEndpoint T‖ + ‖z‖ := norm_add_le _ _
      _ ≤ (T + 3 / 2) + staticContourLocalEtaOuterRadius :=
        add_le_add hsafe hznorm
      _ ≤ T + 4 := by
        dsimp [staticContourLocalEtaOuterRadius]
        linarith
  unfold staticContourLocalEta
  calc
    ‖pairedEtaCore (staticContourSafeEndpoint T + z)‖ ≤
        ‖staticContourSafeEndpoint T + z‖ * staticContourLocalEtaMass :=
      norm_pairedEtaCore_le_localStrip hre
    _ ≤ (T + 4) * staticContourLocalEtaMass :=
      mul_le_mul_of_nonneg_right harg
        (zero_le_one.trans one_le_staticContourLocalEtaMass)
    _ = staticContourLocalEtaMass * (T + 4) := by ring

/-- The norm of the nonconstant term in the eta factor on the safe line. -/
lemma norm_two_mul_two_cpow_neg_safe (T : ℝ) :
    ‖(2 : ℂ) * (2 : ℂ) ^
        (-(staticContourSafeEndpoint T))‖ =
      (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let s : ℂ := staticContourSafeEndpoint T
  have hsre : (-s).re = -(3 / 2 : ℝ) := by
    simp [s, staticContourSafeEndpoint]
  calc
    ‖(2 : ℂ) * (2 : ℂ) ^ (-s)‖ =
        2 * ‖(2 : ℂ) ^ (-s)‖ := by
      rw [norm_mul]
      norm_num
    _ = 2 * (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
      congr 1
      change ‖(((2 : ℝ) : ℂ) ^ (-s))‖ =
        (2 : ℝ) ^ (-(3 / 2 : ℝ))
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
        hsre]
    _ = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
      calc
        2 * (2 : ℝ) ^ (-(3 / 2 : ℝ)) =
            (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.rpow_one]
        _ = (2 : ℝ) ^ ((1 : ℝ) + -(3 / 2 : ℝ)) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by norm_num

/-- A positive, height-independent lower floor for the safe-line eta
factor. -/
def staticContourSafeEtaFactorFloor : ℝ :=
  1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))

lemma staticContourSafeEtaFactorFloor_pos :
    0 < staticContourSafeEtaFactorFloor := by
  unfold staticContourSafeEtaFactorFloor
  have hpow : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < (2 : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  simpa using hpow

lemma staticContourSafeEtaFactorFloor_le (T : ℝ) :
    staticContourSafeEtaFactorFloor ≤
      ‖1 - (2 : ℂ) * (2 : ℂ) ^
        (-(staticContourSafeEndpoint T))‖ := by
  let a : ℂ := (2 : ℂ) * (2 : ℂ) ^
    (-(staticContourSafeEndpoint T))
  have ha : ‖a‖ = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    simpa [a] using norm_two_mul_two_cpow_neg_safe T
  have hpow : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 :=
    (Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by norm_num : -(1 / 2 : ℝ) < 0)).le.trans_eq (by norm_num)
  have hreverse := norm_sub_norm_le (1 : ℂ) a
  rw [norm_one, ha] at hreverse
  simpa [a, staticContourSafeEtaFactorFloor] using hreverse

/-- At the safe center, translated eta is uniformly bounded away from zero.
The zeta lower bound comes from the absolutely convergent Möbius series. -/
lemma staticContourSafeEtaFactorFloor_div_mass_le_norm_localEta_zero
    {T : ℝ} (hT : 0 < T) :
    staticContourSafeEtaFactorFloor /
        staticContourSafeZetaDirichletMass ≤
      ‖staticContourLocalEta T 0‖ := by
  let s : ℂ := staticContourSafeEndpoint T
  have hsre : s.re = 3 / 2 := by simp [s, staticContourSafeEndpoint]
  have heta := pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_im_pos
    (s := s) (by simp [s, staticContourSafeEndpoint])
    (by simpa [s, staticContourSafeEndpoint] using hT)
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; norm_num)
  have hmassPos : 0 < staticContourSafeZetaDirichletMass :=
    one_pos.trans_le one_le_staticContourSafeZetaDirichletMass
  have hinv := norm_inv_riemannZeta_safeLine_le_mass hsre
  have hzetaLower : 1 / staticContourSafeZetaDirichletMass ≤
      ‖riemannZeta s‖ := by
    apply (div_le_iff₀ hmassPos).mpr
    simpa [mul_comm] using (show
        1 ≤ staticContourSafeZetaDirichletMass * ‖riemannZeta s‖ from calc
      1 = ‖(riemannZeta s)⁻¹‖ * ‖riemannZeta s‖ := by
        rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hzeta)]
      _ ≤ staticContourSafeZetaDirichletMass * ‖riemannZeta s‖ :=
        mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
  have hfactor := staticContourSafeEtaFactorFloor_le T
  unfold staticContourLocalEta
  simp only [add_zero]
  rw [heta, norm_mul]
  calc
    staticContourSafeEtaFactorFloor /
        staticContourSafeZetaDirichletMass =
    staticContourSafeEtaFactorFloor *
          (1 / staticContourSafeZetaDirichletMass) := by ring
    _ ≤ ‖1 - 2 * (2 : ℂ) ^ (-s)‖ * ‖riemannZeta s‖ :=
      mul_le_mul hfactor hzetaLower (by positivity) (norm_nonneg _)

/-- A fixed positive constant which packages the safe-center lower bound in
the explicit Jensen estimate. -/
def staticContourLocalEtaJensenConstant : ℝ :=
  staticContourLocalEtaMass * staticContourSafeZetaDirichletMass /
    staticContourSafeEtaFactorFloor

lemma staticContourLocalEtaJensenConstant_pos :
    0 < staticContourLocalEtaJensenConstant := by
  unfold staticContourLocalEtaJensenConstant
  positivity [one_le_staticContourLocalEtaMass,
    one_le_staticContourSafeZetaDirichletMass,
    staticContourSafeEtaFactorFloor_pos]

/-- Moving-center Jensen estimate: the multiplicity-weighted number of eta
zeros in the fixed inner disk is at most a constant times `log (T + 4)`.
The displayed right side is completely explicit and contains no global xi
zero count. -/
theorem sum_divisor_staticContourLocalEta_closedBall_le_log
    {T : ℝ} (hT : 0 < T) :
    (∑ᶠ u, divisor (staticContourLocalEta T)
        (closedBall 0 staticContourLocalEtaInnerRadius) u : ℤ) ≤
      Real.log (staticContourLocalEtaJensenConstant * (T + 4)) /
        Real.log (10 / 9 : ℝ) := by
  let M : ℝ := staticContourLocalEtaMass * (T + 4)
  have hM : 1 ≤ M := by
    dsimp [M]
    nlinarith [one_le_staticContourLocalEtaMass]
  have hcenterLower :=
    staticContourSafeEtaFactorFloor_div_mass_le_norm_localEta_zero hT
  have hcenterFloorPos :
      0 < staticContourSafeEtaFactorFloor /
          staticContourSafeZetaDirichletMass := by
    positivity [staticContourSafeEtaFactorFloor_pos,
      one_le_staticContourSafeZetaDirichletMass]
  have hcenterPos : 0 < ‖staticContourLocalEta T 0‖ :=
    hcenterFloorPos.trans_le hcenterLower
  have houterPos : 0 < staticContourLocalEtaOuterRadius := by
    norm_num [staticContourLocalEtaOuterRadius]
  have hanalytic : AnalyticOnNhd ℂ (staticContourLocalEta T)
      (closedBall 0 |staticContourLocalEtaOuterRadius|) := by
    simpa [abs_of_pos houterPos] using
      analyticOnNhd_staticContourLocalEta_closedBall T
  have hjensen :=
    hanalytic.sum_divisor_le
      (r := staticContourLocalEtaInnerRadius)
      (R := staticContourLocalEtaOuterRadius) (M := M)
      (by norm_num [staticContourLocalEtaInnerRadius])
      (by norm_num [staticContourLocalEtaInnerRadius,
        staticContourLocalEtaOuterRadius]) hM
      (norm_pos_iff.mp hcenterPos) (by
        intro z hz
        apply norm_staticContourLocalEta_le hT.le
        apply sphere_subset_closedBall
        simpa [abs_of_pos houterPos] using hz)
  have hratio : M / ‖staticContourLocalEta T 0‖ ≤
      staticContourLocalEtaJensenConstant * (T + 4) := by
    calc
      M / ‖staticContourLocalEta T 0‖ ≤
          M / (staticContourSafeEtaFactorFloor /
            staticContourSafeZetaDirichletMass) :=
        div_le_div_of_nonneg_left (by positivity) hcenterFloorPos hcenterLower
      _ = staticContourLocalEtaJensenConstant * (T + 4) := by
        dsimp [M, staticContourLocalEtaJensenConstant]
        field_simp [staticContourSafeEtaFactorFloor_pos.ne',
          (one_pos.trans_le one_le_staticContourSafeZetaDirichletMass).ne']
  have hlog : Real.log (M / ‖staticContourLocalEta T 0‖) ≤
      Real.log (staticContourLocalEtaJensenConstant * (T + 4)) := by
    apply Real.log_le_log
    · positivity
    · exact hratio
  have hden : 0 < Real.log (10 / 9 : ℝ) :=
    Real.log_pos (by norm_num)
  calc
    (∑ᶠ u, divisor (staticContourLocalEta T)
        (closedBall 0 staticContourLocalEtaInnerRadius) u : ℤ) ≤
        Real.log (M / ‖staticContourLocalEta T 0‖) /
          Real.log (staticContourLocalEtaOuterRadius /
            staticContourLocalEtaInnerRadius) := by
      have hinnerAbs : |staticContourLocalEtaInnerRadius| =
          staticContourLocalEtaInnerRadius :=
        abs_of_pos staticContourLocalEtaInnerRadius_pos
      rw [hinnerAbs] at hjensen
      exact hjensen
    _ = Real.log (M / ‖staticContourLocalEta T 0‖) /
          Real.log (10 / 9 : ℝ) := by
      norm_num [staticContourLocalEtaInnerRadius,
        staticContourLocalEtaOuterRadius]
    _ ≤ Real.log (staticContourLocalEtaJensenConstant * (T + 4)) /
          Real.log (10 / 9 : ℝ) :=
      div_le_div_of_nonneg_right hlog hden.le

/-- The explicit logarithmic Jensen majorant is `o(T)` along the selected
quantitative heights. -/
lemma tendsto_staticContourLocalEta_logJensenMajorant_div_quantitative_zero :
    Tendsto
      (fun n : ℕ =>
        Real.log
            (staticContourLocalEtaJensenConstant *
              (quantitativeSpectralBoundaryTruncation n + 4)) /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let C : ℝ := staticContourLocalEtaJensenConstant
  have hTatTop : Tendsto T atTop atTop :=
    tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hshift : Tendsto (fun n : ℕ => T n + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 hTatTop
  have hconst : Tendsto (fun n : ℕ => Real.log C / T n)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hTatTop
  have hlog : Tendsto (fun n : ℕ => Real.log (T n + 4) / T n)
      atTop (nhds 0) := by
    have hraw :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-4) 1 one_ne_zero).comp hshift
    refine hraw.congr' (Eventually.of_forall fun n => ?_)
    simp only [Function.comp_apply, pow_one, one_mul]
    congr 1
    ring
  have hsum : Tendsto
      (fun n : ℕ => Real.log C / T n + Real.log (T n + 4) / T n)
      atTop (nhds 0) := by
    simpa using hconst.add hlog
  refine hsum.congr' (Eventually.of_forall fun n => ?_)
  have hTpos : 0 < T n :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hCpos : 0 < C := by
    simpa [C] using staticContourLocalEtaJensenConstant_pos
  change Real.log C / T n + Real.log (T n + 4) / T n =
    Real.log (C * (T n + 4)) / T n
  rw [Real.log_mul hCpos.ne' (by linarith : T n + 4 ≠ 0)]
  ring

/-- The multiplicity-weighted number of paired-eta zeros in the moving local
disk is sublinear in the endpoint height. -/
theorem tendsto_sum_divisor_staticContourLocalEta_closedBall_div_quantitative_zero :
    Tendsto
      (fun n : ℕ =>
        ((∑ᶠ u, divisor
            (staticContourLocalEta
              (quantitativeSpectralBoundaryTruncation n))
            (closedBall 0 staticContourLocalEtaInnerRadius) u : ℤ) : ℝ) /
          quantitativeSpectralBoundaryTruncation n)
      atTop (nhds 0) := by
  let T : ℕ → ℝ := quantitativeSpectralBoundaryTruncation
  let N : ℕ → ℝ := fun n =>
    ((∑ᶠ u, divisor (staticContourLocalEta (T n))
      (closedBall 0 staticContourLocalEtaInnerRadius) u : ℤ) : ℝ)
  let B : ℕ → ℝ := fun n =>
    (Real.log (staticContourLocalEtaJensenConstant * (T n + 4)) / T n) /
      Real.log (10 / 9 : ℝ)
  apply squeeze_zero'
  · exact Eventually.of_forall fun n => by
      have hTpos : 0 < T n :=
        (Nat.cast_nonneg n).trans_lt
          (by simpa [T] using
            (quantitativeSpectralBoundaryTruncation_spec n).1)
      have hanalytic := analyticOnNhd_staticContourLocalEta_closedBall (T n)
      have hanalyticInner : AnalyticOnNhd ℂ
          (staticContourLocalEta (T n))
          (closedBall 0 staticContourLocalEtaInnerRadius) :=
        hanalytic.mono (closedBall_subset_closedBall
          staticContourLocalEtaInnerRadius_lt_outer.le)
      have hsumInt : 0 ≤
          ∑ᶠ u, divisor (staticContourLocalEta (T n))
            (closedBall 0 staticContourLocalEtaInnerRadius) u :=
        finsum_nonneg fun u => hanalyticInner.divisor_nonneg u
      have hN : 0 ≤ N n := by
        dsimp [N]
        exact_mod_cast hsumInt
      exact div_nonneg hN hTpos.le
  · exact Eventually.of_forall fun n => by
      have hTpos : 0 < T n :=
        (Nat.cast_nonneg n).trans_lt
          (by simpa [T] using
            (quantitativeSpectralBoundaryTruncation_spec n).1)
      have hcount := sum_divisor_staticContourLocalEta_closedBall_le_log hTpos
      have hdiv := div_le_div_of_nonneg_right hcount hTpos.le
      calc
        ((↑(∑ᶠ u, divisor (staticContourLocalEta (T n))
              (closedBall 0 staticContourLocalEtaInnerRadius) u) : ℝ) / T n) ≤
            (Real.log (staticContourLocalEtaJensenConstant * (T n + 4)) /
              Real.log (10 / 9 : ℝ)) / T n := hdiv
        _ = (Real.log (staticContourLocalEtaJensenConstant * (T n + 4)) /
              T n) / Real.log (10 / 9 : ℝ) := by ring
  · have hbase :=
      tendsto_staticContourLocalEta_logJensenMajorant_div_quantitative_zero
    have hscaled := hbase.div_const (Real.log (10 / 9 : ℝ))
    simpa [B, T] using hscaled

end

end RiemannGaussian
