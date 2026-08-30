import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredTailQuantitativeAsymptotic
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualComplexAsymptotic
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTail
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Sharp complex asymptotic of the finite centered-residual work

The completed centered residual has an exact triangular one-step work law.
At a hypothetical right-half zero of multiplicity `m`, endpoint normalization
by the slower reflected partner kills the newly exposed order-`m` head and
every transported order below `m - 1`.  The single surviving order `m - 1`
has a universal shifted eta-tail limit.

Consequently the actual finite arithmetic work `W_N = R_N - R_(N+1)` obeys

`(2N+1)^(rho# + 1) * W_N -> 2 * rho# * L(rho)`,

where `L(rho)` is the already proved nonzero complex residual constant and
`rho# = 1 - conjugate(rho)`.  Thus the signed work has a rigorously identified
nonzero phase-bearing leading term under an off-line-zero hypothesis.  This
does not prove RH: the remaining task is an unconditional arithmetic
cancellation theorem strong enough to exclude that asymptotic.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

private theorem tendsto_oddEndpoint_mul_shiftIncrement_two_aux :
    Tendsto (fun N : ℕ =>
      ((2 * N + 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement N)
      atTop (nhds 2) := by
  have hbase : Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ))
      atTop atTop := by
    convert tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2)) using 1
    funext N
    norm_num
  have hlog :=
    (Real.tendsto_mul_log_one_add_div_atTop 2).comp hbase
  apply hlog.congr'
  filter_upwards with N
  dsimp only [Function.comp_apply]
  let M : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  have hM : 0 < M := by dsimp [M]; positivity
  change M * Real.log (1 + 2 / M) =
    M * pairedEtaLogTailShiftIncrement N
  unfold pairedEtaLogTailShiftIncrement pairedEtaLogTailCutoff
  have hsucc : ((2 * (N + 1) + 1 : ℕ) : ℝ) = M + 2 := by
    dsimp [M]
    push_cast
    ring
  rw [hsucc, ← Real.log_div (by linarith) hM.ne']
  congr 2
  field_simp [hM.ne']

private theorem tendsto_oddEndpoint_div_succ_cpow_one_aux (s : ℂ) :
    Tendsto (fun N : ℕ =>
      (((((2 * N + 1 : ℕ) : ℝ) : ℂ) /
        (((2 * (N + 1) + 1 : ℕ) : ℝ) : ℂ))) ^ s)
      atTop (nhds 1) := by
  have hbase : Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ))
      atTop atTop := by
    convert tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2)) using 1
    funext N
    norm_num
  have hinv : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hbase
  have hden : Tendsto (fun N : ℕ =>
      1 + 2 * (((2 * N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 1) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (Filter.Tendsto.const_mul 2 hinv)
  have hratioReal : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) /
        ((2 * (N + 1) + 1 : ℕ) : ℝ))) atTop (nhds 1) := by
    have hinvden := hden.inv₀ (by norm_num)
    have heq : Filter.EventuallyEq atTop (fun N : ℕ =>
        (1 + 2 * (((2 * N + 1 : ℕ) : ℝ))⁻¹)⁻¹)
        (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ) /
          ((2 * (N + 1) + 1 : ℕ) : ℝ)) := by
      filter_upwards with N
      let M : ℝ := ((2 * N + 1 : ℕ) : ℝ)
      have hM : 0 < M := by dsimp [M]; positivity
      have hsucc : ((2 * (N + 1) + 1 : ℕ) : ℝ) = M + 2 := by
        dsimp [M]
        push_cast
        ring
      change (1 + 2 * M⁻¹)⁻¹ = M /
        ((2 * (N + 1) + 1 : ℕ) : ℝ)
      rw [hsucc]
      field_simp [hM.ne', (by linarith : M + 2 ≠ 0)]
    simpa using hinvden.congr' heq
  have hratioComplex : Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ) /
        (((2 * (N + 1) + 1 : ℕ) : ℝ) : ℂ))) atTop (nhds 1) := by
    have hc := Complex.continuous_ofReal.tendsto 1 |>.comp hratioReal
    convert hc using 1
    · funext N
      simp only [Function.comp_apply, ofReal_div, ofReal_natCast]
    · norm_num
  simpa only [Complex.one_cpow] using
    hratioComplex.cpow tendsto_const_nhds Complex.one_mem_slitPlane

private theorem tendsto_shiftIncrement_zero_aux :
    Tendsto pairedEtaLogTailShiftIncrement atTop (nhds 0) := by
  have hscale := tendsto_oddEndpoint_mul_shiftIncrement_two_aux
  have hbase : Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ))
      atTop atTop := by
    convert tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 2)) using 1
    funext N
    norm_num
  have hinv : Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hbase
  have hprod := hscale.mul hinv
  simpa only [mul_zero] using hprod.congr' (Eventually.of_forall fun N => by
    have hM : (((2 * N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hM])

private theorem tendsto_oddEndpoint_mul_shiftIncrement_pow_zero_aux
    {d : ℕ} (hd : 2 ≤ d) :
    Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) *
        pairedEtaLogTailShiftIncrement N ^ d)) atTop (nhds 0) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hscale := tendsto_oddEndpoint_mul_shiftIncrement_two_aux
  have hpow := tendsto_shiftIncrement_zero_aux.pow (e + 1)
  have hprod := hscale.mul hpow
  simpa using hprod.congr' (Eventually.of_forall fun N => by
    push_cast
    change ((2 * (N : ℝ) + 1) *
        pairedEtaLogTailShiftIncrement N) *
          pairedEtaLogTailShiftIncrement N ^ (e + 1) =
      (2 * (N : ℝ) + 1) *
        pairedEtaLogTailShiftIncrement N ^ (2 + e)
    rw [show 2 + e = (e + 1) + 1 by omega, pow_succ]
    ring)

private theorem norm_shiftedHeadLaplaceMoment_le_aux
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaShiftedLogHeadLaplaceMoment k s N‖ ≤
      pairedEtaShiftedLogHeadWidth N ^ (k + 1) := by
  let w : ℝ := pairedEtaShiftedLogHeadWidth N
  have hw : 0 < w := by
    simpa only [w] using pairedEtaShiftedLogHeadWidth_pos N
  rw [pairedEtaShiftedLogHeadLaplaceMoment,
    pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc]
  have hbound : ∀ᵐ u : ℝ ∂volume.restrict (Ioc 0 w),
      ‖(u : ℂ) ^ k * Complex.exp (-s * u)‖ ≤ w ^ k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hu.1,
      Complex.norm_exp]
    have hexp : Real.exp ((-s * (u : ℂ)).re) ≤ 1 := by
      have hre : (-s * (u : ℂ)).re = -s.re * u := by
        simp [Complex.mul_re]
      rw [hre]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hs.le) hu.1.le)
    exact (mul_le_of_le_one_right (pow_nonneg hu.1.le k) hexp).trans
      (pow_le_pow_left₀ hu.1.le hu.2 k)
  change ‖∫ u : ℝ, (u : ℂ) ^ k * Complex.exp (-s * u)
      ∂volume.restrict (Ioc 0 w)‖ ≤ w ^ (k + 1)
  calc
    ‖∫ u : ℝ, (u : ℂ) ^ k * Complex.exp (-s * u)
          ∂volume.restrict (Ioc 0 w)‖ ≤
        w ^ k * (volume.restrict (Ioc 0 w)).real univ :=
      norm_integral_le_of_norm_le_const hbound
    _ = w ^ (k + 1) := by
      rw [measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le hw.le]
      ring
    _ = pairedEtaShiftedLogHeadWidth N ^ (k + 1) := by rfl

private theorem norm_shiftedHeadFourierMoment_le_aux
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) (gamma : ℝ) (N : ℕ) :
    ‖pairedEtaShiftedLogHeadFourierMoment k sigma gamma N‖ ≤
      pairedEtaShiftedLogHeadWidth N ^ (k + 1) := by
  let s : ℂ := (sigma : ℂ) + (gamma : ℂ) * I
  have hs : 0 < s.re := by simpa [s] using hsigma
  have hbound := norm_shiftedHeadLaplaceMoment_le_aux k hs N
  rw [pairedEtaShiftedLogHeadLaplaceMoment_eq_fourierMoment] at hbound
  simpa [s] using hbound

private def finiteWorkHeadBoundConstantAux (rho : NontrivialZetaZero) : ℝ :=
  ‖pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
      (NontrivialZetaZero.conjugatePartner rho).1‖ +
    ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖

private theorem norm_phase_headCoupled_le_aux
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (k N : ℕ) :
    ‖pairedEtaLogTailCutoffOscillation rho.1.im N *
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
          rho k N‖ ≤
      finiteWorkHeadBoundConstantAux rho *
        (((2 * N + 1 : ℕ) : ℝ) ^
          (-(NontrivialZetaZero.conjugatePartner rho).1.re)) *
        pairedEtaShiftedLogHeadWidth N ^ (k + 1) := by
  let p := (NontrivialZetaZero.conjugatePartner rho).1
  let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
  let w : ℝ := pairedEtaShiftedLogHeadWidth N
  let A := pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient rho N
  let B := pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient rho N
  let MP := pairedEtaShiftedLogHeadFourierMoment k (1 - rho.1.re) rho.1.im N
  let MR := pairedEtaShiftedLogHeadFourierMoment k rho.1.re (-rho.1.im) N
  have hx : 0 < x := by dsimp [x]; positivity
  have hxOne : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show 1 ≤ 2 * N + 1 by omega)
  have hpRe : p.re = 1 - rho.1.re := by
    simp [p, NontrivialZetaZero.conjugatePartner_coe]
  have hpLt : p.re < rho.1.re := by rw [hpRe]; linarith
  have hw : 0 < w := by
    simpa only [w] using pairedEtaShiftedLogHeadWidth_pos N
  have hMP : ‖MP‖ ≤ w ^ (k + 1) := by
    simpa only [MP, w] using norm_shiftedHeadFourierMoment_le_aux k
      (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)) rho.1.im N
  have hMR : ‖MR‖ ≤ w ^ (k + 1) := by
    simpa only [MR, w] using norm_shiftedHeadFourierMoment_le_aux k
      (NontrivialZetaZero.zero_lt_re rho) (-rho.1.im) N
  have hA : ‖A‖ =
      ‖pairedEtaXiCompletionFactor p * p‖ * x ^ (-p.re) := by
    unfold A pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    change ‖pairedEtaXiCompletionFactor p * p‖ *
        Real.exp (-(1 - rho.1.re) * Real.log x) = _
    rw [Real.rpow_def_of_pos hx, hpRe]
    congr 2
    ring
  have hB : ‖B‖ ≤
      ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ * x ^ (-p.re) := by
    have hpow : x ^ (-rho.1.re) ≤ x ^ (-p.re) :=
      Real.rpow_le_rpow_of_exponent_le hxOne (by linarith)
    unfold B pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      norm_conj, norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _),
      norm_pairedEtaLogTailCutoffRelativeOscillation]
    rw [show pairedEtaLogTailCutoff N = Real.log x by rfl,
      ← norm_mul (pairedEtaXiCompletionFactor rho.1) rho.1]
    simp only [mul_one]
    change ‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ *
        Real.exp (-rho.1.re * Real.log x) ≤ _
    rw [show Real.exp (-rho.1.re * Real.log x) = x ^ (-rho.1.re) by
      rw [Real.rpow_def_of_pos hx]
      congr 1
      ring]
    exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
  rw [norm_mul, norm_pairedEtaLogTailCutoffOscillation, one_mul]
  unfold pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
  change ‖-A * MP + B * MR‖ ≤ _
  calc
    ‖-A * MP + B * MR‖ ≤ ‖-A * MP‖ + ‖B * MR‖ := norm_add_le _ _
    _ = ‖A‖ * ‖MP‖ + ‖B‖ * ‖MR‖ := by
      simp only [norm_mul, norm_neg]
    _ ≤ ‖A‖ * w ^ (k + 1) + ‖B‖ * w ^ (k + 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hMP (norm_nonneg A))
        (mul_le_mul_of_nonneg_left hMR (norm_nonneg B))
    _ ≤ (‖pairedEtaXiCompletionFactor p * p‖ * x ^ (-p.re)) *
          w ^ (k + 1) +
        (‖pairedEtaXiCompletionFactor rho.1 * rho.1‖ * x ^ (-p.re)) *
          w ^ (k + 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hA.le (pow_nonneg hw.le _))
        (mul_le_mul_of_nonneg_right hB (pow_nonneg hw.le _))
    _ = finiteWorkHeadBoundConstantAux rho * x ^ (-p.re) * w ^ (k + 1) := by
      unfold finiteWorkHeadBoundConstantAux
      simp only [p]
      ring
    _ = _ := by rfl

private def lowerMomentComplexSharpLimitAux
    (rho : NontrivialZetaZero) (k : ℕ) : ℂ :=
  -(pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 *
      (NontrivialZetaZero.conjugatePartner rho).1) *
    ((((k.factorial : ℕ) : ℂ) *
      ((NontrivialZetaZero.conjugatePartner rho).1 ^ (k + 1))⁻¹ / 2))

private theorem tendsto_lowerPhaseWeightedCoupledMoment_aux
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (k : ℕ) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
          (NontrivialZetaZero.conjugatePartner rho).1 *
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
          rho k N)
      atTop (nhds (lowerMomentComplexSharpLimitAux rho k)) := by
  let partner := NontrivialZetaZero.conjugatePartner rho
  have hpartner :=
    tendsto_oddEndpoint_cpow_mul_pairedEtaLogLaplaceMomentCutoffCenteredTail
      k (NontrivialZetaZero.zero_lt_re partner)
  have hpartnerWeighted := Filter.Tendsto.const_mul
    (-(pairedEtaXiCompletionFactor partner.1 * partner.1)) hpartner
  have hpartnerWeighted' : Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ partner.1 *
        (-(pairedEtaXiCompletionFactor partner.1 * partner.1 *
          pairedEtaLogLaplaceMomentCutoffCenteredTail k partner.1 N)))
      atTop (nhds (lowerMomentComplexSharpLimitAux rho k)) := by
    simpa only [lowerMomentComplexSharpLimitAux, partner] using
      hpartnerWeighted.congr' (Eventually.of_forall fun N => by ring)
  have hpartnerLt : partner.1.re < rho.1.re := by
    have h : 1 - rho.1.re < rho.1.re := by linarith
    simpa [partner, NontrivialZetaZero.conjugatePartner_coe] using h
  have horiginalNorm :=
    tendsto_oddEndpoint_smaller_rpow_mul_norm_pairedEtaLogLaplaceMomentCutoffCenteredTail_zero
      k (NontrivialZetaZero.zero_lt_re rho) hpartnerLt
  have horiginalWeightedNorm := Filter.Tendsto.const_mul
    (pairedEtaCompletionSpectralWeight rho) horiginalNorm
  have horiginal : Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ partner.1 *
        ((-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
          starRingEnd ℂ
            (pairedEtaXiCompletionFactor rho.1 * rho.1 *
              pairedEtaLogLaplaceMomentCutoffCenteredTail k rho.1 N)))
      atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun N : ℕ =>
      pairedEtaCompletionSpectralWeight rho *
        ((((2 * N + 1 : ℕ) : ℝ) ^ partner.1.re) *
          ‖pairedEtaLogLaplaceMomentCutoffCenteredTail k rho.1 N‖))
    · intro N
      rw [norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      unfold pairedEtaCompletionSpectralWeight
      simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        norm_conj]
      ring_nf
      exact le_rfl
    · simpa only [mul_zero] using horiginalWeightedNorm
  have hsum := hpartnerWeighted'.add horiginal
  simpa only [add_zero, partner] using hsum.congr'
    (Eventually.of_forall fun N => by
      rw [pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_eq_tails]
      ring)

private theorem tendsto_succ_lowerPhaseWeightedCoupledMoment_aux
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (k : ℕ) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
          (NontrivialZetaZero.conjugatePartner rho).1 *
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
          rho k (N + 1))
      atTop (nhds (lowerMomentComplexSharpLimitAux rho k)) := by
  let p := (NontrivialZetaZero.conjugatePartner rho).1
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have hcoupled := (tendsto_lowerPhaseWeightedCoupledMoment_aux rho hrho k).comp hshift
  have hratio := tendsto_oddEndpoint_div_succ_cpow_one_aux p
  have hprod := hratio.mul hcoupled
  simpa only [one_mul, p] using hprod.congr' (Eventually.of_forall fun N => by
    let M : ℝ := ((2 * N + 1 : ℕ) : ℝ)
    let M' : ℝ := ((2 * (N + 1) + 1 : ℕ) : ℝ)
    let C : ℂ :=
      pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
        rho k (N + 1)
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hM' : 0 < M' := by dsimp [M']; positivity
    have hM'cpow : (M' : ℂ) ^ p ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr hM'.ne'))
    change (((M : ℂ) / (M' : ℂ)) ^ p) *
        ((M' : ℂ) ^ p * C) = (M : ℂ) ^ p * C
    rw [Complex.div_cpow_ofReal_nonneg hM hM'.le]
    field_simp [hM'cpow])

private theorem tendsto_scaled_phase_headCoupled_zero_aux
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
          ((NontrivialZetaZero.conjugatePartner rho).1 + 1) *
        (pairedEtaLogTailCutoffOscillation rho.1.im N *
          pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
            rho (analyticZetaZeroMultiplicity rho) N))
      atTop (nhds 0) := by
  let m := analyticZetaZeroMultiplicity rho
  let p := (NontrivialZetaZero.conjugatePartner rho).1
  let C := finiteWorkHeadBoundConstantAux rho
  have hm : 0 < m := analyticZetaZeroMultiplicity_positive rho
  have hpower := tendsto_oddEndpoint_mul_shiftIncrement_pow_zero_aux
    (d := m + 1) (by omega)
  have hupper : Tendsto (fun N : ℕ =>
      C * (((2 * N + 1 : ℕ) : ℝ) *
        pairedEtaLogTailShiftIncrement N ^ (m + 1)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using Filter.Tendsto.const_mul C hpower
  apply squeeze_zero_norm (a := fun N : ℕ =>
    C * (((2 * N + 1 : ℕ) : ℝ) *
      pairedEtaLogTailShiftIncrement N ^ (m + 1)))
  · intro N
    let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
    let w : ℝ := pairedEtaShiftedLogHeadWidth N
    let delta : ℝ := pairedEtaLogTailShiftIncrement N
    have hx : 0 < x := by dsimp [x]; positivity
    have hw : 0 < w := by
      simpa only [w] using pairedEtaShiftedLogHeadWidth_pos N
    have hdelta : 0 < delta := by
      simpa only [delta] using pairedEtaLogTailShiftIncrement_pos N
    have hwDelta : w ≤ delta := by
      exact (pairedEtaShiftedLogHeadWidth_lt_shiftIncrement N).le
    have hhead := norm_phase_headCoupled_le_aux rho hrho m N
    have hpowLe : w ^ (m + 1) ≤ delta ^ (m + 1) :=
      pow_le_pow_left₀ hw.le hwDelta _
    have hC : 0 ≤ C := by
      unfold C finiteWorkHeadBoundConstantAux
      positivity
    have hxcancel : x ^ (p.re + 1) * x ^ (-p.re) = x := by
      rw [← Real.rpow_add hx,
        show p.re + 1 + -p.re = 1 by ring, Real.rpow_one]
    calc
      ‖((x : ℂ) ^ (p + 1)) *
          (pairedEtaLogTailCutoffOscillation rho.1.im N *
            pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
              rho m N)‖ =
          x ^ (p.re + 1) *
            ‖pairedEtaLogTailCutoffOscillation rho.1.im N *
              pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
                rho m N‖ := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
        simp only [add_re, one_re]
      _ ≤ x ^ (p.re + 1) *
          (C * x ^ (-p.re) * w ^ (m + 1)) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [C, p, x, w, m] using hhead)
          (Real.rpow_nonneg hx.le _)
      _ = C * ((x ^ (p.re + 1) * x ^ (-p.re)) *
          w ^ (m + 1)) := by ring
      _ = C * (x * w ^ (m + 1)) := by
        rw [hxcancel]
      _ ≤ C * (x * delta ^ (m + 1)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpowLe hx.le) hC
      _ = C * (((2 * N + 1 : ℕ) : ℝ) *
          pairedEtaLogTailShiftIncrement N ^ (m + 1)) := by rfl
  · exact hupper

private theorem tendsto_scaled_lowerFinitePrefixWorkTerm_zero_aux
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    {j : ℕ} (hj : j < analyticZetaZeroMultiplicity rho)
    (hdegree : 2 ≤ analyticZetaZeroMultiplicity rho - j) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
          ((NontrivialZetaZero.conjugatePartner rho).1 + 1) *
        (((((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
          (pairedEtaLogTailShiftIncrement N : ℂ) ^
            (analyticZetaZeroMultiplicity rho - j)) *
          pairedEtaCompletedLeadingLogCutoffCenteredFinitePrefixCoupledMoment
            rho j (N + 1)))
      atTop (nhds 0) := by
  let m := analyticZetaZeroMultiplicity rho
  let p := (NontrivialZetaZero.conjugatePartner rho).1
  let d := m - j
  have hscaleReal :=
    tendsto_oddEndpoint_mul_shiftIncrement_pow_zero_aux
      (d := d) (by simpa only [d, m] using hdegree)
  have hscaleComplex : Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ) *
        (pairedEtaLogTailShiftIncrement N : ℂ) ^ d))
      atTop (nhds 0) := by
    have hc := Complex.continuous_ofReal.tendsto 0 |>.comp hscaleReal
    convert hc using 1
    · funext N
      simp only [Function.comp_apply, ofReal_mul, ofReal_pow]
    · norm_num
  have hcoupled := tendsto_succ_lowerPhaseWeightedCoupledMoment_aux rho hrho j
  have hprod := hscaleComplex.mul hcoupled
  have hweighted := Filter.Tendsto.const_mul
    (((m.choose j : ℕ) : ℂ)) hprod
  simpa only [zero_mul, mul_zero] using hweighted.congr'
    (Eventually.of_forall fun N => by
      let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
      have hx : 0 < x := by dsimp [x]; positivity
      have hfinite :=
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_eq_finitePrefix_of_lt_multiplicity
          rho hj (N + 1)
      rw [← hfinite]
      rw [Complex.cpow_add p 1 (Complex.ofReal_ne_zero.mpr hx.ne'),
        Complex.cpow_one]
      simp only [m, p, d, x]
      ring)

private theorem tendsto_scaled_topFinitePrefixWorkTerm_aux
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (k : ℕ) (hm : analyticZetaZeroMultiplicity rho = k + 1) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
          ((NontrivialZetaZero.conjugatePartner rho).1 + 1) *
        (((((analyticZetaZeroMultiplicity rho).choose k : ℕ) : ℂ) *
          (pairedEtaLogTailShiftIncrement N : ℂ) ^
            (analyticZetaZeroMultiplicity rho - k)) *
          pairedEtaCompletedLeadingLogCutoffCenteredFinitePrefixCoupledMoment
            rho k (N + 1)))
      atTop
      (nhds (((((analyticZetaZeroMultiplicity rho).choose k : ℕ) : ℂ) * 2) *
        lowerMomentComplexSharpLimitAux rho k)) := by
  let m := analyticZetaZeroMultiplicity rho
  let p := (NontrivialZetaZero.conjugatePartner rho).1
  have hk : k < analyticZetaZeroMultiplicity rho := by omega
  have hscaleComplex : Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ) *
        (pairedEtaLogTailShiftIncrement N : ℂ)))
      atTop (nhds 2) := by
    have hc := Complex.continuous_ofReal.tendsto 2 |>.comp
      tendsto_oddEndpoint_mul_shiftIncrement_two_aux
    convert hc using 1
    · funext N
      simp only [Function.comp_apply, ofReal_mul]
    · norm_num
  have hcoupled := tendsto_succ_lowerPhaseWeightedCoupledMoment_aux rho hrho k
  have hprod := hscaleComplex.mul hcoupled
  have hweighted := Filter.Tendsto.const_mul
    (((m.choose k : ℕ) : ℂ)) hprod
  have heq : Filter.EventuallyEq atTop
      (fun N : ℕ => (((m.choose k : ℕ) : ℂ) *
        (((((2 * N + 1 : ℕ) : ℝ) : ℂ) *
          (pairedEtaLogTailShiftIncrement N : ℂ)) *
          (((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ p *
            pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
              rho k (N + 1)))))
      (fun N : ℕ =>
        ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (p + 1) *
          (((((m.choose k : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^ (m - k)) *
            pairedEtaCompletedLeadingLogCutoffCenteredFinitePrefixCoupledMoment
              rho k (N + 1)))) := by
    filter_upwards with N
    let x : ℝ := ((2 * N + 1 : ℕ) : ℝ)
    have hx : 0 < x := by dsimp [x]; positivity
    have hfinite :=
      pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_eq_finitePrefix_of_lt_multiplicity
        rho hk (N + 1)
    rw [← hfinite]
    rw [Complex.cpow_add p 1 (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.cpow_one]
    simp only [m, x, hm, Nat.add_sub_cancel_left, pow_one]
    ring
  have hout := hweighted.congr' heq
  simpa only [m, p, mul_assoc] using hout

private theorem tendsto_scaled_finiteWork_raw_aux
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ k : ℕ,
      analyticZetaZeroMultiplicity rho = k + 1 ∧
      Tendsto (fun N : ℕ =>
        ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
            ((NontrivialZetaZero.conjugatePartner rho).1 + 1) *
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
            rho N)
        atTop
        (nhds (((((analyticZetaZeroMultiplicity rho).choose k : ℕ) : ℂ) * 2) *
          lowerMomentComplexSharpLimitAux rho k)) := by
  let m := analyticZetaZeroMultiplicity rho
  let p := (NontrivialZetaZero.conjugatePartner rho).1
  obtain ⟨k, hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (analyticZetaZeroMultiplicity_positive rho))
  refine ⟨k, hm, ?_⟩
  let scale : ℕ → ℂ := fun N =>
    ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (p + 1)
  let head : ℕ → ℂ := fun N =>
    pairedEtaLogTailCutoffOscillation rho.1.im N *
      pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
        rho m N
  let term : ℕ → ℕ → ℂ := fun j N =>
    ((((m.choose j : ℕ) : ℂ) *
      (pairedEtaLogTailShiftIncrement N : ℂ) ^ (m - j)) *
      pairedEtaCompletedLeadingLogCutoffCenteredFinitePrefixCoupledMoment
        rho j (N + 1))
  have hhead : Tendsto (fun N : ℕ => scale N * head N)
      atTop (nhds 0) := by
    simpa only [scale, head, m, p] using
      tendsto_scaled_phase_headCoupled_zero_aux rho hrho
  have hlower : Tendsto (fun N : ℕ =>
      ∑ j ∈ Finset.range k, scale N * term j N)
      atTop (nhds 0) := by
    have hsum := tendsto_finsetSum (Finset.range k) (f := fun j N =>
        scale N * term j N) (a := fun _ => 0) (by
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hjm : j < analyticZetaZeroMultiplicity rho := by omega
      have hdegree : 2 ≤ analyticZetaZeroMultiplicity rho - j := by omega
      simpa only [scale, term, m, p] using
        tendsto_scaled_lowerFinitePrefixWorkTerm_zero_aux
          rho hrho hjm hdegree)
    simpa using hsum
  have htop : Tendsto (fun N : ℕ => scale N * term k N)
      atTop
      (nhds (((((analyticZetaZeroMultiplicity rho).choose k : ℕ) : ℂ) * 2) *
        lowerMomentComplexSharpLimitAux rho k)) := by
    simpa only [scale, term, m, p] using
      tendsto_scaled_topFinitePrefixWorkTerm_aux rho hrho k hm
  have hcombined := hhead.add (hlower.add htop)
  have heq : Filter.EventuallyEq atTop
      (fun N : ℕ => scale N * head N +
        ((∑ j ∈ Finset.range k, scale N * term j N) +
          scale N * term k N))
      (fun N : ℕ => scale N *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
          rho N) := by
    filter_upwards with N
    unfold pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
    rw [hm, Finset.sum_range_succ]
    simp only [head, term, m, hm]
    rw [mul_add, mul_add, Finset.mul_sum]
  have hout := hcombined.congr' heq
  simpa only [zero_add, p, scale] using hout

private theorem topWorkLimit_eq_residualLimit_aux
    (rho : NontrivialZetaZero) (k : ℕ)
    (hm : analyticZetaZeroMultiplicity rho = k + 1) :
    (((((analyticZetaZeroMultiplicity rho).choose k : ℕ) : ℂ) * 2) *
        lowerMomentComplexSharpLimitAux rho k) =
      2 * (NontrivialZetaZero.conjugatePartner rho).1 *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit
          rho := by
  let p := (NontrivialZetaZero.conjugatePartner rho).1
  have hp : p ≠ 0 := by
    intro hzero
    have hpRe : 0 < p.re :=
      NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho)
    rw [hzero] at hpRe
    norm_num at hpRe
  unfold lowerMomentComplexSharpLimitAux
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit
  rw [hm]
  simp only [Nat.choose_succ_self_right,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [p] at hp ⊢
  field_simp [pow_ne_zero _ hp]
  ring


/-- The nonzero complex leading constant of the one-step finite residual work
at a hypothetical right-half off-line zero. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkComplexSharpLimit
    (rho : NontrivialZetaZero) : ℂ :=
  2 * (NontrivialZetaZero.conjugatePartner rho).1 *
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit
      rho

/-- The finite-work leading constant cannot vanish. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkComplexSharpLimit_ne_zero
    (rho : NontrivialZetaZero) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkComplexSharpLimit
      rho ≠ 0 := by
  have hpartner :
      (NontrivialZetaZero.conjugatePartner rho).1 ≠ 0 := by
    intro hzero
    have hre :=
      NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho)
    rw [hzero] at hre
    norm_num at hre
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkComplexSharpLimit
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) hpartner)
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualComplexSharpLimit_ne_zero
      rho)

/-- Sharp phase-bearing asymptotic of the exact finite arithmetic work.
The proof uses the triangular transport law rather than an unjustified
difference of two bare asymptotic equivalences. -/
theorem
    tendsto_oddEndpoint_partner_add_one_cpow_mul_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^
          ((NontrivialZetaZero.conjugatePartner rho).1 + 1) *
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
          rho N)
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkComplexSharpLimit
          rho)) := by
  rcases tendsto_scaled_finiteWork_raw_aux rho hrho with ⟨k, hm, hlimit⟩
  rw [topWorkLimit_eq_residualLimit_aux rho k hm] at hlimit
  simpa only [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkComplexSharpLimit]
    using hlimit

/-- Taking norms gives the exact real decay rate and magnitude of the finite
work at every hypothetical right-half off-line zero. -/
theorem
    tendsto_oddEndpoint_partner_add_one_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N : ℕ =>
      (((2 * N + 1 : ℕ) : ℝ) ^
          ((NontrivialZetaZero.conjugatePartner rho).1.re + 1)) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
          rho N‖)
      atTop
      (nhds
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkComplexSharpLimit
          rho‖) := by
  have hlimit :=
    (tendsto_oddEndpoint_partner_add_one_cpow_mul_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
      rho hrho).norm
  convert hlimit using 1
  funext N
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp only [add_re, one_re]

/-- In particular, the exact finite work is eventually nonzero for a
hypothetical zero strictly to the right of the critical line. -/
theorem
    eventually_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork_ne_zero_of_half_lt_re
    (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∀ᶠ N : ℕ in atTop,
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
        rho N ≠ 0 := by
  have hlimit :=
    tendsto_oddEndpoint_partner_add_one_rpow_mul_norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWork
      rho hrho
  have hpositive := hlimit.eventually_const_lt
    (norm_pos_iff.mpr
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkComplexSharpLimit_ne_zero
        rho))
  filter_upwards [hpositive] with N hN
  intro hzero
  rw [hzero, norm_zero, mul_zero] at hN
  exact (lt_irrefl 0 hN)

end

end RiemannGaussian
