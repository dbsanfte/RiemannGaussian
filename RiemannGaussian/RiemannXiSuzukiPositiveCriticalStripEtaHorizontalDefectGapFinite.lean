import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaHorizontalDefectGapArithmetic

/-!
# Finite telescoping control of the arithmetic eta gaps

The complete explicit gap series is useful only if it has a controlled finite
shadow.  This module pairs the first `N` support differences with the first
`N` adjacent gap differences.  The pair telescopes exactly:

`E_N(s) + G_N(s) = 1 - (2N+1)^(-s)`.

Consequently the finite gap error is exactly the negative finite eta value
minus one elementary endpoint.  Lean derives a norm bound with the endpoint
written as `(2N+1)^(-Re s)` and proves that the gap partial sums at every zeta
zero converge to one.  No rate for the remaining finite eta value is assumed.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The first `N` elementary even-odd arithmetic-gap differences. -/
def pairedEtaGapCorePartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, pairedEtaGapCoreSummand s n

/-- The logarithmic support carried by eta intervals with index at least
`N`. -/
def pairedEtaLogTailSupport (N : ℕ) : Set ℝ :=
  ⋃ n : ℕ, pairedEtaLogInterval (n + N)

/-- Lebesgue measure restricted to the eta support tail beginning at `N`. -/
def pairedEtaLogTailMeasure (N : ℕ) : Measure ℝ :=
  volume.restrict (pairedEtaLogTailSupport N)

/-- The shifted eta intervals in a support tail remain pairwise disjoint. -/
theorem pairwise_disjoint_pairedEtaLogInterval_natAdd (N : ℕ) :
    Pairwise (fun n m : ℕ ↦
      Disjoint (pairedEtaLogInterval (n + N))
        (pairedEtaLogInterval (m + N))) := by
  intro n m hne
  apply pairwise_disjoint_pairedEtaLogInterval
  omega

/-- The eta tail measure is exactly the sum of its shifted interval
restrictions. -/
theorem pairedEtaLogTailMeasure_eq_sum_restrict (N : ℕ) :
    pairedEtaLogTailMeasure N =
      Measure.sum fun n : ℕ ↦
        volume.restrict (pairedEtaLogInterval (n + N)) := by
  unfold pairedEtaLogTailMeasure pairedEtaLogTailSupport
  exact Measure.restrict_iUnion
    (pairwise_disjoint_pairedEtaLogInterval_natAdd N)
    (fun _ ↦ by
      unfold pairedEtaLogInterval
      exact measurableSet_Ioc)

/-- Every eta tail lies to the right of its first odd logarithmic endpoint. -/
theorem pairedEtaLogTailSupport_subset_Ioi_log_odd (N : ℕ) :
    pairedEtaLogTailSupport N ⊆ Ioi (Real.log (2 * N + 1)) := by
  intro t ht
  rw [pairedEtaLogTailSupport, mem_iUnion] at ht
  obtain ⟨n, hn⟩ := ht
  have harg : (2 : ℝ) * N + 1 ≤ 2 * (n + N) + 1 := by
    exact_mod_cast (show 2 * N + 1 ≤ 2 * (n + N) + 1 by omega)
  have hlog : Real.log (2 * N + 1) ≤
      Real.log (2 * (n + N) + 1) :=
    Real.log_le_log (by positivity) harg
  exact hlog.trans_lt (by simpa [Nat.cast_add] using hn.1)

/-- The eta tail measure is dominated by Lebesgue measure on the elementary
right half-line beginning at `log(2N+1)`. -/
theorem pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd (N : ℕ) :
    pairedEtaLogTailMeasure N ≤
      volume.restrict (Ioi (Real.log (2 * N + 1))) := by
  unfold pairedEtaLogTailMeasure
  exact Measure.restrict_mono
    (pairedEtaLogTailSupport_subset_Ioi_log_odd N) le_rfl

/-- Positive-real-part exponentials are integrable on every eta support
tail. -/
theorem integrable_exp_neg_mul_pairedEtaLogTailMeasure
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Integrable (fun t : ℝ ↦ Complex.exp (-s * t))
      (pairedEtaLogTailMeasure N) := by
  have hfull := integrableOn_exp_mul_complex_Ioi (a := -s) (by
    norm_num
    linarith) (Real.log (2 * N + 1))
  have hfull' : Integrable (fun t : ℝ ↦ Complex.exp (-s * t))
      (volume.restrict (Ioi (Real.log (2 * N + 1)))) := by
    apply hfull.congr
    filter_upwards with t
    congr 1
  exact hfull'.mono_measure
    (pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd N)

/-- Integrating over the eta support tail is the shifted infinite sum of its
interval Laplace transforms. -/
theorem integral_exp_neg_mul_pairedEtaLogTailMeasure_eq_tsum_natAdd
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    (∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N) =
      ∑' n : ℕ, pairedEtaLaplaceInterval s (n + N) := by
  have hint := integrable_exp_neg_mul_pairedEtaLogTailMeasure hs N
  rw [pairedEtaLogTailMeasure_eq_sum_restrict] at hint
  rw [pairedEtaLogTailMeasure_eq_sum_restrict, integral_sum_measure hint]
  apply tsum_congr
  intro n
  unfold pairedEtaLaplaceInterval pairedEtaLogInterval
  exact (intervalIntegral.integral_of_le
    (pairedEtaFiniteLogInterval_pos (n + N)).le).symm

/-- The eta core minus its first `N` paired terms is exactly `s` times the
Laplace integral over the actual support tail. -/
theorem pairedEtaCore_sub_partialSum_eq_mul_tailIntegral
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaCore s - pairedEtaCorePartialSum N s =
      s * ∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N := by
  have hsplit :=
    (summable_pairedEtaLaplaceInterval hs).sum_add_tsum_nat_add N
  change pairedEtaFiniteLaplacePartition N s +
      (∑' n : ℕ, pairedEtaLaplaceInterval s (n + N)) =
    pairedEtaLaplacePartition s at hsplit
  rw [pairedEtaCore_eq_mul_laplacePartition hs,
    pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition,
    integral_exp_neg_mul_pairedEtaLogTailMeasure_eq_tsum_natAdd hs]
  rw [← hsplit]
  ring

/-- The norm of the complex Laplace kernel is its real exponential
envelope. -/
theorem norm_cexp_neg_mul_eq_exp_neg_re_mul (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-s * t)‖ = Real.exp (-s.re * t) := by
  rw [Complex.norm_exp]
  norm_num [Complex.mul_re]

/-- The elementary real exponential tail starting at the `N`th odd endpoint
has a closed form. -/
theorem integral_exp_neg_mul_Ioi_log_odd
    {sigma : ℝ} (hsigma : 0 < sigma) (N : ℕ) :
    (∫ t : ℝ in Ioi (Real.log (2 * N + 1)),
      Real.exp (-sigma * t)) =
      ((2 * N + 1 : ℕ) : ℝ) ^ (-sigma) / sigma := by
  rw [integral_exp_mul_Ioi (a := -sigma) (by linarith)]
  rw [neg_div_neg_eq]
  have hbase : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [Real.rpow_def_of_pos hbase, hcast]
  apply congrArg (fun x : ℝ ↦ x / sigma)
  apply congrArg Real.exp
  ring

/-- The eta partial-sum tail has an explicit positive-half-plane bound. -/
theorem norm_pairedEtaCore_sub_partialSum_le
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖pairedEtaCore s - pairedEtaCorePartialSum N s‖ ≤
      ‖s‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re) / s.re) := by
  rw [pairedEtaCore_sub_partialSum_eq_mul_tailIntegral hs, norm_mul]
  have hrealIntegrable : IntegrableOn
      (fun t : ℝ ↦ Real.exp (-s.re * t))
      (Ioi (Real.log (2 * N + 1))) := by
    have h := integrableOn_exp_mul_Ioi (a := -s.re) (by linarith)
      (Real.log (2 * N + 1))
    simpa only [neg_mul] using h
  have hnormIntegral :
      ‖∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N‖ ≤
        ∫ t : ℝ, Real.exp (-s.re * t) ∂pairedEtaLogTailMeasure N := by
    calc
      ‖∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N‖ ≤
          ∫ t : ℝ, ‖Complex.exp (-s * t)‖
            ∂pairedEtaLogTailMeasure N :=
        norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, Real.exp (-s.re * t)
            ∂pairedEtaLogTailMeasure N := by
        apply integral_congr_ae
        filter_upwards with t
        exact norm_cexp_neg_mul_eq_exp_neg_re_mul s t
  have hmeasureIntegral :
      (∫ t : ℝ, Real.exp (-s.re * t) ∂pairedEtaLogTailMeasure N) ≤
        ∫ t : ℝ in Ioi (Real.log (2 * N + 1)),
          Real.exp (-s.re * t) := by
    exact integral_mono_measure
      (pairedEtaLogTailMeasure_le_restrict_Ioi_log_odd N)
      (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)
      hrealIntegrable
  calc
    ‖s‖ *
        ‖∫ t : ℝ, Complex.exp (-s * t) ∂pairedEtaLogTailMeasure N‖ ≤
        ‖s‖ *
          (∫ t : ℝ, Real.exp (-s.re * t)
            ∂pairedEtaLogTailMeasure N) :=
      mul_le_mul_of_nonneg_left hnormIntegral (norm_nonneg s)
    _ ≤ ‖s‖ *
        (∫ t : ℝ in Ioi (Real.log (2 * N + 1)),
          Real.exp (-s.re * t)) :=
      mul_le_mul_of_nonneg_left hmeasureIntegral (norm_nonneg s)
    _ = ‖s‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re) / s.re) := by
      rw [integral_exp_neg_mul_Ioi_log_odd hs]

/-- A support difference plus its adjacent gap difference collapses to the
difference between consecutive odd endpoints. -/
theorem pairedEtaCoreSummand_add_gapCoreSummand
    (s : ℂ) (n : ℕ) :
    pairedEtaCoreSummand s n + pairedEtaGapCoreSummand s n =
      ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) -
        ((((2 * n + 3 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
  unfold pairedEtaCoreSummand pairedEtaGapCoreSummand
  ring

/-- The consecutive odd-endpoint differences telescope exactly. -/
theorem sum_range_pairedEtaOddEndpointDiff_eq
    (N : ℕ) (s : ℂ) :
    ∑ n ∈ Finset.range N,
        (((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) -
          ((((2 * n + 3 : ℕ) : ℝ) : ℂ)) ^ (-s)) =
      1 - ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hendpoint :
          ((((2 * N.succ + 1 : ℕ) : ℝ) : ℂ)) =
            ((((2 * N + 3 : ℕ) : ℝ) : ℂ)) := by
        norm_num
        ring
      rw [hendpoint]
      ring

/-- The first `N` eta-support and gap sums have one exact elementary
telescoping remainder. -/
theorem pairedEtaCorePartialSum_add_gapCorePartialSum
    (N : ℕ) (s : ℂ) :
    pairedEtaCorePartialSum N s + pairedEtaGapCorePartialSum N s =
      1 - ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
  unfold pairedEtaCorePartialSum pairedEtaGapCorePartialSum
  rw [← Finset.sum_add_distrib]
  calc
    ∑ n ∈ Finset.range N,
        (pairedEtaCoreSummand s n + pairedEtaGapCoreSummand s n) =
        ∑ n ∈ Finset.range N,
          (((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) -
            ((((2 * n + 3 : ℕ) : ℝ) : ℂ)) ^ (-s)) := by
      apply Finset.sum_congr rfl
      intro n _
      exact pairedEtaCoreSummand_add_gapCoreSummand s n
    _ = 1 - ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) :=
      sum_range_pairedEtaOddEndpointDiff_eq N s

/-- The finite gap error from one is exactly the negative finite eta value
minus the odd endpoint remainder. -/
theorem pairedEtaGapCorePartialSum_sub_one_eq
    (N : ℕ) (s : ℂ) :
    pairedEtaGapCorePartialSum N s - 1 =
      -pairedEtaCorePartialSum N s -
        ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s) := by
  have hsum := pairedEtaCorePartialSum_add_gapCorePartialSum N s
  have hgap : pairedEtaGapCorePartialSum N s =
      (1 - ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s)) -
        pairedEtaCorePartialSum N s := by
    apply eq_sub_of_add_eq
    simpa [add_comm] using hsum
  rw [hgap]
  ring

/-- The norm of the elementary odd endpoint is its real power with exponent
`-Re s`. -/
theorem norm_pairedEtaOddEndpoint_cpow_neg
    (N : ℕ) (s : ℂ) :
    ‖((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s)‖ =
      (((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

/-- The exact telescope gives a quantitative finite gap-error bound.  The
only non-elementary term left is the actual finite eta value. -/
theorem norm_pairedEtaGapCorePartialSum_sub_one_le
    (N : ℕ) (s : ℂ) :
    ‖pairedEtaGapCorePartialSum N s - 1‖ ≤
      ‖pairedEtaCorePartialSum N s‖ +
        ((2 * N + 1 : ℕ) : ℝ) ^ (-s.re) := by
  rw [pairedEtaGapCorePartialSum_sub_one_eq]
  calc
    ‖-pairedEtaCorePartialSum N s -
        ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s)‖ ≤
        ‖-pairedEtaCorePartialSum N s‖ +
          ‖((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-s)‖ :=
      norm_sub_le _ _
    _ = ‖pairedEtaCorePartialSum N s‖ +
        ((2 * N + 1 : ℕ) : ℝ) ^ (-s.re) := by
      rw [norm_neg, norm_pairedEtaOddEndpoint_cpow_neg]

/-- At a nontrivial zeta zero, the finite eta value has a closed elementary
tail bound. -/
theorem norm_pairedEtaCorePartialSum_nontrivialZetaZero_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCorePartialSum N rho.1‖ ≤
      ‖rho.1‖ *
        (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) / rho.1.re) := by
  have hcore : pairedEtaCore rho.1 = 0 := by
    rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
      (NontrivialZetaZero.zero_lt_re rho) rho.2.2.2,
      rho.2.1, mul_zero]
  have hbound := norm_pairedEtaCore_sub_partialSum_le
    (NontrivialZetaZero.zero_lt_re rho) N
  rw [hcore, zero_sub, norm_neg] at hbound
  exact hbound

/-- Combining the exact telescope with the eta-tail estimate gives a fully
explicit convergence rate for the finite arithmetic-gap sum at every zeta
zero. -/
theorem norm_pairedEtaGapCorePartialSum_nontrivialZetaZero_sub_one_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaGapCorePartialSum N rho.1 - 1‖ ≤
      (‖rho.1‖ / rho.1.re + 1) *
        ((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) := by
  have hre := NontrivialZetaZero.zero_lt_re rho
  have heta := norm_pairedEtaCorePartialSum_nontrivialZetaZero_le rho N
  have hgap := norm_pairedEtaGapCorePartialSum_sub_one_le N rho.1
  calc
    ‖pairedEtaGapCorePartialSum N rho.1 - 1‖ ≤
        ‖pairedEtaCorePartialSum N rho.1‖ +
          ((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) := hgap
    _ ≤ ‖rho.1‖ *
          (((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) / rho.1.re) +
        ((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) :=
      add_le_add heta le_rfl
    _ = (‖rho.1‖ / rho.1.re + 1) *
        ((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) := by
      field_simp [ne_of_gt hre]

/-- The zero and its functional-equation partner satisfy simultaneous
explicit finite-gap rates, with complementary real exponents. -/
theorem nontrivialZetaZero_etaGapComplementaryFiniteRate_certificate
    (rho : NontrivialZetaZero) :
    ∀ N : ℕ,
      ‖pairedEtaGapCorePartialSum N rho.1 - 1‖ ≤
          (‖rho.1‖ / rho.1.re + 1) *
            ((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) ∧
        ‖pairedEtaGapCorePartialSum N
              (NontrivialZetaZero.conjugatePartner rho).1 - 1‖ ≤
          (‖(NontrivialZetaZero.conjugatePartner rho).1‖ /
              (1 - rho.1.re) + 1) *
            ((2 * N + 1 : ℕ) : ℝ) ^ (-(1 - rho.1.re)) := by
  intro N
  refine ⟨
    norm_pairedEtaGapCorePartialSum_nontrivialZetaZero_sub_one_le rho N,
    ?_⟩
  simpa [NontrivialZetaZero.conjugatePartner_coe] using
    (norm_pairedEtaGapCorePartialSum_nontrivialZetaZero_sub_one_le
      (NontrivialZetaZero.conjugatePartner rho) N)

/-- Off the critical line the two rigorously controlled gap rates have
distinct decay exponents `Re rho` and `1 - Re rho`. -/
theorem nontrivialZetaZero_offCritical_etaGapDistinctFiniteRates_certificate
    (rho : NontrivialZetaZero) (hoff : rho.1.re ≠ 1 / 2) :
    rho.1.re ≠ 1 - rho.1.re ∧
      ∀ N : ℕ,
        ‖pairedEtaGapCorePartialSum N rho.1 - 1‖ ≤
            (‖rho.1‖ / rho.1.re + 1) *
              ((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re) ∧
          ‖pairedEtaGapCorePartialSum N
                (NontrivialZetaZero.conjugatePartner rho).1 - 1‖ ≤
            (‖(NontrivialZetaZero.conjugatePartner rho).1‖ /
                (1 - rho.1.re) + 1) *
              ((2 * N + 1 : ℕ) : ℝ) ^ (-(1 - rho.1.re)) := by
  refine ⟨?_, nontrivialZetaZero_etaGapComplementaryFiniteRate_certificate rho⟩
  intro heq
  apply hoff
  linarith

/-- The finite eta values at a nontrivial zeta zero converge to zero. -/
theorem tendsto_pairedEtaCorePartialSum_nontrivialZetaZero_zero
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦ pairedEtaCorePartialSum N rho.1)
      atTop (nhds 0) := by
  have hsummable :=
    summable_pairedEtaCoreSummand (NontrivialZetaZero.zero_lt_re rho)
  have htendsto := hsummable.tendsto_sum_tsum_nat
  have hcore : pairedEtaCore rho.1 = 0 := by
    rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
      (NontrivialZetaZero.zero_lt_re rho) rho.2.2.2,
      rho.2.1, mul_zero]
  rw [← hcore]
  simpa only [pairedEtaCorePartialSum, pairedEtaCore] using htendsto

/-- The explicit odd-endpoint norm remainder tends to zero throughout the
positive half-plane. -/
theorem tendsto_pairedEtaOddEndpoint_rpow_zero
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) ^ (-s.re)) atTop (nhds 0) := by
  have hbase : Tendsto (fun N : ℕ ↦ (2 : ℝ) * N + 1)
      atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num))
  convert (tendsto_rpow_neg_atTop hs).comp hbase using 1
  funext N
  norm_num

/-- At every nontrivial zeta zero, the finite arithmetic-gap sums converge
to their forced exact value one. -/
theorem tendsto_pairedEtaGapCorePartialSum_nontrivialZetaZero_one
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ ↦ pairedEtaGapCorePartialSum N rho.1)
      atTop (nhds 1) := by
  have hsummable :=
    summable_pairedEtaGapCoreSummand (NontrivialZetaZero.zero_lt_re rho)
  have htendsto := hsummable.tendsto_sum_tsum_nat
  rw [← pairedEtaGapCore_eq_one_of_nontrivialZetaZero rho]
  simpa only [pairedEtaGapCorePartialSum, pairedEtaGapCore] using htendsto

/-- The exact finite telescope, its closed power-rate bound, and convergence
to one, packaged at each nontrivial zeta zero. -/
theorem nontrivialZetaZero_etaGapFiniteTelescope_certificate
    (rho : NontrivialZetaZero) :
    (∀ N : ℕ,
      pairedEtaCorePartialSum N rho.1 +
          pairedEtaGapCorePartialSum N rho.1 =
        1 - ((((2 * N + 1 : ℕ) : ℝ) : ℂ)) ^ (-rho.1) ∧
      ‖pairedEtaGapCorePartialSum N rho.1 - 1‖ ≤
        (‖rho.1‖ / rho.1.re + 1) *
          ((2 * N + 1 : ℕ) : ℝ) ^ (-rho.1.re)) ∧
      Tendsto (fun N : ℕ ↦ pairedEtaGapCorePartialSum N rho.1)
        atTop (nhds 1) := by
  refine ⟨?_, tendsto_pairedEtaGapCorePartialSum_nontrivialZetaZero_one rho⟩
  intro N
  exact ⟨pairedEtaCorePartialSum_add_gapCorePartialSum N rho.1,
    norm_pairedEtaGapCorePartialSum_nontrivialZetaZero_sub_one_le rho N⟩

end

end RiemannGaussian
