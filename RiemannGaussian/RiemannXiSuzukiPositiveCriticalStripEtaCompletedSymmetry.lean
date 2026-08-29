import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaEnergy
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaComplementaryTiltRigidity
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFlux
import RiemannGaussian.FiniteToEntireRealApproximation

/-!
# Completed paired eta symmetry

The elementary, polynomial, and Archimedean factors already exposed by the
positive-strip xi logarithmic derivative determine an actual completion of
paired eta. This module constructs that completion, identifies it locally
with the project's entire xi function throughout `0 < re s < 1`, and carries
the full functional-equation symmetry to all of its local derivatives.

At a nontrivial zero the first derivative becomes an exact relation between
the two convergent arithmetic eta derivative series at complementary tilts.
This is genuine completed symmetry, but it is an identity rather than the
missing inequality that would force the zero onto the critical line.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit polynomial--Archimedean numerator completing paired eta. -/
def pairedEtaXiCompletionNumerator (s : ℂ) : ℂ :=
  s * (1 - s) * Complex.Gammaℝ s

/-- The exact factor which converts paired eta into the project's entire xi
normalization inside the open critical strip. -/
def pairedEtaXiCompletionFactor (s : ℂ) : ℂ :=
  pairedEtaXiCompletionNumerator s / pairedEtaFactor s

/-- Paired eta with its exact polynomial, Archimedean, and elementary-factor
completion. -/
def pairedEtaCompletedXi (s : ℂ) : ℂ :=
  pairedEtaXiCompletionFactor s * pairedEtaCore s

/-- The polynomial--Archimedean completion numerator is nonzero in the open
critical strip. -/
theorem pairedEtaXiCompletionNumerator_ne_zero
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaXiCompletionNumerator s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hspos
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hslt
  unfold pairedEtaXiCompletionNumerator
  exact mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1.symm))
    (Gammaℝ_ne_zero_of_re_pos hspos)

/-- The polynomial--Archimedean completion numerator is holomorphic in the
open right half-plane. -/
theorem differentiableAt_pairedEtaXiCompletionNumerator
    {s : ℂ} (hspos : 0 < s.re) :
    DifferentiableAt ℂ pairedEtaXiCompletionNumerator s := by
  unfold pairedEtaXiCompletionNumerator
  exact ((differentiableAt_id.mul
    ((differentiableAt_const (c := (1 : ℂ))).sub
      differentiableAt_id)).mul
        (differentiableAt_Gammaℝ_of_re_pos hspos))

/-- The eta completion factor is nonzero throughout the open critical strip. -/
theorem pairedEtaXiCompletionFactor_ne_zero
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaXiCompletionFactor s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hspos
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hslt
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos hspos
  have hetaFactor : pairedEtaFactor s ≠ 0 := by
    exact pairedEtaFactor_ne_zero_of_re_lt_one hslt
  unfold pairedEtaXiCompletionFactor pairedEtaXiCompletionNumerator
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hs0 h1s) hgamma) hetaFactor

/-- The eta completion factor is holomorphic at every point of the open
critical strip. -/
theorem differentiableAt_pairedEtaXiCompletionFactor
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    DifferentiableAt ℂ pairedEtaXiCompletionFactor s := by
  have hnum : DifferentiableAt ℂ pairedEtaXiCompletionNumerator s := by
    exact differentiableAt_pairedEtaXiCompletionNumerator hspos
  have hden : DifferentiableAt ℂ pairedEtaFactor s :=
    (hasDerivAt_pairedEtaFactor s).differentiableAt
  unfold pairedEtaXiCompletionFactor
  exact hnum.div hden (pairedEtaFactor_ne_zero_of_re_lt_one hslt)

/-- The eta completion factor is analytic at every point of the open critical
strip. -/
theorem analyticAt_pairedEtaXiCompletionFactor
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    AnalyticAt ℂ pairedEtaXiCompletionFactor s := by
  let S : Set ℂ := {z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}
  have hSopen : IsOpen S :=
    (Complex.isOpen_re_gt 0).inter (Complex.isOpen_re_lt 1)
  have hSdiff : DifferentiableOn ℂ pairedEtaXiCompletionFactor S := by
    intro z hz
    exact (differentiableAt_pairedEtaXiCompletionFactor hz.1 hz.2).differentiableWithinAt
  exact hSdiff.analyticAt (hSopen.mem_nhds ⟨hspos, hslt⟩)

/-- The logarithmic derivative of the polynomial--Archimedean numerator is
the explicit completed-zeta correction before removing the eta factor. -/
theorem logDeriv_pairedEtaXiCompletionNumerator
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    logDeriv pairedEtaXiCompletionNumerator s =
      1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma (s / 2) / 2 := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hspos
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hslt
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos hspos
  have hgammaDiff : DifferentiableAt ℂ Complex.Gammaℝ s :=
    differentiableAt_Gammaℝ_of_re_pos hspos
  have hpolyDiff : DifferentiableAt ℂ (fun z : ℂ => z * (1 - z)) s := by
    fun_prop
  have hlinear :
      logDeriv (fun z : ℂ => z * (1 - z)) s =
        1 / s + 1 / (s - 1) := by
    have hderivSub : deriv (fun z : ℂ => 1 - z) s = -1 :=
      ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).deriv.trans (by ring)
    rw [logDeriv_mul (f := fun z : ℂ => z)
      (g := fun z : ℂ => 1 - z) s hs0 h1s
      (by fun_prop) (by fun_prop)]
    simp only [logDeriv_apply, deriv_id'', hderivSub]
    field_simp [hs0, hs1]
    ring
  unfold pairedEtaXiCompletionNumerator
  rw [logDeriv_mul (f := fun z : ℂ => z * (1 - z))
    (g := Complex.Gammaℝ) s (mul_ne_zero hs0 h1s) hgamma
    hpolyDiff hgammaDiff,
    hlinear, logDeriv_Gammaℝ hspos]
  ring

/-- The previously exposed regular xi correction is exactly the logarithmic
derivative of the actual eta completion factor. -/
theorem logDeriv_pairedEtaXiCompletionFactor
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    logDeriv pairedEtaXiCompletionFactor s =
      pairedEtaArithmeticXiRegularCorrection s := by
  have hnumNe := pairedEtaXiCompletionNumerator_ne_zero hspos hslt
  have hdenNe := pairedEtaFactor_ne_zero_of_re_lt_one hslt
  have hnumDiff := differentiableAt_pairedEtaXiCompletionNumerator hspos
  have hdenDiff := (hasDerivAt_pairedEtaFactor s).differentiableAt
  unfold pairedEtaXiCompletionFactor
  rw [logDeriv_div s hnumNe hdenNe hnumDiff hdenDiff,
    logDeriv_pairedEtaXiCompletionNumerator hspos hslt,
    logDeriv_pairedEtaFactor]
  unfold pairedEtaArithmeticXiRegularCorrection
  ring

/-- In the open critical strip, the explicitly completed paired eta function
is exactly the entire xi normalization. -/
theorem pairedEtaCompletedXi_eq_riemannXi
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaCompletedXi s = riemannXi s := by
  have hs1 : s ≠ 1 := by
    intro hs
    subst s
    norm_num at hslt
  have hetaFactor : pairedEtaFactor s ≠ 0 :=
    pairedEtaFactor_ne_zero_of_re_lt_one hslt
  rw [riemannXi_eq_mul_Gammaℝ_riemannZeta_of_re_pos hspos hs1]
  unfold pairedEtaCompletedXi pairedEtaXiCompletionFactor
    pairedEtaXiCompletionNumerator
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hspos hs1]
  change (s * (1 - s) * Complex.Gammaℝ s /
      pairedEtaFactor s) *
      (pairedEtaFactor s * riemannZeta s) =
    s * (1 - s) * Complex.Gammaℝ s * riemannZeta s
  field_simp [hetaFactor]

/-- The completed eta/xi identity holds throughout a neighborhood of every
point in the open critical strip, allowing derivatives to be transported
without a hidden pointwise-to-local step. -/
theorem pairedEtaCompletedXi_eventuallyEq_riemannXi
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaCompletedXi =ᶠ[𝓝 s] riemannXi := by
  filter_upwards [
    (Complex.isOpen_re_gt 0).mem_nhds hspos,
    (Complex.isOpen_re_lt 1).mem_nhds hslt] with w hwpos hwlt
  exact pairedEtaCompletedXi_eq_riemannXi hwpos hwlt

/-- Every iterated derivative of completed paired eta agrees with the
corresponding xi derivative in the open critical strip. -/
theorem iteratedDeriv_pairedEtaCompletedXi_eq_riemannXi
    (n : ℕ) {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    iteratedDeriv n pairedEtaCompletedXi s =
      iteratedDeriv n riemannXi s :=
  (pairedEtaCompletedXi_eventuallyEq_riemannXi hspos hslt).iteratedDeriv_eq n

/-- All xi derivatives inherit the alternating sign of its functional
equation. -/
theorem iteratedDeriv_riemannXi_one_sub (n : ℕ) (s : ℂ) :
    iteratedDeriv n riemannXi (1 - s) =
      (-1 : ℂ) ^ n * iteratedDeriv n riemannXi s := by
  have hfun : (fun z : ℂ => riemannXi (1 - z)) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  have hder := congrFun (congrArg (iteratedDeriv n) hfun) (1 - s)
  rw [iteratedDeriv_comp_const_sub] at hder
  simpa [smul_eq_mul] using hder.symm

/-- Every iterated xi derivative commutes with complex conjugation. -/
theorem iteratedDeriv_riemannXi_conj (n : ℕ) (s : ℂ) :
    iteratedDeriv n riemannXi (starRingEnd ℂ s) =
      starRingEnd ℂ (iteratedDeriv n riemannXi s) := by
  have hfun :
      (starRingEnd ℂ ∘ riemannXi ∘ starRingEnd ℂ) = riemannXi := by
    funext w
    simp [Function.comp_apply, riemannXi_conj]
  have hiter := iteratedDeriv_conj_conj riemannXi n
  rw [hfun] at hiter
  have h := congrFun hiter (starRingEnd ℂ s)
  simpa [Function.comp_apply] using h

/-- Across the critical-line partner, every xi derivative is the conjugate
derivative with the functional-equation parity sign. -/
theorem iteratedDeriv_riemannXi_conjugatePartner
    (n : ℕ) (rho : NontrivialZetaZero) :
    iteratedDeriv n riemannXi
        (NontrivialZetaZero.conjugatePartner rho).1 =
      (-1 : ℂ) ^ n *
        starRingEnd ℂ (iteratedDeriv n riemannXi rho.1) := by
  rw [NontrivialZetaZero.conjugatePartner_coe,
    iteratedDeriv_riemannXi_one_sub,
    iteratedDeriv_riemannXi_conj]

/-- Completed paired eta therefore has the exact complementary local-
coefficient symmetry at every nontrivial zero and every derivative order. -/
theorem iteratedDeriv_pairedEtaCompletedXi_conjugatePartner
    (n : ℕ) (rho : NontrivialZetaZero) :
    iteratedDeriv n pairedEtaCompletedXi
        (NontrivialZetaZero.conjugatePartner rho).1 =
      (-1 : ℂ) ^ n *
        starRingEnd ℂ (iteratedDeriv n pairedEtaCompletedXi rho.1) := by
  rw [iteratedDeriv_pairedEtaCompletedXi_eq_riemannXi n
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
      (NontrivialZetaZero.re_lt_one
        (NontrivialZetaZero.conjugatePartner rho)),
    iteratedDeriv_riemannXi_conjugatePartner,
    iteratedDeriv_pairedEtaCompletedXi_eq_riemannXi n
      (NontrivialZetaZero.zero_lt_re rho)
      (NontrivialZetaZero.re_lt_one rho)]

/-- The analytic order of paired eta is the natural-valued genuine zeta-zero
multiplicity, viewed in `ℕ∞`. -/
theorem analyticOrderAt_pairedEtaCore_eq_multiplicity
    (rho : NontrivialZetaZero) :
    analyticOrderAt pairedEtaCore rho.1 =
      (analyticZetaZeroMultiplicity rho : ℕ∞) := by
  have hfinite : analyticOrderAt pairedEtaCore rho.1 ≠ ⊤ := by
    rw [analyticOrderAt_pairedEtaCore_eq_riemannZeta]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  calc
    analyticOrderAt pairedEtaCore rho.1 =
        (analyticOrderNatAt pairedEtaCore rho.1 : ℕ∞) :=
      (Nat.cast_analyticOrderNatAt hfinite).symm
    _ = (analyticZetaZeroMultiplicity rho : ℕ∞) := by
      rw [analyticOrderNatAt_pairedEtaCore_eq_analyticZetaZeroMultiplicity]

/-- Every paired-eta derivative below the genuine zero multiplicity
vanishes. -/
theorem iteratedDeriv_pairedEtaCore_eq_zero_of_lt_multiplicity
    (rho : NontrivialZetaZero) {k : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) :
    iteratedDeriv k pairedEtaCore rho.1 = 0 := by
  have hanalytic : AnalyticAt ℂ pairedEtaCore rho.1 :=
    analyticOnNhd_pairedEtaCore rho.1
      (NontrivialZetaZero.zero_lt_re rho)
  exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hanalytic).mp
    (analyticOrderAt_pairedEtaCore_eq_multiplicity rho)).1 k hk

/-- The first paired-eta derivative at the genuine zero multiplicity is
nonzero, with no simplicity assumption. -/
theorem iteratedDeriv_pairedEtaCore_multiplicity_ne_zero
    (rho : NontrivialZetaZero) :
    iteratedDeriv (analyticZetaZeroMultiplicity rho)
      pairedEtaCore rho.1 ≠ 0 := by
  have hanalytic : AnalyticAt ℂ pairedEtaCore rho.1 :=
    analyticOnNhd_pairedEtaCore rho.1
      (NontrivialZetaZero.zero_lt_re rho)
  exact ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hanalytic).mp
    (analyticOrderAt_pairedEtaCore_eq_multiplicity rho)).2

/-- At the first nonzero derivative order, completing paired eta multiplies
its leading derivative by the value of the completion factor; all other
Leibniz terms vanish by the exact analytic order. -/
theorem iteratedDeriv_pairedEtaCompletedXi_multiplicity
    (rho : NontrivialZetaZero) :
    iteratedDeriv (analyticZetaZeroMultiplicity rho)
        pairedEtaCompletedXi rho.1 =
      pairedEtaXiCompletionFactor rho.1 *
        iteratedDeriv (analyticZetaZeroMultiplicity rho)
          pairedEtaCore rho.1 := by
  classical
  let m := analyticZetaZeroMultiplicity rho
  have hfactor : ContDiffAt ℂ (m : ℕ∞)
      pairedEtaXiCompletionFactor rho.1 :=
    (analyticAt_pairedEtaXiCompletionFactor
      (NontrivialZetaZero.zero_lt_re rho)
      (NontrivialZetaZero.re_lt_one rho)).contDiffAt
  have hcore : ContDiffAt ℂ (m : ℕ∞) pairedEtaCore rho.1 :=
    (analyticOnNhd_pairedEtaCore rho.1
      (NontrivialZetaZero.zero_lt_re rho)).contDiffAt
  change iteratedDeriv m (pairedEtaXiCompletionFactor * pairedEtaCore)
      rho.1 = _
  rw [iteratedDeriv_mul hfactor hcore, Finset.sum_eq_single 0]
  · simp [m]
  · intro i hi hi0
    have hirange : i < m + 1 := Finset.mem_range.mp hi
    have hsub : m - i < m := by
      have hmpos : 0 < m := analyticZetaZeroMultiplicity_positive rho
      omega
    rw [iteratedDeriv_pairedEtaCore_eq_zero_of_lt_multiplicity rho hsub]
    simp
  · simp

/-- The exact leading paired-eta local coefficient obeys completed
functional-equation symmetry at arbitrary zero multiplicity. -/
theorem pairedEtaLeadingDerivative_conjugatePartner
    (rho : NontrivialZetaZero) :
    pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1 *
        iteratedDeriv (analyticZetaZeroMultiplicity rho) pairedEtaCore
          (NontrivialZetaZero.conjugatePartner rho).1 =
      (-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
        starRingEnd ℂ
          (pairedEtaXiCompletionFactor rho.1 *
            iteratedDeriv (analyticZetaZeroMultiplicity rho)
              pairedEtaCore rho.1) := by
  let m := analyticZetaZeroMultiplicity rho
  have hpartner :
      iteratedDeriv m pairedEtaCompletedXi
          (NontrivialZetaZero.conjugatePartner rho).1 =
        pairedEtaXiCompletionFactor
            (NontrivialZetaZero.conjugatePartner rho).1 *
          iteratedDeriv m pairedEtaCore
            (NontrivialZetaZero.conjugatePartner rho).1 := by
    simpa [m] using
      iteratedDeriv_pairedEtaCompletedXi_multiplicity
        (NontrivialZetaZero.conjugatePartner rho)
  calc
    pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 *
          iteratedDeriv m pairedEtaCore
            (NontrivialZetaZero.conjugatePartner rho).1 =
        iteratedDeriv m pairedEtaCompletedXi
          (NontrivialZetaZero.conjugatePartner rho).1 := hpartner.symm
    _ = (-1 : ℂ) ^ m *
          starRingEnd ℂ (iteratedDeriv m pairedEtaCompletedXi rho.1) :=
      iteratedDeriv_pairedEtaCompletedXi_conjugatePartner m rho
    _ = (-1 : ℂ) ^ m *
        starRingEnd ℂ
          (pairedEtaXiCompletionFactor rho.1 *
            iteratedDeriv m pairedEtaCore rho.1) := by
      rw [iteratedDeriv_pairedEtaCompletedXi_multiplicity]

/-- Solving the leading-coefficient relation gives the raw paired-eta
derivative at the reflected zero for its full analytic multiplicity. -/
theorem iteratedDeriv_pairedEtaCore_conjugatePartner_multiplicity
    (rho : NontrivialZetaZero) :
    iteratedDeriv (analyticZetaZeroMultiplicity rho) pairedEtaCore
        (NontrivialZetaZero.conjugatePartner rho).1 =
      ((-1 : ℂ) ^ (analyticZetaZeroMultiplicity rho) *
        starRingEnd ℂ
          (pairedEtaXiCompletionFactor rho.1 *
            iteratedDeriv (analyticZetaZeroMultiplicity rho)
              pairedEtaCore rho.1)) /
        pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 := by
  have hfactorNe : pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 ≠ 0 :=
    pairedEtaXiCompletionFactor_ne_zero
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
      (NontrivialZetaZero.re_lt_one
        (NontrivialZetaZero.conjugatePartner rho))
  apply (eq_div_iff hfactorNe).2
  rw [mul_comm]
  exact pairedEtaLeadingDerivative_conjugatePartner rho

/-- The completion-weighted magnitudes of the first nonzero paired-eta local
coefficients agree exactly at complementary zeros, for arbitrary
multiplicity. -/
theorem norm_pairedEtaLeadingDerivative_conjugatePartner
    (rho : NontrivialZetaZero) :
    ‖pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1‖ *
        ‖iteratedDeriv (analyticZetaZeroMultiplicity rho) pairedEtaCore
          (NontrivialZetaZero.conjugatePartner rho).1‖ =
      ‖pairedEtaXiCompletionFactor rho.1‖ *
        ‖iteratedDeriv (analyticZetaZeroMultiplicity rho)
          pairedEtaCore rho.1‖ := by
  have hnorm := congrArg norm
    (pairedEtaLeadingDerivative_conjugatePartner rho)
  simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_conj] using hnorm

/-- Paired eta itself vanishes at every nontrivial zeta zero. -/
theorem pairedEtaCore_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZero) :
    pairedEtaCore rho.1 = 0 := by
  rw [pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one
    (NontrivialZetaZero.zero_lt_re rho) rho.2.2.2,
    rho.2.1, mul_zero]

/-- At a zeta zero, the xi derivative is the explicit completion factor
times the genuinely convergent arithmetic eta derivative series. -/
theorem deriv_riemannXi_eq_pairedEtaXiCompletionFactor_mul_arithmeticDerivative
    (rho : NontrivialZetaZero) :
    deriv riemannXi rho.1 =
      pairedEtaXiCompletionFactor rho.1 *
        pairedEtaArithmeticDerivativeValue rho.1 := by
  have hspos := NontrivialZetaZero.zero_lt_re rho
  have hslt := NontrivialZetaZero.re_lt_one rho
  have hlocal := pairedEtaCompletedXi_eventuallyEq_riemannXi hspos hslt
  have hfactor : DifferentiableAt ℂ pairedEtaXiCompletionFactor rho.1 :=
    differentiableAt_pairedEtaXiCompletionFactor hspos hslt
  have heta := hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hspos
  have hcore := pairedEtaCore_eq_zero_of_nontrivialZetaZero rho
  calc
    deriv riemannXi rho.1 = deriv pairedEtaCompletedXi rho.1 :=
      hlocal.deriv_eq.symm
    _ = pairedEtaXiCompletionFactor rho.1 *
          pairedEtaArithmeticDerivativeValue rho.1 := by
      change deriv (pairedEtaXiCompletionFactor * pairedEtaCore) rho.1 = _
      simpa [pairedEtaCompletedXi, hcore] using
        (hfactor.hasDerivAt.mul heta).deriv

/-- The xi derivative commutes with conjugation in the original zeta
coordinate. -/
theorem deriv_riemannXi_conj (s : ℂ) :
    deriv riemannXi (starRingEnd ℂ s) =
      starRingEnd ℂ (deriv riemannXi s) := by
  simpa only [iteratedDeriv_one] using iteratedDeriv_riemannXi_conj 1 s

/-- At the reflected partner, the xi derivative is the negative conjugate of
the original derivative. -/
theorem deriv_riemannXi_conjugatePartner (rho : NontrivialZetaZero) :
    deriv riemannXi (NontrivialZetaZero.conjugatePartner rho).1 =
      -starRingEnd ℂ (deriv riemannXi rho.1) := by
  simpa only [iteratedDeriv_one, pow_one, neg_mul, one_mul] using
    iteratedDeriv_riemannXi_conjugatePartner 1 rho

/-- Exact completed complementary relation between the two convergent
arithmetic eta derivative series at every nontrivial zero. -/
theorem pairedEtaCompletedArithmeticDerivative_conjugatePartner
    (rho : NontrivialZetaZero) :
    pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1 *
        pairedEtaArithmeticDerivativeValue
          (NontrivialZetaZero.conjugatePartner rho).1 =
      -starRingEnd ℂ
        (pairedEtaXiCompletionFactor rho.1 *
          pairedEtaArithmeticDerivativeValue rho.1) := by
  calc
    pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 *
          pairedEtaArithmeticDerivativeValue
            (NontrivialZetaZero.conjugatePartner rho).1 =
        deriv riemannXi
          (NontrivialZetaZero.conjugatePartner rho).1 :=
      (deriv_riemannXi_eq_pairedEtaXiCompletionFactor_mul_arithmeticDerivative
        (NontrivialZetaZero.conjugatePartner rho)).symm
    _ = -starRingEnd ℂ (deriv riemannXi rho.1) :=
      deriv_riemannXi_conjugatePartner rho
    _ = -starRingEnd ℂ
        (pairedEtaXiCompletionFactor rho.1 *
          pairedEtaArithmeticDerivativeValue rho.1) := by
      rw [deriv_riemannXi_eq_pairedEtaXiCompletionFactor_mul_arithmeticDerivative]

/-- Solving the completed relation gives the complementary arithmetic eta
derivative explicitly. -/
theorem pairedEtaArithmeticDerivativeValue_conjugatePartner
    (rho : NontrivialZetaZero) :
    pairedEtaArithmeticDerivativeValue
        (NontrivialZetaZero.conjugatePartner rho).1 =
      (-starRingEnd ℂ
        (pairedEtaXiCompletionFactor rho.1 *
          pairedEtaArithmeticDerivativeValue rho.1)) /
        pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 := by
  have hfactorNe : pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 ≠ 0 :=
    pairedEtaXiCompletionFactor_ne_zero
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
      (NontrivialZetaZero.re_lt_one
        (NontrivialZetaZero.conjugatePartner rho))
  apply (eq_div_iff hfactorNe).2
  rw [mul_comm]
  exact pairedEtaCompletedArithmeticDerivative_conjugatePartner rho

/-- The completed magnitudes of the two convergent arithmetic derivatives
are exactly equal at complementary zeros. -/
theorem norm_pairedEtaCompletedArithmeticDerivative_conjugatePartner
    (rho : NontrivialZetaZero) :
    ‖pairedEtaXiCompletionFactor
        (NontrivialZetaZero.conjugatePartner rho).1‖ *
        ‖pairedEtaArithmeticDerivativeValue
          (NontrivialZetaZero.conjugatePartner rho).1‖ =
      ‖pairedEtaXiCompletionFactor rho.1‖ *
        ‖pairedEtaArithmeticDerivativeValue rho.1‖ := by
  have hnorm := congrArg norm
    (pairedEtaCompletedArithmeticDerivative_conjugatePartner rho)
  simpa only [norm_mul, norm_neg, norm_conj] using hnorm

/-- Vanishing of the first arithmetic eta derivative is preserved by the
critical-line partner. This includes multiple zeros without assuming
simplicity. -/
theorem pairedEtaArithmeticDerivativeValue_conjugatePartner_eq_zero_iff
    (rho : NontrivialZetaZero) :
    pairedEtaArithmeticDerivativeValue
        (NontrivialZetaZero.conjugatePartner rho).1 = 0 ↔
      pairedEtaArithmeticDerivativeValue rho.1 = 0 := by
  have hleft : pairedEtaXiCompletionFactor
      (NontrivialZetaZero.conjugatePartner rho).1 ≠ 0 :=
    pairedEtaXiCompletionFactor_ne_zero
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
      (NontrivialZetaZero.re_lt_one
        (NontrivialZetaZero.conjugatePartner rho))
  have hright : pairedEtaXiCompletionFactor rho.1 ≠ 0 :=
    pairedEtaXiCompletionFactor_ne_zero
      (NontrivialZetaZero.zero_lt_re rho)
      (NontrivialZetaZero.re_lt_one rho)
  constructor
  · intro hzero
    have hrel := pairedEtaCompletedArithmeticDerivative_conjugatePartner rho
    rw [hzero, mul_zero] at hrel
    have hprod : pairedEtaXiCompletionFactor rho.1 *
        pairedEtaArithmeticDerivativeValue rho.1 = 0 := by
      simpa only [neg_eq_zero, map_eq_zero] using hrel.symm
    exact (mul_eq_zero.mp hprod).resolve_left hright
  · intro hzero
    have hrel := pairedEtaCompletedArithmeticDerivative_conjugatePartner rho
    rw [hzero, mul_zero, map_zero, neg_zero] at hrel
    exact (mul_eq_zero.mp hrel).resolve_left hleft

end

end RiemannGaussian
