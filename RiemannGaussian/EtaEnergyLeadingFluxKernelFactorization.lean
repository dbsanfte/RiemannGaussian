import RiemannGaussian.EtaEnergyLeadingFluxKernel
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionMultiplier
import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaGaussianSigmaMoments

/-!
# Pointwise factorization of the higher-multiplicity eta current

The literal adjacent-moment kernel is expanded into four real factors: a
strictly positive cutoff-shift scale, an almost-everywhere strictly negative
odd centered monomial, one cosine phase, and one complementary horizontal-tilt
bracket.  The bracket vanishes identically on the critical line and, away from
that line, has exactly one explicitly located crossover.

Thus the higher-multiplicity frontier has only two possible pointwise sign
changes on its finite positive-measure support: the Fourier cosine and the
single horizontal crossover.  These identities do not assert the still-open
arithmetic cancellation estimate for the kernel integral.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The first `N` finite eta intervals lie strictly below the first omitted
odd logarithmic endpoint. -/
theorem ae_lt_pairedEtaLogTailCutoff_pairedEtaFiniteLogMeasure (N : ℕ) :
    ∀ᵐ t : ℝ ∂pairedEtaFiniteLogMeasure N,
      t < pairedEtaLogTailCutoff N := by
  unfold pairedEtaFiniteLogMeasure
  rw [ae_finsetSum_measure_iff]
  intro n hn
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hlog : Real.log (2 * (n : ℝ) + 2) <
      Real.log (((2 * N + 1 : ℕ) : ℝ)) := by
    apply Real.strictMonoOn_log
    · exact mem_Ioi.mpr (by positivity)
    · exact mem_Ioi.mpr (by positivity)
    · exact_mod_cast (show 2 * n + 2 < 2 * N + 1 by
        have := Finset.mem_range.mp hn
        omega)
  unfold pairedEtaLogTailCutoff
  exact lt_of_le_of_lt ht.2 hlog

private theorem centered_adjacent_power_product_neg
    {x y : ℝ} {k : ℕ} (hk : 1 ≤ k) (hx : x < 0) (hy : y < 0) :
    x ^ (k - 1) * y ^ k < 0 := by
  have hxy : 0 < x * y := mul_pos_of_neg_of_neg hx hy
  have hyPow : y ^ k = y ^ (k - 1) * y := by
    calc
      y ^ k = y ^ ((k - 1) + 1) := by
        congr 1
        omega
      _ = y ^ (k - 1) * y := pow_succ y (k - 1)
  rw [hyPow]
  rw [← mul_assoc, ← mul_pow]
  exact mul_neg_of_pos_of_neg (pow_pos hxy _) hy

private theorem exp_mul_conj_exp_re (s : ℂ) (t u : ℝ) :
    (Complex.exp (-s * t) *
        starRingEnd ℂ (Complex.exp (-s * u))).re =
      Real.exp (-s.re * (t + u)) *
        Real.cos (s.im * (u - t)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add, Complex.exp_re]
  congr 1
  · simp only [Complex.add_re, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      mul_zero, sub_zero]
    ring_nf
  · congr 1
    simp only [Complex.add_im, Complex.neg_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im,
      mul_zero]
    ring_nf

private theorem completed_exponential_feature_pair_re
    (C s : ℂ) (x y t u : ℝ) (a b : ℕ) :
    ((C * (((x : ℂ) ^ a) * Complex.exp (-s * t))) *
        starRingEnd ℂ
          (C * (((y : ℂ) ^ b) * Complex.exp (-s * u)))).re =
      Complex.normSq C * (x ^ a * y ^ b) *
        Real.exp (-s.re * (t + u)) *
          Real.cos (s.im * (u - t)) := by
  have hfactor :
      (C * (((x : ℂ) ^ a) * Complex.exp (-s * t))) *
          starRingEnd ℂ
            (C * (((y : ℂ) ^ b) * Complex.exp (-s * u))) =
        ((Complex.normSq C * (x ^ a * y ^ b) : ℝ) : ℂ) *
          (Complex.exp (-s * t) *
            starRingEnd ℂ (Complex.exp (-s * u))) := by
    rw [map_mul, map_mul, map_pow, Complex.conj_ofReal]
    calc
      C * ((x : ℂ) ^ a * cexp (-s * (t : ℂ))) *
          ((star C) * ((y : ℂ) ^ b *
            star (cexp (-s * (u : ℂ))))) =
        (C * star C) * ((x : ℂ) ^ a * (y : ℂ) ^ b) *
          (cexp (-s * (t : ℂ)) *
            star (cexp (-s * (u : ℂ)))) := by ring_nf
      _ = ((Complex.normSq C * (x ^ a * y ^ b) : ℝ) : ℂ) *
          (cexp (-s * (t : ℂ)) *
            star (cexp (-s * (u : ℂ)))) := by
        have hC : C * star C = (Complex.normSq C : ℂ) := by
          simpa only [starRingEnd_apply] using Complex.mul_conj C
        rw [hC]
        push_cast
        ring_nf
  rw [hfactor]
  have hrealMul (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
  have hexp :
      (cexp (-s * (t : ℂ)) * star (cexp (-s * (u : ℂ)))).re =
        Real.exp (-s.re * (t + u)) * Real.cos (s.im * (u - t)) := by
    simpa only [starRingEnd_apply] using exp_mul_conj_exp_re s t u
  calc
    (((Complex.normSq C * (x ^ a * y ^ b) : ℝ) : ℂ) *
        (cexp (-s * (t : ℂ)) *
          star (cexp (-s * (u : ℂ))))).re =
      Complex.normSq C * (x ^ a * y ^ b) *
        (cexp (-s * (t : ℂ)) *
          star (cexp (-s * (u : ℂ)))).re := by
      rw [hrealMul]
    _ = Complex.normSq C * (x ^ a * y ^ b) *
        Real.exp (-s.re * (t + u)) * Real.cos (s.im * (u - t)) := by
      rw [hexp]
      ring_nf

/-- The sole complementary horizontal factor in the higher-multiplicity
leading-current kernel. -/
def pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket
    (rho : NontrivialZetaZero) (v : ℝ) : ℝ :=
  pairedEtaCompletedLaplaceWeight
      (NontrivialZetaZero.conjugatePartner rho).1 *
        Real.exp (-(1 - rho.1.re) * v) -
    pairedEtaCompletedLaplaceWeight rho.1 *
      Real.exp (-rho.1.re * v)

/-- The reflected-partner lower--top pairing is a completion weight times an
odd centered monomial, a complementary exponential tilt, and one cosine. -/
theorem topPrefixFinitePartnerLower_mul_conj_top_re
    (rho : NontrivialZetaZero) (N : ℕ) (t u : ℝ) :
    (pairedEtaTopPrefixFinitePartnerLowerFeature rho (N + 1) t *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
            rho (N + 1) u)).re =
      pairedEtaCompletedLaplaceWeight
          (NontrivialZetaZero.conjugatePartner rho).1 *
        ((t - pairedEtaLogTailCutoff (N + 2)) ^
            (analyticZetaZeroMultiplicity rho - 2) *
          (u - pairedEtaLogTailCutoff (N + 2)) ^
            (analyticZetaZeroMultiplicity rho - 1)) *
        Real.exp (-(1 - rho.1.re) * (t + u)) *
        Real.cos (rho.1.im * (u - t)) := by
  unfold pairedEtaTopPrefixFinitePartnerLowerFeature
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
    pairedEtaCompletedLaplaceWeight
  simpa only [NontrivialZetaZero.conjugatePartner_coe,
      Complex.sub_re, Complex.one_re, Complex.conj_re,
      Complex.sub_im, Complex.one_im, Complex.conj_im,
      zero_sub, neg_neg, Nat.add_assoc] using
    completed_exponential_feature_pair_re
      (pairedEtaXiCompletionFactor
          (NontrivialZetaZero.conjugatePartner rho).1 *
        (NontrivialZetaZero.conjugatePartner rho).1)
      (NontrivialZetaZero.conjugatePartner rho).1
      (t - pairedEtaLogTailCutoff (N + 2))
      (u - pairedEtaLogTailCutoff (N + 2)) t u
      (analyticZetaZeroMultiplicity rho - 2)
      (analyticZetaZeroMultiplicity rho - 1)

private theorem parity_conjugate_pair_re (m : ℕ) (A B : ℂ) :
    (((-1 : ℂ) ^ m * starRingEnd ℂ A) *
        starRingEnd ℂ ((-1 : ℂ) ^ m * starRingEnd ℂ B)).re =
      (B * starRingEnd ℂ A).re := by
  have hr : ((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m) = 1 := by
    rw [← mul_pow]
    norm_num
  simp only [map_mul, map_pow, map_neg, map_one,
    starRingEnd_apply, star_star]
  calc
    (((-1 : ℂ) ^ m * starRingEnd ℂ A) *
        ((-1 : ℂ) ^ m * B)).re =
      ((((-1 : ℂ) ^ m) * ((-1 : ℂ) ^ m)) *
        (B * starRingEnd ℂ A)).re := by ring_nf
    _ = (B * starRingEnd ℂ A).re := by rw [hr, one_mul]

/-- The parity-conjugated original lower--top pairing has the same monomial
and cosine, with the original complementary tilt and completion weight. -/
theorem topPrefixFiniteConjugateLower_mul_conj_top_re
    (rho : NontrivialZetaZero) (N : ℕ) (t u : ℝ) :
    (pairedEtaTopPrefixFiniteConjugateLowerFeature rho (N + 1) t *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
            rho (N + 1) u)).re =
      pairedEtaCompletedLaplaceWeight rho.1 *
        ((t - pairedEtaLogTailCutoff (N + 2)) ^
            (analyticZetaZeroMultiplicity rho - 2) *
          (u - pairedEtaLogTailCutoff (N + 2)) ^
            (analyticZetaZeroMultiplicity rho - 1)) *
        Real.exp (-rho.1.re * (t + u)) *
        Real.cos (rho.1.im * (u - t)) := by
  let C := pairedEtaXiCompletionFactor rho.1 * rho.1
  let x := t - pairedEtaLogTailCutoff (N + 2)
  let y := u - pairedEtaLogTailCutoff (N + 2)
  let a := analyticZetaZeroMultiplicity rho - 2
  let b := analyticZetaZeroMultiplicity rho - 1
  let E : ℝ → ℂ := fun v => Complex.exp (-rho.1 * v)
  let A : ℂ := C * (((x : ℝ) : ℂ) ^ a * E t)
  let B : ℂ := C * (((y : ℝ) : ℂ) ^ b * E u)
  have hrewrite :
      (pairedEtaTopPrefixFiniteConjugateLowerFeature rho (N + 1) t *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
              rho (N + 1) u)).re =
        ((C * (((y : ℝ) : ℂ) ^ b * E u)) *
          starRingEnd ℂ
            (C * (((x : ℝ) : ℂ) ^ a * E t))).re := by
    unfold pairedEtaTopPrefixFiniteConjugateLowerFeature
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
    simpa only [A, B, C, x, y, a, b, E, Nat.add_assoc] using
      parity_conjugate_pair_re
        (analyticZetaZeroMultiplicity rho) A B
  rw [hrewrite]
  unfold pairedEtaCompletedLaplaceWeight
  have hcos : Real.cos (rho.1.im * (t - u)) =
      Real.cos (rho.1.im * (u - t)) := by
    rw [show rho.1.im * (t - u) = -(rho.1.im * (u - t)) by ring_nf,
      Real.cos_neg]
  have h := completed_exponential_feature_pair_re C rho.1 y x u t b a
  rw [hcos] at h
  simpa only [C, x, y, a, b, E, mul_comm, add_comm] using h

/-- Fully real factorization of the higher-multiplicity adjacent-current
kernel. -/
def pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel
    (rho : NontrivialZetaZero) (N : ℕ) (z : ℝ × ℝ) : ℝ :=
  2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) *
      pairedEtaLogTailShiftIncrement (N + 1)) *
    ((z.1 - pairedEtaLogTailCutoff (N + 2)) ^
        (analyticZetaZeroMultiplicity rho - 2) *
      (z.2 - pairedEtaLogTailCutoff (N + 2)) ^
        (analyticZetaZeroMultiplicity rho - 1)) *
    Real.cos (rho.1.im * (z.2 - z.1)) *
    pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket rho (z.1 + z.2)

/-- The literal adjacent-current kernel is pointwise equal to its four-factor
real form. -/
theorem topPrefixFiniteEnergyAdjacentMomentKernel_eq_factored
    (rho : NontrivialZetaZero) (N : ℕ) (z : ℝ × ℝ) :
    pairedEtaTopPrefixFiniteEnergyAdjacentMomentKernel rho N z =
      pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N z := by
  unfold pairedEtaTopPrefixFiniteEnergyAdjacentMomentKernel
    pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel
    pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket
  rw [Complex.sub_re, topPrefixFinitePartnerLower_mul_conj_top_re,
    topPrefixFiniteConjugateLower_mul_conj_top_re]
  ring_nf

/-- At multiplicity at least two, the odd centered monomial is strictly
negative almost everywhere on the successor finite eta product measure. -/
theorem ae_topPrefixFiniteEnergyAdjacentCenteredMonomial_neg
    (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ∀ᵐ z : ℝ × ℝ
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod
        (pairedEtaFiniteLogMeasure (N + 2))),
      (z.1 - pairedEtaLogTailCutoff (N + 2)) ^
          (analyticZetaZeroMultiplicity rho - 2) *
        (z.2 - pairedEtaLogTailCutoff (N + 2)) ^
          (analyticZetaZeroMultiplicity rho - 1) < 0 := by
  rw [Measure.ae_prod_iff_ae_ae (by measurability)]
  filter_upwards
    [ae_lt_pairedEtaLogTailCutoff_pairedEtaFiniteLogMeasure (N + 2)]
    with t ht
  filter_upwards
    [ae_lt_pairedEtaLogTailCutoff_pairedEtaFiniteLogMeasure (N + 2)]
    with u hu
  let k := analyticZetaZeroMultiplicity rho - 1
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hneg := centered_adjacent_power_product_neg hk
    (sub_neg.mpr ht) (sub_neg.mpr hu)
  simpa only [k, show analyticZetaZeroMultiplicity rho - 1 - 1 =
      analyticZetaZeroMultiplicity rho - 2 by omega] using hneg

/-- At multiplicity at least two, the cutoff-shift scale in the factored
kernel is strictly positive. -/
theorem topPrefixFiniteEnergyAdjacentScale_pos
    (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    0 < 2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) *
      pairedEtaLogTailShiftIncrement (N + 1)) := by
  have hmNat : 0 < analyticZetaZeroMultiplicity rho - 1 := by omega
  have hmReal : 0 < ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) := by
    exact_mod_cast hmNat
  exact mul_pos (by norm_num)
    (mul_pos hmReal (pairedEtaLogTailShiftIncrement_pos (N + 1)))

/-- A critical-line zero is fixed by reflection across the critical line. -/
theorem conjugatePartner_eq_self_of_re_eq_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re = 1 / 2) :
    NontrivialZetaZero.conjugatePartner rho = rho := by
  apply Subtype.ext
  rw [NontrivialZetaZero.conjugatePartner_coe]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
    ring_nf

/-- On the critical line, the complementary horizontal bracket vanishes
pointwise. -/
theorem topPrefixFiniteEnergyHorizontalTiltBracket_eq_zero_of_re_eq_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re = 1 / 2) (v : ℝ) :
    pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket rho v = 0 := by
  have hp := conjugatePartner_eq_self_of_re_eq_half rho hrho
  unfold pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket
  rw [hp, hrho]
  ring_nf

/-- The unique candidate crossover time for the complementary horizontal
bracket away from the critical line. -/
def pairedEtaTopPrefixFiniteEnergyHorizontalTiltCrossover
    (rho : NontrivialZetaZero) : ℝ :=
  (Real.log (pairedEtaCompletedLaplaceWeight rho.1) -
      Real.log (pairedEtaCompletedLaplaceWeight
        (NontrivialZetaZero.conjugatePartner rho).1)) /
    (2 * rho.1.re - 1)

/-- Away from the critical line, the horizontal bracket has exactly one zero,
at the explicit completion-weight crossover. -/
theorem topPrefixFiniteEnergyHorizontalTiltBracket_eq_zero_iff_eq_crossover
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) (v : ℝ) :
    pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket rho v = 0 ↔
      v = pairedEtaTopPrefixFiniteEnergyHorizontalTiltCrossover rho := by
  let A := pairedEtaCompletedLaplaceWeight
    (NontrivialZetaZero.conjugatePartner rho).1
  let B := pairedEtaCompletedLaplaceWeight rho.1
  have hA : 0 < A := by
    dsimp only [A]
    exact pairedEtaCompletedLaplaceWeight_pos
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
      (NontrivialZetaZero.re_lt_one
        (NontrivialZetaZero.conjugatePartner rho))
  have hB : 0 < B := by
    dsimp only [B]
    exact pairedEtaCompletedLaplaceWeight_pos
      (NontrivialZetaZero.zero_lt_re rho)
      (NontrivialZetaZero.re_lt_one rho)
  have hden : 2 * rho.1.re - 1 ≠ 0 := by
    intro h
    apply hrho
    linarith
  unfold pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket
    pairedEtaTopPrefixFiniteEnergyHorizontalTiltCrossover
  change A * Real.exp (-(1 - rho.1.re) * v) -
      B * Real.exp (-rho.1.re * v) = 0 ↔
    v = (Real.log B - Real.log A) / (2 * rho.1.re - 1)
  rw [sub_eq_zero]
  constructor
  · intro h
    have hexpEq :
        Real.exp (Real.log A + -(1 - rho.1.re) * v) =
          Real.exp (Real.log B + -rho.1.re * v) := by
      rw [Real.exp_add, Real.exp_add,
        Real.exp_log hA, Real.exp_log hB]
      exact h
    have hlin : Real.log A + -(1 - rho.1.re) * v =
        Real.log B + -rho.1.re * v :=
      Real.exp_injective hexpEq
    apply (eq_div_iff hden).2
    linarith only [hlin]
  · intro h
    have hmul : v * (2 * rho.1.re - 1) =
        Real.log B - Real.log A := (eq_div_iff hden).mp h
    have hlin : Real.log A + -(1 - rho.1.re) * v =
        Real.log B + -rho.1.re * v := by
      linarith only [hmul]
    calc
      A * Real.exp (-(1 - rho.1.re) * v) =
          Real.exp (Real.log A + -(1 - rho.1.re) * v) := by
        rw [Real.exp_add, Real.exp_log hA]
      _ = Real.exp (Real.log B + -rho.1.re * v) :=
        congrArg Real.exp hlin
      _ = B * Real.exp (-rho.1.re * v) := by
        rw [Real.exp_add, Real.exp_log hB]

/-- The sign of the off-critical horizontal bracket is exactly the oriented
distance from its unique crossover. -/
theorem topPrefixFiniteEnergyHorizontalTiltBracket_pos_iff_oriented_crossover
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) (v : ℝ) :
    0 < pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket rho v ↔
      0 < (2 * rho.1.re - 1) *
        (v - pairedEtaTopPrefixFiniteEnergyHorizontalTiltCrossover rho) := by
  let A := pairedEtaCompletedLaplaceWeight
    (NontrivialZetaZero.conjugatePartner rho).1
  let B := pairedEtaCompletedLaplaceWeight rho.1
  have hA : 0 < A := by
    dsimp only [A]
    exact pairedEtaCompletedLaplaceWeight_pos
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
      (NontrivialZetaZero.re_lt_one
        (NontrivialZetaZero.conjugatePartner rho))
  have hB : 0 < B := by
    dsimp only [B]
    exact pairedEtaCompletedLaplaceWeight_pos
      (NontrivialZetaZero.zero_lt_re rho)
      (NontrivialZetaZero.re_lt_one rho)
  have hden : 2 * rho.1.re - 1 ≠ 0 := by
    intro h
    apply hrho
    linarith
  unfold pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket
    pairedEtaTopPrefixFiniteEnergyHorizontalTiltCrossover
  change 0 < A * Real.exp (-(1 - rho.1.re) * v) -
      B * Real.exp (-rho.1.re * v) ↔
    0 < (2 * rho.1.re - 1) *
      (v - (Real.log B - Real.log A) / (2 * rho.1.re - 1))
  rw [sub_pos]
  rw [show A * Real.exp (-(1 - rho.1.re) * v) =
      Real.exp (Real.log A + -(1 - rho.1.re) * v) by
        rw [Real.exp_add, Real.exp_log hA],
    show B * Real.exp (-rho.1.re * v) =
      Real.exp (Real.log B + -rho.1.re * v) by
        rw [Real.exp_add, Real.exp_log hB],
    Real.exp_lt_exp]
  have hcross : (2 * rho.1.re - 1) *
      ((Real.log B - Real.log A) / (2 * rho.1.re - 1)) =
        Real.log B - Real.log A := by
    exact mul_div_cancel₀ _ hden
  constructor <;> intro h <;> linarith only [h, hcross]

/-- On the critical line the adjacent-moment kernel vanishes pointwise. -/
theorem topPrefixFiniteEnergyAdjacentMomentKernel_eq_zero_of_re_eq_half
    (rho : NontrivialZetaZero) (hrho : rho.1.re = 1 / 2)
    (N : ℕ) (z : ℝ × ℝ) :
    pairedEtaTopPrefixFiniteEnergyAdjacentMomentKernel rho N z = 0 := by
  rw [topPrefixFiniteEnergyAdjacentMomentKernel_eq_factored]
  unfold pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel
  rw [topPrefixFiniteEnergyHorizontalTiltBracket_eq_zero_of_re_eq_half
    rho hrho]
  ring_nf

/-- The factored adjacent kernel remains genuinely integrable on the finite
positive eta product measure. -/
theorem integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N)
      ((pairedEtaFiniteLogMeasure (N + 2)).prod
        (pairedEtaFiniteLogMeasure (N + 2))) := by
  apply (integrable_topPrefixFiniteEnergyAdjacentMomentKernel rho N).congr
  filter_upwards with z
  exact topPrefixFiniteEnergyAdjacentMomentKernel_eq_factored rho N z

/-- At multiplicity at least two, the isolated leading flux is the integral
of the fully factored adjacent kernel. -/
theorem topPrefixFiniteEnergyLeadingFlux_eq_integral_factoredAdjacentMomentKernel_of_two_le_multiplicity
    (rho : NontrivialZetaZero)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      ∫ z : ℝ × ℝ,
        pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N z
        ∂((pairedEtaFiniteLogMeasure (N + 2)).prod
          (pairedEtaFiniteLogMeasure (N + 2))) := by
  rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_adjacentMomentKernel_of_two_le_multiplicity
    rho hm N]
  apply integral_congr_ae
  filter_upwards with z
  exact topPrefixFiniteEnergyAdjacentMomentKernel_eq_factored rho N z

/-- Almost every two-time point lies in the exact open support window for the
sum coordinate. -/
theorem ae_sum_mem_pairedEtaFiniteLogMeasure_supportWindow (N : ℕ) :
    ∀ᵐ z : ℝ × ℝ
      ∂((pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)),
      0 < z.1 + z.2 ∧
        z.1 + z.2 < 2 * pairedEtaLogTailCutoff N := by
  rw [Measure.ae_prod_iff_ae_ae (by measurability)]
  filter_upwards [ae_pos_pairedEtaFiniteLogMeasure N,
    ae_lt_pairedEtaLogTailCutoff_pairedEtaFiniteLogMeasure N]
    with t htPos htCut
  filter_upwards [ae_pos_pairedEtaFiniteLogMeasure N,
    ae_lt_pairedEtaLogTailCutoff_pairedEtaFiniteLogMeasure N]
    with u huPos huCut
  constructor <;> linarith

/-- If the unique horizontal crossover lies outside the finite support
window, the horizontal bracket is nonzero almost everywhere on that window. -/
theorem ae_topPrefixFiniteEnergyHorizontalTiltBracket_ne_zero_of_crossover_outside
    (rho : NontrivialZetaZero) (hrho : rho.1.re ≠ 1 / 2) (N : ℕ)
    (hout : pairedEtaTopPrefixFiniteEnergyHorizontalTiltCrossover rho ≤ 0 ∨
      2 * pairedEtaLogTailCutoff (N + 2) ≤
        pairedEtaTopPrefixFiniteEnergyHorizontalTiltCrossover rho) :
    ∀ᵐ z : ℝ × ℝ
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod
        (pairedEtaFiniteLogMeasure (N + 2))),
      pairedEtaTopPrefixFiniteEnergyHorizontalTiltBracket
        rho (z.1 + z.2) ≠ 0 := by
  filter_upwards
    [ae_sum_mem_pairedEtaFiniteLogMeasure_supportWindow (N + 2)]
    with z hz
  rw [Ne,
    topPrefixFiniteEnergyHorizontalTiltBracket_eq_zero_iff_eq_crossover
      rho hrho]
  intro heq
  rcases hout with hout | hout
  · linarith
  · linarith

end

end RiemannGaussian
