import RiemannGaussian.EtaCurrentFiniteMomentPair

/-!
# Arithmetic midpoint evaluation on the actual simple-zero head

The head coordinate is translated by the old cutoff, whereas the finite
prefix moments are centered at the successor cutoff. Both origins remain
in the exact midpoint identity, together with the negative head sign.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The negative completed new-head moment in its actual shifted coordinate. -/
def pairedEtaHeadCompletedMoment (rho : NontrivialZetaZero) (N k : ℕ) : ℂ :=
  (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    (-pairedEtaLogLaplaceMomentCutoffCenteredHead k rho.1 (N + 1))

/-- The literal negative completed head feature of arbitrary shifted order. -/
def pairedEtaHeadCompletedMomentFeature (rho : NontrivialZetaZero) (N k : ℕ) (t : ℝ) : ℂ :=
  (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    (-Complex.exp (-rho.1 * (pairedEtaLogTailCutoff (N + 1) : ℂ)) *
      ((t : ℂ) ^ k * Complex.exp (-rho.1 * t)))

/-- Every actual completed head moment has an integrable shifted feature. -/
theorem integrable_pairedEtaHeadCompletedMomentFeature (rho : NontrivialZetaZero) (N k : ℕ) :
    Integrable (pairedEtaHeadCompletedMomentFeature rho N k) (pairedEtaShiftedLogHeadMeasure (N + 1)) :=
  ((integrable_pairedEtaShiftedLogHeadLaplaceMoment_integrand k
    (NontrivialZetaZero.zero_lt_re rho) (N + 1)).const_mul _).const_mul _

/-- Integrating the actual head feature recovers its negative arithmetic head moment. -/
theorem integral_pairedEtaHeadCompletedMomentFeature (rho : NontrivialZetaZero) (N k : ℕ) :
    (∫ t, pairedEtaHeadCompletedMomentFeature rho N k t ∂pairedEtaShiftedLogHeadMeasure (N + 1)) =
      pairedEtaHeadCompletedMoment rho N k := by
  unfold pairedEtaHeadCompletedMomentFeature pairedEtaHeadCompletedMoment
    pairedEtaLogLaplaceMomentCutoffCenteredHead pairedEtaShiftedLogHeadLaplaceMoment
  rw [integral_const_mul, integral_const_mul]
  ring

/-- Raising a shifted head order multiplies its feature by the shifted time. -/
theorem pairedEtaHeadCompletedMomentFeature_succ (rho : NontrivialZetaZero) (N k : ℕ) (t : ℝ) :
    pairedEtaHeadCompletedMomentFeature rho N (k + 1) t =
      (t : ℂ) * pairedEtaHeadCompletedMomentFeature rho N k t := by
  unfold pairedEtaHeadCompletedMomentFeature
  rw [pow_succ]
  ring

/-- The complex arithmetic pair of the negative head and successor finite prefix. -/
def pairedEtaHeadCompletedMomentPair (rho : NontrivialZetaZero) (N k l : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N k)
    (pairedEtaFiniteCompletedMoment (NontrivialZetaZero.conjugatePartner rho) (N + 2) l)
    (pairedEtaHeadCompletedMoment rho N k) (pairedEtaFiniteCompletedMoment rho (N + 2) l)

/-- The literal complex signed head/prefix product kernel. -/
def pairedEtaHeadCompletedMomentPairKernel (rho : NontrivialZetaZero) (N k l : ℕ) (p : ℝ × ℝ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaHeadCompletedMomentFeature (NontrivialZetaZero.conjugatePartner rho) N k p.1)
    (pairedEtaFiniteCompletedMomentFeature (NontrivialZetaZero.conjugatePartner rho) (N + 2) l p.2)
    (pairedEtaHeadCompletedMomentFeature rho N k p.1) (pairedEtaFiniteCompletedMomentFeature rho (N + 2) l p.2)

/-- The signed head/prefix kernel is integrable on its two actual measures. -/
theorem integrable_pairedEtaHeadCompletedMomentPairKernel (rho : NontrivialZetaZero) (N k l : ℕ) :
    Integrable (pairedEtaHeadCompletedMomentPairKernel rho N k l)
      ((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))) :=
  integrable_etaSignedCompletedPair
    (integrable_pairedEtaHeadCompletedMomentFeature _ _ _)
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)
    (integrable_pairedEtaHeadCompletedMomentFeature _ _ _)
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)

/-- Genuine head/prefix product integration evaluates the complete signed arithmetic pair. -/
theorem integral_pairedEtaHeadCompletedMomentPairKernel (rho : NontrivialZetaZero) (N k l : ℕ) :
    (∫ p, pairedEtaHeadCompletedMomentPairKernel rho N k l p
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))) =
      pairedEtaHeadCompletedMomentPair rho N k l := by
  unfold pairedEtaHeadCompletedMomentPairKernel
  rw [integral_etaSignedCompletedPair
    (integrable_pairedEtaHeadCompletedMomentFeature _ _ _)
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)
    (integrable_pairedEtaHeadCompletedMomentFeature _ _ _)
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)]
  simp only [integral_pairedEtaHeadCompletedMomentFeature, integral_pairedEtaFiniteCompletedMomentFeature,
    pairedEtaHeadCompletedMomentPair]

/-- The physical head midpoint raises either moment order and retains both
the head origin and the successor prefix center. -/
theorem pairedEtaHeadCompletedMomentPairKernel_midpoint (rho : NontrivialZetaZero) (N k l : ℕ) (p : ℝ × ℝ) :
    pairedEtaHeadCompletedMomentPairKernel rho N k l p *
        ((p.1 + pairedEtaLogTailCutoff (N + 1) + p.2) / 2 : ℝ) =
      (((pairedEtaLogTailCutoff (N + 1) + pairedEtaLogTailCutoff (N + 2)) / 2 : ℝ) : ℂ) *
          pairedEtaHeadCompletedMomentPairKernel rho N k l p +
        (pairedEtaHeadCompletedMomentPairKernel rho N (k + 1) l p +
          pairedEtaHeadCompletedMomentPairKernel rho N k (l + 1) p) / 2 := by
  unfold pairedEtaHeadCompletedMomentPairKernel
  simp only [pairedEtaHeadCompletedMomentFeature_succ, pairedEtaFiniteCompletedMomentFeature_succ,
    etaSignedCompletedPair, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- The physical midpoint-weighted head/prefix kernel is integrable on its actual domain. -/
theorem integrable_pairedEtaHeadCompletedMomentPairKernel_midpoint
    (rho : NontrivialZetaZero) (N k l : ℕ) :
    Integrable (fun p ↦ pairedEtaHeadCompletedMomentPairKernel rho N k l p *
      ((p.1 + pairedEtaLogTailCutoff (N + 1) + p.2) / 2 : ℝ))
      ((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))) := by
  apply ((integrable_pairedEtaHeadCompletedMomentPairKernel rho N k l).const_mul
    (((pairedEtaLogTailCutoff (N + 1) + pairedEtaLogTailCutoff (N + 2)) / 2 : ℝ) : ℂ) |>.add
      (((integrable_pairedEtaHeadCompletedMomentPairKernel rho N (k + 1) l).add
        (integrable_pairedEtaHeadCompletedMomentPairKernel rho N k (l + 1))).div_const 2)).congr
  filter_upwards with p
  exact (pairedEtaHeadCompletedMomentPairKernel_midpoint rho N k l p).symm

/-- The physical head midpoint integral is the exact two-origin finite
arithmetic expression, with its signed complex orientation retained. -/
theorem integral_pairedEtaHeadCompletedMomentPairKernel_midpoint
    (rho : NontrivialZetaZero) (N k l : ℕ) :
    (∫ p, pairedEtaHeadCompletedMomentPairKernel rho N k l p *
        ((p.1 + pairedEtaLogTailCutoff (N + 1) + p.2) / 2 : ℝ)
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))) =
      (((pairedEtaLogTailCutoff (N + 1) + pairedEtaLogTailCutoff (N + 2)) / 2 : ℝ) : ℂ) *
          pairedEtaHeadCompletedMomentPair rho N k l +
        (pairedEtaHeadCompletedMomentPair rho N (k + 1) l +
          pairedEtaHeadCompletedMomentPair rho N k (l + 1)) / 2 := by
  simp_rw [pairedEtaHeadCompletedMomentPairKernel_midpoint]
  rw [integral_add
      (f := fun p ↦ (((pairedEtaLogTailCutoff (N + 1) + pairedEtaLogTailCutoff (N + 2)) / 2 : ℝ) : ℂ) *
        pairedEtaHeadCompletedMomentPairKernel rho N k l p)
      (g := fun p ↦ (pairedEtaHeadCompletedMomentPairKernel rho N (k + 1) l p +
        pairedEtaHeadCompletedMomentPairKernel rho N k (l + 1) p) / 2)
      ((integrable_pairedEtaHeadCompletedMomentPairKernel rho N k l).const_mul _)
      (((integrable_pairedEtaHeadCompletedMomentPairKernel rho N (k + 1) l).add
        (integrable_pairedEtaHeadCompletedMomentPairKernel rho N k (l + 1))).div_const 2),
    integral_const_mul, integral_div, integral_add
      (f := fun p ↦ pairedEtaHeadCompletedMomentPairKernel rho N (k + 1) l p)
      (g := fun p ↦ pairedEtaHeadCompletedMomentPairKernel rho N k (l + 1) p)
      (integrable_pairedEtaHeadCompletedMomentPairKernel rho N (k + 1) l)
      (integrable_pairedEtaHeadCompletedMomentPairKernel rho N k (l + 1))]
  simp only [integral_pairedEtaHeadCompletedMomentPairKernel]

/-- The actual head current is the real part of its signed complex head/prefix kernel. -/
theorem pairedEtaHeadKernel_eq_completedMomentPair (rho : NontrivialZetaZero) (N : ℕ) (p : ℝ × ℝ) :
    pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p =
      2 * (pairedEtaHeadCompletedMomentPairKernel rho N 0 (analyticZetaZeroMultiplicity rho - 1) p).re := by
  unfold pairedEtaTopPrefixFiniteEnergyHeadKernel pairedEtaHeadCompletedMomentPairKernel
  rw [etaSignedCompletedPair_eq_parity_pair (analyticZetaZeroMultiplicity rho)]
  simp only [pairedEtaHeadCompletedMomentFeature, pow_zero, one_mul]
  rfl

/-- At a simple zero, the unchanged leading current is the actual order-zero head/prefix pair. -/
theorem pairedEtaLeadingCurrent_eq_headCompletedMomentPair (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N =
      2 * (pairedEtaHeadCompletedMomentPair rho N 0 0).re := by
  rw [topPrefixFiniteEnergyLeadingFlux_eq_integral_headKernel_of_multiplicity_eq_one rho hm N]
  simp_rw [pairedEtaHeadKernel_eq_completedMomentPair, hm, Nat.sub_self]
  rw [integral_const_mul, integral_etaMomentPair_re (integrable_pairedEtaHeadCompletedMomentPairKernel rho N 0 0),
    integral_pairedEtaHeadCompletedMomentPairKernel]

/-- The actual simple-zero midpoint coefficient is evaluated in the two
finite eta moment pairs, retaining both physical cutoff origins. -/
theorem pairedEtaLeadingCurrentMidpointMoment_eq_head_arithmetic (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    pairedEtaLeadingCurrentMidpointMoment rho N =
      ((pairedEtaLogTailCutoff (N + 1) + pairedEtaLogTailCutoff (N + 2)) / 2) *
          pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N +
        (pairedEtaHeadCompletedMomentPair rho N 1 0).re +
          (pairedEtaHeadCompletedMomentPair rho N 0 1).re := by
  rw [pairedEtaLeadingCurrentMidpointMoment, if_pos hm]
  simp_rw [pairedEtaHeadKernel_eq_completedMomentPair, hm, Nat.sub_self]
  have he (p : ℝ × ℝ) :
      2 * (pairedEtaHeadCompletedMomentPairKernel rho N 0 0 p).re *
          ((p.1 + pairedEtaLogTailCutoff (N + 1) + p.2) / 2) =
        2 * (pairedEtaHeadCompletedMomentPairKernel rho N 0 0 p *
          ((p.1 + pairedEtaLogTailCutoff (N + 1) + p.2) / 2 : ℝ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_etaMomentPair_re (integrable_pairedEtaHeadCompletedMomentPairKernel_midpoint rho N 0 0),
    integral_pairedEtaHeadCompletedMomentPairKernel_midpoint, pairedEtaLeadingCurrent_eq_headCompletedMomentPair rho hm]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.div_ofNat_re]
  ring

end

end RiemannGaussian
