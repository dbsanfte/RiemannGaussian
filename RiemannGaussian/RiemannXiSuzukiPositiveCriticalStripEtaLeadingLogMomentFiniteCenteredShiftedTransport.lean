import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredShiftedInterference

/-!
# Arithmetic transport of the shifted centered eta residual

The shifted eta tail at cutoff `N` is not an unrelated measure at every
cutoff.  It is exactly the first translated support interval plus the tail at
`N+1`, translated by the arithmetic logarithmic increment

`Delta_N = log (2N+3) - log (2N+1)`.

Lean proves this measure recursion and identifies the head measure with
Lebesgue measure on `(0,w_N]`, where
`0 < w_N < Delta_N`; the strict gap is the translated omitted eta interval.
The recursion propagates to every shifted Laplace and Fourier--Laplace moment
through an exact finite binomial formula.

After inserting both complementary tilts, completion factors, conjugation,
and cutoff phases, the same formula becomes a triangular transport system for
the completed coupled moments.  Its top-order specialization gives an exact
discrete work law for consecutive completed residuals: the increment is the
new arithmetic head contribution plus lower-order transported coupled
moments.  This is eta-specific structure beyond generic positive-measure
facts.  Turning the triangular system into off-line coercivity remains open.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The logarithmic translation from cutoff `N` to cutoff `N+1`. -/
def pairedEtaLogTailShiftIncrement (N : ℕ) : ℝ :=
  pairedEtaLogTailCutoff (N + 1) - pairedEtaLogTailCutoff N

/-- The width of the first eta support interval after translating cutoff `N`
to the origin. -/
def pairedEtaShiftedLogHeadWidth (N : ℕ) : ℝ :=
  Real.log (((2 * N + 2 : ℕ) : ℝ)) - pairedEtaLogTailCutoff N

/-- The first support-interval measure at cutoff `N`, translated to begin at
the origin. -/
def pairedEtaShiftedLogHeadMeasure (N : ℕ) : Measure ℝ :=
  Measure.map (fun t : ℝ ↦ t - pairedEtaLogTailCutoff N)
    (volume.restrict (pairedEtaLogInterval N))

/-- The order-`k` complex Laplace moment of the translated first support
interval. -/
def pairedEtaShiftedLogHeadLaplaceMoment
    (k : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  ∫ u : ℝ, (u : ℂ) ^ k * Complex.exp (-s * u)
    ∂pairedEtaShiftedLogHeadMeasure N

/-- The first translated support interval's order-`k` moment with real decay
and Fourier frequency displayed separately. -/
def pairedEtaShiftedLogHeadFourierMoment
    (k : ℕ) (sigma gamma : ℝ) (N : ℕ) : ℂ :=
  ∫ u : ℝ,
    (u : ℂ) ^ k * (Real.exp (-sigma * u) : ℂ) *
      Complex.exp (-((gamma * u : ℝ) : ℂ) * I)
    ∂pairedEtaShiftedLogHeadMeasure N

/-- The unit Fourier phase accumulated across one cutoff translation. -/
def pairedEtaLogTailShiftOscillation (gamma : ℝ) (N : ℕ) : ℂ :=
  Complex.exp
    (-((gamma * pairedEtaLogTailShiftIncrement N : ℝ) : ℂ) * I)

/-- The order-`k` complementary completed coupling on the shifted tail at
cutoff `N`.  At the zero multiplicity it is the previously defined coupled
core. -/
def pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment
    (rho : NontrivialZetaZero) (k N : ℕ) : ℂ :=
  -pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient rho N *
      pairedEtaShiftedLogTailFourierMoment
        k (1 - rho.1.re) rho.1.im N +
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient rho N *
      pairedEtaShiftedLogTailFourierMoment
        k rho.1.re (-rho.1.im) N

/-- The order-`k` complementary completed contribution of the newly exposed
first shifted support interval. -/
def pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
    (rho : NontrivialZetaZero) (k N : ℕ) : ℂ :=
  -pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient rho N *
      pairedEtaShiftedLogHeadFourierMoment
        k (1 - rho.1.re) rho.1.im N +
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient rho N *
      pairedEtaShiftedLogHeadFourierMoment
        k rho.1.re (-rho.1.im) N

/-- The shifted coupled moment with its common arithmetic cutoff phase
restored. -/
def pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
    (rho : NontrivialZetaZero) (k N : ℕ) : ℂ :=
  pairedEtaLogTailCutoffOscillation rho.1.im N *
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment rho k N

/-- Every consecutive arithmetic cutoff translation has strictly positive
length. -/
theorem pairedEtaLogTailShiftIncrement_pos (N : ℕ) :
    0 < pairedEtaLogTailShiftIncrement N := by
  unfold pairedEtaLogTailShiftIncrement pairedEtaLogTailCutoff
  apply sub_pos.mpr
  apply Real.strictMonoOn_log
  · exact mem_Ioi.mpr (by positivity)
  · exact mem_Ioi.mpr (by positivity)
  · exact_mod_cast (show 2 * N + 1 < 2 * (N + 1) + 1 by omega)

/-- Every translated first support interval has strictly positive width. -/
theorem pairedEtaShiftedLogHeadWidth_pos (N : ℕ) :
    0 < pairedEtaShiftedLogHeadWidth N := by
  unfold pairedEtaShiftedLogHeadWidth pairedEtaLogTailCutoff
  apply sub_pos.mpr
  apply Real.strictMonoOn_log
  · exact mem_Ioi.mpr (by positivity)
  · exact mem_Ioi.mpr (by positivity)
  · exact_mod_cast (show 2 * N + 1 < 2 * N + 2 by omega)

/-- The first support interval is strictly shorter than the full cutoff
translation; the remaining positive length is the intervening eta gap. -/
theorem pairedEtaShiftedLogHeadWidth_lt_shiftIncrement (N : ℕ) :
    pairedEtaShiftedLogHeadWidth N < pairedEtaLogTailShiftIncrement N := by
  unfold pairedEtaShiftedLogHeadWidth pairedEtaLogTailShiftIncrement pairedEtaLogTailCutoff
  apply sub_lt_sub_right
  apply Real.strictMonoOn_log
  · exact mem_Ioi.mpr (by positivity)
  · exact mem_Ioi.mpr (by positivity)
  · exact_mod_cast (show 2 * N + 2 < 2 * (N + 1) + 1 by omega)

/-- The translated head measure is literally Lebesgue measure restricted to
the interval from zero to its arithmetic width. -/
theorem pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc (N : ℕ) :
    pairedEtaShiftedLogHeadMeasure N =
      volume.restrict (Ioc 0 (pairedEtaShiftedLogHeadWidth N)) := by
  let f : ℝ → ℝ := fun t ↦ t - pairedEtaLogTailCutoff N
  have hemb : MeasurableEmbedding f :=
    measurableEmbedding_sub_pairedEtaLogTailCutoff N
  have hpres : MeasurePreserving f volume volume := by
    refine ⟨hemb.measurable, ?_⟩
    simpa [f, sub_eq_add_neg] using
      (map_add_right_eq_self volume (-pairedEtaLogTailCutoff N))
  have hrestrict :=
    hpres.restrict_image_emb hemb (pairedEtaLogInterval N)
  have himage : f '' pairedEtaLogInterval N =
      Ioc 0 (pairedEtaShiftedLogHeadWidth N) := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases ht with ⟨htl, htu⟩
      constructor
      · exact sub_pos.mpr (by
          simpa [pairedEtaLogInterval, pairedEtaLogTailCutoff] using htl)
      · unfold pairedEtaShiftedLogHeadWidth
        have htu' : t ≤ Real.log (((2 * N + 2 : ℕ) : ℝ)) := by
          simpa [pairedEtaLogInterval] using htu
        linarith
    · rintro ⟨hu0, huw⟩
      refine ⟨u + pairedEtaLogTailCutoff N, ?_, by
        unfold f
        ring⟩
      constructor
      · have : pairedEtaLogTailCutoff N <
            u + pairedEtaLogTailCutoff N := by linarith
        simpa [pairedEtaLogInterval, pairedEtaLogTailCutoff] using this
      · unfold pairedEtaShiftedLogHeadWidth at huw
        have : u + pairedEtaLogTailCutoff N ≤
            Real.log (((2 * N + 2 : ℕ) : ℝ)) := by linarith
        simpa [pairedEtaLogInterval] using this
  unfold pairedEtaShiftedLogHeadMeasure
  rw [hrestrict.map_eq, himage]

/-- The eta support tail at `N` is its first interval disjointly followed by
the support tail at `N+1`. -/
theorem pairedEtaLogTailSupport_eq_interval_union_succ (N : ℕ) :
    pairedEtaLogTailSupport N =
      pairedEtaLogInterval N ∪ pairedEtaLogTailSupport (N + 1) := by
  ext t
  constructor
  · intro ht
    rw [pairedEtaLogTailSupport, mem_iUnion] at ht
    obtain ⟨n, hn⟩ := ht
    rcases n with _ | n
    · exact Or.inl (by simpa using hn)
    · right
      rw [pairedEtaLogTailSupport, mem_iUnion]
      refine ⟨n, ?_⟩
      have hidx : n.succ + N = n + (N + 1) := by omega
      rw [← hidx]
      exact hn
  · rintro (ht | ht)
    · rw [pairedEtaLogTailSupport, mem_iUnion]
      exact ⟨0, by simpa using ht⟩
    · rw [pairedEtaLogTailSupport, mem_iUnion] at ht ⊢
      obtain ⟨n, hn⟩ := ht
      refine ⟨n + 1, ?_⟩
      have hidx : (n + 1) + N = n + (N + 1) := by omega
      rw [hidx]
      exact hn

/-- The first eta interval at `N` is disjoint from the entire successor
support tail. -/
theorem disjoint_pairedEtaLogInterval_tailSupport_succ (N : ℕ) :
    Disjoint (pairedEtaLogInterval N)
      (pairedEtaLogTailSupport (N + 1)) := by
  rw [Set.disjoint_left]
  intro t htN htTail
  rw [pairedEtaLogTailSupport, mem_iUnion] at htTail
  obtain ⟨n, hn⟩ := htTail
  have hd := pairwise_disjoint_pairedEtaLogInterval
    (show N ≠ n + (N + 1) by omega)
  exact Set.disjoint_left.mp hd htN hn

/-- Before translation, the eta tail measure is exactly the first interval
measure plus the successor tail measure. -/
theorem pairedEtaLogTailMeasure_eq_head_add_succ (N : ℕ) :
    pairedEtaLogTailMeasure N =
      volume.restrict (pairedEtaLogInterval N) +
        pairedEtaLogTailMeasure (N + 1) := by
  unfold pairedEtaLogTailMeasure
  rw [pairedEtaLogTailSupport_eq_interval_union_succ,
    Measure.restrict_union (disjoint_pairedEtaLogInterval_tailSupport_succ N)
      (measurableSet_pairedEtaLogTailSupport (N + 1))]

/-- After recentering, the eta tail measure is its explicit head interval plus
the successor shifted tail translated by the arithmetic cutoff increment. -/
theorem pairedEtaShiftedLogTailMeasure_eq_head_add_translate_succ (N : ℕ) :
    pairedEtaShiftedLogTailMeasure N =
      pairedEtaShiftedLogHeadMeasure N +
        Measure.map (fun u : ℝ ↦ u + pairedEtaLogTailShiftIncrement N)
          (pairedEtaShiftedLogTailMeasure (N + 1)) := by
  have hfN : Measurable (fun t : ℝ ↦ t - pairedEtaLogTailCutoff N) :=
    measurable_id.sub measurable_const
  have hfS : Measurable
      (fun t : ℝ ↦ t - pairedEtaLogTailCutoff (N + 1)) :=
    measurable_id.sub measurable_const
  have hg : Measurable (fun u : ℝ ↦ u + pairedEtaLogTailShiftIncrement N) :=
    measurable_id.add measurable_const
  unfold pairedEtaShiftedLogTailMeasure pairedEtaShiftedLogHeadMeasure
  rw [pairedEtaLogTailMeasure_eq_head_add_succ, Measure.map_add _ _ hfN]
  congr 1
  rw [Measure.map_map hg hfS]
  apply Measure.map_congr
  filter_upwards with t
  unfold pairedEtaLogTailShiftIncrement
  simp only [Function.comp_apply]
  ring_nf

/-- Every head-interval Laplace moment is absolutely integrable when the real
tilt is positive. -/
theorem integrable_pairedEtaShiftedLogHeadLaplaceMoment_integrand
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    Integrable (fun u : ℝ ↦
      (u : ℂ) ^ k * Complex.exp (-s * u))
      (pairedEtaShiftedLogHeadMeasure N) := by
  have hfull :=
    integrable_pairedEtaShiftedLogTailLaplaceMoment_integrand k hs N
  rw [pairedEtaShiftedLogTailMeasure_eq_head_add_translate_succ] at hfull
  exact hfull.left_of_add_measure

/-- The shifted order-`k` Laplace moment obeys the exact cutoff transport law:
one head moment plus a translated finite binomial combination of successor
moments. -/
theorem pairedEtaShiftedLogTailLaplaceMoment_transport
    (k : ℕ) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    pairedEtaShiftedLogTailLaplaceMoment k s N =
      pairedEtaShiftedLogHeadLaplaceMoment k s N +
        Complex.exp (-s * (pairedEtaLogTailShiftIncrement N : ℂ)) *
          ∑ j ∈ Finset.range (k + 1),
            ((k.choose j : ℕ) : ℂ) *
              (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
              pairedEtaShiftedLogTailLaplaceMoment j s (N + 1) := by
  let f : ℝ → ℂ := fun u ↦
    (u : ℂ) ^ k * Complex.exp (-s * u)
  have hfull : Integrable f (pairedEtaShiftedLogTailMeasure N) :=
    integrable_pairedEtaShiftedLogTailLaplaceMoment_integrand k hs N
  rw [pairedEtaShiftedLogTailMeasure_eq_head_add_translate_succ] at hfull
  have hhead : Integrable f (pairedEtaShiftedLogHeadMeasure N) :=
    hfull.left_of_add_measure
  have htranslated : Integrable f
      (Measure.map (fun u : ℝ ↦ u + pairedEtaLogTailShiftIncrement N)
        (pairedEtaShiftedLogTailMeasure (N + 1))) :=
    hfull.right_of_add_measure
  have hg : Measurable (fun u : ℝ ↦ u + pairedEtaLogTailShiftIncrement N) :=
    measurable_id.add measurable_const
  have hgEmb : MeasurableEmbedding
      (fun u : ℝ ↦ u + pairedEtaLogTailShiftIncrement N) := by
    let e : ℝ ≃ₜ ℝ := Homeomorph.addRight (pairedEtaLogTailShiftIncrement N)
    simpa [e] using e.isClosedEmbedding.measurableEmbedding
  unfold pairedEtaShiftedLogTailLaplaceMoment
  rw [pairedEtaShiftedLogTailMeasure_eq_head_add_translate_succ,
    integral_add_measure hhead htranslated]
  change (∫ u : ℝ, f u ∂pairedEtaShiftedLogHeadMeasure N) +
      (∫ u : ℝ, f u
        ∂Measure.map (fun u : ℝ ↦ u + pairedEtaLogTailShiftIncrement N)
          (pairedEtaShiftedLogTailMeasure (N + 1))) = _
  rw [hgEmb.integral_map]
  dsimp only [f]
  rw [show (∫ u : ℝ, (u : ℂ) ^ k * Complex.exp (-s * u)
        ∂pairedEtaShiftedLogHeadMeasure N) =
      pairedEtaShiftedLogHeadLaplaceMoment k s N by rfl]
  congr 1
  calc
    (∫ u : ℝ,
        (((u + pairedEtaLogTailShiftIncrement N : ℝ) : ℂ) ^ k) *
          Complex.exp
            (-s * ((u + pairedEtaLogTailShiftIncrement N : ℝ) : ℂ))
        ∂pairedEtaShiftedLogTailMeasure (N + 1)) =
        ∫ u : ℝ,
          Complex.exp (-s * (pairedEtaLogTailShiftIncrement N : ℂ)) *
            ∑ j ∈ Finset.range (k + 1),
              ((k.choose j : ℕ) : ℂ) *
                (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
                ((u : ℂ) ^ j * Complex.exp (-s * u))
          ∂pairedEtaShiftedLogTailMeasure (N + 1) := by
      apply integral_congr_ae
      filter_upwards with u
      have hexp : Complex.exp (-s * ((u + pairedEtaLogTailShiftIncrement N : ℝ) : ℂ)) =
          Complex.exp (-s * (pairedEtaLogTailShiftIncrement N : ℂ)) *
            Complex.exp (-s * (u : ℂ)) := by
        rw [show -s * ((u + pairedEtaLogTailShiftIncrement N : ℝ) : ℂ) =
            -s * (pairedEtaLogTailShiftIncrement N : ℂ) + -s * (u : ℂ) by
          push_cast
          ring,
          Complex.exp_add]
      rw [hexp]
      rw [show ((u + pairedEtaLogTailShiftIncrement N : ℝ) : ℂ) =
          (u : ℂ) + (pairedEtaLogTailShiftIncrement N : ℂ) by norm_cast,
        add_pow]
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = Complex.exp (-s * (pairedEtaLogTailShiftIncrement N : ℂ)) *
        ∫ u : ℝ,
          ∑ j ∈ Finset.range (k + 1),
            ((k.choose j : ℕ) : ℂ) *
              (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
              ((u : ℂ) ^ j * Complex.exp (-s * u))
          ∂pairedEtaShiftedLogTailMeasure (N + 1) := by
      rw [integral_const_mul]
    _ = Complex.exp (-s * (pairedEtaLogTailShiftIncrement N : ℂ)) *
        ∑ j ∈ Finset.range (k + 1),
          ((k.choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
            (∫ u : ℝ, (u : ℂ) ^ j * Complex.exp (-s * u)
              ∂pairedEtaShiftedLogTailMeasure (N + 1)) := by
      congr 1
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul]
      · intro j hj
        exact
          (integrable_pairedEtaShiftedLogTailLaplaceMoment_integrand
            j hs (N + 1)).const_mul
              (((k.choose j : ℕ) : ℂ) *
                (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j))
    _ = _ := rfl

/-- Separating real and imaginary coordinates identifies the head Laplace
moment with its Fourier--Laplace presentation. -/
theorem pairedEtaShiftedLogHeadLaplaceMoment_eq_fourierMoment
    (k : ℕ) (s : ℂ) (N : ℕ) :
    pairedEtaShiftedLogHeadLaplaceMoment k s N =
      pairedEtaShiftedLogHeadFourierMoment k s.re s.im N := by
  unfold pairedEtaShiftedLogHeadLaplaceMoment pairedEtaShiftedLogHeadFourierMoment
  apply integral_congr_ae
  filter_upwards with u
  rw [complex_exp_neg_mul_real_eq_decay_mul_oscillation]
  ring

/-- The exact shifted moment transport law with real decay and the unit
translation phase displayed separately. -/
theorem pairedEtaShiftedLogTailFourierMoment_transport
    (k : ℕ) {sigma : ℝ} (hsigma : 0 < sigma)
    (gamma : ℝ) (N : ℕ) :
    pairedEtaShiftedLogTailFourierMoment k sigma gamma N =
      pairedEtaShiftedLogHeadFourierMoment k sigma gamma N +
        (Real.exp (-sigma * pairedEtaLogTailShiftIncrement N) : ℂ) *
          pairedEtaLogTailShiftOscillation gamma N *
          ∑ j ∈ Finset.range (k + 1),
            ((k.choose j : ℕ) : ℂ) *
              (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
              pairedEtaShiftedLogTailFourierMoment
                j sigma gamma (N + 1) := by
  let s : ℂ := (sigma : ℂ) + (gamma : ℂ) * I
  have hs : 0 < s.re := by simpa [s] using hsigma
  have h := pairedEtaShiftedLogTailLaplaceMoment_transport k hs N
  rw [pairedEtaShiftedLogTailLaplaceMoment_eq_fourierMoment,
    pairedEtaShiftedLogHeadLaplaceMoment_eq_fourierMoment] at h
  simp_rw [pairedEtaShiftedLogTailLaplaceMoment_eq_fourierMoment] at h
  rw [complex_exp_neg_mul_real_eq_decay_mul_oscillation] at h
  simpa only [s, add_re, ofReal_re, mul_re, mul_im, I_re, I_im,
    ofReal_im, mul_zero, mul_one, sub_self, add_zero, zero_add, add_im,
    pairedEtaLogTailShiftOscillation] using h

/-- The partner coefficient absorbs its successor real decay, leaving exactly
the common one-step Fourier phase and the coefficient at `N+1`. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient_transport
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient rho N *
        (Real.exp (-(1 - rho.1.re) * pairedEtaLogTailShiftIncrement N) : ℂ) *
        pairedEtaLogTailShiftOscillation rho.1.im N =
      pairedEtaLogTailShiftOscillation rho.1.im N *
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
          rho (N + 1) := by
  have hreal :
      Real.exp (-(1 - rho.1.re) * pairedEtaLogTailCutoff N) *
          Real.exp (-(1 - rho.1.re) * pairedEtaLogTailShiftIncrement N) =
        Real.exp (-(1 - rho.1.re) * pairedEtaLogTailCutoff (N + 1)) := by
    rw [← Real.exp_add]
    congr 1
    unfold pairedEtaLogTailShiftIncrement
    ring
  have hrealC :
      (Real.exp (-(1 - rho.1.re) * pairedEtaLogTailCutoff N) : ℂ) *
          (Real.exp (-(1 - rho.1.re) * pairedEtaLogTailShiftIncrement N) : ℂ) =
        (Real.exp
          (-(1 - rho.1.re) * pairedEtaLogTailCutoff (N + 1)) : ℂ) := by
    exact_mod_cast hreal
  unfold pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
  calc
    _ = (pairedEtaXiCompletionFactor
            (NontrivialZetaZero.conjugatePartner rho).1 *
          (NontrivialZetaZero.conjugatePartner rho).1) *
        ((Real.exp
            (-(1 - rho.1.re) * pairedEtaLogTailCutoff N) : ℂ) *
          (Real.exp
            (-(1 - rho.1.re) * pairedEtaLogTailShiftIncrement N) : ℂ)) *
        pairedEtaLogTailShiftOscillation rho.1.im N := by ring
    _ = _ := by rw [hrealC]; ring

/-- The conjugated coefficient and reversed-frequency successor phase combine
to the same common one-step phase times the coefficient at `N+1`. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient_transport
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient rho N *
        (Real.exp (-rho.1.re * pairedEtaLogTailShiftIncrement N) : ℂ) *
        pairedEtaLogTailShiftOscillation (-rho.1.im) N =
      pairedEtaLogTailShiftOscillation rho.1.im N *
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
          rho (N + 1) := by
  have hreal :
      Real.exp (-rho.1.re * pairedEtaLogTailCutoff N) *
          Real.exp (-rho.1.re * pairedEtaLogTailShiftIncrement N) =
        Real.exp (-rho.1.re * pairedEtaLogTailCutoff (N + 1)) := by
    rw [← Real.exp_add]
    congr 1
    unfold pairedEtaLogTailShiftIncrement
    ring
  have hrealC :
      (Real.exp (-rho.1.re * pairedEtaLogTailCutoff N) : ℂ) *
          (Real.exp (-rho.1.re * pairedEtaLogTailShiftIncrement N) : ℂ) =
        (Real.exp (-rho.1.re * pairedEtaLogTailCutoff (N + 1)) : ℂ) := by
    exact_mod_cast hreal
  have hphase :
      pairedEtaLogTailCutoffRelativeOscillation rho.1.im N *
          pairedEtaLogTailShiftOscillation (-rho.1.im) N =
        pairedEtaLogTailShiftOscillation rho.1.im N *
          pairedEtaLogTailCutoffRelativeOscillation rho.1.im (N + 1) := by
    unfold pairedEtaLogTailCutoffRelativeOscillation pairedEtaLogTailShiftOscillation
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold pairedEtaLogTailShiftIncrement
    push_cast
    ring
  unfold pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
  calc
    _ = ((-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
          starRingEnd ℂ (pairedEtaXiCompletionFactor rho.1 * rho.1)) *
        ((Real.exp (-rho.1.re * pairedEtaLogTailCutoff N) : ℂ) *
          (Real.exp (-rho.1.re * pairedEtaLogTailShiftIncrement N) : ℂ)) *
        (pairedEtaLogTailCutoffRelativeOscillation rho.1.im N *
          pairedEtaLogTailShiftOscillation (-rho.1.im) N) := by ring
    _ = _ := by rw [hrealC, hphase]; ring

/-- Complementary shifted coupled moments form an exact triangular transport
system: the order-`k` moment at `N` is the new head contribution plus a
binomial combination of every successor order through `k`, all carrying one
common phase. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment_transport
    (rho : NontrivialZetaZero) (k N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment rho k N =
      pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment rho k N +
        pairedEtaLogTailShiftOscillation rho.1.im N *
          ∑ j ∈ Finset.range (k + 1),
            ((k.choose j : ℕ) : ℂ) *
              (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
              pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment rho j (N + 1) := by
  have hpartner := pairedEtaShiftedLogTailFourierMoment_transport k
    (sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)) rho.1.im N
  have hrho := pairedEtaShiftedLogTailFourierMoment_transport k
    (NontrivialZetaZero.zero_lt_re rho) (-rho.1.im) N
  unfold pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment
  rw [hpartner, hrho]
  unfold pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment
  have hA := pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient_transport rho N
  have hB := pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient_transport rho N
  let A :=
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient rho N
  let B :=
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient rho N
  let AS :=
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPartnerCoefficient
      rho (N + 1)
  let BS :=
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedConjugateCoefficient
      rho (N + 1)
  let O := pairedEtaLogTailShiftOscillation rho.1.im N
  let c : ℕ → ℂ := fun j ↦
    ((k.choose j : ℕ) : ℂ) *
      (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j)
  let MP : ℕ → ℂ := fun j ↦
    pairedEtaShiftedLogTailFourierMoment
      j (1 - rho.1.re) rho.1.im (N + 1)
  let MR : ℕ → ℂ := fun j ↦
    pairedEtaShiftedLogTailFourierMoment
      j rho.1.re (-rho.1.im) (N + 1)
  have hA' : A *
        (Real.exp (-(1 - rho.1.re) * pairedEtaLogTailShiftIncrement N) : ℂ) * O =
      O * AS := by simpa [A, O, AS] using hA
  have hB' : B *
        (Real.exp (-rho.1.re * pairedEtaLogTailShiftIncrement N) : ℂ) *
        pairedEtaLogTailShiftOscillation (-rho.1.im) N =
      O * BS := by simpa [B, O, BS] using hB
  have hsum :
      -AS * (∑ j ∈ Finset.range (k + 1), c j * MP j) +
          BS * (∑ j ∈ Finset.range (k + 1), c j * MR j) =
        ∑ j ∈ Finset.range (k + 1),
          c j * (-AS * MP j + BS * MR j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change -A *
        (pairedEtaShiftedLogHeadFourierMoment k (1 - rho.1.re) rho.1.im N +
          (Real.exp (-(1 - rho.1.re) * pairedEtaLogTailShiftIncrement N) : ℂ) * O *
            ∑ j ∈ Finset.range (k + 1), c j * MP j) +
      B *
        (pairedEtaShiftedLogHeadFourierMoment k rho.1.re (-rho.1.im) N +
          (Real.exp (-rho.1.re * pairedEtaLogTailShiftIncrement N) : ℂ) *
            pairedEtaLogTailShiftOscillation (-rho.1.im) N *
            ∑ j ∈ Finset.range (k + 1), c j * MR j) =
      (-A * pairedEtaShiftedLogHeadFourierMoment
          k (1 - rho.1.re) rho.1.im N +
        B * pairedEtaShiftedLogHeadFourierMoment
          k rho.1.re (-rho.1.im) N) +
      O * ∑ j ∈ Finset.range (k + 1),
        c j * (-AS * MP j + BS * MR j)
  calc
    _ = (-A * pairedEtaShiftedLogHeadFourierMoment
            k (1 - rho.1.re) rho.1.im N +
          B * pairedEtaShiftedLogHeadFourierMoment
            k rho.1.re (-rho.1.im) N) +
        (-(A *
            (Real.exp (-(1 - rho.1.re) * pairedEtaLogTailShiftIncrement N) : ℂ) * O) *
            (∑ j ∈ Finset.range (k + 1), c j * MP j) +
          (B * (Real.exp (-rho.1.re * pairedEtaLogTailShiftIncrement N) : ℂ) *
            pairedEtaLogTailShiftOscillation (-rho.1.im) N) *
            (∑ j ∈ Finset.range (k + 1), c j * MR j)) := by ring
    _ = (-A * pairedEtaShiftedLogHeadFourierMoment
            k (1 - rho.1.re) rho.1.im N +
          B * pairedEtaShiftedLogHeadFourierMoment
            k rho.1.re (-rho.1.im) N) +
        (-(O * AS) *
            (∑ j ∈ Finset.range (k + 1), c j * MP j) +
          (O * BS) *
            (∑ j ∈ Finset.range (k + 1), c j * MR j)) := by
      rw [hA', hB']
    _ = (-A * pairedEtaShiftedLogHeadFourierMoment
            k (1 - rho.1.re) rho.1.im N +
          B * pairedEtaShiftedLogHeadFourierMoment
            k rho.1.re (-rho.1.im) N) +
        O * (-AS * (∑ j ∈ Finset.range (k + 1), c j * MP j) +
          BS * (∑ j ∈ Finset.range (k + 1), c j * MR j)) := by ring
    _ = _ := by rw [hsum]

/-- The cutoff phase at `N` times the one-step phase is exactly the cutoff
phase at `N+1`. -/
theorem pairedEtaLogTailCutoffOscillation_mul_shiftOscillation
    (gamma : ℝ) (N : ℕ) :
    pairedEtaLogTailCutoffOscillation gamma N *
        pairedEtaLogTailShiftOscillation gamma N =
      pairedEtaLogTailCutoffOscillation gamma (N + 1) := by
  unfold pairedEtaLogTailCutoffOscillation pairedEtaLogTailShiftOscillation
  rw [← Complex.exp_add]
  congr 1
  unfold pairedEtaLogTailShiftIncrement
  push_cast
  ring

/-- Restoring the cutoff phase removes the common step oscillation from the
triangular transport law. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_transport
    (rho : NontrivialZetaZero) (k N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment rho k N =
      pairedEtaLogTailCutoffOscillation rho.1.im N *
          pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment rho k N +
        ∑ j ∈ Finset.range (k + 1),
          ((k.choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
            pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment rho j (N + 1) := by
  unfold pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
  rw [pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment_transport]
  let P := pairedEtaLogTailCutoffOscillation rho.1.im N
  let PS := pairedEtaLogTailCutoffOscillation rho.1.im (N + 1)
  let O := pairedEtaLogTailShiftOscillation rho.1.im N
  let c : ℕ → ℂ := fun j ↦
    ((k.choose j : ℕ) : ℂ) *
      (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j)
  let C : ℕ → ℂ := fun j ↦ pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment rho j (N + 1)
  have hphase : P * O = PS := by
    simpa [P, O, PS] using
      pairedEtaLogTailCutoffOscillation_mul_shiftOscillation rho.1.im N
  change P *
      (pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment rho k N +
        O * ∑ j ∈ Finset.range (k + 1), c j * C j) =
    P * pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment rho k N +
      ∑ j ∈ Finset.range (k + 1), c j * (PS * C j)
  calc
    _ = P * pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment rho k N +
        (P * O) * ∑ j ∈ Finset.range (k + 1), c j * C j := by ring
    _ = P * pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment rho k N +
        PS * ∑ j ∈ Finset.range (k + 1), c j * C j := by rw [hphase]
    _ = _ := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Isolating the top successor order gives a discrete work law: the
phase-weighted order-`k` increment is the head term plus only strictly lower
successor moments. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_sub_succ
    (rho : NontrivialZetaZero) (k N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment rho k N -
        pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment rho k (N + 1) =
      pairedEtaLogTailCutoffOscillation rho.1.im N *
          pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment rho k N +
        ∑ j ∈ Finset.range k,
          ((k.choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^ (k - j) *
            pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment rho j (N + 1) := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_transport,
    Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
    pow_zero]
  ring

/-- The previously constructed shifted coupled core is precisely the coupled
moment at the analytic zero multiplicity. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore_eq_coupledMoment
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment rho (analyticZetaZeroMultiplicity rho) N := by
  simpa only [pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledMoment] using
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore_eq_coefficients_mul_moments
      rho N

/-- The actual completed centered partner residual is the phase-weighted
coupled moment at the analytic zero multiplicity. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_phaseWeightedCoupledMoment
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment
        rho (analyticZetaZeroMultiplicity rho) N := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_oscillation_mul_shiftedCoupledCore,
    pairedEtaCompletedLeadingLogCutoffCenteredShiftedCoupledCore_eq_coupledMoment]
  rfl

/-- Consecutive actual completed residuals satisfy the exact eta-specific
triangular work law: their difference is the newly exposed arithmetic head
plus the transported hierarchy of orders below the zero multiplicity. -/
theorem pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_sub_succ
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho N -
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual rho (N + 1) =
      pairedEtaLogTailCutoffOscillation rho.1.im N *
          pairedEtaCompletedLeadingLogCutoffCenteredShiftedHeadCoupledMoment rho (analyticZetaZeroMultiplicity rho) N +
        ∑ j ∈ Finset.range (analyticZetaZeroMultiplicity rho),
          ((((analyticZetaZeroMultiplicity rho).choose j : ℕ) : ℂ) *
            (pairedEtaLogTailShiftIncrement N : ℂ) ^
              (analyticZetaZeroMultiplicity rho - j)) *
            pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment rho j (N + 1) := by
  rw [pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_phaseWeightedCoupledMoment,
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidual_eq_phaseWeightedCoupledMoment]
  exact pairedEtaCompletedLeadingLogCutoffCenteredShiftedPhaseWeightedCoupledMoment_sub_succ
    rho (analyticZetaZeroMultiplicity rho) N

end

end RiemannGaussian
