import RiemannGaussian.EtaCurrentWeightedReconstruction

/-!
# Exact tilted heat composition with the intermediate phase retained

Two equal-width transitions compose to a broader Gaussian with a shifted
intermediate center. The full-line integral contains the exact factor
`exp(a²h²-a(t+u))`. This full-line statement precedes the actual eta support,
gap, and nonpositive-time decomposition; none of these corrections is zero
by a free Gaussian semigroup argument.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The two actual equal-width heat envelopes before restricting the
intermediate time to an eta support or gap. -/
def pairedEtaFullTwoHeatEnvelope (a h t u w : ℝ) : ℝ :=
  Real.exp (-a * (t + w) / 2) * etaNormalizedHeatKernel (Real.sqrt 2 * h) (w - t) *
    Real.exp (-a * (w + u) / 2) * etaNormalizedHeatKernel (Real.sqrt 2 * h) (u - w)

/-- The two full-time transitions retain both ordered probe phases. -/
def pairedEtaFullTwoHeatKernel (a h : ℝ) (phi psi : ℝ → ℝ) (t u w : ℝ) : ℂ :=
  (pairedEtaFullTwoHeatEnvelope a h t u w : ℂ) *
    pairedEtaHeatPhaseUnit phi (w, t) * pairedEtaHeatPhaseUnit psi (u, w)

/-- Two equal transition Gaussians factor at their arithmetic midpoint,
with both normalized Gaussian factors retained. -/
theorem etaNormalizedHeatKernel_two_transition_product {h : ℝ} (hh : 0 < h) (t u w : ℝ) :
    etaNormalizedHeatKernel (Real.sqrt 2 * h) (w - t) *
      etaNormalizedHeatKernel (Real.sqrt 2 * h) (u - w) =
        etaNormalizedHeatKernel (2 * h) (u - t) *
          etaNormalizedHeatKernel h (w - (t + u) / 2) := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have he : -(1 / 4) * ((w - t) / (Real.sqrt 2 * h)) ^ 2 +
      -(1 / 4) * ((u - w) / (Real.sqrt 2 * h)) ^ 2 =
      -(1 / 4) * ((u - t) / (2 * h)) ^ 2 + -(1 / 4) * ((w - (t + u) / 2) / h) ^ 2 := by
    field_simp
    nlinarith [hs]
  unfold etaNormalizedHeatKernel
  rw [div_mul_div_comm, div_mul_div_comm, ← Real.exp_add, ← Real.exp_add, he]
  congr 1
  nlinarith [hs]

/-- Midpoint factorization of the entire tilted two-transition envelope. -/
theorem pairedEtaFullTwoHeatEnvelope_eq_midpoint {h : ℝ} (hh : 0 < h) (a t u w : ℝ) :
    pairedEtaFullTwoHeatEnvelope a h t u w =
      etaNormalizedHeatKernel (2 * h) (u - t) * etaTiltedHeatEnvelope a h ((t + u) / 2, w) := by
  have he : Real.exp (-a * (t + w) / 2) * Real.exp (-a * (w + u) / 2) =
      Real.exp (-a * ((t + u) / 2 + w)) := by rw [← Real.exp_add]; congr 1; ring
  unfold pairedEtaFullTwoHeatEnvelope etaTiltedHeatEnvelope
  calc
    _ = (Real.exp (-a * (t + w) / 2) * Real.exp (-a * (w + u) / 2)) *
        (etaNormalizedHeatKernel (Real.sqrt 2 * h) (w - t) *
          etaNormalizedHeatKernel (Real.sqrt 2 * h) (u - w)) := by ring
    _ = _ := by rw [he, etaNormalizedHeatKernel_two_transition_product hh]; ring

/-- Completing the square retains the full-line amplification and the
shift of the intermediate Gaussian center. -/
theorem pairedEtaFullTwoHeatEnvelope_complete_square {h : ℝ} (hh : 0 < h) (a t u w : ℝ) :
    pairedEtaFullTwoHeatEnvelope a h t u w =
      (Real.exp (a ^ 2 * h ^ 2 - a * (t + u)) * etaNormalizedHeatKernel (2 * h) (u - t)) *
        etaNormalizedHeatKernel h (w - ((t + u) / 2 - 2 * a * h ^ 2)) := by
  rw [pairedEtaFullTwoHeatEnvelope_eq_midpoint hh, etaTiltedHeatEnvelope_complete_square hh]
  rw [show a ^ 2 * h ^ 2 - 2 * a * ((t + u) / 2) = a ^ 2 * h ^ 2 - a * (t + u) by ring]
  ring

/-- The real two-transition envelope is positive everywhere. -/
theorem pairedEtaFullTwoHeatEnvelope_pos {h : ℝ} (hh : 0 < h) (a t u w : ℝ) :
    0 < pairedEtaFullTwoHeatEnvelope a h t u w := by
  rw [pairedEtaFullTwoHeatEnvelope_eq_midpoint hh]
  exact mul_pos (etaNormalizedHeatKernel_pos (by positivity) _) (etaTiltedHeatEnvelope_pos hh a _)

/-- Every full-line intermediate-time envelope slice is genuinely integrable. -/
theorem integrable_pairedEtaFullTwoHeatEnvelope {h : ℝ} (hh : 0 < h) (a t u : ℝ) :
    Integrable (pairedEtaFullTwoHeatEnvelope a h t u) := by
  have heq := funext (pairedEtaFullTwoHeatEnvelope_eq_midpoint hh a t u)
  rw [heq]
  exact (integrable_etaTiltedHeatEnvelope_slice hh a ((t + u) / 2)).const_mul _

/-- Exact full-line composition: the tilt contributes its exponential
factor, rather than an unmodified heat semigroup. -/
theorem integral_pairedEtaFullTwoHeatEnvelope {h : ℝ} (hh : 0 < h) (a t u : ℝ) :
    (∫ w, pairedEtaFullTwoHeatEnvelope a h t u w) =
      Real.exp (a ^ 2 * h ^ 2 - a * (t + u)) * etaNormalizedHeatKernel (2 * h) (u - t) := by
  simp_rw [pairedEtaFullTwoHeatEnvelope_complete_square hh]
  rw [integral_const_mul, integral_sub_right_eq_self, integral_etaNormalizedHeatKernel hh, mul_one]

/-- The ordered complex phase kernel is jointly measurable. -/
theorem measurable_pairedEtaFullTwoHeatKernel {phi psi : ℝ → ℝ}
    (hphi : Measurable phi) (hpsi : Measurable psi) (a h : ℝ) :
    Measurable (fun z : (ℝ × ℝ) × ℝ ↦ pairedEtaFullTwoHeatKernel a h phi psi z.1.1 z.1.2 z.2) := by
  have he : Measurable (fun z : (ℝ × ℝ) × ℝ ↦ pairedEtaFullTwoHeatEnvelope a h z.1.1 z.1.2 z.2) := by
    unfold pairedEtaFullTwoHeatEnvelope etaNormalizedHeatKernel
    fun_prop
  have hp := (measurable_pairedEtaHeatPhaseUnit hphi).comp
    (measurable_snd.prodMk (measurable_fst.comp measurable_fst) :
      Measurable (fun z : (ℝ × ℝ) × ℝ ↦ (z.2, z.1.1)))
  have hq := (measurable_pairedEtaHeatPhaseUnit hpsi).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd :
      Measurable (fun z : (ℝ × ℝ) × ℝ ↦ (z.1.2, z.2)))
  exact (he.complex_ofReal.mul hp).mul hq

/-- Taking the norm removes only the two unit phases, leaving the exact
positive two-transition envelope. -/
theorem norm_pairedEtaFullTwoHeatKernel {h : ℝ} (hh : 0 < h) (a : ℝ)
    (phi psi : ℝ → ℝ) (t u w : ℝ) :
    ‖pairedEtaFullTwoHeatKernel a h phi psi t u w‖ = pairedEtaFullTwoHeatEnvelope a h t u w := by
  simp only [pairedEtaFullTwoHeatKernel, norm_mul, norm_pairedEtaHeatPhaseUnit, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pairedEtaFullTwoHeatEnvelope_pos hh a t u w)]

/-- Arbitrary measurable ordered phases preserve full-line slice integrability. -/
theorem integrable_pairedEtaFullTwoHeatKernel {h : ℝ} (hh : 0 < h) (a t u : ℝ)
    {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (pairedEtaFullTwoHeatKernel a h phi psi t u) := by
  apply (integrable_pairedEtaFullTwoHeatEnvelope hh a t u).mono'
  · have hm : Measurable (fun w : ℝ ↦ ((t, u), w)) := measurable_const.prodMk measurable_id
    exact ((measurable_pairedEtaFullTwoHeatKernel hphi hpsi a h).comp hm).aestronglyMeasurable
  · exact Eventually.of_forall fun w ↦ (norm_pairedEtaFullTwoHeatKernel hh a phi psi t u w).le

/-- With one common probe phase, the intermediate phase cancels exactly. -/
theorem pairedEtaFullTwoHeatKernel_same_phase (a h : ℝ) (phi : ℝ → ℝ) (t u w : ℝ) :
    pairedEtaFullTwoHeatKernel a h phi phi t u w =
      (pairedEtaFullTwoHeatEnvelope a h t u w : ℂ) * pairedEtaHeatPhaseUnit phi (u, t) := by
  unfold pairedEtaFullTwoHeatKernel pairedEtaHeatPhaseUnit
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The full-line composition retains the common endpoint phase and its
exact tilted Gaussian amplitude. -/
theorem integral_pairedEtaFullTwoHeatKernel_same_phase {h : ℝ} (hh : 0 < h)
    (a : ℝ) (phi : ℝ → ℝ) (t u : ℝ) :
    (∫ w, pairedEtaFullTwoHeatKernel a h phi phi t u w) =
      (Real.exp (a ^ 2 * h ^ 2 - a * (t + u)) * etaNormalizedHeatKernel (2 * h) (u - t) : ℝ) *
        pairedEtaHeatPhaseUnit phi (u, t) := by
  simp_rw [pairedEtaFullTwoHeatKernel_same_phase]
  rw [integral_mul_const, integral_complex_ofReal, integral_pairedEtaFullTwoHeatEnvelope hh]

/-- On the actual gap, the unrestricted phase kernel equals the existing
ordered return core at equal tilts and widths. -/
theorem pairedEtaOrderedGapReturnKernelCore_eq_fullTwoHeat_of_mem_gap (a h : ℝ)
    (phi psi : ℝ → ℝ) (t u : ℝ) {w : ℝ} (hw : w ∈ pairedEtaLogGapSupport) :
    pairedEtaOrderedGapReturnKernelCore a h a h phi psi t u w =
      pairedEtaFullTwoHeatKernel a h phi psi t u w := by
  have hc : pairedEtaLogIndicator w = 0 := Set.indicator_of_notMem hw.2 _
  simp only [pairedEtaOrderedGapReturnKernelCore, hc, sub_zero, mul_one,
    pairedEtaFullTwoHeatKernel, pairedEtaFullTwoHeatEnvelope]

/-- On the proved reconstruction schedule, the full-line Gaussian
amplification is exactly exponential in the fourth power of the cutoff.
This is an envelope factor, not a lower bound for any signed current. -/
theorem pairedEtaCurrentReconstructionSchedule_fullLine_amplification (N : ℕ) :
    Real.exp (pairedEtaCurrentReconstructionTilt N ^ 2 * pairedEtaCurrentReconstructionWidth N ^ 2) =
      Real.exp ((N + 1 : ℝ) ^ 4) := by
  congr 1
  unfold pairedEtaCurrentReconstructionTilt pairedEtaCurrentReconstructionWidth
  field_simp

end

end RiemannGaussian
