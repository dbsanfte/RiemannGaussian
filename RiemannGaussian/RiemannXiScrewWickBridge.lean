import RiemannGaussian.RiemannXiBoundarySpatialHeat
import RiemannGaussian.GaussianDigammaTransform

/-!
# A screw-time / Wick-time bridge for the complete spectral-xi divisor

This file connects the positive boundary heat trace to a reflected-pair
exponential mode in complex screw time.  For a spectral point `alpha`, the
kernel

`-i (alpha - conj alpha) exp (-i (alpha - conj alpha) t)`

is `2 h exp (2 h t)` on real time, where `h = im alpha`.  On imaginary time
`t = i s`, its normalized Gaussian average is instead
`2 h exp (-tau h^2)`.  Thus the same entire mode realizes both exponential
screw growth and the Gaussian height damping already obtained from spatially
integrating the boundary heat kernel.

The construction is then lifted without finiteness assumptions to genuine
finite zeta-zero windows and to an extended nonnegative real-time mass.  The
finite Wick-rotated windows converge to the normalized boundary spatial heat,
even when the complete mass is infinite.  Finally, RH is proved equivalent to
subexponential growth of the positive real-time reflected-pair mass.  This
last equivalence is a spectral criterion, not yet an arithmetic estimate: the
remaining frontier is to derive its growth hypothesis from an arithmetic
screw function or an explicit-formula rigidity theorem.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- The entire exponential mode associated with an ordered reflected pair of
spectral coordinates. -/
def reflectedPairScrewKernel
    (t alpha beta : ℂ) : ℂ :=
  -Complex.I * (alpha - beta) *
    Complex.exp (-Complex.I * (alpha - beta) * t)

/-- A reflected-pair screw mode is entire in complex screw time. -/
theorem differentiable_reflectedPairScrewKernel_time
    (alpha beta : ℂ) :
    Differentiable ℂ (fun t : ℂ ↦
      reflectedPairScrewKernel t alpha beta) := by
  unfold reflectedPairScrewKernel
  fun_prop

/-- On real screw time, a conjugate pair of height `h` contributes the real
exponential mode `2 h exp (2 h t)`. -/
theorem reflectedPairScrewKernel_conj_realTime
    (t : ℝ) (alpha : ℂ) :
    reflectedPairScrewKernel (t : ℂ) alpha (starRingEnd ℂ alpha) =
      (2 * alpha.im * Real.exp (2 * alpha.im * t) : ℝ) := by
  unfold reflectedPairScrewKernel
  have hdiff : alpha - starRingEnd ℂ alpha =
      (2 * alpha.im : ℝ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp
      ring
  rw [hdiff]
  have hexponent : -Complex.I * ((2 * alpha.im : ℝ) * Complex.I) *
      (t : ℂ) = ((2 * alpha.im * t : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hexponent, ← Complex.ofReal_exp]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- On imaginary screw time, the same pair becomes the oscillatory mode
`2 h exp (i 2 h s)`. -/
theorem reflectedPairScrewKernel_conj_wickTime
    (s : ℝ) (alpha : ℂ) :
    reflectedPairScrewKernel (Complex.I * (s : ℂ))
        alpha (starRingEnd ℂ alpha) =
      (2 * alpha.im : ℝ) *
        Complex.exp (Complex.I * (2 * alpha.im * s : ℝ)) := by
  unfold reflectedPairScrewKernel
  have hdiff : alpha - starRingEnd ℂ alpha =
      (2 * alpha.im : ℝ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp
      ring
  rw [hdiff]
  congr 1
  · push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · congr 1
    push_cast
    ring_nf
    rw [Complex.I_pow_three]
    ring

/-- The unnormalized Gaussian average of the Wick-rotated conjugate-pair mode
is its Gaussian height damping times `sqrt (pi * tau)`. -/
theorem integral_reflectedPairScrewKernel_conj_wickGaussian
    {tau : ℝ} (htau : 0 < tau) (alpha : ℂ) :
    (∫ s : ℝ,
      Complex.exp (((-(s ^ 2 / tau) : ℝ) : ℂ)) *
        reflectedPairScrewKernel (Complex.I * (s : ℂ))
          alpha (starRingEnd ℂ alpha)) =
      (2 * alpha.im * Real.sqrt (Real.pi * tau) *
        Real.exp (-(tau * alpha.im ^ 2)) : ℝ) := by
  have hfun : (fun s : ℝ ↦
      Complex.exp (((-(s ^ 2 / tau) : ℝ) : ℂ)) *
        reflectedPairScrewKernel (Complex.I * (s : ℂ))
          alpha (starRingEnd ℂ alpha)) =
      fun s : ℝ ↦ (2 * alpha.im : ℝ) *
        complexTranslatedGaussianOscillation tau⁻¹ 0
          (2 * alpha.im) s := by
    funext s
    rw [reflectedPairScrewKernel_conj_wickTime]
    unfold complexTranslatedGaussianOscillation
    rw [show
        Complex.exp (((-(s ^ 2 / tau) : ℝ) : ℂ)) *
            ((2 * alpha.im : ℝ) *
              Complex.exp (Complex.I * (2 * alpha.im * s : ℝ))) =
          (2 * alpha.im : ℝ) *
            (Complex.exp (((-(s ^ 2 / tau) : ℝ) : ℂ)) *
              Complex.exp (Complex.I * (2 * alpha.im * s : ℝ))) by
        ring,
      ← Complex.exp_add]
    apply congrArg (fun z : ℂ ↦ (2 * alpha.im : ℝ) * Complex.exp z)
    push_cast
    field_simp [htau.ne']
    ring
  rw [hfun, MeasureTheory.integral_const_mul,
    integral_complexTranslatedGaussianOscillation (inv_pos.mpr htau)]
  have hsqrt : Real.pi / tau⁻¹ = Real.pi * tau := by
    field_simp [htau.ne']
  have hexponent :
      (-((2 * alpha.im) ^ 2) / (4 * tau⁻¹) : ℝ) =
        -(tau * alpha.im ^ 2) := by
    field_simp [htau.ne']
    ring
  rw [hsqrt, hexponent]
  norm_num
  ring

/-- The normalized Gaussian average of a reflected-pair mode along imaginary
screw time. -/
def reflectedPairScrewWickGaussianAverage
    (tau : ℝ) (alpha beta : ℂ) : ℂ :=
  (Real.sqrt (Real.pi * tau) : ℂ)⁻¹ *
    ∫ s : ℝ,
      Complex.exp (((-(s ^ 2 / tau) : ℝ) : ℂ)) *
        reflectedPairScrewKernel (Complex.I * (s : ℂ)) alpha beta

/-- The normalized Wick Gaussian average of a conjugate pair is exactly
`2 h exp (-tau h^2)`. -/
theorem reflectedPairScrewWickGaussianAverage_conj
    {tau : ℝ} (htau : 0 < tau) (alpha : ℂ) :
    reflectedPairScrewWickGaussianAverage tau alpha
        (starRingEnd ℂ alpha) =
      (2 * alpha.im * Real.exp (-(tau * alpha.im ^ 2)) : ℝ) := by
  rw [reflectedPairScrewWickGaussianAverage,
    integral_reflectedPairScrewKernel_conj_wickGaussian htau]
  have hsqrt : Real.sqrt (Real.pi * tau) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos Real.pi_pos htau)
  have hsqrtC : (Real.sqrt (Real.pi * tau) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsqrt
  push_cast
  field_simp [hsqrtC]

/-- The multiplicity-weighted Wick Gaussian screw contribution of one upper
spectral zeta zero and its conjugate partner. -/
def zetaUpperReflectedScrewWickSummand
    (tau : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℂ) *
      reflectedPairScrewWickGaussianAverage tau
        (zetaSpectralCoordinate rho.1)
        (zetaSpectralCoordinate
          (NontrivialZetaZero.conjugatePartner rho).1)
  else 0

/-- A zeta reflected-pair Wick contribution is twice its established
Gaussian-weighted upper-height summand. -/
theorem zetaUpperReflectedScrewWickSummand_eq_heightGaussian
    {tau : ℝ} (htau : 0 < tau) (rho : NontrivialZetaZero) :
    zetaUpperReflectedScrewWickSummand tau rho =
      (2 * zetaUpperSpectralHeightGaussianSummand tau rho : ℝ) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperReflectedScrewWickSummand, if_pos hupper,
      NontrivialZetaZero.spectralCoordinate_conjugatePartner,
      reflectedPairScrewWickGaussianAverage_conj htau,
      zetaUpperSpectralHeightGaussianSummand,
      zetaUpperSpectralHeightSummand, if_pos hupper]
    push_cast
    ring
  · rw [zetaUpperReflectedScrewWickSummand, if_neg hupper,
      zetaUpperSpectralHeightGaussianSummand,
      zetaUpperSpectralHeightSummand, if_neg hupper]
    norm_num

/-- Taking half the real part recovers exactly the nonnegative Gaussian
upper-height summand. -/
theorem zetaUpperReflectedScrewWickSummand_re_div_two
    {tau : ℝ} (htau : 0 < tau) (rho : NontrivialZetaZero) :
    (zetaUpperReflectedScrewWickSummand tau rho).re / 2 =
      zetaUpperSpectralHeightGaussianSummand tau rho := by
  rw [zetaUpperReflectedScrewWickSummand_eq_heightGaussian htau]
  norm_num

/-- The finite positive Wick-rotated screw mass in a genuine zeta-zero
spectral window. -/
def riemannXiUpperReflectedScrewWickMassWindow
    (tau T : ℝ) : ℝ≥0∞ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    ENNReal.ofReal
      ((zetaUpperReflectedScrewWickSummand tau rho).re / 2)

/-- Every finite Wick screw window is the corresponding Gaussian upper-height
window. -/
theorem riemannXiUpperReflectedScrewWickMassWindow_eq_heightGaussianWindow
    {tau : ℝ} (htau : 0 < tau) (T : ℝ) :
    riemannXiUpperReflectedScrewWickMassWindow tau T =
      ∑ rho ∈ spectralZetaZeroWindow T,
        ENNReal.ofReal
          (zetaUpperSpectralHeightGaussianSummand tau rho) := by
  unfold riemannXiUpperReflectedScrewWickMassWindow
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [zetaUpperReflectedScrewWickSummand_re_div_two htau]

/-- Cofinal finite Wick screw windows converge to the complete Gaussian
upper-height mass, with no finiteness assumption. -/
theorem tendsto_riemannXiUpperReflectedScrewWickMassWindow
    {tau : ℝ} (htau : 0 < tau) :
    Tendsto (riemannXiUpperReflectedScrewWickMassWindow tau) atTop
      (nhds (riemannXiUpperSpectralHeightGaussianMass tau)) := by
  have hheight : Tendsto
      (fun T : ℝ ↦ ∑ rho ∈ spectralZetaZeroWindow T,
        ENNReal.ofReal
          (zetaUpperSpectralHeightGaussianSummand tau rho))
      atTop (nhds (riemannXiUpperSpectralHeightGaussianMass tau)) := by
    unfold riemannXiUpperSpectralHeightGaussianMass
    exact ENNReal.summable.hasSum.comp tendsto_spectralZetaZeroWindow_atTop
  apply hheight.congr'
  exact Eventually.of_forall fun T ↦
    (riemannXiUpperReflectedScrewWickMassWindow_eq_heightGaussianWindow
      htau T).symm

/-- The same finite windows converge to the normalized spatial boundary heat,
including when the common extended-real value is infinite. -/
theorem tendsto_riemannXiUpperReflectedScrewWickMassWindow_normalizedSpatialHeat
    {tau : ℝ} (htau : 0 < tau) :
    Tendsto (riemannXiUpperReflectedScrewWickMassWindow tau) atTop
      (nhds (riemannXiUpperHyperbolicBoundarySpatialHeatMass tau /
        ENNReal.ofReal (2 * Real.sqrt (Real.pi / tau)))) := by
  rw [riemannXiUpperHyperbolicBoundarySpatialHeatMass_normalized htau]
  exact tendsto_riemannXiUpperReflectedScrewWickMassWindow htau

/-- The multiplicity-weighted real-time reflected-pair screw mode attached to
one upper spectral zeta zero. -/
def zetaUpperReflectedScrewGrowthSummand
    (t : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  if 0 < (zetaSpectralCoordinate rho.1).im then
    (analyticZetaZeroMultiplicity rho : ℂ) *
      reflectedPairScrewKernel (t : ℂ)
        (zetaSpectralCoordinate rho.1)
        (zetaSpectralCoordinate
          (NontrivialZetaZero.conjugatePartner rho).1)
  else 0

/-- Half the real part of a real-time screw mode is its upper height times the
positive exponential factor `exp (2 h t)`. -/
theorem zetaUpperReflectedScrewGrowthSummand_re_div_two
    (t : ℝ) (rho : NontrivialZetaZero) :
    (zetaUpperReflectedScrewGrowthSummand t rho).re / 2 =
      zetaUpperSpectralHeightSummand rho *
        Real.exp (2 * (zetaSpectralCoordinate rho.1).im * t) := by
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · rw [zetaUpperReflectedScrewGrowthSummand, if_pos hupper,
      NontrivialZetaZero.spectralCoordinate_conjugatePartner,
      reflectedPairScrewKernel_conj_realTime,
      zetaUpperSpectralHeightSummand, if_pos hupper]
    norm_num
    rw [show
        (2 : ℂ) * (1 / 2 - ((rho.1.re : ℝ) : ℂ)) * (t : ℂ) =
          ((2 * (1 / 2 - rho.1.re) * t : ℝ) : ℂ) by
        push_cast
        ring,
      Complex.exp_ofReal_re]
    ring
  · rw [zetaUpperReflectedScrewGrowthSummand, if_neg hupper,
      zetaUpperSpectralHeightSummand, if_neg hupper]
    norm_num

/-- The complete positive reflected-pair screw growth mass.  Extended values
avoid assuming convergence of the full spectral series. -/
def riemannXiUpperReflectedScrewGrowthMass (t : ℝ) : ℝ≥0∞ :=
  ∑' rho : NontrivialZetaZero,
    ENNReal.ofReal
      ((zetaUpperReflectedScrewGrowthSummand t rho).re / 2)

/-- Subexponential growth means that, for every positive rate, the complete
positive screw mass is bounded by some constant times that exponential on
nonnegative real time. -/
def RiemannXiUpperReflectedScrewGrowthSubexponential : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      riemannXiUpperReflectedScrewGrowthMass t ≤
        ENNReal.ofReal (C * Real.exp (epsilon * t))

/-- At real time zero, screw growth mass is exactly the full upper spectral
height mass. -/
theorem riemannXiUpperReflectedScrewGrowthMass_zero :
    riemannXiUpperReflectedScrewGrowthMass 0 =
      riemannXiUpperSpectralHeightMass := by
  unfold riemannXiUpperReflectedScrewGrowthMass
    riemannXiUpperSpectralHeightMass
  congr 1
  funext rho
  rw [zetaUpperReflectedScrewGrowthSummand_re_div_two]
  norm_num

/-- RH annihilates the complete reflected-pair screw mass at every real time. -/
theorem riemannXiUpperReflectedScrewGrowthMass_eq_zero_of_rh
    (hRH : RiemannHypothesis) (t : ℝ) :
    riemannXiUpperReflectedScrewGrowthMass t = 0 := by
  unfold riemannXiUpperReflectedScrewGrowthMass
  rw [ENNReal.tsum_eq_zero]
  intro rho
  rw [zetaUpperReflectedScrewGrowthSummand_re_div_two]
  have him : (zetaSpectralCoordinate rho.1).im = 0 :=
    (riemannHypothesis_iff_spectralCoordinate_real.mp hRH)
      rho.1 rho.2.1 rho.2.2.1 rho.2.2.2
  rw [zetaUpperSpectralHeightSummand, if_neg (by linarith),
    zero_mul, ENNReal.ofReal_zero]

/-- At every fixed real time, vanishing of the complete positive screw mass is
equivalent to RH. -/
theorem riemannXiUpperReflectedScrewGrowthMass_eq_zero_iff_rh
    (t : ℝ) :
    riemannXiUpperReflectedScrewGrowthMass t = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    have hsummand : 0 < zetaUpperSpectralHeightSummand rho := by
      rw [zetaUpperSpectralHeightSummand, if_pos hwupper]
      exact mul_pos
        (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
        hwupper
    have hpositive : 0 < zetaUpperSpectralHeightSummand rho *
        Real.exp (2 * (zetaSpectralCoordinate rho.1).im * t) :=
      mul_pos hsummand (Real.exp_pos _)
    have hterm : 0 < ENNReal.ofReal
        ((zetaUpperReflectedScrewGrowthSummand t rho).re / 2) := by
      rw [zetaUpperReflectedScrewGrowthSummand_re_div_two]
      exact ENNReal.ofReal_pos.mpr hpositive
    have hle : ENNReal.ofReal
        ((zetaUpperReflectedScrewGrowthSummand t rho).re / 2) ≤
        riemannXiUpperReflectedScrewGrowthMass t := by
      exact ENNReal.le_tsum rho
    rw [hzero] at hle
    exact (not_lt_of_ge hle) hterm
  · intro hRH
    exact riemannXiUpperReflectedScrewGrowthMass_eq_zero_of_rh hRH t

/-- The complete positive reflected-pair screw mass is subexponential exactly
when RH holds.  In the reverse direction, one upper zero of height `a` gives a
positive `exp (2 a t)` term, contradicting the required `exp (a t)` bound. -/
theorem riemannXiUpperReflectedScrewGrowthSubexponential_iff_rh :
    RiemannXiUpperReflectedScrewGrowthSubexponential ↔
      RiemannHypothesis := by
  constructor
  · intro hsub
    by_contra hRH
    obtain ⟨w, hwzero, hwupper⟩ :=
      exists_riemannXiSpectral_upper_zero_of_not_riemannHypothesis hRH
    obtain ⟨rho, rfl⟩ :=
      (riemannXiSpectral_eq_zero_iff_exists_zetaZero w).mp hwzero
    let a : ℝ := (zetaSpectralCoordinate rho.1).im
    let c : ℝ := zetaUpperSpectralHeightSummand rho
    have ha : 0 < a := by
      exact hwupper
    have hc : 0 < c := by
      dsimp [c]
      rw [zetaUpperSpectralHeightSummand, if_pos hwupper]
      exact mul_pos
        (by exact_mod_cast analyticZetaZeroMultiplicity_positive rho)
        hwupper
    obtain ⟨C, hC, hbound⟩ := hsub a ha
    let q : ℝ := C / c + 1
    let t : ℝ := q / a
    have hq : 0 < q := by
      dsimp [q]
      have hdiv : 0 ≤ C / c := div_nonneg hC hc.le
      linarith
    have ht : 0 ≤ t := (div_pos hq ha).le
    have hat : a * t = q := by
      dsimp [t]
      field_simp [ha.ne']
    have hterm : ENNReal.ofReal
        (c * Real.exp (2 * a * t)) ≤
        riemannXiUpperReflectedScrewGrowthMass t := by
      unfold riemannXiUpperReflectedScrewGrowthMass
      have hle := ENNReal.le_tsum
        (f := fun rho : NontrivialZetaZero ↦
          ENNReal.ofReal
            ((zetaUpperReflectedScrewGrowthSummand t rho).re / 2)) rho
      rw [zetaUpperReflectedScrewGrowthSummand_re_div_two] at hle
      exact hle
    have hchain : ENNReal.ofReal (c * Real.exp (2 * a * t)) ≤
        ENNReal.ofReal (C * Real.exp (a * t)) :=
      hterm.trans (hbound t ht)
    have hright : 0 ≤ C * Real.exp (a * t) :=
      mul_nonneg hC (Real.exp_pos _).le
    have hreal : c * Real.exp (2 * a * t) ≤
        C * Real.exp (a * t) :=
      (ENNReal.ofReal_le_ofReal_iff hright).mp hchain
    have hcancel : c * Real.exp (a * t) ≤ C := by
      have hexp : 0 < Real.exp (a * t) := Real.exp_pos _
      apply le_of_mul_le_mul_right _ hexp
      calc
        (c * Real.exp (a * t)) * Real.exp (a * t) =
            c * Real.exp (2 * a * t) := by
              rw [mul_assoc, ← Real.exp_add]
              congr 2
              ring
        _ ≤ C * Real.exp (a * t) := hreal
    rw [hat] at hcancel
    have hexpLower : q + 1 ≤ Real.exp q := Real.add_one_le_exp q
    have hscale : c * (q + 1) ≤ c * Real.exp q :=
      mul_le_mul_of_nonneg_left hexpLower hc.le
    have hstrict : C < c * Real.exp q := by
      calc
        C < C + 2 * c := by linarith
        _ = c * (q + 1) := by
          dsimp [q]
          field_simp [hc.ne']
          ring
        _ ≤ c * Real.exp q := hscale
    exact (not_lt_of_ge hcancel) hstrict
  · intro hRH epsilon _hepsilon
    refine ⟨0, le_rfl, ?_⟩
    intro t _ht
    rw [riemannXiUpperReflectedScrewGrowthMass_eq_zero_of_rh hRH]
    exact bot_le

end

end RiemannGaussian
