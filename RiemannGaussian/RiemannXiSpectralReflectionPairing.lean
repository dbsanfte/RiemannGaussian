import RiemannGaussian.RiemannXiBlaschkeLogDerivativeCancellation

/-!
# Reflection pairing of finite spectral-xi Cauchy windows

The full finite Cauchy divisor sum in the genuine `xi'/xi` decomposition is
partitioned into upper, critical-line, and lower spectral zeros.  Critical-line
reflection identifies the lower sum with the reflected upper sum.  Combining
the resulting plus-pair sum with the signed Blaschke logarithmic derivative
puts the actual spectral-xi remainder and the finite Blaschke product in one
exact identity.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Critical-line zeros in one finite symmetric spectral window. -/
def spectralCriticalZetaZeroWindow (T : ℝ) : Finset NontrivialZetaZero :=
  (spectralZetaZeroWindow T).filter fun rho =>
    (zetaSpectralCoordinate rho.1).im = 0

/-- Lower spectral zeros in one finite symmetric spectral window. -/
def spectralLowerZetaZeroWindow (T : ℝ) : Finset NontrivialZetaZero :=
  (spectralZetaZeroWindow T).filter fun rho =>
    (zetaSpectralCoordinate rho.1).im < 0

@[simp]
theorem mem_spectralCriticalZetaZeroWindow
    {T : ℝ} {rho : NontrivialZetaZero} :
    rho ∈ spectralCriticalZetaZeroWindow T ↔
      rho ∈ spectralZetaZeroWindow T ∧
        (zetaSpectralCoordinate rho.1).im = 0 := by
  simp [spectralCriticalZetaZeroWindow]

@[simp]
theorem mem_spectralLowerZetaZeroWindow
    {T : ℝ} {rho : NontrivialZetaZero} :
    rho ∈ spectralLowerZetaZeroWindow T ↔
      rho ∈ spectralZetaZeroWindow T ∧
        (zetaSpectralCoordinate rho.1).im < 0 := by
  simp [spectralLowerZetaZeroWindow]

/-- The principal part at the reflected zero is the corresponding reflected
denominator with the same genuine multiplicity. -/
theorem zetaSpectralLogDerivativePrincipalPart_conjugatePartner
    (rho : NontrivialZetaZero) (z : ℂ) :
    zetaSpectralLogDerivativePrincipalPart
        (NontrivialZetaZero.conjugatePartner rho) z =
      (analyticZetaZeroMultiplicity rho : ℂ) /
        (z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) := by
  unfold zetaSpectralLogDerivativePrincipalPart
  rw [analyticZetaZeroMultiplicity_conjugatePartner,
    NontrivialZetaZero.spectralCoordinate_conjugatePartner]

/-- The upper, critical-line, and lower Cauchy pieces of one finite window. -/
def riemannXiSpectralUpperCauchyWindow (z : ℂ) (T : ℝ) : ℂ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    zetaSpectralLogDerivativePrincipalPart rho z

/-- The critical-line Cauchy part of one finite spectral window. -/
def riemannXiSpectralCriticalCauchyWindow (z : ℂ) (T : ℝ) : ℂ :=
  ∑ rho ∈ spectralCriticalZetaZeroWindow T,
    zetaSpectralLogDerivativePrincipalPart rho z

/-- The lower Cauchy part of one finite spectral window. -/
def riemannXiSpectralLowerCauchyWindow (z : ℂ) (T : ℝ) : ℂ :=
  ∑ rho ∈ spectralLowerZetaZeroWindow T,
    zetaSpectralLogDerivativePrincipalPart rho z

/-- Every finite full Cauchy window is the sum of its upper, critical-line,
and lower pieces. -/
theorem riemannXiSpectralWindowCauchySum_eq_upper_add_critical_add_lower
    (z : ℂ) (T : ℝ) :
    riemannXiSpectralWindowCauchySum T z =
      riemannXiSpectralUpperCauchyWindow z T +
        riemannXiSpectralCriticalCauchyWindow z T +
          riemannXiSpectralLowerCauchyWindow z T := by
  unfold riemannXiSpectralWindowCauchySum
    riemannXiSpectralUpperCauchyWindow
    riemannXiSpectralCriticalCauchyWindow
    riemannXiSpectralLowerCauchyWindow
    spectralUpperZetaZeroWindow
    spectralCriticalZetaZeroWindow
    spectralLowerZetaZeroWindow
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho _hrho
  let y : ℝ := (zetaSpectralCoordinate rho.1).im
  by_cases hypos : 0 < y
  · change 0 < (zetaSpectralCoordinate rho.1).im at hypos
    have hyzero : (zetaSpectralCoordinate rho.1).im ≠ 0 := ne_of_gt hypos
    have hyneg : ¬(zetaSpectralCoordinate rho.1).im < 0 :=
      not_lt_of_ge hypos.le
    rw [if_pos hypos, if_neg hyzero, if_neg hyneg]
    ring
  · by_cases hyzero : y = 0
    · change ¬0 < (zetaSpectralCoordinate rho.1).im at hypos
      change (zetaSpectralCoordinate rho.1).im = 0 at hyzero
      have hyneg : ¬(zetaSpectralCoordinate rho.1).im < 0 := by
        linarith
      rw [if_neg hypos, if_pos hyzero, if_neg hyneg]
      ring
    · have hyneg : y < 0 := lt_of_le_of_ne (not_lt.mp hypos) hyzero
      change ¬0 < (zetaSpectralCoordinate rho.1).im at hypos
      change (zetaSpectralCoordinate rho.1).im ≠ 0 at hyzero
      change (zetaSpectralCoordinate rho.1).im < 0 at hyneg
      rw [if_neg hypos, if_neg hyzero, if_pos hyneg]
      ring

/-- Critical-line reflection maps the finite upper window bijectively onto
the finite lower window. -/
theorem riemannXiSpectralLowerCauchyWindow_eq_upper_conjugatePartner_sum
    {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    riemannXiSpectralLowerCauchyWindow z T =
      ∑ rho ∈ spectralUpperZetaZeroWindow T,
        zetaSpectralLogDerivativePrincipalPart
          (NontrivialZetaZero.conjugatePartner rho) z := by
  unfold riemannXiSpectralLowerCauchyWindow
  symm
  refine Finset.sum_bij
    (fun rho _hrho => NontrivialZetaZero.conjugatePartner rho)
    ?_ ?_ ?_ ?_
  · intro rho hrho
    have hmem := (mem_spectralUpperZetaZeroWindow.mp hrho).1
    have hupper := (mem_spectralUpperZetaZeroWindow.mp hrho).2
    apply mem_spectralLowerZetaZeroWindow.mpr
    constructor
    · exact (conjugatePartner_mem_spectralZetaZeroWindow_iff hT rho).2 hmem
    · have him :
          (zetaSpectralCoordinate
            (NontrivialZetaZero.conjugatePartner rho).1).im =
            -(zetaSpectralCoordinate rho.1).im := by
        rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
        simp
      rw [him]
      linarith
  · intro rho₁ _hrho₁ rho₂ _hrho₂ heq
    exact NontrivialZetaZero.conjugatePartnerEquiv.injective heq
  · intro rho hrho
    have hmem := (mem_spectralLowerZetaZeroWindow.mp hrho).1
    have hlower := (mem_spectralLowerZetaZeroWindow.mp hrho).2
    refine ⟨NontrivialZetaZero.conjugatePartner rho, ?_, ?_⟩
    · apply mem_spectralUpperZetaZeroWindow.mpr
      constructor
      · exact (conjugatePartner_mem_spectralZetaZeroWindow_iff hT rho).2 hmem
      · have him :
            (zetaSpectralCoordinate
              (NontrivialZetaZero.conjugatePartner rho).1).im =
              -(zetaSpectralCoordinate rho.1).im := by
          rw [NontrivialZetaZero.spectralCoordinate_conjugatePartner]
          simp
        rw [him]
        linarith
    · simp
  · intro rho _hrho
    rfl

/-- The signed Blaschke logarithmic-derivative sum is upper Cauchy minus its
reflected lower counterpart. -/
theorem riemannXiUpperBlaschkeLogDerivativeWindow_eq_upper_sub_reflected
    (z : ℂ) (T : ℝ) :
    riemannXiUpperBlaschkeLogDerivativeWindow z T =
      riemannXiSpectralUpperCauchyWindow z T -
        ∑ rho ∈ spectralUpperZetaZeroWindow T,
          zetaSpectralLogDerivativePrincipalPart
            (NontrivialZetaZero.conjugatePartner rho) z := by
  unfold riemannXiUpperBlaschkeLogDerivativeWindow
    riemannXiSpectralUpperCauchyWindow
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho _hrho
  unfold zetaUpperBlaschkeLogDerivativeSummand
  rw [zetaSpectralLogDerivativePrincipalPart_conjugatePartner]
  unfold zetaSpectralLogDerivativePrincipalPart
  ring

/-- The genuine full Cauchy window, its critical-line part, and the signed
Blaschke sum recover twice the upper Cauchy part exactly. -/
theorem two_mul_riemannXiSpectralUpperCauchyWindow_eq_full_sub_critical_add_blaschke
    {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    2 * riemannXiSpectralUpperCauchyWindow z T =
      (riemannXiSpectralWindowCauchySum T z -
        riemannXiSpectralCriticalCauchyWindow z T) +
          riemannXiUpperBlaschkeLogDerivativeWindow z T := by
  rw [riemannXiSpectralWindowCauchySum_eq_upper_add_critical_add_lower,
    riemannXiSpectralLowerCauchyWindow_eq_upper_conjugatePartner_sum hT,
    riemannXiUpperBlaschkeLogDerivativeWindow_eq_upper_sub_reflected]
  ring

/-- Unified finite-window identity: twice the upper divisor Cauchy sum is the
actual spectral-xi logarithmic derivative minus its analytic window remainder
and critical-line part, plus the finite spectral Blaschke logarithmic
derivative. -/
theorem two_mul_riemannXiSpectralUpperCauchyWindow_eq_xiLogDeriv_sub_remainders_add_blaschke
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {T : ℝ} (hT : 0 ≤ T) :
    2 * riemannXiSpectralUpperCauchyWindow z T =
      (logDeriv riemannXiSpectral z -
          riemannXiSpectralWindowLogDerivativeRawRemainder T z -
          riemannXiSpectralCriticalCauchyWindow z T) +
        logDeriv (riemannXiUpperBlaschkeProductWindow T) z := by
  rw [logDeriv_riemannXiUpperBlaschkeProductWindow_eq_sum hz hxi T]
  have hpair :=
    two_mul_riemannXiSpectralUpperCauchyWindow_eq_full_sub_critical_add_blaschke
      hT z
  have hcauchy :
      riemannXiSpectralWindowCauchySum T z =
        logDeriv riemannXiSpectral z -
          riemannXiSpectralWindowLogDerivativeRawRemainder T z := by
    rw [logDeriv_riemannXiSpectral_eq_windowCauchySum_add_rawRemainder]
    ring
  rw [hcauchy] at hpair
  exact hpair

end

end RiemannGaussian
