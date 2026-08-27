import RiemannGaussian.RiemannXiBlaschkePhaseDispersion

/-!
# Unit-phase geometry of finite Blaschke cancellation

Each pairwise angular defect in the finite Blaschke phase-dispersion energy is
exactly one half the product of the two term norms times the squared chordal
distance between their unit complex phases.  The identity is valid even when
a term is zero, using the zero-normalized phase convention.

At every noncolliding upper observation point, all signed spectral Blaschke
terms belonging to upper zeros are nonzero.  Their normalized phases therefore
lie on the unit circle, and the canonical cancellation-energy branch is a
literal positive weighted phase-separation branch.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The unit complex phase of a nonzero number, with zero sent to zero. -/
def complexUnitPhase (w : ℂ) : ℂ :=
  w / (‖w‖ : ℂ)

@[simp]
theorem complexUnitPhase_zero : complexUnitPhase 0 = 0 := by
  simp [complexUnitPhase]

/-- A nonzero number has a normalized phase of norm one. -/
theorem norm_complexUnitPhase {w : ℂ} (hw : w ≠ 0) :
    ‖complexUnitPhase w‖ = 1 := by
  simp [complexUnitPhase, hw]

/-- The real inner product of two unit phases is the original real inner
product divided by the product of the norms. -/
theorem re_inner_complexUnitPhase {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (inner ℂ (complexUnitPhase u) (complexUnitPhase v)).re =
      (inner ℂ u v).re / (‖u‖ * ‖v‖) := by
  simp [complexUnitPhase, RCLike.inner_apply, div_eq_mul_inv,
    Complex.mul_re, hu, hv]
  ring

/-- Every complex pairwise angular defect is a weighted squared chordal
distance between normalized phases. -/
theorem complex_pairPhaseDefect_eq_weighted_unitPhase_distance_sq
    (u v : ℂ) :
    ‖u‖ * ‖v‖ - (inner ℂ u v).re =
      (‖u‖ * ‖v‖ / 2) *
        ‖complexUnitPhase u - complexUnitPhase v‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu, complexUnitPhase]
  by_cases hv : v = 0
  · simp [hv, complexUnitPhase]
  rw [norm_sub_sq (𝕜 := ℂ)]
  rw [norm_complexUnitPhase hu, norm_complexUnitPhase hv]
  change ‖u‖ * ‖v‖ - (inner ℂ u v).re =
    ‖u‖ * ‖v‖ / 2 *
      (1 ^ 2 - 2 * (inner ℂ (complexUnitPhase u) (complexUnitPhase v)).re +
        1 ^ 2)
  rw [re_inner_complexUnitPhase hu hv]
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  field_simp
  ring

/-- The weighted squared chordal phase-separation energy of the signed
Blaschke terms in one finite upper spectral window. -/
def riemannXiUpperBlaschkePhaseChordEnergyWindow (z : ℂ) (T : ℝ) : ℝ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    ∑ sigma ∈ spectralUpperZetaZeroWindow T,
      (‖zetaUpperBlaschkeLogDerivativeSummand z rho‖ *
          ‖zetaUpperBlaschkeLogDerivativeSummand z sigma‖ / 2) *
        ‖complexUnitPhase (zetaUpperBlaschkeLogDerivativeSummand z rho) -
            complexUnitPhase
              (zetaUpperBlaschkeLogDerivativeSummand z sigma)‖ ^ 2

/-- Pairwise phase dispersion is exactly the weighted squared chordal
phase-separation energy. -/
theorem riemannXiUpperBlaschkePhaseDispersionWindow_eq_phaseChordEnergy
    (z : ℂ) (T : ℝ) :
    riemannXiUpperBlaschkePhaseDispersionWindow z T =
      riemannXiUpperBlaschkePhaseChordEnergyWindow z T := by
  unfold riemannXiUpperBlaschkePhaseDispersionWindow
    finiteComplexPhaseDispersion
    riemannXiUpperBlaschkePhaseChordEnergyWindow
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  exact
    complex_pairPhaseDefect_eq_weighted_unitPhase_distance_sq
      (zetaUpperBlaschkeLogDerivativeSummand z rho)
      (zetaUpperBlaschkeLogDerivativeSummand z sigma)

/-- At a noncolliding upper observation point, the signed Blaschke term of
every upper spectral zero is nonzero. -/
theorem zetaUpperBlaschkeLogDerivativeSummand_ne_zero
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    (rho : NontrivialZetaZero)
    (hupper : 0 < (zetaSpectralCoordinate rho.1).im) :
    zetaUpperBlaschkeLogDerivativeSummand z rho ≠ 0 := by
  let alpha : ℂ := zetaSpectralCoordinate rho.1
  have hne : z ≠ alpha := by
    intro heq
    apply hxi
    rw [heq]
    exact (riemannXiSpectral_eq_zero_iff_exists_zetaZero _).2 ⟨rho, rfl⟩
  have hconj : z - starRingEnd ℂ alpha ≠ 0 :=
    sub_conj_ne_zero_of_im_pos hz hupper
  have halphaConj : alpha ≠ starRingEnd ℂ alpha := by
    intro heq
    have him : alpha.im = -alpha.im := by
      simpa using congrArg Complex.im heq
    dsimp [alpha] at him
    linarith
  have hpair :
      1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha) =
        (alpha - starRingEnd ℂ alpha) /
          ((z - alpha) * (z - starRingEnd ℂ alpha)) := by
    field_simp [sub_ne_zero.mpr hne, hconj]
    ring
  have hmNat : analyticZetaZeroMultiplicity rho ≠ 0 :=
    Nat.ne_of_gt (analyticZetaZeroMultiplicity_positive rho)
  have hm : (analyticZetaZeroMultiplicity rho : ℂ) ≠ 0 := by
    exact_mod_cast hmNat
  unfold zetaUpperBlaschkeLogDerivativeSummand
  change (analyticZetaZeroMultiplicity rho : ℂ) *
      (1 / (z - alpha) - 1 / (z - starRingEnd ℂ alpha)) ≠ 0
  rw [hpair]
  exact mul_ne_zero hm
    (div_ne_zero (sub_ne_zero.mpr halphaConj)
      (mul_ne_zero (sub_ne_zero.mpr hne) hconj))

/-- Consequently every signed term in a finite upper window has a genuine
unit-circle phase. -/
theorem norm_complexUnitPhase_zetaUpperBlaschkeLogDerivativeSummand
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0)
    {T : ℝ} {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralUpperZetaZeroWindow T) :
    ‖complexUnitPhase (zetaUpperBlaschkeLogDerivativeSummand z rho)‖ = 1 :=
  norm_complexUnitPhase
    (zetaUpperBlaschkeLogDerivativeSummand_ne_zero hz hxi rho
      (mem_spectralUpperZetaZeroWindow.mp hrho).2)

/-- An eventual phase-dispersion threshold transfers exactly to the weighted
unit-phase chordal energy. -/
theorem eventually_phaseChordEnergy_of_eventually_phaseDispersion
    {z : ℂ} {e : ℝ}
    (hdispersion : ∀ᶠ T : ℝ in atTop,
      e ≤ riemannXiUpperBlaschkePhaseDispersionWindow z T) :
    ∀ᶠ T : ℝ in atTop,
      e ≤ riemannXiUpperBlaschkePhaseChordEnergyWindow z T := by
  filter_upwards [hdispersion] with T hT
  rwa [← riemannXiUpperBlaschkePhaseDispersionWindow_eq_phaseChordEnergy]

end

end RiemannGaussian
