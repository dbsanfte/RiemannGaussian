/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Strength audit of the published quasi-RH probe calibration

This audits the algebra of the low estimate and Mellin normalization in
equations (12.4), (15.6), (15.9) of the pinned OpenAI quasi-RH manuscript.
It does not import that manuscript's arithmetic estimates into Lean.

If the same low-exponent formula is retained, and every fully rescaled
averaging length remains nonnegative, changing these scales alone cannot
calibrate a zero-free boundary below `5/6`. An explicit nonzero phased
power signal satisfies that low allowance and has zero comparison error.
This is a failed exponent-preflight, not a counterfeit Hecke character,
theta probe or claim that other coupled arithmetic estimates are impossible.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RiemannGaussian.ZetaQuasiRHProbeCalibration

/-- Logarithmic low allowance in the existing reflected/Poisson separation. -/
def lowExponent (x y : ℝ) : ℝ := x/2+(y-x)/12

/-- Constant part of the Mellin signal exponent, with `h=1+ell-x`. -/
def signalShift (x ell : ℝ) : ℝ := x/2-1+(1+ell-x)/6

/-- The boundary at which the retained low and source exponents agree. -/
def calibratedBoundary (x y ell : ℝ) : ℝ := lowExponent x y-signalShift x ell

/-- The complete scale dependence is one signed length balance. -/
theorem calibratedBoundary_eq (x y ell : ℝ) :
    calibratedBoundary x y ell=5/6+(x+y-2*ell)/12 := by
  unfold calibratedBoundary lowExponent signalShift
  ring

/-- Fully rescaling every selected slot subtracts `ell` from both ranges.
Preserving their nonnegative lengths forces this uniform barrier. -/
theorem fiveSixths_le_boundary {x y ell : ℝ}
    (hx : ell ≤ x) (hy : ell ≤ y) :
    (5/6 : ℝ) ≤ calibratedBoundary x y ell := by
  rw [calibratedBoundary_eq]
  linarith

/-- Under the published total-length relation, the boundary is affine in
the total marked-prime length. -/
theorem boundary_eq_of_total {x y ell : ℝ} (htotal : x+y+ell=1) :
    calibratedBoundary x y ell=11/12-ell/4 := by
  rw [calibratedBoundary_eq]
  linarith

/-- Nonnegative fully rescaled lengths cap the marked length by `1/3`. -/
theorem marked_length_le_third {x y ell : ℝ}
    (hx : ell ≤ x) (hy : ell ≤ y) (htotal : x+y+ell=1) :
    ell ≤ (1/3 : ℝ) := by
  linarith

/-- The exact published parameters recover `7/8`, with no floating input. -/
theorem published_boundary :
    calibratedBoundary (17/48) (23/48) (1/6)=(7/8 : ℝ) := by
  norm_num [calibratedBoundary,lowExponent,signalShift]

/-- A positive strict low-side margin requires a source to the right of
`5/6`, even before any high-side, contour or rounding cost is paid. -/
theorem source_gt_fiveSixths_of_low_margin {x y ell beta loss : ℝ}
    (hx : ell ≤ x) (hy : ell ≤ y) (hloss : 0 ≤ loss)
    (hmargin : lowExponent x y+loss < beta+signalShift x ell) :
    (5/6 : ℝ) < beta := by
  have hb := fiveSixths_le_boundary hx hy
  unfold calibratedBoundary at hb
  linarith

/-- Retaining this low allowance cannot calibrate at the RH boundary. -/
theorem no_low_margin_at_half {x y ell loss : ℝ}
    (hx : ell ≤ x) (hy : ell ≤ y) (hloss : 0 ≤ loss) :
    ¬lowExponent x y+loss < (1/2 : ℝ)+signalShift x ell := by
  intro h
  have := source_gt_fiveSixths_of_low_margin hx hy hloss h
  norm_num at this

/-- A diagnostic power mode with the full fixed-height Mellin phase.
No literal arithmetic or automorphic compatibility is asserted for it. -/
def powerSignal (beta gamma x ell Z : ℝ) : ℂ :=
  (Z : ℂ)^((beta+signalShift x ell : ℝ)+Complex.I*gamma)

/-- Its size is exactly the source exponent, independently of height. -/
theorem norm_powerSignal {Z : ℝ} (hZ : 0 < Z) (beta gamma x ell : ℝ) :
    ‖powerSignal beta gamma x ell Z‖=Real.rpow Z (beta+signalShift x ell) := by
  unfold powerSignal
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]
  norm_num

/-- The source remains nonzero at every positive physical scale. -/
theorem powerSignal_ne_zero {Z : ℝ} (hZ : 0 < Z) (beta gamma x ell : ℝ) :
    powerSignal beta gamma x ell Z ≠ 0 := by
  intro h
  have hn := norm_powerSignal hZ beta gamma x ell
  rw [h,norm_zero] at hn
  exact (Real.rpow_pos_of_pos hZ _).ne' hn.symm

/-- Below the calibrated boundary a nonzero phased source is admitted
by the exact retained low allowance, even with perfect comparison. -/
theorem powerSignal_admitted_by_low {x y ell beta gamma Z : ℝ}
    (hbeta : beta ≤ calibratedBoundary x y ell) (hZ : 1 ≤ Z) :
    ‖powerSignal beta gamma x ell Z‖ ≤ Real.rpow Z (lowExponent x y) := by
  rw [norm_powerSignal (zero_lt_one.trans_le hZ)]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  unfold calibratedBoundary at hbeta
  linarith

/-- In particular, every real source at or left of `5/6` survives this
exponent-only test on all admissible rescaled lengths. -/
theorem sub_fiveSixths_source_admitted {x y ell beta gamma Z : ℝ}
    (hx : ell ≤ x) (hy : ell ≤ y) (hbeta : beta ≤ (5/6 : ℝ)) (hZ : 1 ≤ Z) :
    ‖powerSignal beta gamma x ell Z‖ ≤ Real.rpow Z (lowExponent x y) :=
  powerSignal_admitted_by_low (hbeta.trans (fiveSixths_le_boundary hx hy)) hZ

/-- Choosing the same signal as the probe makes the high-side error
identically zero; improving that error alone does not repair this gate. -/
theorem perfect_comparison (beta gamma x ell Z : ℝ) :
    powerSignal beta gamma x ell Z-powerSignal beta gamma x ell Z=0 := sub_self _

/-- With a common normalized Mellin shape, changing only scale geometry
multiplies every diagnostic source by the same factor relative to any
reference exponent. This is a signal preflight, not a physical probe identity. -/
theorem powerSignal_eq_reference_factor {Z : ℝ} (hZ : 0 < Z)
    (beta gamma beta0 gamma0 x ell : ℝ) :
    powerSignal beta gamma x ell Z=
      (Z : ℂ)^((beta-beta0 : ℝ)+Complex.I*(gamma-gamma0))*
        powerSignal beta0 gamma0 x ell Z := by
  unfold powerSignal
  rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hZ.ne')]
  congr 1
  push_cast
  ring

/-- Join arbitrary finite complex comparison coefficients before any norm.
Pure scale changes leave the entire source dependence in one common factor. -/
theorem centered_power_sum_eq {ι : Type*} (S : Finset ι) (b : ι → ℂ)
    (x ell : ι → ℝ) {Z : ℝ} (hZ : 0 < Z) (beta gamma beta0 gamma0 : ℝ) :
    (∑ i ∈ S,b i*powerSignal beta gamma (x i) (ell i) Z)=
      (Z : ℂ)^((beta-beta0 : ℝ)+Complex.I*(gamma-gamma0))*
        ∑ i ∈ S,b i*powerSignal beta0 gamma0 (x i) (ell i) Z := by
  simp_rw [powerSignal_eq_reference_factor hZ beta gamma beta0 gamma0]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Exact same-shape scale centering cannot cancel a reference signal
while retaining any other exponent or height. No arithmetic mean or
exceptional-frequency cancellation is assumed or deduced here. -/
theorem centered_power_sum_eq_zero_iff {ι : Type*} (S : Finset ι) (b : ι → ℂ)
    (x ell : ι → ℝ) {Z : ℝ} (hZ : 0 < Z) (beta gamma beta0 gamma0 : ℝ) :
    (∑ i ∈ S,b i*powerSignal beta gamma (x i) (ell i) Z)=0 ↔
      (∑ i ∈ S,b i*powerSignal beta0 gamma0 (x i) (ell i) Z)=0 := by
  rw [centered_power_sum_eq S b x ell hZ beta gamma beta0 gamma0]
  have hf : (Z : ℂ)^((beta-beta0 : ℝ)+Complex.I*(gamma-gamma0)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hf
  · intro h
    rw [h,mul_zero]

/-- At the fixed published geometry, reaching the critical-line signal
requires a strictly greater than `3/8` saving in the low exponent. This
states the missing strength, not the existence of such an arithmetic saving. -/
theorem critical_margin_iff (gain : ℝ) :
    lowExponent (17/48) (23/48)-gain <
      (1/2 : ℝ)+signalShift (17/48) (1/6) ↔ (3/8 : ℝ) < gain := by
  norm_num [lowExponent,signalShift]
  constructor <;> intro h <;> linarith

/-- A hypothetical full square-root saving across a row family of width
`5/6` would leave the exact positive exponent margin `1/24`. Neither
randomness nor independent row cancellation is assumed as a theorem. -/
theorem row_squareRoot_margin :
    ((1/2 : ℝ)+signalShift (17/48) (1/6))-
      (lowExponent (17/48) (23/48)-(5/6)/2)=1/24 := by
  norm_num [lowExponent,signalShift]

/-- Even perfect removal of the `Pa^(1/6)` Gram allowance only removes
the `(y-x)/12` loss after the existing Cauchy--Schwarz step. This is a
strength preflight, not a proved exceptional-frequency cancellation. -/
theorem lowExponent_sub_exceptional_loss (x y : ℝ) :
    lowExponent x y-(y-x)/12=x/2 := by
  unfold lowExponent
  ring

/-- At the published geometry that entire loss is only `1/96`. -/
theorem published_exceptional_loss :
    (((23/48 : ℝ)-(17/48))/12)=1/96 := by
  norm_num

/-- Keeping the existing source calibration, perfect exceptional removal
would leave boundary `83/96`, rather than the critical line. -/
theorem boundary_after_exceptional_removal :
    calibratedBoundary (17/48) (23/48) (1/6)-1/96=(83/96 : ℝ) := by
  rw [published_boundary]
  norm_num

/-- The hypothetical improved low exponent remains above the critical-line
signal by the explicit positive amount `35/96`. -/
theorem critical_gap_after_exceptional_removal :
    (lowExponent (17/48) (23/48)-1/96)-
      ((1/2 : ℝ)+signalShift (17/48) (1/6))=35/96 := by
  norm_num [lowExponent,signalShift]

/-- Perfect exceptional removal alone cannot close the critical-line
exponent comparison, even with no additional loss. -/
theorem no_critical_margin_after_exceptional_removal :
    ¬lowExponent (17/48) (23/48)-1/96 <
      (1/2 : ℝ)+signalShift (17/48) (1/6) := by
  norm_num [lowExponent,signalShift]

/-- A nonzero critical-line diagnostic signal still obeys that strengthened
low allowance at every scale, with the full fixed-height phase retained. -/
theorem critical_signal_admitted_after_exceptional_removal
    {Z : ℝ} (hZ : 1 ≤ Z) (gamma : ℝ) :
    ‖powerSignal (1/2) gamma (17/48) (1/6) Z‖ ≤
      Real.rpow Z (lowExponent (17/48) (23/48)-1/96) := by
  rw [norm_powerSignal (zero_lt_one.trans_le hZ)]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  norm_num [lowExponent,signalShift]

end RiemannGaussian.ZetaQuasiRHProbeCalibration
