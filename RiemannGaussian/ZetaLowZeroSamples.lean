/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaEulerMaclaurinValue

/-!
# Two actual zeta value certificates for low-zero isolation

Both inequalities are checked against the complete Euler--Maclaurin
expression and its proved error. The decimal center is an exact rational
candidate; its proximity to a zero is a conclusion of the subsequent
isolation argument, not an assumption in either computation.
-/

namespace RiemannGaussian.ZetaLowZeroSamples
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaEulerMaclaurinValue

/-- Precision used for both literal complex value checks. -/
def config : DyadicConfig := {precision := -50, taylorDepth := 24}

/-- Exact rational ordinate proposed for the isolating disc. -/
def ordinate : ℚ := 14134725141735 / 10 ^ 12

/-- Real displacement used to estimate the derivative. -/
def step : ℚ := 1 / 1000000

/-- The rational candidate center on the critical line. -/
noncomputable def center : ℂ := (1 / 2 : ℂ) + (ordinate : ℂ) * Complex.I

/-- A rational approximate derivative; no derivative value is assumed. -/
noncomputable def slope : ℂ := (3 / 4 : ℂ) + (1 / 8 : ℂ) * Complex.I

/-- Kernel-checked small residual at the candidate center. -/
theorem center_check : closeCheck config 34
    (rational config.precision (1 / 2) ordinate) 0 0 (1 / 10 ^ 8) = true := by
  decide +kernel

/-- Kernel-checked nearby value, relative to the proposed affine slope. -/
theorem step_check : closeCheck config 34
    (rational config.precision (1 / 2 + step) ordinate)
    ((3 / 4) * step) ((1 / 8) * step) (1 / 20000000) = true := by
  decide +kernel


end RiemannGaussian.ZetaLowZeroSamples
