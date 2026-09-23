/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHardyProductCertificate

/-!
# Four kernel-checked signs of actual Hardy Z

Exact rational products and one certified phase angle per sample are
combined with the complete Euler--Maclaurin expression and its analytic
remainder. These signs bracket three distinct critical-line zeros. A
separate complete count is required to exclude unseen zeros.
-/

namespace RiemannGaussian.ZetaHardySamples
open LeanCert.Core LeanCert.Engine ZetaHardyProductCertificate ZetaHardyPhase

private def cfg : DyadicConfig := {precision := -32, taylorDepth := 12}

private def angle (a : ℚ) : IntervalRat := ⟨a / 10^6, (a + 1) / 10^6, by linarith⟩

private theorem checked_fourteen : signCheck cfg 34 14 (angle 35029) false = true := by
  decide +kernel

private theorem checked_fifteen : signCheck cfg 35 15 (angle 37529) true = true := by
  decide +kernel

private theorem checked_twentyTwo : signCheck cfg 42 22 (angle 55013) false = true := by
  decide +kernel

private theorem checked_twentySix : signCheck cfg 46 26 (angle 64989) true = true := by
  decide +kernel

/-- The actual Hardy value at height fourteen is strictly negative. -/
theorem negative_fourteen : hardy 14 < 0 := by simpa using hardy_sign_of_check checked_fourteen

/-- The actual Hardy value at height fifteen is strictly positive. -/
theorem positive_fifteen : 0 < hardy 15 := by simpa using hardy_sign_of_check checked_fifteen

/-- The actual Hardy value at height twenty-two is strictly negative. -/
theorem negative_twentyTwo : hardy 22 < 0 := by simpa using hardy_sign_of_check checked_twentyTwo

/-- The actual Hardy value at height twenty-six is strictly positive. -/
theorem positive_twentySix : 0 < hardy 26 := by simpa using hardy_sign_of_check checked_twentySix

end RiemannGaussian.ZetaHardySamples
