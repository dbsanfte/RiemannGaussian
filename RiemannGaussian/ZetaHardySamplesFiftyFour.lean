/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHardyBatchData

/-!
# Eight further kernel-checked signs of actual Hardy Z

The same fully checked eighty-term cache supplies all samples. Every sign
check includes its Gamma rotation, angle bracket, actual sample geometry
and the complete analytic error. Completeness is proved separately.
-/

namespace RiemannGaussian.ZetaHardySamplesFiftyFour
open ZetaHardyBatchData ZetaHardyPhase

private theorem checked_thirtyOne : signCheck 31 77441 false = true := by
  decide +kernel

private theorem checked_thirtyFour : signCheck 34 84901 true = true := by
  decide +kernel

private theorem checked_thirtyEight : signCheck 38 94833 false = true := by
  decide +kernel

private theorem checked_fortyTwo : signCheck 42 104746 true = true := by
  decide +kernel

private theorem checked_fortyFour : signCheck 44 109695 false = true := by
  decide +kernel

private theorem checked_fortyNine : signCheck 49 122043 true = true := by
  decide +kernel

private theorem checked_fiftyOne : signCheck 51 126972 false = true := by
  decide +kernel

private theorem checked_fiftyFour : signCheck 54 134354 true = true := by
  decide +kernel

/-- The actual Hardy value at height 31 is strictly negative. -/
theorem negative_thirtyOne : hardy 31 < 0 := by
  simpa using hardy_sign_of_check (by norm_num) checked_thirtyOne

/-- The actual Hardy value at height 34 is strictly positive. -/
theorem positive_thirtyFour : 0 < hardy 34 := by
  simpa using hardy_sign_of_check (by norm_num) checked_thirtyFour

/-- The actual Hardy value at height 38 is strictly negative. -/
theorem negative_thirtyEight : hardy 38 < 0 := by
  simpa using hardy_sign_of_check (by norm_num) checked_thirtyEight

/-- The actual Hardy value at height 42 is strictly positive. -/
theorem positive_fortyTwo : 0 < hardy 42 := by
  simpa using hardy_sign_of_check (by norm_num) checked_fortyTwo

/-- The actual Hardy value at height 44 is strictly negative. -/
theorem negative_fortyFour : hardy 44 < 0 := by
  simpa using hardy_sign_of_check (by norm_num) checked_fortyFour

/-- The actual Hardy value at height 49 is strictly positive. -/
theorem positive_fortyNine : 0 < hardy 49 := by
  simpa using hardy_sign_of_check (by norm_num) checked_fortyNine

/-- The actual Hardy value at height 51 is strictly negative. -/
theorem negative_fiftyOne : hardy 51 < 0 := by
  simpa using hardy_sign_of_check (by norm_num) checked_fiftyOne

/-- The actual Hardy value at height 54 is strictly positive. -/
theorem positive_fiftyFour : 0 < hardy 54 := by
  simpa using hardy_sign_of_check (by norm_num) checked_fiftyFour

end RiemannGaussian.ZetaHardySamplesFiftyFour
