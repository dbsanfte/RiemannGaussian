/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import RiemannGaussian.MontgomeryVaughan.Eigen
import RiemannGaussian.MontgomeryVaughan.Duality

/-!
# The Montgomery–Vaughan weighted Hilbert inequality

`eigen_bound` (`RiemannGaussian/MontgomeryVaughan/Eigen.lean`) is exactly `EigenBound 13`; the spectral reduction of
`Duality.lean` turns it into `MVDiag 13` and, via polarization
(`RiemannGaussian/MontgomeryVaughan.lean`), into the explicit bilinear theorem
`MVHilbert 26`.
-/

noncomputable section

namespace RiemannGaussian
namespace MontgomeryVaughan

theorem eigenBound_thirteen : EigenBound 13 :=
  fun _ι _ _ _freq _δ h u hu μ heig => eigen_bound h u hu μ heig

/-- **`MVDiag 13`** — the weighted Hilbert inequality, literature (diagonal) form. -/
theorem mvDiag_thirteen : MVDiag 13 := mvDiag_of_eigenBound eigenBound_thirteen

/-- **Bilinear Montgomery--Vaughan with explicit constant `26`.** -/
theorem mvHilbert_twentySix : MVHilbert 26 := by
  convert MVHilbert_of_diag (C := 13) (by norm_num) mvDiag_thirteen using 1
  norm_num

/-- **H-MV:** `∃ C > 0, MVHilbert C`. -/
theorem mv_hilbert : ∃ C : ℝ, 0 < C ∧ MVHilbert C :=
  ⟨26, by norm_num, mvHilbert_twentySix⟩

end MontgomeryVaughan
end RiemannGaussian

end
