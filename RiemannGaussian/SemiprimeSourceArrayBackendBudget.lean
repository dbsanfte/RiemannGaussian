/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceProgramStorage

/-! # Numeric envelope for the executed source-array backend
This isolates monotonic resource substitution from all source syntax and interpreter
terms. The two summands are exactly the acquisition and bit-work bounds.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceArrayBackendBudget
open SemiprimeReportPolynomialGrowth

/-- Sum of the actual coefficient backend's two displayed work bounds. -/
def envelope (M T V b : ℕ) : ℕ :=
  M*(8*(b+1)+16)+1+T*(8*(V+1)+17)+1+2*(b+1)+5+4*(V+1)+10+
    (T*(SemiprimeSourceProgramBits.stepBudget V (b+1) (V+1)+3)+1+
      (V+1)*(8*(b+1)+15*(V+1)+30)+2)

/-- Monotonicity uses only four independent natural-number resources. -/
theorem envelope_mono {M T V b M' T' V' b' : ℕ}
    (hM : M ≤ M') (hT : T ≤ T') (hV : V ≤ V') (hb : b ≤ b') :
    envelope M T V b ≤ envelope M' T' V' b' := by
  unfold envelope SemiprimeSourceProgramBits.stepBudget
  gcongr

/-- The diagonal has fixed monomial growth, with input-independent constants. -/
theorem diagonal_monomial : ∃ C k : ℕ, ∀ S, envelope S S S S ≤ C*(S+1)^k := by
  change Bound (fun S => envelope S S S S)
  simp only [envelope, SemiprimeSourceProgramBits.stepBudget]
  boundArithmetic

end RiemannGaussian.SemiprimeSourceArrayBackendBudget
