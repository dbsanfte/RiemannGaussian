/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePointRotation

/-!
# The second hidden branch of product colour

Equal public product colour can conceal reversal of both local signs. A
selector retaining only opposite colours can therefore exclude a useful
point even when it changes both local curve/twist choices. The numerical
certificate below is a recovery regression, not a universal coverage or
complete elliptic-group-law verification. Checked in the ordinary library; numerical probes remain optional.
-/

namespace RiemannGaussian.SemiprimeColourCoverage

open SemiprimeGroupSelection

/-- Equal product colour means either neither local sign, or both, changed.
Together with `product_colour_flip_exactly_one` this retains all four
hidden branches without claiming that any has a short period. -/
theorem product_colour_same_both_or_neither {ep eq fp fq : ℤ}
    (hep : ep = 1 ∨ ep = -1) (heq : eq = 1 ∨ eq = -1)
    (hfp : fp = 1 ∨ fp = -1) (hfq : fq = 1 ∨ fq = -1)
    (hsame : fp*fq = ep*eq) :
    (fp = ep ∧ fq = eq) ∨ (fp = -ep ∧ fq = -eq) := by
  rcases hep with rfl | rfl <;>
    rcases heq with rfl | rfl <;>
    rcases hfp with rfl | rfl <;>
    rcases hfq with rfl | rfl <;> norm_num at *

/-- The observed original and useful local sign pairs have the SAME
public product and differ on both fields. Actual Legendre evaluations
remain part of the separate known-prime diagnostic. -/
theorem same_colour_control_signs :
    (-1 : ℤ)*1 = 1*(-1) ∧ (-1 : ℤ) ≠ 1 ∧ (1 : ℤ) ≠ -1 := by
  norm_num

/-- Exact public recovery signal for the same-colour sigma-eleven point.
This proper divisor certificate does not verify the full Python algorithm. -/
theorem same_colour_control_signal :
    Nat.gcd 244150615831 10273242508 = 494191 ∧
      ProperDivisor 244150615831 494191 := by
  norm_num [ProperDivisor]

/-- This finite selector miss is a genuine semiprime at width eighty;
it is also near a square, so it is not intrinsically hard for Fermat. -/
theorem same_colour_control_semiprime :
    Nat.Prime 494041 ∧ Nat.Prime 494191 ∧
      (494041 : ℕ)*494191 = 244150615831 ∧
      79^6 < (244150615831 : ℕ) ∧ (244150615831 : ℕ) ≤ 80^6 ∧
      (494116 : ℕ)^2-75^2 = 244150615831 := by
  norm_num

end RiemannGaussian.SemiprimeColourCoverage
