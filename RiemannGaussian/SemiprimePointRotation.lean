/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeGroupCoverage

/-!
# Public point rotation and its rough-prime limitation

Homogeneous Montgomery colour needs no coordinate inversion. A projected
point in a prime-order quotient is either the identity or has that same
prime order, so changing points cannot shorten a nonidentity rough-prime
period. Two exact GCD certificates replay point-rotation recoveries on the
previous finite-menu failures. This does not certify the complete elliptic
group law, the recorded curve cardinalities, or universal sixth-root time.
This side-investigation algebra is checked in the ordinary library; numerical probes remain optional.
-/

namespace RiemannGaussian.SemiprimePointRotation

open SemiprimeRoughProjection SemiprimeGroupSelection

/-- Affine right-hand side of a Montgomery model. -/
def montgomeryRhs {K : Type*} [CommRing K] (A x : K) : K :=
  x^3 + A*x^2 + x

/-- Homogeneous colour polynomial; evaluating this avoids X/Z. -/
def homogeneousColour {K : Type*} [CommRing K] (A X Z : K) : K :=
  X*Z*(X^2+A*X*Z+Z^2)

theorem homogeneousColour_eq_scaled_rhs {K : Type*} [Field K]
    (A X Z : K) (hZ : Z ≠ 0) :
    homogeneousColour A X Z = montgomeryRhs A (X/Z)*Z^4 := by
  unfold homogeneousColour montgomeryRhs
  field_simp

/-- A quadratic multiplicative colour is unchanged by the homogeneous
fourth-power rescaling. The character premise is explicit. -/
theorem homogeneousColour_character {K S : Type*} [Field K] [Monoid S]
    (χ : K →* S) (A X Z : K) (hZ : Z ≠ 0) (hχ : χ (Z^2) = 1) :
    χ (homogeneousColour A X Z) = χ (montgomeryRhs A (X/Z)) := by
  rw [homogeneousColour_eq_scaled_rhs A X Z hZ, map_mul]
  have he : Z^4 = (Z^2)^2 := by ring
  rw [he, map_pow, hχ, one_pow, mul_one]

/-- Reversing the publicly available product colour flips exactly one
local colour. No individual prime character is queried by this identity. -/
theorem product_colour_flip_exactly_one {ep eq fp fq : ℤ}
    (hep : ep = 1 ∨ ep = -1) (heq : eq = 1 ∨ eq = -1)
    (hfp : fp = 1 ∨ fp = -1) (hfq : fq = 1 ∨ fq = -1)
    (hflip : fp*fq = -(ep*eq)) :
    (fp = -ep ∧ fq = eq) ∨ (fp = ep ∧ fq = -eq) := by
  rcases hep with rfl | rfl <;>
    rcases heq with rfl | rfl <;>
    rcases hfp with rfl | rfl <;>
    rcases hfq with rfl | rfl <;> norm_num at *

/-- Changing the point inside a projected prime-order population gives
only identity or the same prime period. It cannot produce a smaller
nonidentity period within that population. -/
theorem projected_prime_dichotomy {G : Type*} [Group G] (a : G)
    {h ℓ E : ℕ} (hh : 0 < h) (hℓ : ℓ.Prime)
    (ha : orderOf a ∣ h*ℓ) (hE : h ∣ E) :
    a^E = 1 ∨ orderOf (a^E) = ℓ := by
  have hd := partial_projection_order_dvd a hh ha hE
  rcases (Nat.dvd_prime hℓ).mp hd with hone | hprime
  · exact Or.inl (orderOf_eq_one_iff.mp hone)
  · exact Or.inr hprime

theorem projected_prime_order_of_ne_one {G : Type*} [Group G] (a : G)
    {h ℓ E : ℕ} (hh : 0 < h) (hℓ : ℓ.Prime)
    (ha : orderOf a ∣ h*ℓ) (hE : h ∣ E) (hne : a^E ≠ 1) :
    orderOf (a^E) = ℓ := by
  exact (projected_prime_dichotomy a hh hℓ ha hE).resolve_left hne

/-- No positive short closure exists in a nonidentity large-prime
projected population. This statement is uniform over all starting points. -/
theorem projected_prime_no_short_power {G : Type*} [Group G] (a : G)
    {h ℓ E d : ℕ} (hh : 0 < h) (hℓ : ℓ.Prime)
    (ha : orderOf a ∣ h*ℓ) (hE : h ∣ E) (hne : a^E ≠ 1)
    (hd : 0 < d) (hdℓ : d < ℓ) : (a^E)^d ≠ 1 := by
  intro he
  have hdvd := orderOf_dvd_of_pow_eq_one he
  rw [projected_prime_order_of_ne_one a hh hℓ ha hE hne] at hdvd
  exact (Nat.not_dvd_of_pos_of_lt hd hdℓ) hdvd

/-- Both Montgomery x-coordinate orientations miss when the projected
prime period exceeds the entire B-by-B cover, including its sum edge. -/
theorem projected_prime_no_two_orientation_cover {G : Type*} [Group G]
    (a : G) {h ℓ E B j i : ℕ} (hh : 0 < h) (hℓ : ℓ.Prime)
    (ha : orderOf a ∣ h*ℓ) (hE : h ∣ E) (hne : a^E ≠ 1)
    (hlarge : B^2+B < ℓ)
    (hj : 1 ≤ j) (hjB : j ≤ B) (hi : i < B) :
    (a^E)^(B*j) ≠ (a^E)^i ∧ (a^E)^(B*j)*(a^E)^i ≠ 1 := by
  have hBj : B ≤ B*j := by nlinarith
  have hile : i ≤ B*j := by omega
  have hdiff : 0 < B*j-i := by omega
  have hprod : B*j ≤ B^2 := by nlinarith
  have hdiffℓ : B*j-i < ℓ := by omega
  have hsum : 0 < B*j+i := by omega
  have hsumℓ : B*j+i < ℓ := by omega
  constructor
  · intro he
    have hz : (a^E)^(B*j-i) = 1 := by
      apply mul_right_cancel (b := (a^E)^i)
      rw [← pow_add, Nat.sub_add_cancel hile, he, one_mul]
    exact projected_prime_no_short_power a hh hℓ ha hE hne hdiff hdiffℓ hz
  · rw [← pow_add]
    exact projected_prime_no_short_power a hh hℓ ha hE hne hsum hsumℓ

/-- The two observed large-prime channels for sigma seven on the
separated control. These numerical constants are prime and beyond the
cover. Curve-order interpretation requires the separate finite-field audit. -/
theorem separated_rough_channels :
    Nat.Prime 25469 ∧ Nat.Prime 16963 ∧
      61^2+61 < (25469 : ℕ) ∧ 61^2+61 < (16963 : ℕ) := by
  norm_num

/-- Replay the sigma-eleven, affine-x-three proper-factor certificate. -/
theorem first_control_point_signal :
    Nat.gcd 62108022589 2497552906 = 248909 ∧
      ProperDivisor 62108022589 248909 := by
  norm_num [ProperDivisor]

/-- Replay the sigma-six, affine-x-two proper-factor certificate. -/
theorem separated_control_point_signal :
    Nat.gcd 46840800959 21203535748 = 203653 ∧
      ProperDivisor 46840800959 203653 := by
  norm_num [ProperDivisor]

/-- Arithmetic characteristics of the new public-menu miss. This checks
the semiprime and sixth-root budget, not the Python control flow. -/
theorem point_menu_miss_semiprime_and_budget :
    Nat.Prime 252983 ∧ Nat.Prime 283573 ∧
      (252983 : ℕ)*283573 = 71739148259 ∧
      64^6 < (71739148259 : ℕ) ∧ (71739148259 : ℕ) ≤ 65^6 ∧
      65^2 < (252983 : ℕ) ∧ 65^2 < (283573 : ℕ) := by
  norm_num

/-- The public colour-selected fallback recovers a factor on the input
missed by the fixed seven-point palette. This certifies the GCD signal;
it does not assert universal coverage of colour selection. -/
theorem colour_selected_new_control_signal :
    Nat.gcd 71739148259 38765850005 = 252983 ∧
      ProperDivisor 71739148259 252983 := by
  norm_num [ProperDivisor]

end RiemannGaussian.SemiprimePointRotation
