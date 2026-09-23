/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovLiteratureIteration

/-!
# Conditioning with the prime and quotient powers coupled

The next residue bound is uniform in its literal integer tail endpoint.
This allows the prime cost and the quotient moment power to be combined
before the prime is replaced by its packet upper endpoint. The packet
therefore pays the exponent e-lambda, not e. The exact minimum tail size,
all polynomial types and the original dilation remain explicit.
-/

namespace RiemannGaussian.VinogradovPowerConditioning
noncomputable section
open scoped BigOperators
open Polynomial VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovPolynomialNonsingular VinogradovTypeMaximum VinogradovMixedDifferencing
open VinogradovLiteratureIteration

/-- Pay an integer quotient and its prime coefficient together. -/
theorem prime_quotient_le {Q p U E : ℕ} (hp : 0 < p) (hpU : p ≤ U)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (hgap : lambda ≤ (E : ℝ)) :
    (p : ℝ) ^ E * ((Q / p : ℕ) : ℝ) ^ lambda ≤
      (U : ℝ) ^ ((E : ℝ) - lambda) * (Q : ℝ) ^ lambda := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  calc
    _ ≤ (p : ℝ) ^ E * ((Q : ℝ) / p) ^ lambda :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le hlambda) (by positivity)
    _ = (p : ℝ) ^ ((E : ℝ) - lambda) * (Q : ℝ) ^ lambda := by
      rw [Real.div_rpow (Nat.cast_nonneg _) hpR.le, Real.rpow_sub hpR, Real.rpow_natCast]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hpR.le (by exact_mod_cast hpU) (sub_nonneg.mpr hgap))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- A uniform next residue estimate bounds the actual original type
count with the reduced prime exponent e-lambda. No fixed endpoint is
substituted before that cancellation. -/
theorem typeCount_le_of_power_bound {m d T e P s M U r Q Qmin q : ℕ}
    {B lambda : ℝ} {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P) (hMdeg : d + m ≤ M)
    (hT0 : 0 < T) (hT : T ≤ P ^ d) (π : Finset ℕ)
    (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ U)
    (hbudget : P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p)
    (hr1 : 1 ≤ r) (hr : r ≤ d + m) (hds : d ≤ s) (hs : 1 ≤ s)
    (hq : 0 < q) (hQ : 16 * s ^ 2 * U ≤ Q) (hmin : Qmin * U ≤ Q)
    (hB : 0 ≤ B) (hlambda : 0 ≤ lambda)
    (hgap : lambda ≤ (conditioningExponent d r s : ℝ))
    (hbound : ∀ (e' p X : ℕ) (hp : p.Prime) (G : Fin m → ℤ[X]),
      HasType G d T e' → M < p → p ≤ U → Qmin ≤ X →
      residueMixedMoment m s P (p ^ r) (pow_pos hp.pos r)
        (fullFrequency d G) (monomialTail m d p q X) ≤ B * (X : ℝ) ^ lambda) :
    (typeCount d P s F (monomialTail m d 1 q Q) : ℝ) ≤
      ((4 * π.card * d.factorial * m.factorial : ℕ) : ℝ) * B *
        (U : ℝ) ^ ((conditioningExponent d r s : ℝ) - lambda) * (Q : ℝ) ^ lambda := by
  obtain ⟨e', p, xi, hp, G, hG, hpM, hpU, _hpT, _hxi, hb⟩ :=
    VinogradovUnrestrictedConditioning.exists_conditioning_of_packet hF hm hP hMdeg
      hT0 hT π hπ hbudget hr1 hr hds hs hq hQ
  have hX : Qmin ≤ Q / p := (Nat.le_div_iff_mul_le hp.pos).mpr
    ((Nat.mul_le_mul_left Qmin hpU).trans hmin)
  have hc : (((4 * π.card * d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) *
      ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ)) =
      ((4 * π.card * d.factorial * m.factorial : ℕ) : ℝ) *
        (p : ℝ) ^ conditioningExponent d r s := by
    simp only [conditioningExponent, Nat.cast_mul, Nat.cast_pow, pow_add]
    ring
  rw [hc] at hb
  have hres := hbound e' p (Q / p) hp G hG hpM hpU hX
  calc
    _ ≤ ((4 * π.card * d.factorial * m.factorial : ℕ) : ℝ) *
        (p : ℝ) ^ conditioningExponent d r s * (B * ((Q / p : ℕ) : ℝ) ^ lambda) :=
      hb.trans (mul_le_mul_of_nonneg_left hres (by positivity))
    _ = (((4 * π.card * d.factorial * m.factorial : ℕ) : ℝ) * B) *
        ((p : ℝ) ^ conditioningExponent d r s * ((Q / p : ℕ) : ℝ) ^ lambda) := by ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (prime_quotient_le hp.pos hpU hlambda hgap)
        (mul_nonneg (Nat.cast_nonneg _) hB)

end
end RiemannGaussian.VinogradovPowerConditioning
