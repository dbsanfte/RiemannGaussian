/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordScales
import RiemannGaussian.VinogradovPowerConditioning

/-!
# The quantitative mixed step at Ford's original scales

The prime coefficient and the actual quotient source moment are kept
coupled. Ford's original scale inequality then removes every residual
power of the physical endpoint from the off-diagonal branch. Finite
packet width, factorial costs and the next coefficient remain explicit.
-/

namespace RiemannGaussian.VinogradovFordStep
noncomputable section
open scoped BigOperators
open Polynomial VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovPolynomialNonsingular VinogradovTypeMaximum VinogradovMixedDifferencing
open VinogradovMeanValue VinogradovLiteratureIteration VinogradovLiteratureStep
open VinogradovFordScales VinogradovPowerConditioning

/-- The normalized exponent inequality pays the full off-diagonal power
by the selected prime, including the shrinking Holder exponent. -/
theorem scale_power_le {m r : ℕ} (hm : 0 < m) {P p phi psi g : ℝ}
    (hP : 1 ≤ P) (hp : P ^ phi ≤ p)
    (hbalance : 1 / 2 - r * phi + g / (2 * (m : ℝ)) * psi ≤ 0) :
    P ^ (((m : ℝ) + psi * g) * (((m : ℝ) + 1) / (2 * (m : ℝ)))) ≤
      p ^ (r * (m + 1)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hP0 : 0 < P := by linarith
  have hbal : 1 / 2 + g * psi / (2 * (m : ℝ)) ≤ r * phi := by
    have he : g / (2 * (m : ℝ)) * psi = g * psi / (2 * (m : ℝ)) := by ring
    rw [he] at hbalance
    linarith
  have hmul := mul_le_mul_of_nonneg_left hbal (show 0 ≤ 2 * (m : ℝ) by positivity)
  have he : 2 * (m : ℝ) * (1 / 2 + g * psi / (2 * (m : ℝ))) = m + psi * g := by
    field_simp
  rw [he] at hmul
  have hexp : ((m : ℝ) + psi * g) * (((m : ℝ) + 1) / (2 * (m : ℝ))) ≤
      phi * ((r * (m + 1) : ℕ) : ℝ) := by
    calc
      _ ≤ (2 * (m : ℝ) * (r * phi)) * (((m : ℝ) + 1) / (2 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_right hmul (by positivity)
      _ = _ := by push_cast; field_simp
  calc
    _ ≤ P ^ (phi * ((r * (m + 1) : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hP hexp
    _ = (P ^ phi) ^ (r * (m + 1)) := by rw [Real.rpow_mul hP0.le, Real.rpow_natCast]
    _ ≤ _ := pow_le_pow_left₀ (Real.rpow_nonneg hP0.le _) hp _

/-- The entire mixed off-diagonal term loses its physical-endpoint
power at an admissible scale. The surviving coefficient is explicit. -/
theorem mixed_term_le {m r : ℕ} (hm : 1 ≤ m)
    {P p U C B A eta Q lambda phi psi g : ℝ}
    (hP : 1 ≤ P) (hp : 0 < p) (hU : 0 ≤ U) (hC : 0 < C) (hB : 0 ≤ B)
    (hA : 0 ≤ A) (heta : 0 < eta) (hQ : 0 < Q)
    (hg : 0 ≤ g) (hprime : P ^ phi ≤ p) (hpacket : U ≤ eta * P ^ psi)
    (hbalance : 1 / 2 - r * phi + g / (2 * (m : ℝ)) * psi ≤ 0) :
    (2 / p ^ (r * (m + 1))) *
      (C * Q ^ lambda) ^ (((m : ℝ) - 1) / (2 * (m : ℝ))) *
      (A * (C * B * P ^ m) * U ^ g * Q ^ lambda) ^
        (((m : ℝ) + 1) / (2 * (m : ℝ))) ≤
      2 * (A * B * eta ^ g) ^ (((m : ℝ) + 1) / (2 * (m : ℝ))) * C * Q ^ lambda := by
  let alpha : ℝ := ((m : ℝ) + 1) / (2 * (m : ℝ))
  let beta : ℝ := ((m : ℝ) - 1) / (2 * (m : ℝ))
  let S : ℝ := C * Q ^ lambda
  let H : ℝ := A * B * eta ^ g
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hP0 : 0 < P := by linarith
  have hS : 0 < S := mul_pos hC (Real.rpow_pos_of_pos hQ _)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have ha : 0 ≤ alpha := by dsimp [alpha]; positivity
  have hab : beta + alpha = 1 := by dsimp [alpha, beta]; field_simp; ring
  have hpow := Real.rpow_le_rpow hU hpacket hg
  rw [Real.mul_rpow heta.le (Real.rpow_nonneg hP0.le _), ← Real.rpow_mul hP0.le] at hpow
  have hinside : A * (C * B * P ^ m) * U ^ g * Q ^ lambda ≤
      S * H * P ^ ((m : ℝ) + psi * g) := by
    calc
      _ ≤ A * (C * B * P ^ m) * (eta ^ g * P ^ (psi * g)) * Q ^ lambda := by gcongr
      _ = _ := by
        rw [Real.rpow_add hP0, Real.rpow_natCast]
        dsimp [S, H]
        ring
  have hfactor : S ^ beta * (S * H * P ^ ((m : ℝ) + psi * g)) ^ alpha =
      S * H ^ alpha * P ^ (((m : ℝ) + psi * g) * alpha) := by
    rw [Real.mul_rpow (mul_nonneg hS.le hH) (Real.rpow_nonneg hP0.le _),
      Real.mul_rpow hS.le hH, ← Real.rpow_mul hP0.le]
    calc
      _ = (S ^ beta * S ^ alpha) * H ^ alpha * P ^ (((m : ℝ) + psi * g) * alpha) := by ring
      _ = _ := by rw [← Real.rpow_add hS, hab, Real.rpow_one]
  have hscale := scale_power_le (m := m) (r := r) (by omega) hP hprime hbalance
  change _ ≤ 2 * H ^ alpha * C * Q ^ lambda
  calc
    _ ≤ (2 / p ^ (r * (m + 1))) * S ^ beta *
        (S * H * P ^ ((m : ℝ) + psi * g)) ^ alpha := by
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hinside ha) (by positivity)
    _ = (2 / p ^ (r * (m + 1))) * (S * H ^ alpha * P ^ (((m : ℝ) + psi * g) * alpha)) := by
      rw [mul_assoc, hfactor]
    _ ≤ (2 / p ^ (r * (m + 1))) * (S * H ^ alpha * p ^ (r * (m + 1))) := by
      gcongr
    _ = _ := by
      dsimp [S]
      field_simp

/-- One backward step for the actual residue mixed moment at admissible
scales. The coefficient is independent of P and Q: all residual physical
endpoint powers have been paid by the chosen prime. -/
theorem backward_power_step {m d T e P s M U r Q Qmin p q : ℕ}
    {C B lambda phi psi eta : ℝ} {F : Fin (m + 1) → ℤ[X]}
    (hF : HasType F d T e) (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P)
    (hMdeg : d + 1 + m ≤ M) (hT0 : 0 < T) (hT : T ≤ P ^ d)
    (π : Finset ℕ) (hπ : ∀ p' ∈ π, p'.Prime ∧ M < p' ∧ p' ≤ U)
    (hbudget : P ^ (d + 1 + 2 * m.choose 2) < ∏ p' ∈ π, p')
    (hr1 : 1 ≤ r) (hr : r ≤ d + 1 + m) (hds : d + 1 ≤ s) (hs : 1 ≤ s)
    (hp : 0 < p) (hq : 0 < q) (hQ1 : 1 ≤ Q)
    (hQ : 16 * s ^ 2 * U ≤ Q) (hmin : Qmin * U ≤ Q)
    (hC : 0 < C) (hB : 0 ≤ B) (hlambda : 0 ≤ lambda) (heta : 0 < eta)
    (hgap : lambda ≤ (conditioningExponent (d + 1) r s : ℝ))
    (hprime : (P : ℝ) ^ phi ≤ p) (hpacket : (U : ℝ) ≤ eta * (P : ℝ) ^ psi)
    (hbalance : 1 / 2 - r * phi +
      ((conditioningExponent (d + 1) r s : ℝ) - lambda) / (2 * (m : ℝ)) * psi ≤ 0)
    (hsource : meanValue s (d + (m + 1)) Q ≤ C * (Q : ℝ) ^ lambda)
    (hbound : ∀ (T' e' p' q' X : ℕ) (hp' : p'.Prime) (G : Fin m → ℤ[X]),
      0 < T' → T' ≤ P ^ (d + 1) → HasType G (d + 1) T' e' →
      M < p' → p' ≤ U → 0 < q' → Qmin ≤ X →
      residueMixedMoment m s P (p' ^ r) (pow_pos hp'.pos r)
        (fullFrequency (d + 1) G) (monomialTail m (d + 1) p' q' X) ≤
          C * B * (P : ℝ) ^ m * (X : ℝ) ^ lambda) :
    residueMixedMoment (m + 1) s P (p ^ r) (pow_pos hp r)
      (fullFrequency d F) (monomialTail (m + 1) d p q Q) ≤
      C * (2 ^ (m + 1) *
        max (((d + (m + 1) : ℕ) : ℝ) ^ (m + 1))
          (2 * (((4 * π.card * (d + 1).factorial * m.factorial : ℕ) : ℝ) *
            B * eta ^ ((conditioningExponent (d + 1) r s : ℝ) - lambda)) ^
              (((m : ℝ) + 1) / (2 * (m : ℝ))))) *
                (P : ℝ) ^ (m + 1) * (Q : ℝ) ^ lambda := by
  have hPpos : 1 ≤ P := by
    have hmpos : 0 < 4 * m ^ 4 := by positivity
    omega
  obtain ⟨T', G, hlo, hhi, hG, hb⟩ :=
    exists_difference_step (by omega) hF s P Q p q r hp hq hPpos
  have hT' : T' ≤ P ^ (d + 1) := by
    rw [pow_succ, mul_comm]
    exact hhi.trans (Nat.mul_le_mul_left P hT)
  have hT'0 : 0 < T' := lt_of_lt_of_le hT0 hlo
  have hcount := typeCount_le_of_power_bound hG hm hP hMdeg hT'0 hT' π hπ hbudget
    hr1 hr hds hs (Nat.mul_pos hp hq) hQ hmin
    (show 0 ≤ C * B * (P : ℝ) ^ m by positivity) hlambda hgap
    (fun e' p' X hp' H hH hpM hpU hX =>
      hbound T' e' p' (p * q) X hp' H hT'0 hT' hH hpM hpU (Nat.mul_pos hp hq) hX)
  let A : ℝ := ((4 * π.card * (d + 1).factorial * m.factorial : ℕ) : ℝ)
  let alpha : ℝ := ((m : ℝ) + 1) / (2 * (m : ℝ))
  let beta : ℝ := ((m : ℝ) - 1) / (2 * (m : ℝ))
  let gap : ℝ := (conditioningExponent (d + 1) r s : ℝ) - lambda
  let cost : ℝ := 2 * (A * B * eta ^ gap) ^ alpha
  have hJ0 : 0 ≤ meanValue s (d + (m + 1)) Q :=
    MeasureTheory.integral_nonneg (fun _ => by positivity)
  have ha : 0 ≤ alpha := by dsimp [alpha]; positivity
  have hbeta : 0 ≤ beta := by
    dsimp [beta]
    apply div_nonneg _ (by positivity)
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hoff : (2 / (p : ℝ) ^ (r * (m + 1))) *
      meanValue s (d + (m + 1)) Q ^ beta *
      (typeCount (d + 1) P s G (monomialTail m (d + 1) 1 (p * q) Q) : ℝ) ^ alpha ≤
        cost * (C * (Q : ℝ) ^ lambda) := by
    calc
      _ ≤ (2 / (p : ℝ) ^ (r * (m + 1))) *
          (C * (Q : ℝ) ^ lambda) ^ beta *
          (A * (C * B * (P : ℝ) ^ m) * (U : ℝ) ^ gap * (Q : ℝ) ^ lambda) ^ alpha := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hJ0 hsource hbeta) (by positivity)
        · exact Real.rpow_le_rpow (Nat.cast_nonneg _) hcount ha
        · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
        · positivity
      _ ≤ _ := by
        simpa only [cost, mul_assoc] using mixed_term_le (m := m) (r := r) (by omega)
          (by exact_mod_cast hPpos) (by exact_mod_cast hp) (Nat.cast_nonneg U)
          hC hB (Nat.cast_nonneg _) heta (by exact_mod_cast (show 0 < Q by omega))
          (sub_nonneg.mpr hgap) hprime hpacket hbalance
  apply hb.trans
  calc
    _ ≤ (2 * (P : ℝ)) ^ (m + 1) *
        max ((((d + (m + 1) : ℕ) : ℝ) ^ (m + 1)) * (C * (Q : ℝ) ^ lambda))
          (cost * (C * (Q : ℝ) ^ lambda)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact max_le_max (mul_le_mul_of_nonneg_left hsource (by positivity)) hoff
    _ = _ := by
      rw [← max_mul_of_nonneg _ _ (show 0 ≤ C * (Q : ℝ) ^ lambda by positivity), mul_pow]
      dsimp [cost, A, alpha, gap]
      ring

end
end RiemannGaussian.VinogradovFordStep
