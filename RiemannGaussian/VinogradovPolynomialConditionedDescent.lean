/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovRowTransport
import RiemannGaussian.VinogradovNonsingularDescent

/-!
# The original nonsingular count reaches the next polynomial type

Low-degree tail conditioning, quotient completion, endpoint deletion,
binomial row transport, the degree-modulus fibre bound and quantitative
differencing are composed on the actual original nonsingular count.
Every numerical cost and both physical endpoints are explicit.
-/

namespace RiemannGaussian.VinogradovPolynomialConditionedDescent
noncomputable section
open scoped BigOperators Classical
open Polynomial VinogradovMeanValue VinogradovPolynomialSystems
open VinogradovPolynomialDifferencing VinogradovPolynomialNonsingular
open VinogradovMixedDifferencing VinogradovMixedMoments
open VinogradovBinomialRows VinogradovResidueEndpoint VinogradovRowTransport

/-- The original nonsingular count enters the literal residue mixed
moment at `floor(Q/p)`, with every conditioning and endpoint cost proved.
The selected polynomial system is the exact binomial transform of the
original one and has the same type parameters. -/
theorem exists_conditioning {p m d r T e s : ℕ} [Fact p.Prime]
    (hpdeg : d + m < p) (hp2 : 2 < p) (hpT : ¬p ∣ T)
    (hr1 : 1 ≤ r) (hr : r ≤ d + m) (hds : d ≤ s) (hs : 1 ≤ s)
    {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (P Q q : ℕ) (hq : 0 < q) (hQ : 16 * s ^ 2 ≤ Q / p) :
    ∃ xi : ℕ, xi < p ∧ HasType (rowSystem d (shiftAmount p q xi) F) d T e ∧
      (nonsingularCount p m d P s F (monomialTail m d 1 q Q) : ℝ) ≤
        ((2 * d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) *
          ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) *
            residueMixedMoment m s P (p ^ r) (pow_pos (Fact.out : p.Prime).pos r)
              (fullFrequency d (rowSystem d (shiftAmount p q xi) F))
              (monomialTail m d p q (Q / p)) := by
  obtain ⟨xi, hxi, hbound⟩ := exists_floor_tail_bound (by omega : d < p) hds hs m P Q q hq hQ F
  have hG := hasType_rowSystem hF (shiftAmount p q xi)
  refine ⟨xi, hxi, hG, ?_⟩
  rw [shifted_mixedMoment_eq_count] at hbound
  have hc := prime_dilated_count_le hpdeg hp2 hpT hr1 hr hG P (Q / p) q s
  have he := hbound.trans (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _))
  simpa only [mul_assoc] using he

/-- The original nonsingular count reaches an attained lower-degree
polynomial system, with the required quotient tail endpoint and every
constant evaluated. No analytic bound is assumed along this chain.
The unrestricted entry point is supplied separately in
`VinogradovUnrestrictedConditioning`; controlled iteration remains open. -/
theorem exists_descent {p m d r T e s : ℕ} [Fact p.Prime]
    (hm : 1 ≤ m) (hpdeg : d + (m + 1) < p) (hp2 : 2 < p) (hpT : ¬p ∣ T)
    (hr1 : 1 ≤ r) (hr : r ≤ d + (m + 1)) (hds : d ≤ s) (hs : 1 ≤ s)
    {F : Fin (m + 1) → ℤ[X]} (hF : HasType F d T e)
    (P Q q : ℕ) (hq : 0 < q) (hP : p ^ r ≤ P) (hQ : 16 * s ^ 2 ≤ Q / p) :
    ∃ (xi h T' : ℕ) (G : Fin m → ℤ[X]),
      xi < p ∧ 1 ≤ h ∧ h ≤ P / p ^ r ∧ T' = (h * p ^ r) * T ∧ T ≤ T' ∧ T' ≤ P * T ∧
      G = (fun j => difference ((h * p ^ r : ℕ) : ℤ)
        ((rowSystem d (shiftAmount p q xi) F) j.succ)) ∧
      HasType G (d + 1) T' e ∧
      (nonsingularCount p (m + 1) d P s F (monomialTail (m + 1) d 1 q Q) : ℝ) ≤
        ((2 * d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) *
          ((p ^ ((r - d) * (r - d - 1) / 2) * (m + 1).factorial : ℕ) : ℝ) *
            max ((2 * ((m + 1 : ℕ) : ℝ) * P) ^ (m + 1) * meanValue s (d + (m + 1)) (Q / p))
              (2 * (2 * (P / p ^ r : ℕ)) ^ (m + 1) *
                (mixedMoment m s (fun x : Fin P => nextFrequency d G (x.val + 1))
                  (monomialTail (m + 1) d p q (Q / p)) ^ (((m : ℝ) + 1) / (2 * (m : ℝ))) *
                meanValue s (d + (m + 1)) (Q / p) ^ (((m : ℝ) - 1) / (2 * (m : ℝ))))) := by
  obtain ⟨xi, hxi, hbound⟩ :=
    exists_floor_tail_bound (by omega : d < p) hds hs (m + 1) P Q q hq hQ F
  have hG := hasType_rowSystem hF (shiftAmount p q xi)
  obtain ⟨h, T', G, hh, hHP, heT, hlo, hhi, heG, htype, hc⟩ :=
    VinogradovNonsingularDescent.exists_nonsingular_descent hm hpdeg hp2 hpT hr1 hr
      hG P (Q / p) q s hq hP
  refine ⟨xi, h, T', G, hxi, hh, hHP, heT, hlo, hhi, heG, htype, ?_⟩
  rw [shifted_mixedMoment_eq_count] at hbound
  have he := hbound.trans (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _))
  simpa only [mul_assoc] using he

end
end RiemannGaussian.VinogradovPolynomialConditionedDescent
