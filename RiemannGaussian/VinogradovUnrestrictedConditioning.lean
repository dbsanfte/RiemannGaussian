/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPolynomialPrimeTransfer

/-!
# The full original type count enters the conditioned residue moment

Compose the attained type maximum, two-sided repeated-tuple absorption,
one eligible separating prime, original tail conditioning, endpoint
deletion, row transport and the modular fibre bound. Every numerical cost
is explicit. The general interface accepts any actual finite prime packet
with the full discriminant product budget. Its original specialization
retains the proved Bertrand endpoint `2^R*M`.
-/

namespace RiemannGaussian.VinogradovUnrestrictedConditioning
noncomputable section
open scoped BigOperators
open Polynomial VinogradovPolynomialSystems VinogradovPolynomialDifferencing
open VinogradovTypeMaximum VinogradovPolynomialPrimeTransfer
open VinogradovPolynomialNonsingular VinogradovMixedDifferencing
open VinogradovBinomialRows VinogradovRowTransport

/-- The unrestricted original count reaches the conditioned residue
moment using any actual prime packet with the displayed product budget.
Its full cardinality and upper endpoint remain in the numerical costs. -/
theorem exists_conditioning_of_packet {m d T e P s M U r Q q : ℕ}
    {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P) (hMdeg : d + m ≤ M)
    (hT0 : 0 < T) (hT : T ≤ P ^ d) (π : Finset ℕ)
    (hπ : ∀ p ∈ π, p.Prime ∧ M < p ∧ p ≤ U)
    (hbudget : P ^ (d + 2 * m.choose 2) < ∏ p ∈ π, p)
    (hr1 : 1 ≤ r) (hr : r ≤ d + m) (hds : d ≤ s) (hs : 1 ≤ s)
    (hq : 0 < q) (hQ : 16 * s ^ 2 * U ≤ Q) :
    ∃ (e' p xi : ℕ) (hp : p.Prime) (G : Fin m → ℤ[X]),
      HasType G d T e' ∧ M < p ∧ p ≤ U ∧ ¬p ∣ T ∧ xi < p ∧
      (typeCount d P s F (monomialTail m d 1 q Q) : ℝ) ≤
        ((4 * π.card * d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) *
          ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) *
            residueMixedMoment m s P (p ^ r) (pow_pos hp.pos r)
              (fullFrequency d G) (monomialTail m d p q (Q / p)) := by
  obtain ⟨e', p, H, hH, hp, hpM, hpU, hpT, hcount⟩ :=
    exists_prime_carrying_count_of_packet hF hm hP hT0 hT π hπ hbudget
      (monomialTail m d 1 q Q)
  let : Fact p.Prime := ⟨hp⟩
  have hfloor : 16 * s ^ 2 ≤ Q / p := (Nat.le_div_iff_mul_le hp.pos).mpr
    ((Nat.mul_le_mul_left (16 * s ^ 2) hpU).trans hQ)
  obtain ⟨xi, hxi, hG, hcondition⟩ :=
    VinogradovPolynomialConditionedDescent.exists_conditioning
      (by omega : d + m < p) (by omega : 2 < p) hpT hr1 hr hds hs hH P Q q hq hfloor
  refine ⟨e', p, xi, hp, rowSystem d (shiftAmount p q xi) H,
    hG, hpM, hpU, hpT, hxi, ?_⟩
  have hc : (typeCount d P s F (monomialTail m d 1 q Q) : ℝ) ≤
      ((2 * π.card : ℕ) : ℝ) * (nonsingularCount p m d P s H (monomialTail m d 1 q Q) : ℝ) := by
    exact_mod_cast hcount
  have h := hc.trans (mul_le_mul_of_nonneg_left hcondition (Nat.cast_nonneg (2 * π.card)))
  convert h using 1 <;> try rfl
  push_cast
  ring


/-- The complete unrestricted original mixed count reaches an actual
residue mixed moment of the same type, with one eligible prime, the
quotient endpoint, and the fully paid coefficient `4*R*d!*m!*p^...`.
The displayed packet and endpoint size conditions are explicit. -/
theorem exists_conditioning {m d T e P s M R r Q q : ℕ}
    {F : Fin m → ℤ[X]} (hF : HasType F d T e)
    (hm : 2 ≤ m) (hP : 4 * m ^ 4 ≤ P) (hMdeg : d + m ≤ M)
    (hT0 : 0 < T) (hT : T ≤ P ^ d)
    (hbudget : P ^ (d + 2 * m.choose 2) < M ^ R)
    (hr1 : 1 ≤ r) (hr : r ≤ d + m) (hds : d ≤ s) (hs : 1 ≤ s)
    (hq : 0 < q) (hQ : 16 * s ^ 2 * (2 ^ R * M) ≤ Q) :
    ∃ (e' p xi : ℕ) (hp : p.Prime) (G : Fin m → ℤ[X]),
      HasType G d T e' ∧ M < p ∧ p ≤ 2 ^ R * M ∧ ¬p ∣ T ∧ xi < p ∧
      (typeCount d P s F (monomialTail m d 1 q Q) : ℝ) ≤
        ((4 * R * d.factorial * p ^ (2 * s - d) : ℕ) : ℝ) *
          ((p ^ ((r - d) * (r - d - 1) / 2) * m.factorial : ℕ) : ℝ) *
            residueMixedMoment m s P (p ^ r) (pow_pos hp.pos r)
              (fullFrequency d G) (monomialTail m d p q (Q / p)) := by
  obtain ⟨π, hcard, hπ, hprod, _⟩ :=
    VinogradovTwoBlockPacket.exists_uniform_two_block_packet M R m d P
      (by omega : 0 < M) hbudget
  simpa only [hcard] using exists_conditioning_of_packet hF hm hP hMdeg hT0 hT
    π hπ hprod hr1 hr hds hs hq hQ

end
end RiemannGaussian.VinogradovUnrestrictedConditioning
