/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovSignedTailMoment

/-!
# Signed coarse congruence fibres and the actual Cauchy energy step

The complete complex Gram identity retains all original cross terms before
Cauchy spends the actual fibre cardinality. The proved signed coarse count
therefore pays an explicit triangular prime-power cost and the original
sign factorial for every complex weight family on the fibre.

The literal positive residue-window Fourier sums keep their full signed
power vectors. Reversing a phase is exactly conjugation; their conditioned
products receive the pointwise Cauchy estimate used in efficient congruencing
(Wooley 2012, equation (6.5)). Summing all target fibres, transferring the
result to the complete conditioned moment, and the high-moment iteration
still require their own proofs.
-/

namespace RiemannGaussian.VinogradovCongruenceEnergy
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open UnitAddTorus

/-- The complex square keeps every ordered pair and original complex weight. -/
theorem sum_energy_eq_gram {α : Type*} (S : Finset α) (w : α → ℂ) :
    ‖∑ x ∈ S, w x‖ ^ 2 =
      (∑ x ∈ S, ∑ y ∈ S, w x * conj (w y)).re := by
  rw [← Finset.sum_mul_sum, ← map_sum, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_re]

/-- The Cauchy cost is the actual fibre cardinality; all weights remain
inside the diagonal energy after the exact Gram identity. -/
theorem sum_energy_le_card_mul {α : Type*} (S : Finset α) (w : α → ℂ) :
    ‖∑ x ∈ S, w x‖ ^ 2 ≤ (S.card : ℝ) * ∑ x ∈ S, ‖w x‖ ^ 2 := by
  have hn := norm_sum_le S w
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun x => ‖w x‖)
  calc
    ‖∑ x ∈ S, w x‖ ^ 2 ≤ (∑ x ∈ S, ‖w x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ (S.card : ℝ) * ∑ x ∈ S, ‖w x‖ ^ 2 := by simpa using hc

/-- The complete original signed coarse congruence fibre retains its
common class, normalized next digits, all degree moduli and full target. -/
def coarseFibre {p k a b : ℕ} (colour : Fin k → Bool) (xi : ℕ) (eta : ℤ)
    (target : Fin k → ℤ) : Finset (Fin k → Fin (p ^ (k * b))) :=
  Finset.univ.filter (fun x =>
    (∀ j, (x j).val % p ^ a = xi) ∧
    Function.Injective (fun j => (((x j).val / p ^ a : ℕ) : ZMod p)) ∧ ∀ i : Fin k,
    (p : ℤ) ^ ((i.val + 1) * b) ∣
      (∑ j, VinogradovSignedCongruence.sign (colour j) * (((x j).val : ℤ) - eta) ^ (i.val + 1)) -
      target i)

/-- All original complex cross terms remain available on the actual fibre. -/
theorem coarse_fibre_energy_eq_gram {p k a b : ℕ}
    (colour : Fin k → Bool) (xi : ℕ) (eta : ℤ) (target : Fin k → ℤ)
    (w : (Fin k → Fin (p ^ (k * b))) → ℂ) :
    ‖∑ x ∈ coarseFibre (p := p) (a := a) (b := b) colour xi eta target, w x‖ ^ 2 =
      (∑ x ∈ coarseFibre (p := p) (a := a) (b := b) colour xi eta target,
        ∑ y ∈ coarseFibre (p := p) (a := a) (b := b) colour xi eta target, w x * conj (w y)).re :=
  sum_energy_eq_gram _ w

/-- The actual signed coarse counting theorem pays the pointwise Cauchy
step for every complex fibre weight, with the sign factorial retained. -/
theorem coarse_fibre_energy_le {p k a b : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a ≤ b)
    (colour : Fin k → Bool) (xi : ℕ) (eta : ℤ) (target : Fin k → ℤ)
    (w : (Fin k → Fin (p ^ (k * b))) → ℂ) :
    ‖∑ x ∈ coarseFibre (p := p) (a := a) (b := b) colour xi eta target, w x‖ ^ 2 ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
          ∑ x ∈ coarseFibre (p := p) (a := a) (b := b) colour xi eta target, ‖w x‖ ^ 2 := by
  have hc := VinogradovCoarseCongruence.conditioned_residue_card_le hkp hk hab colour xi eta target
  have hcR : ((coarseFibre (p := p) (a := a) (b := b) colour xi eta target).card : ℝ) ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) := by exact_mod_cast hc
  exact (sum_energy_le_card_mul _ w).trans
    (mul_le_mul_of_nonneg_right hcR (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-- The actual finite Fourier sum over a positive integer residue window,
with its signed full power vector. -/
def residuePolynomial (q xi X k : ℕ) (c : ℤ) (theta : UnitAddTorus (Fin k)) : ℂ :=
  ∑ n : VinogradovResidueMoment.ResidueWindow q xi X,
    mFourier (fun i => c * VinogradovMeanValue.monomialFrequency k (n.val.val + 1) i) theta

/-- Reversing the complete phase vector conjugates the actual residue sum. -/
theorem residuePolynomial_neg (q xi X k : ℕ) (c : ℤ) (theta : UnitAddTorus (Fin k)) :
    residuePolynomial q xi X k (-c) theta = conj (residuePolynomial q xi X k c theta) := by
  have hf (n : VinogradovResidueMoment.ResidueWindow q xi X) :
      (fun i => -c * VinogradovMeanValue.monomialFrequency k (n.val.val + 1) i) =
        -(fun i => c * VinogradovMeanValue.monomialFrequency k (n.val.val + 1) i) := by
    funext i
    simp only [Pi.neg_apply, neg_mul]
  simp only [residuePolynomial, hf, mFourier_neg, map_sum]

/-- Each retained sign is either the original residue sum or its exact
complex conjugate, before its modulus is used. -/
theorem residuePolynomial_sign (q xi X k : ℕ) (colour : Bool) (theta : UnitAddTorus (Fin k)) :
    residuePolynomial q xi X k (VinogradovSignedCongruence.sign colour) theta =
      if colour then residuePolynomial q xi X k 1 theta
        else conj (residuePolynomial q xi X k 1 theta) := by
  cases colour
  · simpa only [VinogradovSignedCongruence.sign, Bool.false_eq_true, ↓reduceIte] using
      residuePolynomial_neg q xi X k 1 theta
  · rfl

/-- Both phase orientations have the same actual residue-sum norm. -/
theorem norm_residuePolynomial_sign (q xi X k : ℕ) (colour : Bool) (theta : UnitAddTorus (Fin k)) :
    ‖residuePolynomial q xi X k (VinogradovSignedCongruence.sign colour) theta‖ =
      ‖residuePolynomial q xi X k 1 theta‖ := by
  rw [residuePolynomial_sign]
  split_ifs <;> simp

/-- The literal conditioned product keeps every residue coordinate and
its original phase orientation. -/
def coarseSignedProduct {p k b : ℕ} (X : ℕ) (colour : Fin k → Bool)
    (theta : UnitAddTorus (Fin k)) (x : Fin k → Fin (p ^ (k * b))) : ℂ :=
  ∏ j, residuePolynomial (p ^ (k * b)) (x j).val X k
    (VinogradovSignedCongruence.sign (colour j)) theta

/-- The exact sign/conjugation identity pays the product norm only after
retaining the full complex product. -/
theorem coarseSignedProduct_norm_sq {p k b : ℕ} (X : ℕ) (colour : Fin k → Bool)
    (theta : UnitAddTorus (Fin k)) (x : Fin k → Fin (p ^ (k * b))) :
    ‖coarseSignedProduct X colour theta x‖ ^ 2 =
      ∏ j, ‖residuePolynomial (p ^ (k * b)) (x j).val X k 1 theta‖ ^ 2 := by
  simp only [coarseSignedProduct, norm_prod, norm_residuePolynomial_sign, Finset.prod_pow]

/-- The signed coarse fibre count pays the actual pointwise Cauchy step
for products of original positive residue-window Fourier sums. -/
theorem coarse_product_energy_le {p k a b : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a ≤ b) (X : ℕ)
    (colour : Fin k → Bool) (xi : ℕ) (eta : ℤ) (target : Fin k → ℤ)
    (theta : UnitAddTorus (Fin k)) :
    ‖∑ x ∈ coarseFibre (p := p) (a := a) (b := b) colour xi eta target,
        coarseSignedProduct X colour theta x‖ ^ 2 ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
      ∑ x ∈ coarseFibre (p := p) (a := a) (b := b) colour xi eta target,
        ∏ j, ‖residuePolynomial (p ^ (k * b)) (x j).val X k 1 theta‖ ^ 2 := by
  simpa only [coarseSignedProduct_norm_sq] using
    coarse_fibre_energy_le hkp hk hab colour xi eta target (coarseSignedProduct X colour theta)

end
end RiemannGaussian.VinogradovCongruenceEnergy
