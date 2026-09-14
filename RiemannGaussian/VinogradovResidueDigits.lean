/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCongruencingStep

/-!
# Exact next-digit residue windows and full complex polynomial sums

For every nonzero integer base, the original coarse class and next quotient
digit determine exactly the next residue class. An explicit equivalence
keeps the original positive finite window, including every endpoint.
Restricting to a finite set of digits gives exactly the sum of the actual
finer-residue polynomials. The identity holds before taking any norm and
provides the finite refinement needed by singular conditioning.
-/

namespace RiemannGaussian.VinogradovResidueDigits
noncomputable section
open scoped Classical BigOperators
open UnitAddTorus MeasureTheory
open VinogradovResidueEnergy VinogradovResidueMoment VinogradovPartitionEnergy

/-- The original next quotient digit, reduced in the base ring. -/
def nextDigit {p b eta X : ℕ} (n : ResidueWindow (p ^ b) eta X) : ZMod p :=
  ((n.val.val + 1) / p ^ b : ℕ)

/-- The exact finer residue represented by a coarse class and its next digit. -/
def nextClass (p b eta : ℕ) (d : ZMod p) : ℕ := eta + p ^ b * d.val

/-- A canonical coarse class and next digit give a canonical finer residue. -/
theorem nextClass_lt {p b eta : ℕ} [NeZero p] (heta : eta < p ^ b) (d : ZMod p) :
    nextClass p b eta d < p ^ (b + 1) := by
  unfold nextClass
  have hd := d.val_lt
  rw [pow_succ]
  calc
    eta + p ^ b * d.val < p ^ b + p ^ b * d.val := Nat.add_lt_add_right heta _
    _ = p ^ b * (d.val + 1) := by ring
    _ ≤ p ^ b * p := Nat.mul_le_mul_left _ hd

/-- The original positive entry has exactly the finer class reconstructed from its coarse class and digit. -/
theorem mod_next_eq {p b eta X : ℕ} (n : ResidueWindow (p ^ b) eta X) :
    (n.val.val + 1) % p ^ (b + 1) = nextClass p b eta (nextDigit n) := by
  have he := Nat.mod_add_div ((n.val.val + 1) % p ^ (b + 1)) (p ^ b)
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow p (by omega : b ≤ b + 1)), n.property] at he
  rw [pow_succ, Nat.mod_mul_right_div_self] at he
  simpa only [nextClass, nextDigit, ZMod.val_natCast, pow_succ] using he.symm

/-- Finer residue membership is exactly coarse membership together with the original quotient digit. -/
theorem residue_next_iff {p b eta X : ℕ} [NeZero p] (heta : eta < p ^ b)
    (d : ZMod p) (n : Fin X) :
    (n.val + 1) % p ^ (b + 1) = nextClass p b eta d ↔
      (n.val + 1) % p ^ b = eta ∧ (((n.val + 1) / p ^ b : ℕ) : ZMod p) = d := by
  constructor
  · intro he
    have hc := congrArg (fun m => m % p ^ b) he
    have hd := congrArg (fun m => m / p ^ b) he
    have hp : 0 < p ^ b := pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _
    have hc' : (n.val + 1) % p ^ b = eta := by
      simpa only [Nat.mod_mod_of_dvd _ (pow_dvd_pow p (by omega : b ≤ b + 1)),
        nextClass, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt heta] using hc
    refine ⟨hc', ?_⟩
    rw [pow_succ, Nat.mod_mul_right_div_self, nextClass,
      Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt heta, zero_add] at hd
    apply (ZMod.val_injective p)
    simpa only [ZMod.val_natCast] using hd
  · rintro ⟨hc, hd⟩
    have he := mod_next_eq (p := p) (b := b) (eta := eta) ⟨n, hc⟩
    simpa only [nextDigit, hd] using he

/-- The original digit fibre is equivalent to its actual finer positive residue window, without extending the cutoff. -/
def digitWindowEquiv {p b eta X : ℕ} [NeZero p] (heta : eta < p ^ b) (d : ZMod p) :
    {n : ResidueWindow (p ^ b) eta X // nextDigit n = d} ≃
      ResidueWindow (p ^ (b + 1)) (nextClass p b eta d) X where
  toFun n := ⟨n.val.val, (residue_next_iff heta d n.val.val).mpr ⟨n.val.property, n.property⟩⟩
  invFun n := ⟨⟨n.val, ((residue_next_iff heta d n.val).mp n.property).1⟩,
    ((residue_next_iff heta d n.val).mp n.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An arbitrary finite class restriction partitions the full complex weighted polynomial exactly. -/
theorem polynomial_palette {ι κ d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (w : ι → ℂ) (c : ι → κ) (S : Finset κ) (theta : UnitAddTorus d) :
    polynomial v (fun x => if c x ∈ S then w x else 0) theta =
      ∑ a ∈ S, polynomial v (VinogradovMomentPartition.targetWeight c w a) theta := by
  unfold polynomial VinogradovMomentPartition.targetWeight
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- The actual single-digit Fourier fibre is exactly the original finer-residue polynomial. -/
theorem digit_fibre_eq_residue {p b eta X k : ℕ} [NeZero p]
    (heta : eta < p ^ b) (d : ZMod p) (theta : UnitAddTorus (Fin k)) :
    polynomial (fun n : ResidueWindow (p ^ b) eta X =>
      VinogradovMeanValue.monomialFrequency k (n.val.val + 1))
      (VinogradovMomentPartition.targetWeight nextDigit (fun _ => 1) d) theta =
    VinogradovCongruenceEnergy.residuePolynomial (p ^ (b + 1)) (nextClass p b eta d) X k 1 theta := by
  let : Fintype {n : ResidueWindow (p ^ b) eta X // nextDigit n = d} :=
    @Subtype.fintype _ _ (fun _ => Classical.propDecidable _) _
  rw [VinogradovProductEnergy.target_polynomial_eq_subtype]
  simp only [one_mul, VinogradovCongruenceEnergy.residuePolynomial]
  apply Fintype.sum_equiv (digitWindowEquiv (X := X) heta d)
  intro n
  rfl

/-- The original residue polynomial restricted to a finite set of next digits, before any norm. -/
def palettePolynomial (p b eta X k : ℕ) (S : Finset (ZMod p)) : UnitAddTorus (Fin k) → ℂ :=
  polynomial (fun n : ResidueWindow (p ^ b) eta X =>
    VinogradovMeanValue.monomialFrequency k (n.val.val + 1))
    (fun n => if nextDigit n ∈ S then 1 else 0)

/-- The full class-set polynomial is exactly the sum of actual finer-residue polynomials. -/
theorem palettePolynomial_eq_sum {p b eta X k : ℕ} [NeZero p]
    (heta : eta < p ^ b) (S : Finset (ZMod p)) (theta : UnitAddTorus (Fin k)) :
    palettePolynomial p b eta X k S theta =
      ∑ d ∈ S, VinogradovCongruenceEnergy.residuePolynomial
        (p ^ (b + 1)) (nextClass p b eta d) X k 1 theta := by
  unfold palettePolynomial
  trans ∑ d ∈ S, polynomial
    (fun n : ResidueWindow (p ^ b) eta X => VinogradovMeanValue.monomialFrequency k (n.val.val + 1))
    (VinogradovMomentPartition.targetWeight nextDigit (fun _ => 1) d) theta
  · convert polynomial_palette
      (fun n : ResidueWindow (p ^ b) eta X => VinogradovMeanValue.monomialFrequency k (n.val.val + 1))
      (fun _ => 1) nextDigit S theta using 1
    congr!
  · apply Finset.sum_congr rfl
    intro d hd
    exact digit_fibre_eq_residue heta d theta

/-- Keeping every next digit recovers the entire original residue polynomial. -/
theorem palettePolynomial_univ (p b eta X k : ℕ) [NeZero p] (theta : UnitAddTorus (Fin k)) :
    palettePolynomial p b eta X k Finset.univ theta =
      VinogradovCongruenceEnergy.residuePolynomial (p ^ b) eta X k 1 theta := by
  simp only [palettePolynomial, polynomial, Finset.mem_univ, if_true, one_mul,
    VinogradovCongruenceEnergy.residuePolynomial]

end
end RiemannGaussian.VinogradovResidueDigits
