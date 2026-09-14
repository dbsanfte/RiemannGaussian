/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovSingularConditioning
import RiemannGaussian.VinogradovProductEnergy

/-!
# Exact initial block factorization and next-digit refinement

Split an original tuple into its selected block and full tail before taking
norms. The polynomial identity allows arbitrary complex weights on both
factors. For the actual separated monomial family it identifies the self
energy with I_(0,0). Exact residue refinement and finite Holder then give
I_(0,0)<=p^(2s)*max_eta I_(0,1), retaining actual residue moments.
-/

namespace RiemannGaussian.VinogradovInitialFactor
noncomputable section
open scoped Classical BigOperators
open UnitAddTorus MeasureTheory
open VinogradovMeanValue VinogradovShiftedMoment VinogradovPartitionEnergy
open VinogradovProductEnergy VinogradovResidueEnergy VinogradovSingularConditioning
/-- The original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The full original tuple is exactly its first block and remaining tuple. -/
def splitTupleEquiv (k s : ℕ) (ι : Type*) :
    (Fin (k + s) → ι) ≃ (Fin k → ι) × (Fin s → ι) where
  toFun x := (fun j => x (Fin.castAdd s j), fun j => x (Fin.natAdd k j))
  invFun z := Fin.append z.1 z.2
  left_inv x := by
    funext j
    exact Fin.addCases_castAdd_natAdd x j
  right_inv z := by
    apply Prod.ext <;> funext j <;> simp

/-- The complete original frequency splits exactly with no loss of lower coordinates. -/
theorem tupleFrequency_split {ι d : Type*} (k s : ℕ) (v : ι → d → ℤ)
    (x : Fin (k + s) → ι) :
    tupleFrequency (k + s) v x =
      tupleFrequency k v (fun j => x (Fin.castAdd s j)) +
        tupleFrequency s v (fun j => x (Fin.natAdd k j)) := by
  exact Fin.sum_univ_add (fun j => v (x j))

/-- Every original complex block weight, tail weight and block restriction survives the exact polynomial factorization. -/
theorem polynomial_split_restricted {ι d : Type*} [Fintype ι] [Fintype d]
    (k s : ℕ) (v : ι → d → ℤ) (P : (Fin k → ι) → Prop) [DecidablePred P]
    (w : (Fin k → ι) → ℂ) (z : (Fin s → ι) → ℂ) (theta : UnitAddTorus d) :
    polynomial (tupleFrequency (k + s) v)
      (fun x => (if P (fun j => x (Fin.castAdd s j)) then w (fun j => x (Fin.castAdd s j)) else 0) *
        z (fun j => x (Fin.natAdd k j))) theta =
      polynomial (tupleFrequency k v) (fun x => if P x then w x else 0) theta *
        polynomial (tupleFrequency s v) z theta := by
  rw [← polynomial_prod]
  unfold polynomial
  apply Fintype.sum_equiv (splitTupleEquiv k s ι)
  intro x
  rw [tupleFrequency_split]
  rfl

/-- An indicator polynomial equals the literal sum over its original restricted index family. -/
theorem polynomial_restricted_eq_subtype {ι d : Type*} [Fintype ι] [Fintype d]
    (v : ι → d → ℤ) (P : ι → Prop) [DecidablePred P] (w : ι → ℂ) (theta : UnitAddTorus d) :
    polynomial v (fun x => if P x then w x else 0) theta =
      polynomial (fun x : {x : ι // P x} => v x.val) (fun x => w x.val) theta := by
  unfold polynomial
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- Distinct positive residues and the actual level-zero conditioned block are the same original tuples. -/
def modBlockEquiv (p k X : ℕ) :
    {x : Fin k → Fin X // Function.Injective (fun j => ((x j).val + 1) % p)} ≃
      ConditionedWindow p k 0 0 X where
  toFun x := ⟨x.val, (by intro j; exact Nat.mod_one _), by
    simp only [pow_zero, Nat.div_one]
    intro i j hij
    apply x.property
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hij⟩
  invFun x := ⟨x.val, by
    intro i j hij
    apply x.property.2
    simp only [pow_zero, Nat.div_one]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hij⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The original block restriction is precisely the existing conditioned positive block polynomial. -/
theorem block_polynomial_eq_conditioned (p k X : ℕ) (theta : UnitAddTorus (Fin k)) :
    polynomial (tupleFrequency k (fun n : Fin X => monomialFrequency k (n.val + 1)))
      (fun x => if Function.Injective (fun j => ((x j).val + 1) % p) then 1 else 0) theta =
      polynomial (blockFrequency (p := p) (a := 0) (xi := 0) (X := X) (fun _ => true))
        (fun _ => 1) theta := by
  rw [polynomial_restricted_eq_subtype]
  unfold polynomial
  apply Fintype.sum_equiv (modBlockEquiv p k X)
  intro x
  simp only [one_mul]
  apply congrArg (fun v : Fin k → ℤ => mFourier v theta)
  funext i
  simp only [tupleFrequency, blockFrequency, Finset.sum_apply, monomialFrequency,
    VinogradovSignedCongruence.sign, if_true, one_mul, modBlockEquiv, Equiv.coe_fn_mk,
    Nat.cast_add, Nat.cast_one]

/-- Modulus one imposes no restriction on the original positive interval. -/
def fullResidueEquiv (X : ℕ) : VinogradovResidueMoment.ResidueWindow 1 0 X ≃ Fin X where
  toFun := Subtype.val
  invFun n := ⟨n, Nat.mod_one _⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The full positive-interval polynomial is the actual modulus-one residue polynomial. -/
theorem full_polynomial_eq_residue (k X : ℕ) (theta : UnitAddTorus (Fin k)) :
    polynomial (fun n : Fin X => monomialFrequency k (n.val + 1)) (fun _ => 1) theta =
      VinogradovCongruenceEnergy.residuePolynomial 1 0 X k 1 theta := by
  unfold polynomial VinogradovCongruenceEnergy.residuePolynomial
  simp only [one_mul]
  symm
  exact Fintype.sum_equiv (fullResidueEquiv X) _ _ (fun _ => rfl)

/-- The unweighted tuple sum is the exact original power. -/
theorem tuple_polynomial_one {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) (theta : UnitAddTorus d) :
    polynomial (tupleFrequency s v) (fun _ => 1) theta = polynomial v (fun _ => 1) theta ^ s := by
  simpa only [polynomial, one_mul, tupleFrequency] using (power_expansion v s theta).symm

/-- The separated original polynomial is exactly the conditioned block times the full residue tail, before taking a norm. -/
theorem separated_polynomial_eq_product (p k s X : ℕ) (theta : UnitAddTorus (Fin k)) :
    polynomial (tupleFrequency (k + s) (fun n : Fin X => monomialFrequency k (n.val + 1)))
      (fun x => if Function.Injective (fun j : Fin k => ((x (Fin.castAdd s j)).val + 1) % p) then 1 else 0) theta =
      polynomial (blockFrequency (p := p) (a := 0) (xi := 0) (X := X) (fun _ => true))
        (fun _ => 1) theta * VinogradovCongruenceEnergy.residuePolynomial 1 0 X k 1 theta ^ s := by
  have he := polynomial_split_restricted k s (fun n : Fin X => monomialFrequency k (n.val + 1))
    (fun x => Function.Injective (fun j => ((x j).val + 1) % p)) (fun _ => 1) (fun _ => 1) theta
  simp only [mul_one] at he
  rw [block_polynomial_eq_conditioned, tuple_polynomial_one, full_polynomial_eq_residue] at he
  exact he

/-- The full retained self energy is the actual existing mixed moment at levels zero and zero. -/
theorem separated_energy_eq_mixedMoment (p k s X : ℕ) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (tupleFrequency (k + s) (fun n : Fin X => monomialFrequency k (n.val + 1)))
        (fun x => if Function.Injective (fun j : Fin k => ((x (Fin.castAdd s j)).val + 1) % p) then 1 else 0) theta‖ ^ 2) =
      mixedMoment p k 0 0 0 0 X s (fun _ => true) := by
  simp only [separated_polynomial_eq_product, norm_mul, mul_pow, norm_pow, ← pow_mul,
    Nat.mul_comm s 2, mixedMoment, pow_zero]

/-- Exact next-digit refinement and the proved finite Holder estimate put the initial mixed energy into the existing level-zero/one maximum. -/
theorem initial_mixed_le_next (p k s X : ℕ) [NeZero p] (hs : 0 < s) :
    mixedMoment p k 0 0 0 0 X s (fun _ => true) ≤
      (p : ℝ) ^ (2 * s) * nextMixedMaximum p k 0 0 0 X s (fun _ => true) := by
  have he := palette_mixed_integral_le (p := p) (k := k) (a := 0) (b := 0) (xi := 0)
    (eta := 0) (X := X) (s := s) (by norm_num) hs (fun _ => true) Finset.univ
  simpa only [VinogradovResidueDigits.palettePolynomial_univ, Finset.card_univ, ZMod.card,
    mixedMoment, pow_zero] using he

end
end RiemannGaussian.VinogradovInitialFactor
