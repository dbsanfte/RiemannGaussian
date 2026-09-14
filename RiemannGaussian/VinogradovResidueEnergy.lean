/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPartitionEnergy

/-!
# Whole conditioned moments from the actual signed residue count

Reduction of original block entries modulo `p^(k*b)` preserves the coarse
class, the normalized next digit, and every translated signed degree target.
The proved prime-power count therefore pays the entire original torus energy
by the sum of its finer residue energies. Both the collision and fibre-size
conditions of the general energy theorem are discharged from actual tail
windows and the signed congruence theorem.

The terminal finite-window statement includes every admissible positive block
and tail tuple, retaining arbitrary complex configuration weights and all
correlations within them. This is the whole-moment transfer underlying Wooley
(2012), equation (6.6). Product factorization, subsequent Hölder estimates,
singular conditioning and the high-moment iteration require separate proofs.
-/

namespace RiemannGaussian.VinogradovResidueEnergy
noncomputable section
open scoped BigOperators ComplexConjugate Classical
open MeasureTheory UnitAddTorus VinogradovMomentPartition VinogradovPartitionEnergy

/-- Canonical finer residue tuples retain their common coarse class and
distinct normalized next digits. -/
abbrev GoodResidue (p k a b xi : ℕ) :=
  {x : Fin k → Fin (p ^ (k * b)) //
    (∀ j, (x j).val % p ^ a = xi) ∧
    Function.Injective (fun j => (((x j).val / p ^ a : ℕ) : ZMod p))}

/-- Reduce each original natural block entry to its canonical finer residue. -/
def residueTuple {p k b : ℕ} [NeZero p] (x : Fin k → ℕ) : Fin k → Fin (p ^ (k * b)) :=
  fun j => ⟨x j % p ^ (k * b), Nat.mod_lt _ (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _)⟩

/-- Reduction above the next-digit precision leaves the actual quotient
digit unchanged. Division is in the natural numbers before reduction. -/
theorem mod_quotient_digit (n p a m : ℕ) (ham : a + 1 ≤ m) :
    ((n % p ^ m) / p ^ a) % p = (n / p ^ a) % p := by
  rw [← Nat.mod_mul_right_div_self, ← pow_succ,
    Nat.mod_mod_of_dvd n (pow_dvd_pow p ham), pow_succ,
    Nat.mod_mul_right_div_self]

/-- Canonical reduction preserves the original coarse residue class. -/
theorem residueTuple_class {p k a b : ℕ} [NeZero p]
    (ha : a ≤ k * b) (x : Fin k → ℕ) (j : Fin k) :
    (residueTuple (p := p) (b := b) x j).val % p ^ a = x j % p ^ a :=
  Nat.mod_mod_of_dvd _ (pow_dvd_pow p ha)

/-- The normalized next digit survives reduction of the original entry. -/
theorem residueTuple_digit {p k a b : ℕ} [NeZero p]
    (ha : a + 1 ≤ k * b) (x : Fin k → ℕ) (j : Fin k) :
    (((residueTuple (p := p) (b := b) x j).val / p ^ a : ℕ) : ZMod p) =
      ((x j / p ^ a : ℕ) : ZMod p) := by
  change (((x j % p ^ (k * b)) / p ^ a : ℕ) : ZMod p) = _
  rw [← ZMod.natCast_mod ((x j % p ^ (k * b)) / p ^ a) p,
    mod_quotient_digit (x j) p a (k * b) ha, ZMod.natCast_mod]

/-- The original coarse class and next-digit distinctness construct an
actual admissible canonical tuple, without an extra nonsingularity premise. -/
def conditionedResidue {p k a b xi : ℕ} [NeZero p]
    (ha : a + 1 ≤ k * b) (x : Fin k → ℕ)
    (hx : ∀ j, x j % p ^ a = xi)
    (hd : Function.Injective (fun j => ((x j / p ^ a : ℕ) : ZMod p))) :
    GoodResidue p k a b xi :=
  ⟨residueTuple x,
    (fun j => (residueTuple_class (by omega) x j).trans (hx j)), by
      intro j l he
      apply hd
      simpa only [residueTuple_digit ha] using he⟩

/-- Every lower prime-power residue of the original entry is unchanged. -/
theorem residueTuple_cast {p k b d : ℕ} [NeZero p]
    (hd : d ≤ k * b) (x : Fin k → ℕ) (j : Fin k) :
    (((residueTuple (p := p) (b := b) x j).val : ℕ) : ZMod (p ^ d)) =
      (x j : ZMod (p ^ d)) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  exact Nat.mod_mod_of_dvd _ (pow_dvd_pow p hd)


/-- The complete translated weighted degree signature survives reduction
of all original entries; no degree or sign is discarded. -/
theorem residueTuple_signature {p k b : ℕ} [NeZero p]
    (eta : ℤ) (c : Fin k → ℤ) (x : Fin k → ℕ) :
    blockSignature (q := p) (b := b) eta c
      (fun _ : Unit => fun j => ((residueTuple (p := p) (b := b) x j).val : ℤ)) () =
    blockSignature (q := p) (b := b) eta c (fun _ : Unit => fun j => (x j : ℤ)) () := by
  funext i
  simp only [blockSignature, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_sub, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro j hj
  rw [residueTuple_cast (Nat.mul_le_mul_right b (Nat.succ_le_of_lt i.isLt))]

/-- Keep all translated signed degree targets of one admissible residue tuple. -/
def residueSignature {p k a b xi : ℕ} (eta : ℤ) (colour : Fin k → Bool)
    (x : GoodResidue p k a b xi) : (i : Fin k) → ZMod (p ^ ((i.val + 1) * b)) :=
  blockSignature (q := p) (b := b) eta (fun j => VinogradovSignedCongruence.sign (colour j))
    (fun _ : Unit => fun j => ((x.val j).val : ℤ)) ()

/-- The actual signed coarse counting theorem bounds every complete
signature fibre, retaining its two colour factorials. -/
theorem residueSignature_card_le {p k a b xi : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a ≤ b) (eta : ℤ) (colour : Fin k → Bool)
    (target : (i : Fin k) → ZMod (p ^ ((i.val + 1) * b))) :
    (Finset.univ.filter (fun x : GoodResidue p k a b xi =>
      residueSignature eta colour x = target)).card ≤
      p ^ ((a + b) * (k * (k - 1) / 2)) * VinogradovSignedCongruence.colourFactorial colour := by
  apply le_trans (Finset.card_le_card_of_injOn Subtype.val ?_ ?_)
    (VinogradovCoarseCongruence.conditioned_residue_card_le hkp hk hab colour xi eta
      (fun i => ((target i).val : ℤ)))
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property.1, x.property.2, ?_⟩
    intro i
    have he := congrFun (Finset.mem_filter.mp hx).2 i
    have hc : ((∑ j, VinogradovSignedCongruence.sign (colour j) *
        (((x.val j).val : ℤ) - eta) ^ (i.val + 1) : ℤ) : ZMod (p ^ ((i.val + 1) * b))) =
        (((target i).val : ℤ) : ZMod (p ^ ((i.val + 1) * b))) := by
      simpa only [residueSignature, blockSignature, Int.cast_natCast, ZMod.natCast_zmod_val] using he
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ (p ^ ((i.val + 1) * b))).mp hc.symm
    simpa only [Nat.cast_pow] using hd
  · exact fun _ _ _ _ h => Subtype.val_injective h


/-- The constructed admissible residue tuple has exactly the original
block signature at every degree-specific precision. -/
theorem conditionedResidue_signature {p k a b xi : ℕ} [NeZero p]
    (ha : a + 1 ≤ k * b) (x : Fin k → ℕ)
    (hx : ∀ j, x j % p ^ a = xi)
    (hd : Function.Injective (fun j => ((x j / p ^ a : ℕ) : ZMod p)))
    (eta : ℤ) (colour : Fin k → Bool) :
    residueSignature eta colour (conditionedResidue ha x hx hd) =
      blockSignature (q := p) (b := b) eta (fun j => VinogradovSignedCongruence.sign (colour j))
        (fun _ : Unit => fun j => (x j : ℤ)) () :=
  residueTuple_signature eta _ x

/-- Use the same normalized Haar measure as the original moment identity. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle Haar measure is a probability measure. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The actual signed residue count controls the entire original weighted
moment by its finer block-residue energies. Arbitrary finite configuration
correlations and integer tail coefficients remain; literal positive tail
windows discharge divisibility and collision orthogonality. -/
theorem conditioned_whole_integral_le {ι : Type*} [Fintype ι]
    {p k a b r X xi : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b)
    (eta : ℤ) (colour : Fin k → Bool) (tau : Fin r → ℤ)
    (x : ι → Fin k → ℕ)
    (u : ι → Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X)
    (w : ι → ℂ) (hx : ∀ z j, x z j % p ^ a = xi)
    (hd : ∀ z, Function.Injective (fun j => ((x z j / p ^ a : ℕ) : ZMod p))) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (mixedFrequency (fun j => VinogradovSignedCongruence.sign (colour j)) tau
        (fun z j => (x z j : ℤ)) (fun z j => ((u z j).val.val + 1 : ℤ))) w theta‖ ^ 2) ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
      ∑ c : GoodResidue p k a b xi, ∫ theta : UnitAddTorus (Fin k),
        ‖polynomial (mixedFrequency (fun j => VinogradovSignedCongruence.sign (colour j)) tau
          (fun z j => (x z j : ℤ)) (fun z j => ((u z j).val.val + 1 : ℤ)))
          (targetWeight (fun z => residueTuple (p := p) (b := b) (x z)) w c.val) theta‖ ^ 2 := by
  classical
  have ha : a + 1 ≤ k * b := by
    calc
      a + 1 ≤ b := hab
      _ ≤ k * b := by simpa only [Nat.mul_comm k b] using Nat.le_mul_of_pos_right b hk
  let fine (z : ι) : GoodResidue p k a b xi := conditionedResidue ha (x z) (hx z) (hd z)
  let v := mixedFrequency (fun j => VinogradovSignedCongruence.sign (colour j)) tau
    (fun z j => (x z j : ℤ)) (fun z j => ((u z j).val.val + 1 : ℤ))
  have hs (z : ι) : residueSignature eta colour (fine z) =
      blockSignature (q := p) (b := b) eta (fun j => VinogradovSignedCongruence.sign (colour j))
        (fun z j => (x z j : ℤ)) z := conditionedResidue_signature ha (x z) (hx z) (hd z) eta colour
  have hcollision : ∀ z z', v z = v z' →
      residueSignature eta colour (fine z) = residueSignature eta colour (fine z') := by
    intro z z' he
    rw [hs z, hs z']
    apply mixed_collision_signature eta _ tau _ _ ?_ z z' he
    intro y j
    have hy := (VinogradovResidueMoment.residue_mod_iff_dvd_sub eta ((u y j).val.val + 1)).mp
      (u y j).property
    simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hy
  have hc (target : (i : Fin k) → ZMod (p ^ ((i.val + 1) * b))) :
      ((Finset.univ.filter (fun c : GoodResidue p k a b xi => residueSignature eta colour c = target)).card : ℝ) ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) := by
    exact_mod_cast residueSignature_card_le hkp hk (Nat.le_of_lt hab) eta colour target
  have he := whole_integral_le v w fine (residueSignature eta colour)
    ((p ^ ((a + b) * (k * (k - 1) / 2)) *
      VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) hcollision (by
        intro target
        convert hc target using 1
        congr 2
        ext c
        simp)
  have hw (c : GoodResidue p k a b xi) : targetWeight fine w c =
      targetWeight (fun z => residueTuple (p := p) (b := b) (x z)) w c.val := by
    funext z
    unfold targetWeight
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ (congrArg Subtype.val h₁))
    · exact False.elim (h₁ (Subtype.ext h₂))
    · rfl
  simpa only [hw] using he


/-- All positive blocks up to the actual endpoint, in the specified coarse
class and with distinct normalized next digits. -/
abbrev ConditionedWindow (p k a xi X : ℕ) :=
  {x : Fin k → Fin X //
    (∀ j, ((x j).val + 1) % p ^ a = xi) ∧
    Function.Injective (fun j => ((((x j).val + 1) / p ^ a : ℕ) : ZMod p))}

/-- The full original family of admissible positive blocks and literal
finite positive residue tails. -/
abbrev WindowConfiguration (p k a b r xi X : ℕ) (eta : ℤ) :=
  ConditionedWindow p k a xi X ×
    (Fin r → VinogradovConditionedCompletion.PrimeTailWindow p b eta X)

/-- Retain each literal positive integer in the original block window. -/
def windowBlock {p k a b r xi X : ℕ} {eta : ℤ}
    (z : WindowConfiguration p k a b r xi X eta) : Fin k → ℕ :=
  fun j => (z.1.val j).val + 1

/-- The complete original signed block and integer-weighted tail frequency. -/
def windowFrequency {p k a b r xi X : ℕ} {eta : ℤ}
    (colour : Fin k → Bool) (tau : Fin r → ℤ) :
    WindowConfiguration p k a b r xi X eta → Fin k → ℤ :=
  mixedFrequency (fun j => VinogradovSignedCongruence.sign (colour j)) tau
    (fun z j => (windowBlock z j : ℤ)) (fun z j => ((z.2 j).val.val + 1 : ℤ))

/-- The full actual finite-window moment satisfies the finer-residue energy
bound, with all block conditions supplied by its original index family.
Every complex configuration weight and all its correlations are retained. -/
theorem window_whole_integral_le {p k a b r xi X : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b)
    (eta : ℤ) (colour : Fin k → Bool) (tau : Fin r → ℤ)
    (w : WindowConfiguration p k a b r xi X eta → ℂ) :
    (∫ theta : UnitAddTorus (Fin k), ‖polynomial (windowFrequency colour tau) w theta‖ ^ 2) ≤
      ((p ^ ((a + b) * (k * (k - 1) / 2)) *
        VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
      ∑ c : GoodResidue p k a b xi, ∫ theta : UnitAddTorus (Fin k),
        ‖polynomial (windowFrequency colour tau)
          (targetWeight (fun z => residueTuple (p := p) (b := b) (windowBlock z)) w c.val) theta‖ ^ 2 :=
  conditioned_whole_integral_le hkp hk hab eta colour tau windowBlock Prod.snd w
    (fun z => z.1.property.1) (fun z => z.1.property.2)

end
end RiemannGaussian.VinogradovResidueEnergy
