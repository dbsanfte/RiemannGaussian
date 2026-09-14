/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovConditioningSupport
import RiemannGaussian.VinogradovResidueDigits
import RiemannGaussian.VinogradovMomentReduction

/-!
# An explicit bound for the actual singular conditioning contribution

The literal conditioned block times the full residue tail defines the
original mixed moment. Its collision system splits exactly according to the
union of next-digit classes from both sides. The singular part is covered by
sets of k-1 classes, retaining the complete signed frequency equation.
Exact complex factorization and next-digit refinement precede the finite
Holder inequality and justified integral exchanges.

The terminal bound is choose(p,k-1)*(k-1)^(2s) times the actual next-level
mixed-moment maximum. Every block sign, original cutoff and residue class
survives; no moment budget is a hypothesis. This makes the singular
contribution in Wooley (2012), equation (5.2), explicit:
https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf
The nonsingular estimate and finite conditioning recurrence are proved in
`VinogradovNonsingularConditioning`; their explicit initial remainder saving
is in `VinogradovConditioningPowerSaving`. High-moment exponent improvement
and the Vinogradov--Korobov zero-free proof remain open.
-/

namespace RiemannGaussian.VinogradovSingularConditioning
noncomputable section
open scoped Classical BigOperators
open UnitAddTorus MeasureTheory
open VinogradovMeanValue VinogradovShiftedMoment VinogradovPartitionEnergy
open VinogradovResidueEnergy VinogradovResidueMoment VinogradovProductEnergy
open VinogradovConditioningSupport VinogradovResidueDigits
/-- Use the original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The original conditioned block and all original full residue-tail entries. -/
abbrev Configuration (p k a b xi eta X s : ℕ) :=
  ConditionedWindow p k a xi X × (Fin s → ResidueWindow (p ^ b) eta X)

/-- The complete original signed block frequency plus every original tail power coordinate. -/
def frequency {p k a b xi eta X s : ℕ} (colour : Fin k → Bool)
    (z : Configuration p k a b xi eta X s) : Fin k → ℤ :=
  blockFrequency colour z.1 + tupleFrequency s
    (fun n : ResidueWindow (p ^ b) eta X => monomialFrequency k (n.val.val + 1)) z.2

/-- The actual set of quotient-digit classes used by all entries of one full tail. -/
def classSupport {p k a b xi eta X s : ℕ} (z : Configuration p k a b xi eta X s) :
    Finset (ZMod p) := Finset.univ.image (fun j => nextDigit (z.2 j))

/-- Original equal-frequency pairs whose two tails together use fewer than k next-digit classes. -/
def singularCount {p k a b xi eta X s : ℕ} (colour : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s =>
    frequency colour xy.1 = frequency colour xy.2 ∧
      (classSupport xy.1 ∪ classSupport xy.2).card < k)).card

/-- A full-tail class restriction factors exactly into its original coordinate indicators. -/
theorem palette_weight_eq_tuple {p k a b xi eta X s : ℕ} (S : Finset (ZMod p))
    (z : Configuration p k a b xi eta X s) :
    (if classSupport z ⊆ S then (1 : ℂ) else 0) =
      tupleWeight s (fun n : ResidueWindow (p ^ b) eta X => if nextDigit n ∈ S then 1 else 0) z.2 := by
  have he : classSupport z ⊆ S ↔ ∀ j, nextDigit (z.2 j) ∈ S := by
    constructor
    · intro h j
      exact h (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    · intro h d hd
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
      exact h j
  by_cases h : classSupport z ⊆ S
  · have hj := he.mp h
    simp [h, tupleWeight, hj]
  · have hj := mt he.mpr h
    obtain ⟨j, hj⟩ := not_forall.mp hj
    simp only [h, if_false, tupleWeight]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

/-- The entire restricted configuration polynomial equals the original signed block times the powered class-set tail, before any norm. -/
theorem palette_configuration_eq_product {p k a b xi eta X s : ℕ}
    (colour : Fin k → Bool) (S : Finset (ZMod p)) (theta : UnitAddTorus (Fin k)) :
    polynomial (frequency (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := s) colour)
      (fun z => if classSupport z ⊆ S then 1 else 0) theta =
    polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta *
      palettePolynomial p b eta X k S theta ^ s := by
  have hw : (fun z : Configuration p k a b xi eta X s => if classSupport z ⊆ S then (1 : ℂ) else 0) =
      (fun z => tupleWeight s (fun n : ResidueWindow (p ^ b) eta X =>
        if nextDigit n ∈ S then 1 else 0) z.2) := by
    funext z
    exact palette_weight_eq_tuple S z
  rw [hw]
  unfold frequency
  have hp := polynomial_prod (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour)
    (tupleFrequency s (fun n : ResidueWindow (p ^ b) eta X => monomialFrequency k (n.val.val + 1)))
    (fun _ => 1) (tupleWeight s (fun n => if nextDigit n ∈ S then 1 else 0)) theta
  simp only [one_mul] at hp
  rw [hp]
  congr 1
  exact (weighted_power_expansion s
    (fun n : ResidueWindow (p ^ b) eta X => monomialFrequency k (n.val.val + 1))
    (fun n => if nextDigit n ∈ S then 1 else 0) theta).symm

/-- The actual singular collision count receives a sum of literal signed-block and restricted-tail mixed energies. -/
theorem singular_count_le_palette_mixed {p k a b xi eta X s : ℕ} [NeZero p]
    (hkp : k ≤ p) (colour : Fin k → Bool) :
    (singularCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := s) colour : ℝ) ≤
      ∑ S ∈ smallPalettes p k, ∫ theta : UnitAddTorus (Fin k),
        ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta‖ ^ 2 *
        ‖palettePolynomial p b eta X k S theta‖ ^ (2 * s) := by
  have he := singular_count_le_palette_energy hkp
    (frequency (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := s) colour) classSupport
  apply he.trans_eq
  apply Finset.sum_congr rfl
  intro S hS
  apply integral_congr_ae
  filter_upwards [] with theta
  rw [palette_configuration_eq_product, norm_mul, mul_pow, norm_pow, ← pow_mul, Nat.mul_comm s 2]

/-- The actual original conditioned-block and unrestricted residue-tail mixed moment. -/
def mixedMoment (p k a b xi eta X s : ℕ) (colour : Fin k → Bool) : ℝ :=
  ∫ theta : UnitAddTorus (Fin k),
    ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta‖ ^ 2 *
    ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ b) eta X k 1 theta‖ ^ (2 * s)

/-- Original equal-frequency pairs whose two tails together use at least k next-digit classes. -/
def nonsingularCount {p k a b xi eta X s : ℕ} (colour : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s =>
    frequency colour xy.1 = frequency colour xy.2 ∧
      k ≤ (classSupport xy.1 ∪ classSupport xy.2).card)).card

/-- The actual mixed torus moment equals the complete original configuration collision count. -/
theorem mixedMoment_eq_full_count {p k a b xi eta X s : ℕ} [NeZero p]
    (colour : Fin k → Bool) :
    mixedMoment p k a b xi eta X s colour =
      ((Finset.univ.filter (fun xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s =>
        frequency colour xy.1 = frequency colour xy.2)).card : ℝ) := by
  have he := restricted_energy_eq_count
    (frequency (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := s) colour)
    (fun _ => True)
  simp only [if_true, and_true] at he
  have hn (theta : UnitAddTorus (Fin k)) :
      ‖polynomial (frequency (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := s) colour)
        (fun _ => 1) theta‖ ^ 2 =
      ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta‖ ^ 2 *
        ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ b) eta X k 1 theta‖ ^ (2 * s) := by
    have hp := palette_configuration_eq_product (p := p) (a := a) (b := b) (xi := xi)
      (eta := eta) (X := X) (s := s) colour Finset.univ theta
    simp only [Finset.subset_univ, if_true, palettePolynomial_univ] at hp
    rw [hp, norm_mul, mul_pow, norm_pow, ← pow_mul, Nat.mul_comm s 2]
  simp_rw [hn] at he
  exact he

/-- The literal mixed moment splits exactly into its two complementary joint-support collision counts. -/
theorem mixedMoment_eq_singular_add_nonsingular {p k a b xi eta X s : ℕ} [NeZero p]
    (colour : Fin k → Bool) :
    mixedMoment p k a b xi eta X s colour =
      (singularCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := s) colour : ℝ) +
        nonsingularCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := s) colour := by
  rw [mixedMoment_eq_full_count]
  have he := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun xy : Configuration p k a b xi eta X s × Configuration p k a b xi eta X s =>
      frequency colour xy.1 = frequency colour xy.2))
    (fun xy => (classSupport xy.1 ∪ classSupport xy.2).card < k)
  simp only [Finset.filter_filter, not_lt] at he
  have hR := congrArg (fun n : ℕ => (n : ℝ)) he.symm
  simp only [Nat.cast_add] at hR
  convert hR using 1
  congr!

/-- The actual finite maximum of finer-residue mixed moments, retaining the original signed block and cutoff. -/
def nextMixedMaximum (p k a b xi X s : ℕ) [NeZero p] (colour : Fin k → Bool) : ℝ :=
  (Finset.univ : Finset (Fin (p ^ (b + 1)))).sup' Finset.univ_nonempty
    (fun c => mixedMoment p k a (b + 1) xi c.val X s colour)

/-- Each canonical finer-residue mixed moment is bounded by the actual maximum. -/
theorem mixedMoment_le_nextMixedMaximum {p k a b xi X s : ℕ} [NeZero p]
    (colour : Fin k → Bool) (c : Fin (p ^ (b + 1))) :
    mixedMoment p k a (b + 1) xi c.val X s colour ≤ nextMixedMaximum p k a b xi X s colour := by
  unfold nextMixedMaximum
  exact Finset.le_sup' (fun c : Fin (p ^ (b + 1)) =>
    mixedMoment p k a (b + 1) xi c.val X s colour) (Finset.mem_univ c)

/-- Only after exact class refinement, finite Holder bounds the original tail power with its actual class-count cost. -/
theorem palette_norm_power_le {p b eta X k s : ℕ} [NeZero p]
    (heta : eta < p ^ b) (hs : 0 < s) (S : Finset (ZMod p)) (theta : UnitAddTorus (Fin k)) :
    ‖palettePolynomial p b eta X k S theta‖ ^ (2 * s) ≤
      (S.card : ℝ) ^ (2 * s - 1) * ∑ d ∈ S,
        ‖VinogradovCongruenceEnergy.residuePolynomial
          (p ^ (b + 1)) (nextClass p b eta d) X k 1 theta‖ ^ (2 * s) := by
  rw [palettePolynomial_eq_sum heta]
  have he := VinogradovMomentReduction.norm_weighted_power_bound S (fun _ => 1)
    (fun d => VinogradovCongruenceEnergy.residuePolynomial
      (p ^ (b + 1)) (nextClass p b eta d) X k 1 theta) (by simp) (p := 2 * s) (by omega)
  simpa only [Complex.ofReal_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] using he

/-- The literal restricted mixed energy receives the actual next-level moment maximum, with every integral condition discharged. -/
theorem palette_mixed_integral_le {p k a b xi eta X s : ℕ} [NeZero p]
    (heta : eta < p ^ b) (hs : 0 < s) (colour : Fin k → Bool) (S : Finset (ZMod p)) :
    (∫ theta : UnitAddTorus (Fin k),
      ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta‖ ^ 2 *
      ‖palettePolynomial p b eta X k S theta‖ ^ (2 * s)) ≤
      (S.card : ℝ) ^ (2 * s) * nextMixedMaximum p k a b xi X s colour := by
  let G : UnitAddTorus (Fin k) → ℝ := fun theta =>
    ‖polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1) theta‖ ^ 2
  let f (d : ZMod p) : UnitAddTorus (Fin k) → ℝ := fun theta =>
    ‖VinogradovCongruenceEnergy.residuePolynomial
      (p ^ (b + 1)) (nextClass p b eta d) X k 1 theta‖ ^ (2 * s)
  have hG : Continuous G := (continuous_polynomial _ _).norm.pow 2
  have hf (d : ZMod p) : Continuous (f d) := by
    unfold f VinogradovCongruenceEnergy.residuePolynomial
    fun_prop
  have hi (d : ZMod p) : Integrable (fun theta => G theta * f d theta) :=
    (hG.mul (hf d)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hleft : Integrable (fun theta => G theta * ‖palettePolynomial p b eta X k S theta‖ ^ (2 * s)) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply hG.mul
    exact (continuous_polynomial _ _).norm.pow (2 * s)
  have hright : Integrable (fun theta => G theta *
      ((S.card : ℝ) ^ (2 * s - 1) * ∑ d ∈ S, f d theta)) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact hG.mul (continuous_const.mul (continuous_finsetSum _ (fun d _ => hf d)))
  have he : (∫ theta, G theta * ‖palettePolynomial p b eta X k S theta‖ ^ (2 * s)) ≤
      ∫ theta, G theta * ((S.card : ℝ) ^ (2 * s - 1) * ∑ d ∈ S, f d theta) := by
    apply integral_mono hleft hright
    intro theta
    exact mul_le_mul_of_nonneg_left (palette_norm_power_le heta hs S theta) (sq_nonneg _)
  have heq : (fun theta => G theta * ((S.card : ℝ) ^ (2 * s - 1) * ∑ d ∈ S, f d theta)) =
      (fun theta => (S.card : ℝ) ^ (2 * s - 1) * ∑ d ∈ S, G theta * f d theta) := by
    funext theta
    rw [← Finset.mul_sum]
    ring
  rw [heq, integral_const_mul, integral_finsetSum _ (fun d _ => hi d)] at he
  have hm (d : ZMod p) : (∫ theta, G theta * f d theta) ≤ nextMixedMaximum p k a b xi X s colour := by
    exact mixedMoment_le_nextMixedMaximum colour
      ⟨nextClass p b eta d, nextClass_lt (p := p) (b := b) heta d⟩
  calc
    _ ≤ (S.card : ℝ) ^ (2 * s - 1) * ∑ d ∈ S, ∫ theta, G theta * f d theta := he
    _ ≤ (S.card : ℝ) ^ (2 * s - 1) * ((S.card : ℝ) * nextMixedMaximum p k a b xi X s colour) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ ∑ _d ∈ S, nextMixedMaximum p k a b xi X s colour := Finset.sum_le_sum (fun d _ => hm d)
        _ = _ := by simp
    _ = _ := by
      rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ 2 * s)]

/-- The original singular contribution is bounded by the explicit binomial and finite Holder cost times the actual finer mixed-moment maximum. -/
theorem singular_count_le_next_mixed_max {p k a b xi eta X s : ℕ} [NeZero p]
    (hkp : k ≤ p) (heta : eta < p ^ b) (hs : 0 < s) (colour : Fin k → Bool) :
    (singularCount (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) (s := s) colour : ℝ) ≤
      (p.choose (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ (2 * s) *
        nextMixedMaximum p k a b xi X s colour := by
  apply (singular_count_le_palette_mixed hkp colour).trans
  calc
    _ ≤ ∑ S ∈ smallPalettes p k,
        (S.card : ℝ) ^ (2 * s) * nextMixedMaximum p k a b xi X s colour :=
      Finset.sum_le_sum (fun S _ => palette_mixed_integral_le heta hs colour S)
    _ = _ := by
      have hc (S : Finset (ZMod p)) (hS : S ∈ smallPalettes p k) : S.card = k - 1 :=
        (Finset.mem_powersetCard.mp hS).2
      calc
        _ = ∑ _S ∈ smallPalettes p k,
            ((k - 1 : ℕ) : ℝ) ^ (2 * s) * nextMixedMaximum p k a b xi X s colour := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [hc S hS]
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, smallPalettes_card]; ring

end
end RiemannGaussian.VinogradovSingularConditioning
