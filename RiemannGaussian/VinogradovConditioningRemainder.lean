/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNonsingularConditioning

/-!
# Finite conditioning with its actual higher-moment remainder

The original mixed moment receives a two-scale Holder bound in actual
homogeneous moments, with every quotient endpoint retained. The proved
one-step conditioning inequality then iterates to every finite depth.
All residue maxima, induced-colour maxima and accumulated costs are actual;
the original signed mixed moments remain upstream of these maxima.

These are the finite ingredients of Wooley (2012), equations (5.4)-(5.5).
The explicit deep-remainder power saving is in
`VinogradovConditioningPowerSaving`; full high-moment iteration is still open.
-/

namespace RiemannGaussian.VinogradovConditioningRemainder
noncomputable section
open UnitAddTorus MeasureTheory
open VinogradovMeanValue VinogradovShiftedMoment VinogradovPartitionEnergy
open VinogradovResidueEnergy VinogradovResidueMoment VinogradovProductEnergy
open VinogradovConditioningHolder VinogradovSingularConditioning
open VinogradovNonsingularConditioning
/-- Use the original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Bound the actual full residue moment by the homogeneous moment with its exact padded quotient endpoint. -/
theorem residue_moment_le {p b eta X r k : ℕ} [NeZero p] :
    (∫ theta : UnitAddTorus (Fin k),
      ‖VinogradovCongruenceEnergy.residuePolynomial (p ^ b) eta X k 1 theta‖ ^ (2 * r)) ≤
      meanValue r k (X / p ^ b + 1) := by
  simp only [VinogradovCongruenceEnergy.residuePolynomial, one_mul]
  change moment r (fun n : ResidueWindow (p ^ b) eta X => monomialFrequency k (n.val.val + 1)) ≤ _
  rw [moment_eq_collisionCount]
  have he := residue_window_shift_le_meanValue (q := p ^ b) (xi := eta) (X := X)
    (NeZero.ne (p ^ b)) r k 0
  simpa only [tupleFrequency_count_zero] using he

/-- The two-scale pointwise Holder factorization includes zero values and every positive integer order. -/
theorem separated_atom {k u : ℕ} (hu : 0 < u) {g f : ℝ} (hg : 0 ≤ g) (hf : 0 ≤ f) :
    (g ^ (2 * (u + 1))) ^ (1 / ((u + 1 : ℕ) : ℝ)) *
      (f ^ (2 * ((u + 1) * k))) ^ (1 - 1 / ((u + 1 : ℕ) : ℝ)) =
      g ^ 2 * f ^ (2 * (k * u)) := by
  have he := conditioning_atom (k := k) (q := u + 1) (by omega)
    (w := 1) (g := g ^ 2) (f := f ^ 2) (by norm_num) (pow_nonneg hg _) (pow_nonneg hf _)
  simp only [one_mul, Nat.add_sub_cancel, ← pow_mul] at he
  have hexp : 2 * (k * (u + 1)) = 2 * ((u + 1) * k) := by ring
  simpa only [hexp] using he

/-- The original signed mixed moment receives actual homogeneous moments at both quotient scales. -/
theorem mixed_le_higher_moments {p k a b xi eta X u : ℕ} [NeZero p]
    (hu : 0 < u) (colour : Fin k → Bool) :
    mixedMoment p k a b xi eta X (k * u) colour ≤
      meanValue ((u + 1) * k) k (X / p ^ a + 1) ^ (1 / ((u + 1 : ℕ) : ℝ)) *
      meanValue ((u + 1) * k) k (X / p ^ b + 1) ^ (1 - 1 / ((u + 1 : ℕ) : ℝ)) := by
  let A := polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colour) (fun _ => 1)
  let f := VinogradovCongruenceEnergy.residuePolynomial (p ^ b) eta X k 1
  have hA : Continuous A := continuous_polynomial _ _
  have hf : Continuous f := by unfold f VinogradovCongruenceEnergy.residuePolynomial; fun_prop
  have huR : (1 : ℝ) < ((u + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < u + 1)
  have hpos : 0 < 1 / ((u + 1 : ℕ) : ℝ) := by positivity
  have hlt : 1 / ((u + 1 : ℕ) : ℝ) < 1 := (div_lt_one (by linarith)).mpr huR
  have he := VinogradovInterpolation.integral_geometric_le hpos hlt
    (fun theta => ‖A theta‖ ^ (2 * (u + 1)))
    (fun theta => ‖f theta‖ ^ (2 * ((u + 1) * k)))
    (hA.norm.pow _) (hf.norm.pow _) (fun _ => by positivity) (fun _ => by positivity)
  simp only [separated_atom hu (norm_nonneg _) (norm_nonneg _)] at he
  apply he.trans
  apply mul_le_mul
  · exact Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity))
      (VinogradovConditionedHigherMoment.conditioned_moment_le colour) hpos.le
  · exact Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity))
      residue_moment_le (by linarith)
  · exact Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _
  · exact Real.rpow_nonneg (by rw [meanValue_eq_count]; positivity) _

/-- The actual finite maximum of original mixed moments over canonical tail residues. -/
def levelMixedMaximum (p k a b xi X u : ℕ) [NeZero p] (colour : Fin k → Bool) : ℝ :=
  (Finset.univ : Finset (Fin (p ^ b))).sup' Finset.univ_nonempty
    (fun c => mixedMoment p k a b xi c.val X (k * u) colour)

/-- The actual finite maximum over canonical tail residues and induced block colours. -/
def levelConditionedMaximum (p k a b xi X u : ℕ) [NeZero p] (colour : Fin k → Bool) : ℝ :=
  (Finset.univ : Finset (Fin (p ^ b))).sup' Finset.univ_nonempty
    (fun c => conditionedMaximum p k a b xi c.val X u colour)

/-- The complete explicit coefficient of the next-level moment in one conditioning step. -/
def singularCost (p k u : ℕ) : ℝ :=
  (2 * u : ℝ) * (p.choose (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ (2 * (k * u))

/-- The complete ordered-block selection cost after Holder absorption. -/
def selectionCost (k u : ℕ) : ℝ := ((2 * (k * u)).descFactorial k : ℝ) ^ (2 * u)

/-- Each canonical conditioned maximum lies below the actual level maximum. -/
theorem level_conditioned_le {p k a b xi X u : ℕ} [NeZero p]
    (colour : Fin k → Bool) (c : Fin (p ^ b)) :
    conditionedMaximum p k a b xi c.val X u colour ≤ levelConditionedMaximum p k a b xi X u colour :=
  Finset.le_sup' (fun d : Fin (p ^ b) => conditionedMaximum p k a b xi d.val X u colour)
    (Finset.mem_univ c)

/-- Apply the proved original conditioning inequality uniformly over the actual finite residue maximum. -/
theorem level_conditioning_step {p k a b xi X u : ℕ} [NeZero p]
    (hkp : k ≤ p) (hk : 0 < k) (hu : 0 < u) (colour : Fin k → Bool) :
    levelMixedMaximum p k a b xi X u colour ≤
      singularCost p k u * levelMixedMaximum p k a (b + 1) xi X u colour +
        selectionCost k u * levelConditionedMaximum p k a b xi X u colour := by
  apply Finset.sup'_le Finset.univ_nonempty
  intro c hc
  have he := conditioning_step (a := a) (xi := xi) (X := X) hkp hk c.isLt hu colour
  apply he.trans
  have hK := mul_le_mul_of_nonneg_left (level_conditioned_le (p := p) (a := a) (xi := xi)
    (X := X) (u := u) colour c) (show 0 ≤ selectionCost k u by unfold selectionCost; positivity)
  change (2 * u : ℝ) * ((p.choose (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ (2 * (k * u)) *
    levelMixedMaximum p k a (b + 1) xi X u colour) +
    selectionCost k u * conditionedMaximum p k a b xi c.val X u colour ≤ _
  calc
    _ ≤ (2 * u : ℝ) * ((p.choose (k - 1) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ (2 * (k * u)) *
        levelMixedMaximum p k a (b + 1) xi X u colour) +
        selectionCost k u * levelConditionedMaximum p k a b xi X u colour :=
      add_le_add (le_refl _) hK
    _ = _ := by unfold singularCost; ring

/-- Iterate a quantitative recurrence to a finite depth while retaining every weighted intermediate term. -/
theorem finite_step_iteration (A D : ℝ) (hA : 0 ≤ A) (I K : ℕ → ℝ)
    (hstep : ∀ b, I b ≤ A * I (b + 1) + D * K b) (b H : ℕ) :
    I b ≤ A ^ H * I (b + H) + D * ∑ h ∈ Finset.range H, A ^ h * K (b + h) := by
  induction H with
  | zero => simp
  | succ H ih =>
    calc
      I b ≤ A ^ H * I (b + H) + D * ∑ h ∈ Finset.range H, A ^ h * K (b + h) := ih
      _ ≤ A ^ H * (A * I (b + H + 1) + D * K (b + H)) +
          D * ∑ h ∈ Finset.range H, A ^ h * K (b + h) :=
        add_le_add (mul_le_mul_of_nonneg_left (hstep (b + H)) (pow_nonneg hA H)) (le_refl _)
      _ = _ := by rw [Finset.sum_range_succ, pow_succ]; simp only [Nat.add_assoc]; ring

/-- The actual original mixed maximum receives a finite conditioned sum and its explicit deeper-level remainder. -/
theorem finite_conditioning_iteration {p k a xi X u : ℕ} [NeZero p]
    (hkp : k ≤ p) (hk : 0 < k) (hu : 0 < u) (colour : Fin k → Bool) (b H : ℕ) :
    levelMixedMaximum p k a b xi X u colour ≤
      singularCost p k u ^ H * levelMixedMaximum p k a (b + H) xi X u colour +
      selectionCost k u * ∑ h ∈ Finset.range H,
        singularCost p k u ^ h * levelConditionedMaximum p k a (b + h) xi X u colour := by
  apply finite_step_iteration (singularCost p k u) (selectionCost k u)
    (by unfold singularCost; positivity)
    (fun b => levelMixedMaximum p k a b xi X u colour)
    (fun b => levelConditionedMaximum p k a b xi X u colour)
  intro j
  exact level_conditioning_step hkp hk hu colour

/-- The entire actual deeper-residue maximum has the same two-scale homogeneous moment bound. -/
theorem level_mixed_le_higher {p k a b xi X u : ℕ} [NeZero p]
    (hu : 0 < u) (colour : Fin k → Bool) :
    levelMixedMaximum p k a b xi X u colour ≤
      meanValue ((u + 1) * k) k (X / p ^ a + 1) ^ (1 / ((u + 1 : ℕ) : ℝ)) *
      meanValue ((u + 1) * k) k (X / p ^ b + 1) ^ (1 - 1 / ((u + 1 : ℕ) : ℝ)) := by
  apply Finset.sup'_le Finset.univ_nonempty
  intro c hc
  exact mixed_le_higher_moments hu colour

/-- Replace the iterated remainder by its actual homogeneous moments, retaining all finite costs and rounding. -/
theorem finite_conditioning_remainder {p k a xi X u : ℕ} [NeZero p]
    (hkp : k ≤ p) (hk : 0 < k) (hu : 0 < u) (colour : Fin k → Bool) (b H : ℕ) :
    levelMixedMaximum p k a b xi X u colour ≤
      singularCost p k u ^ H *
        (meanValue ((u + 1) * k) k (X / p ^ a + 1) ^ (1 / ((u + 1 : ℕ) : ℝ)) *
         meanValue ((u + 1) * k) k (X / p ^ (b + H) + 1) ^ (1 - 1 / ((u + 1 : ℕ) : ℝ))) +
      selectionCost k u * ∑ h ∈ Finset.range H,
        singularCost p k u ^ h * levelConditionedMaximum p k a (b + h) xi X u colour := by
  apply (finite_conditioning_iteration hkp hk hu colour b H).trans
  apply add_le_add _ (le_refl _)
  exact mul_le_mul_of_nonneg_left (level_mixed_le_higher hu colour)
    (pow_nonneg (by unfold singularCost; positivity) H)

end
end RiemannGaussian.VinogradovConditioningRemainder
