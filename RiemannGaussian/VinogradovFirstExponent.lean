/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovInitialSaving

/-!
# An unconditional first improvement of the global Vinogradov exponent

For every k>=2 and u>=k, prove positive C and a finite threshold X0 with
J_((u+1)k,k)(X)<=C*X^(k(2u+1)-1/(3k)) for every X>=X0.
The initial p^(-1/3) saving is converted exactly on explicit power cutoffs.
A frequency-preserving injection proves monotonicity, and nearby power
cutoffs then cover every sufficiently large original interval. All packet
and prime thresholds are discharged; no moment estimate is assumed.

This is a first improvement over the repository's elementary exponent,
not the critical mean-value exponent needed for the full VK argument.
No new zero-free region or saving for the original weighted Riesz carrier
is asserted. The existential terminal threshold is not numerically evaluated.
-/

namespace RiemannGaussian.VinogradovFirstExponent
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovNormalizedIteration VinogradovCongruencingScaling VinogradovNonsingularConditioning
open VinogradovRemainderScaling VinogradovIteratedCongruencing
open VinogradovInitialSaving

/-- Convert the prime-scale saving to an exact exponent improvement at power cutoffs. -/
theorem first_saving_scale_identity (k L : ℕ) (hk : 0 < k) {A M : ℝ}
    (hA : 0 < A) (hM : 0 < M) :
    ((A * M) ^ k) ^ L * M ^ (-1 / 3 : ℝ) =
      A ^ (1 / 3 : ℝ) * ((A * M) ^ k) ^ ((L : ℝ) - 1 / (3 * (k : ℝ))) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hX : 0 < (A * M) ^ k := pow_pos (mul_pos hA hM) _
  rw [← Real.rpow_natCast ((A * M) ^ k) L]
  simp only [Real.rpow_def_of_pos hX, Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hM,
    ← Real.exp_add, Real.log_pow, Real.log_mul hA.ne' hM.ne']
  congr 1
  field_simp
  ring

/-- A concrete improvement by 1/(3k) in the global high-moment exponent on explicit growing cutoffs. -/
theorem global_meanValue_first_exponent_at_power_cutoff (M R k u : ℕ)
    (hk : 2 ≤ k) (hu : k ≤ u) (hM : 1 < M) (hpacket : 2 ^ R ≤ M)
    (hR : 2 * (k * (k * (k - 1))) < R) (hsize : 4 * k ^ 4 ≤ M)
    (hprime : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (M : ℝ)) :
    meanValue ((u + 1) * k) k ((2 ^ R * M) ^ k) ≤
      ((2 * (R : ℝ)) ^ 2 * firstSavingConstant k u * ((2 ^ R : ℕ) : ℝ) ^ (1 / 3 : ℝ)) *
        (((2 ^ R * M) ^ k : ℕ) : ℝ) ^
          (((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ))) := by
  have hbudget := VinogradovInitialIteration.packet_budget_at_power_cutoff M R k (k - 1)
    hM hpacket (by simpa only [Nat.add_sub_of_le (by omega : 1 ≤ k)] using hR)
  have hkm : 1 + (k - 1) = k := by omega
  rw [hkm] at hbudget
  have hsizeX : 4 * k ^ 4 ≤ (2 ^ R * M) ^ k := by
    have hbase : M ≤ 2 ^ R * M := Nat.le_mul_of_pos_left _ (by positivity)
    exact hsize.trans (hbase.trans (Nat.le_pow (by omega)))
  have he := global_meanValue_first_saving M R k u ((2 ^ R * M) ^ k)
    hk hu (by omega) (by omega) hbudget hsizeX (le_refl _) hprime
  apply he.trans_eq
  have hscale := first_saving_scale_identity k (k * (2 * u + 1)) (by omega)
    (A := ((2 ^ R : ℕ) : ℝ)) (M := (M : ℝ)) (by positivity) (by exact_mod_cast (by omega : 0 < M))
  simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at hscale ⊢
  calc
    _ = ((2 * (R : ℝ)) ^ 2 * firstSavingConstant k u) *
      ((((2 : ℝ) ^ R * M) ^ k) ^ (k * (2 * u + 1)) * (M : ℝ) ^ (-1 / 3 : ℝ)) := by ring
    _ = _ := by rw [hscale]; ring


/-- A frequency-preserving injection retains every original collision pair. -/
theorem crossCount_le_of_embedding {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (v : ι → d → ℤ) (w : κ → d → ℤ) (e : ι ↪ κ) (he : ∀ i, w (e i) = v i) :
    VinogradovCrossMoment.crossCount v v ≤ VinogradovCrossMoment.crossCount w w := by
  unfold VinogradovCrossMoment.crossCount
  apply Finset.card_le_card_of_injOn (fun xy => (e xy.1, e xy.2))
  · intro xy hxy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp only [he]
    exact (Finset.mem_filter.mp hxy).2
  · intro xy _ zw _ h
    exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))

/-- Increasing the original interval preserves every full equal-frequency solution. -/
theorem meanValue_mono (s k : ℕ) {X Y : ℕ} (hXY : X ≤ Y) :
    meanValue s k X ≤ meanValue s k Y := by
  simp only [meanValue, VinogradovInitialExceptional.moment_eq_crossCount]
  apply Nat.cast_le.mpr
  let e : (Fin s → Fin X) ↪ (Fin s → Fin Y) := ⟨fun x j => Fin.castLE hXY (x j), by
    intro x y he
    funext j
    exact Fin.ext (congrArg (fun z => (z j).val) he)⟩
  exact crossCount_le_of_embedding _ _ e (fun _ => rfl)

/-- Every sufficiently large endpoint lies below a nearby explicit power cutoff whose base exceeds a prescribed threshold. -/
theorem exists_nearby_power_cutoff (A k B X : ℕ) (hA : 0 < A) (hk : 0 < k)
    (hB : 1 ≤ B) (hX : (A * B) ^ k < X) :
    ∃ M : ℕ, B < M ∧ X ≤ (A * M) ^ k ∧ (A * M) ^ k ≤ 2 ^ k * X := by
  have hex : ∃ M : ℕ, X ≤ (A * M) ^ k := by
    refine ⟨X, ?_⟩
    exact (Nat.le_mul_of_pos_left X hA).trans (Nat.le_pow hk)
  let M := Nat.find hex
  have hupper : X ≤ (A * M) ^ k := Nat.find_spec hex
  have hBM : B < M := by
    by_contra h
    have hc := Nat.pow_le_pow_left (Nat.mul_le_mul_left A (by omega : M ≤ B)) k
    omega
  have hM2 : 2 ≤ M := by omega
  have hprev : (A * (M - 1)) ^ k < X := Nat.lt_of_not_ge (Nat.find_min hex (by omega : M - 1 < M))
  refine ⟨M, hBM, hupper, ?_⟩
  have hbase : A * M ≤ 2 * (A * (M - 1)) := by
    have hstep : M ≤ 2 * (M - 1) := by omega
    nlinarith
  calc
    _ ≤ (2 * (A * (M - 1))) ^ k := Nat.pow_le_pow_left hbase _
    _ = 2 ^ k * (A * (M - 1)) ^ k := mul_pow _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ hprev.le

/-- The first improved moment exponent is positive throughout the actual degree/order range. -/
theorem first_exponent_pos {k u : ℕ} (hk : 2 ≤ k) (hu : k ≤ u) :
    0 < (((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ))) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have huR : (k : ℝ) ≤ u := by exact_mod_cast hu
  have hfrac : 1 / (3 * (k : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  push_cast
  nlinarith

/-- The improved exponent holds at every endpoint above an explicit fixed threshold, not just at the power cutoffs. -/
theorem global_meanValue_first_exponent (R k u B X : ℕ)
    (hk : 2 ≤ k) (hu : k ≤ u) (hB : 2 ≤ B) (hpacket : 2 ^ R ≤ B)
    (hR : 2 * (k * (k * (k - 1))) < R) (hsize : 4 * k ^ 4 ≤ B)
    (hprime : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (B : ℝ))
    (hX : (2 ^ R * B) ^ k < X) :
    meanValue ((u + 1) * k) k X ≤
      ((2 * (R : ℝ)) ^ 2 * firstSavingConstant k u * ((2 ^ R : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
        ((2 ^ k : ℕ) : ℝ) ^ ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ))))) *
          (X : ℝ) ^ ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) := by
  obtain ⟨M, hBM, hXY, hYX⟩ := exists_nearby_power_cutoff (2 ^ R) k B X
    (by positivity) (by omega) (by omega) hX
  have he := global_meanValue_first_exponent_at_power_cutoff M R k u hk hu (by omega)
    (hpacket.trans hBM.le) hR (hsize.trans hBM.le) (hprime.trans (by exact_mod_cast hBM.le))
  have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((2 ^ R * M) ^ k : ℕ))
    (by exact_mod_cast hYX : (((2 ^ R * M) ^ k : ℕ) : ℝ) ≤ ((2 ^ k * X : ℕ) : ℝ))
    (first_exponent_pos hk hu).le
  apply (meanValue_mono ((u + 1) * k) k hXY).trans (he.trans _)
  calc
    _ ≤ ((2 * (R : ℝ)) ^ 2 * firstSavingConstant k u * ((2 ^ R : ℕ) : ℝ) ^ (1 / 3 : ℝ)) *
      ((2 ^ k * X : ℕ) : ℝ) ^ ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) :=
      mul_le_mul_of_nonneg_left hp (by unfold firstSavingConstant selectionCost elementaryConstant; positivity)
    _ = _ := by
      rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
      ring


/-- The original global mean value has an unconditional first improved exponent for every degree at least two and every u at least k. -/
theorem exists_global_first_exponent (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      meanValue ((u + 1) * k) k X ≤
        C * (X : ℝ) ^ ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) := by
  let R := 2 * (k * (k * (k - 1))) + 1
  have hR : 2 * (k * (k * (k - 1))) < R := by unfold R; omega
  obtain ⟨B, hB⟩ := exists_nat_ge (max (2 : ℝ)
    (max ((2 ^ R : ℕ) : ℝ) (max ((4 * k ^ 4 : ℕ) : ℝ)
      ((elementaryConstant k u * iterationConstant k u) ^ 2))))
  have hB2 : 2 ≤ B := by exact_mod_cast (le_max_left _ _).trans hB
  have hinner := (le_max_right _ _).trans hB
  have hpacket : 2 ^ R ≤ B := by exact_mod_cast (le_max_left _ _).trans hinner
  have hlast := (le_max_right _ _).trans hinner
  have hsize : 4 * k ^ 4 ≤ B := by exact_mod_cast (le_max_left _ _).trans hlast
  have hprime : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (B : ℝ) :=
    (le_max_right _ _).trans hlast
  let C := (2 * (R : ℝ)) ^ 2 * firstSavingConstant k u * ((2 ^ R : ℕ) : ℝ) ^ (1 / 3 : ℝ) *
    ((2 ^ k : ℕ) : ℝ) ^ ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ))))
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by unfold R; omega : 0 < R)
  have hF : 0 < firstSavingConstant k u := by
    unfold firstSavingConstant selectionCost elementaryConstant
    positivity
  refine ⟨C, ?_, (2 ^ R * B) ^ k + 1, ?_⟩
  · unfold C
    positivity
  · intro X hX
    exact global_meanValue_first_exponent R k u B X hk hu hB2 hpacket hR hsize hprime (by omega)

end
end RiemannGaussian.VinogradovFirstExponent
