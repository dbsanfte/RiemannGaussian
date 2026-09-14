/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovNegativeProfile

/-!
# The negative conditioned profile saves the original global moment

Cap the proved negative profile at -1/2 and use the complete initial
conditioning allowance at depth one. Its deep remainder and its entire
intermediate level then share one negative prime-power bound. The initial
residue cost cancels the full moment normalization exactly at any real
exponent. A genuine separating prime packet transfers that saving to the
original global mean value, with every conditioned-energy premise discharged.

The general source is a stated homogeneous moment budget above critical.
All prime-size, packet, padded-quotient and finite-depth conditions remain
explicit. The global exponent bootstrap discharges them at growing cutoffs.
-/

namespace RiemannGaussian.VinogradovProfileSaving
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovNormalizedIteration VinogradovCongruencingScaling VinogradovNonsingularConditioning
open VinogradovProfileIteration VinogradovNegativeProfile

/-- The negative profile controls the complete initial allowance at depth one, including its deep remainder. -/
theorem exists_initial_allowance_saving {k u N₀ : ℕ} {C lam : ℝ}
    (hk : 2 ≤ k) (hu : k ≤ u) (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 < lam)
    (hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) :
    ∃ beta : ℝ, -(1 / 2 : ℝ) ≤ beta ∧ beta < 0 ∧ ∃ S : ℕ, 2 ≤ S ∧
      ∃ B : ℝ, 1 ≤ B ∧ ∀ (p xi X : ℕ) [Fact p.Prime],
      p ^ S ≤ X → N₀ ≤ X / p ^ S + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) →
      ∀ colour : Fin k → Bool,
      conditioningAllowance p k 0 1 xi X u 1 colour lam ≤ B * (p : ℝ) ^ beta := by
  obtain ⟨beta, hbeta, T, hT, B, hB, he⟩ := exists_negative_profile hk hu hC hlam hbudget
  let beta' := max beta (-(1 / 2 : ℝ))
  have hbeta' : beta' < 0 := max_lt hbeta (by norm_num)
  have hB0 : 0 ≤ B := by linarith
  have hE0 : 0 ≤ selectionCost k u := by unfold selectionCost; positivity
  refine ⟨beta', le_max_right _ _, hbeta', max T 2, le_max_right _ _,
    1 + selectionCost k u * B, by nlinarith, ?_⟩
  intro p xi X inst hX hN hp colour
  have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : p.Prime)).le
  obtain ⟨hXT, hNT⟩ := quotient_budget_mono hp0 (le_max_left T 2) hX hN
  have hn : normalizedLevel p k 0 1 xi X u colour lam ≤ B * (p : ℝ) ^ beta := by
    apply normalized_level_le_of_all ((Nat.pow_pos hp0).trans_le hX) colour lam _
    intro eta heta colourB
    have ha := he p 0 1 xi eta X (by omega)
      (by simpa only [mul_one] using hXT) (by simpa only [mul_one] using hNT) hp heta colour colourB
    simpa only [Nat.cast_zero, Nat.cast_one, mul_zero, zero_add, mul_one] using ha
  have hn' := hn.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hp1 (le_max_left beta (-(1 / 2 : ℝ)))) hB0)
  unfold conditioningAllowance
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, mul_zero,
    Real.rpow_zero, one_mul, add_zero, Nat.cast_one]
  calc
    _ ≤ (p : ℝ) ^ beta' + selectionCost k u * (B * (p : ℝ) ^ beta') :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hp1 (le_max_right _ _))
        (mul_le_mul_of_nonneg_left hn' hE0)
    _ = _ := by ring

/-- The initial residue cost cancels the full source normalization at every real exponent. -/
theorem initial_scale_identity {x P : ℝ} (hx : 0 < x) (hP : 0 < P) (k u lam : ℝ) :
    P ^ (2 * k * u) * momentScale x P k u 0 1 lam = x ^ lam := by
  unfold momentScale
  simp_rw [VinogradovRemainderScaling.quotient_power_exp hx hP]
  simp only [Real.rpow_def_of_pos hP, Real.rpow_def_of_pos hx, ← Real.exp_add]
  congr 1
  ring

/-- A general admissible homogeneous exponent above critical admits an independent prime-scale saving in the original global mean value, with every conditioned energy discharged. -/
theorem exists_global_profile_saving {k u N₀ : ℕ} {C lam : ℝ}
    (hk : 2 ≤ k) (hu : k ≤ u) (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 < lam)
    (hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) :
    ∃ beta : ℝ, -(1 / 2 : ℝ) ≤ beta ∧ beta < 0 ∧ ∃ S : ℕ, 2 ≤ S ∧
      ∃ B : ℝ, 1 ≤ B ∧ ∀ M R X : ℕ,
      0 < M → 0 < R → X ^ (k * (k - 1)) < M ^ R → 4 * k ^ 4 ≤ X →
      (2 ^ R * M) ^ S ≤ X → N₀ ≤ X / (2 ^ R * M) ^ S + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (M : ℝ) →
      meanValue ((u + 1) * k) k X ≤
        (2 * (R : ℝ)) ^ 2 * B * (X : ℝ) ^ lam * (M : ℝ) ^ beta := by
  obtain ⟨beta, hbetalow, hbeta, S, hS, B, hB, hallow⟩ :=
    exists_initial_allowance_saving hk hu hC hlam hbudget
  refine ⟨beta, hbetalow, hbeta, S, hS, B, hB, ?_⟩
  intro M R X hM hR hpacket hsize hcutoff hN hprime
  obtain ⟨p, hp, hMp, hpM, eta, hentry⟩ :=
    VinogradovInitialConditioning.exists_initial_conditioning M R k (k * u) X
      hk (Nat.mul_pos (by omega) (by omega)) hM hR hpacket hsize
  let : Fact p.Prime := ⟨hp⟩
  have hpow : p ^ S ≤ (2 ^ R * M) ^ S := Nat.pow_le_pow_left hpM _
  have hXp : p ^ S ≤ X := hpow.trans hcutoff
  have hquot : X / (2 ^ R * M) ^ S ≤ X / p ^ S :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos hp.pos)).mpr
      ((Nat.mul_le_mul_left _ hpow).trans (Nat.div_mul_le_self X ((2 ^ R * M) ^ S)))
  have hNp : N₀ ≤ X / p ^ S + 1 := by omega
  have hprimep : (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) :=
    hprime.trans (by exact_mod_cast hMp.le)
  have hXpos : 0 < X := (Nat.pow_pos hp.pos).trans_le hXp
  obtain ⟨hX0, hN0⟩ := quotient_budget_mono hp.pos (show 0 ≤ S by omega) hXp hNp
  obtain ⟨hX2, hN2⟩ := quotient_budget_mono hp.pos hS hXp hNp
  have hlevel : VinogradovSingularConditioning.mixedMoment p k 0 1 0 eta.val X (k * u)
      (fun _ => true) ≤ levelMixedMaximum p k 0 1 0 X u (fun _ => true) := by
    unfold levelMixedMaximum
    apply Finset.le_sup'
      (fun c : Fin (p ^ 1) => VinogradovSingularConditioning.mixedMoment p k 0 1 0 c.val X
        (k * u) (fun _ => true)) (b := ⟨eta.val, by simpa only [pow_one] using eta.isLt⟩)
    exact Finset.mem_univ _
  have hiteration := mixed_le_scale_allowance_of_scaled_bounds (a := 0) (b := 1) (xi := 0)
    (H := 1) hk hu (by omega) (by omega) (by omega) hXpos hC hlam.le hprimep
    (hbudget p 0 X hp.pos hX0 hN0) (hbudget p 2 X hp.pos hX2 hN2) (fun _ => true)
  have hscale := momentScale_pos (show (0 : ℝ) < X by exact_mod_cast hXpos)
    (show (0 : ℝ) < p by exact_mod_cast hp.pos) (k : ℝ) (u : ℝ) 0 1 lam
  have hI := hlevel.trans (hiteration.trans (mul_le_mul_of_nonneg_left
    (hallow p 0 X hXp hNp hprimep (fun _ => true))
      (by simpa only [Nat.cast_zero, Nat.cast_one] using hscale.le)))
  have he := hentry.trans (mul_le_mul_of_nonneg_left hI (by positivity))
  have horder : k + k * u = (u + 1) * k := by ring
  rw [horder] at he
  have hid : (p : ℝ) ^ (2 * (k * u)) * momentScale X p k u 0 1 lam = (X : ℝ) ^ lam := by
    have h := initial_scale_identity (show (0 : ℝ) < X by exact_mod_cast hXpos)
      (show (0 : ℝ) < p by exact_mod_cast hp.pos) (k : ℝ) (u : ℝ) lam
    simpa only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using h
  have hP : (p : ℝ) ^ beta ≤ (M : ℝ) ^ beta :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hM) (by exact_mod_cast hMp.le) hbeta.le
  calc
    _ ≤ _ := he
    _ = (2 * (R : ℝ)) ^ 2 * B *
        ((p : ℝ) ^ (2 * (k * u)) * momentScale X p k u 0 1 lam) * (p : ℝ) ^ beta := by
      simp only [Nat.cast_zero, Nat.cast_one]
      ring
    _ = (2 * (R : ℝ)) ^ 2 * B * (X : ℝ) ^ lam * (p : ℝ) ^ beta := by rw [hid]
    _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)

end
end RiemannGaussian.VinogradovProfileSaving
