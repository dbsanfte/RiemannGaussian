/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovInitialConditioning
import RiemannGaussian.VinogradovNormalizedIteration

/-!
# Initial global conditioning reaches the actual finite recurrence

One prime from the uniform separating packet enters the existing finite
conditioning recurrence. Its initial residue cost cancels exactly against
the source normalization. The full global mean value is therefore bounded
by the actual normalized remainder and complete intermediate-energy sum.

The prime threshold and finite cutoff are paid by explicit conditions on
the packet parameters. No upper mean-value budget is assumed. The remaining
conditioned energies receive a first independent saving in
`VinogradovInitialSaving`; this finite entry alone gives no VK zero-free region.
-/

namespace RiemannGaussian.VinogradovInitialIteration
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovInitialConditioning
open VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovNormalizedIteration VinogradovCongruencingScaling

/-- The literal initial residue cost cancels the fine scale exactly. -/
theorem initial_scale_identity (p k X u : ℕ) (hp : 0 < p) :
    (p : ℝ) ^ (2 * (k * u)) *
      momentScale X p k u 0 1 (((k * (2 * u + 1) : ℕ) : ℝ)) =
        (X : ℝ) ^ (k * (2 * u + 1)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hscale := elementary_scale p k 0 1 X u
  simp only [Nat.cast_zero, Nat.cast_one] at hscale
  rw [hscale]
  simp only [pow_zero, div_one, pow_one, div_pow]
  calc
    _ = (X : ℝ) ^ k * (X : ℝ) ^ (2 * (k * u)) := by field_simp
    _ = _ := by rw [← pow_add]; congr 1; ring

/-- The original global mean value reaches the full actual finite allowance at one eligible prime, with no supplied moment estimate. -/
theorem exists_initial_finite_iteration (M R k u H X : ℕ)
    (hk : 2 ≤ k) (hu : k ≤ u) (hH : 1 ≤ H) (hM : 0 < M) (hR : 0 < R)
    (hbudget : X ^ (k * (k - 1)) < M ^ R) (hsize : 4 * k ^ 4 ≤ X)
    (hcutoff : (2 ^ R * M) ^ (1 + H) ≤ X)
    (hprime : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (M : ℝ)) :
    ∃ (p : ℕ) (hp : p.Prime),
      let _ : NeZero p := ⟨hp.ne_zero⟩
      M < p ∧ p ≤ 2 ^ R * M ∧
        meanValue ((u + 1) * k) k X ≤
          (2 * (R : ℝ)) ^ 2 * (X : ℝ) ^ (k * (2 * u + 1)) *
            conditioningAllowance p k 0 1 0 X u H (fun _ => true)
              (((k * (2 * u + 1) : ℕ) : ℝ)) := by
  obtain ⟨p, hp, hMp, hpM, eta, hentry⟩ := exists_initial_conditioning
    M R k (k * u) X hk (Nat.mul_pos (by omega) (by omega)) hM hR hbudget hsize
  let : NeZero p := ⟨hp.ne_zero⟩
  have hlevel : VinogradovSingularConditioning.mixedMoment p k 0 1 0 eta.val X (k * u)
      (fun _ => true) ≤ levelMixedMaximum p k 0 1 0 X u (fun _ => true) := by
    unfold levelMixedMaximum
    apply Finset.le_sup'
      (fun c : Fin (p ^ 1) => VinogradovSingularConditioning.mixedMoment p k 0 1 0 c.val X
        (k * u) (fun _ => true)) (b := ⟨eta.val, by simpa only [pow_one] using eta.isLt⟩)
    exact Finset.mem_univ _
  have hcost : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (p : ℝ) :=
    hprime.trans (by exact_mod_cast hMp.le)
  have hX : p ^ (1 + H) ≤ X := (Nat.pow_le_pow_left hpM _).trans hcutoff
  have hiteration := mixed_le_scale_allowance (a := 0) (b := 1) (xi := 0)
    hk hu (by omega) hH (by omega) hX hcost (fun _ => true)
  have hbound := hentry.trans (mul_le_mul_of_nonneg_left
    (hlevel.trans hiteration) (by positivity))
  refine ⟨p, hp, hMp, hpM, ?_⟩
  have horder : k + k * u = (u + 1) * k := by ring
  rw [horder] at hbound
  calc
    _ ≤ _ := hbound
    _ = _ := by
      simp only [Nat.cast_zero, Nat.cast_one]
      rw [mul_assoc, ← mul_assoc ((p : ℝ) ^ _)]
      rw [initial_scale_identity p k X u hp.pos]
      ring

/-- The packet budget is realized at explicit power cutoffs for arbitrarily large base parameters. -/
theorem packet_budget_at_power_cutoff (M R k H : ℕ) (hM : 1 < M)
    (hpacket : 2 ^ R ≤ M) (hR : 2 * ((1 + H) * (k * (k - 1))) < R) :
    ((2 ^ R * M) ^ (1 + H)) ^ (k * (k - 1)) < M ^ R := by
  have hbase : 2 ^ R * M ≤ M ^ 2 := by nlinarith
  calc
    _ = (2 ^ R * M) ^ ((1 + H) * (k * (k - 1))) := by rw [← pow_mul]
    _ ≤ (M ^ 2) ^ ((1 + H) * (k * (k - 1))) := Nat.pow_le_pow_left hbase _
    _ = M ^ (2 * ((1 + H) * (k * (k - 1)))) := by rw [← pow_mul]
    _ < _ := Nat.pow_lt_pow_right hM hR

/-- On explicit growing cutoffs, the initial finite recurrence needs only fixed degree/depth thresholds and a sufficiently large base. -/
theorem initial_finite_iteration_at_power_cutoff (M R k u H : ℕ)
    (hk : 2 ≤ k) (hu : k ≤ u) (hH : 1 ≤ H) (hM : 1 < M)
    (hpacket : 2 ^ R ≤ M) (hR : 2 * ((1 + H) * (k * (k - 1))) < R)
    (hsize : 4 * k ^ 4 ≤ M)
    (hprime : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (M : ℝ)) :
    ∃ (p : ℕ) (hp : p.Prime),
      let _ : NeZero p := ⟨hp.ne_zero⟩
      M < p ∧ p ≤ 2 ^ R * M ∧
        meanValue ((u + 1) * k) k ((2 ^ R * M) ^ (1 + H)) ≤
          (2 * (R : ℝ)) ^ 2 * (((2 ^ R * M) ^ (1 + H) : ℕ) : ℝ) ^ (k * (2 * u + 1)) *
            conditioningAllowance p k 0 1 0 ((2 ^ R * M) ^ (1 + H)) u H (fun _ => true)
              (((k * (2 * u + 1) : ℕ) : ℝ)) := by
  apply exists_initial_finite_iteration M R k u H _ hk hu hH (by omega) (by omega)
    (packet_budget_at_power_cutoff M R k H hM hpacket hR)
  · have hbase : M ≤ 2 ^ R * M := Nat.le_mul_of_pos_left _ (by positivity)
    exact hsize.trans (hbase.trans (Nat.le_pow (by omega)))
  · exact le_refl _
  · exact hprime

end
end RiemannGaussian.VinogradovInitialIteration
