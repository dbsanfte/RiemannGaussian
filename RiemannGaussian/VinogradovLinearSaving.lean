/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovLinearProfile

/-!
# Linear constant transport from negative profiles to the global moment

The complete initial allowance, actual prime packet and original global
mean value retain a multiplier chosen before the homogeneous source
constant. The prime threshold depends only on the iteration cost. This
version still clips the initial negative profile at minus one half; the
stronger defect remainder is available upstream for further improvement.
-/

namespace RiemannGaussian.VinogradovLinearSaving
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovRemainderScaling
open VinogradovConditioningPowerSaving VinogradovSingularConditioning
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovNonsingularConditioning VinogradovProfileIteration
open VinogradovFirstExponent VinogradovExponentBootstrap
open VinogradovDefectRemainder
open VinogradovConstantPreservation
open VinogradovLinearProfile

/-- A fixed positive defect gives one negative profile and constants before
choosing the source constant, with exact linear dependence on that constant. -/
theorem exists_linear_negative_profile (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 < defect) :
    ∃ beta : ℝ, beta < 0 ∧ ∃ T : ℕ, 1 ≤ T ∧ ∃ B : ℝ, 1 ≤ B ∧
      ∀ C : ℝ, 1 ≤ C → ∀ (lam : ℝ) (N₀ : ℕ),
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
        meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) →
      let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
      ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ (T * b) ≤ X → N₀ ≤ X / p ^ (T * b) + 1 →
      iterationConstant k u ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
        (C * B) * (p : ℝ) ^ (delta * a + beta * b) := by
  have hu1 : (1 : ℝ) < u := by exact_mod_cast (by omega : 1 < u)
  have hr : (k : ℝ) / u ≤ 1 := (div_le_one (by linarith)).mpr (by exact_mod_cast hu)
  have hc : 0 < (1 - 1 / (u : ℝ)) * defect := by
    have he : 1 / (u : ℝ) < 1 := (div_lt_one (by linarith)).mpr hu1
    exact mul_pos (by linarith) hdefect0
  obtain ⟨n, hn⟩ := exists_negative_affineProfile (B := (k : ℝ) * u) hr hc
  obtain ⟨T, hT, B, hB, he⟩ := linear_constant_profile_iteration k u hk hu defect hdefect0.le n
  exact ⟨_, hn, T, hT, B, hB, he⟩

/-- The complete initial allowance has a negative exponent and depth independent of the source exponent, constant and quotient threshold. -/
theorem exists_linear_initial_allowance (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 < defect) :
    ∃ beta : ℝ, -(1 / 2 : ℝ) ≤ beta ∧ -defect / 2 ≤ beta ∧ beta < 0 ∧
      ∃ S : ℕ, 2 ≤ S ∧ ∃ B : ℝ, 1 ≤ B ∧ ∀ C : ℝ, 1 ≤ C →
      ∀ (lam : ℝ) (N₀ : ℕ),
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
        meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) →
      ∀ (p xi X : ℕ) [Fact p.Prime],
      p ^ S ≤ X → N₀ ≤ X / p ^ S + 1 →
      iterationConstant k u ^ 2 ≤ (p : ℝ) →
      ∀ colour : Fin k → Bool,
      constantAllowance C p k 0 1 xi X u 1 colour lam ≤ (C * B) * (p : ℝ) ^ beta := by
  obtain ⟨beta, hbeta, T, hT, B, hB, hprev⟩ := exists_linear_negative_profile k u hk hu defect hdefect0
  let beta' := max beta (max (-(1 / 2 : ℝ)) (-defect / 2))
  have hhalf : -(1 / 2 : ℝ) ≤ beta' := (le_max_left _ _).trans (le_max_right _ _)
  have hdef : -defect / 2 ≤ beta' := (le_max_right _ _).trans (le_max_right _ _)
  have hbeta' : beta' < 0 := max_lt hbeta (max_lt (by norm_num) (by linarith))
  refine ⟨beta', hhalf, hdef, hbeta', max T 2, le_max_right _ _,
    1 + selectionCost k u * B, ?_, ?_⟩
  · have hE : 0 ≤ selectionCost k u := by unfold selectionCost; positivity
    nlinarith only [hE, hB]
  intro C hC
  have he := hprev C hC
  have hB0 : 0 ≤ B := by linarith
  have hE0 : 0 ≤ selectionCost k u := by unfold selectionCost; positivity
  intro lam N₀ hdefect hbudget p xi X inst hX hN hp colour
  have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : p.Prime)).le
  obtain ⟨hXT, hNT⟩ := quotient_budget_mono hp0 (le_max_left T 2) hX hN
  have hn : normalizedLevel p k 0 1 xi X u colour lam ≤ (C * B) * (p : ℝ) ^ beta := by
    apply normalized_level_le_of_all ((Nat.pow_pos hp0).trans_le hX) colour lam _
    intro eta heta colourB
    have ha := he lam N₀ hdefect hbudget p 0 1 xi eta X (by omega)
      (by simpa only [mul_one] using hXT) (by simpa only [mul_one] using hNT) hp heta colour colourB
    simpa only [Nat.cast_zero, Nat.cast_one, mul_zero, zero_add, mul_one] using ha
  have hn' := hn.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hp1 (le_max_left beta (max (-(1 / 2 : ℝ)) (-defect / 2)))) (mul_nonneg (zero_le_one.trans hC) hB0))
  unfold constantAllowance
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, mul_zero,
    Real.rpow_zero, one_mul, add_zero, Nat.cast_one]
  calc
    _ ≤ C * (p : ℝ) ^ beta' + selectionCost k u * ((C * B) * (p : ℝ) ^ beta') :=
      add_le_add (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1 hhalf) (zero_le_one.trans hC))
        (mul_le_mul_of_nonneg_left hn' hE0)
    _ = _ := by ring

/-- The original prime packet transports any proved initial-allowance bound
with its literal depth, multiplier and negative prime exponent unchanged. -/
theorem global_meanValue_of_initial_allowance (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (C : ℝ) (hC : 1 ≤ C) (lam : ℝ) (N₀ : ℕ)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 < lam)
    (hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam)
    (beta : ℝ) (hbeta : beta < 0) (S : ℕ) (hS : 2 ≤ S) (B : ℝ) (hB : 1 ≤ B)
    (hallow : ∀ (p xi X : ℕ) [Fact p.Prime],
      p ^ S ≤ X → N₀ ≤ X / p ^ S + 1 → iterationConstant k u ^ 2 ≤ (p : ℝ) →
      ∀ colour : Fin k → Bool,
      constantAllowance C p k 0 1 xi X u 1 colour lam ≤ (C * B) * (p : ℝ) ^ beta)
    (M R X : ℕ) (hM : 0 < M) (hR : 0 < R)
    (hpacket : X ^ (k * (k - 1)) < M ^ R) (hsize : 4 * k ^ 4 ≤ X)
    (hcutoff : (2 ^ R * M) ^ S ≤ X) (hN : N₀ ≤ X / (2 ^ R * M) ^ S + 1)
    (hprime : iterationConstant k u ^ 2 ≤ (M : ℝ)) :
    meanValue ((u + 1) * k) k X ≤
      (2 * (R : ℝ)) ^ 2 * (C * B) * (X : ℝ) ^ lam * (M : ℝ) ^ beta := by
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
  have hprimep : iterationConstant k u ^ 2 ≤ (p : ℝ) :=
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
  have hiteration := mixed_le_constant_allowance (a := 0) (b := 1) (xi := 0)
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
    have h := VinogradovProfileSaving.initial_scale_identity (show (0 : ℝ) < X by exact_mod_cast hXpos)
      (show (0 : ℝ) < p by exact_mod_cast hp.pos) (k : ℝ) (u : ℝ) lam
    simpa only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using h
  have hP : (p : ℝ) ^ beta ≤ (M : ℝ) ^ beta :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hM) (by exact_mod_cast hMp.le) hbeta.le
  calc
    _ ≤ _ := he
    _ = (2 * (R : ℝ)) ^ 2 * (C * B) *
        ((p : ℝ) ^ (2 * (k * u)) * momentScale X p k u 0 1 lam) * (p : ℝ) ^ beta := by
      simp only [Nat.cast_zero, Nat.cast_one]
      ring
    _ = (2 * (R : ℝ)) ^ 2 * (C * B) * (X : ℝ) ^ lam * (p : ℝ) ^ beta := by rw [hid]
    _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)


/-- One fixed lower exponent defect gives a uniform negative prime-power saving for the original global mean value. -/
theorem exists_linear_global_profile_saving (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    (defect : ℝ) (hdefect0 : 0 < defect) :
    ∃ beta : ℝ, -(1 / 2 : ℝ) ≤ beta ∧ -defect / 2 ≤ beta ∧ beta < 0 ∧
      ∃ S : ℕ, 2 ≤ S ∧ ∃ B : ℝ, 1 ≤ B ∧ ∀ C : ℝ, 1 ≤ C →
      ∀ (lam : ℝ) (N₀ : ℕ),
      defect ≤ lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 →
      (∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
        meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam) →
      ∀ M R X : ℕ,
      0 < M → 0 < R → X ^ (k * (k - 1)) < M ^ R → 4 * k ^ 4 ≤ X →
      (2 ^ R * M) ^ S ≤ X → N₀ ≤ X / (2 ^ R * M) ^ S + 1 →
      iterationConstant k u ^ 2 ≤ (M : ℝ) →
      meanValue ((u + 1) * k) k X ≤
        (2 * (R : ℝ)) ^ 2 * (C * B) * (X : ℝ) ^ lam * (M : ℝ) ^ beta := by
  obtain ⟨beta, hbetalow, hbetadefect, hbeta, S, hS, B, hB, hallow⟩ :=
    exists_linear_initial_allowance k u hk hu defect hdefect0
  refine ⟨beta, hbetalow, hbetadefect, hbeta, S, hS, B, hB, ?_⟩
  intro C hC lam N₀ hdefect hbudget M R X hM hR hpacket hsize hcutoff hN hprime
  apply global_meanValue_of_initial_allowance k u hk hu C hC lam N₀
    (by linarith) hbudget beta hbeta S hS B hB
    (hallow C hC lam N₀ hdefect hbudget) M R X hM hR hpacket hsize hcutoff hN hprime

end
end RiemannGaussian.VinogradovLinearSaving
