/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovConditionedUpper

/-!
# Uniform iteration of the actual conditioned-energy profiles

Keep the whole finite intermediate-energy sum through its exact geometric
factorization. The existing prime budget controls the geometric ratio,
without a factor proportional to the number of levels. The resulting affine
recurrence improves a uniform exponent profile for every original residue
and both colours. The finite induction constructs one depth threshold that
pays every descendant cutoff and actual padded quotient.

The general induction has one explicitly stated homogeneous moment budget.
It assumes no estimates on later conditioned energies: those are proved
by the induction. The negative-profile specialization is in
`VinogradovNegativeProfile`; no zeta region is asserted here.
-/

namespace RiemannGaussian.VinogradovProfileIteration
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovNonsingularConditioning
open VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovCongruencingScaling VinogradovNormalizedIteration

/-- Every finite geometric sum with ratio at most one half costs at most two, independently of its depth. -/
theorem finite_geometric_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (H : ℕ) :
    ∑ h ∈ Finset.range H, r ^ h ≤ 2 := by
  have he := geom_sum_mul_neg r H
  have hs : 0 ≤ ∑ h ∈ Finset.range H, r ^ h := Finset.sum_nonneg (fun h _ => pow_nonneg hr0 h)
  nlinarith [pow_nonneg hr0 H, mul_nonneg hs (show 0 ≤ 1 / 2 - r by linarith)]

/-- The full singular weight and every fine-scale profile factor combine into one exact geometric ratio. -/
theorem profile_weight_identity {P : ℝ} (hP : 0 < P) (S k u b delta beta : ℝ) (h : ℕ) :
    S ^ h * P ^ (-2 * k * u * h) * P ^ (delta * b + beta * (k * b + h)) =
      P ^ ((delta + k * beta) * b) * (S * P ^ (beta - 2 * k * u)) ^ h := by
  have hpowers : P ^ (-2 * k * u * h) * P ^ (delta * b + beta * (k * b + h)) =
      P ^ ((delta + k * beta) * b) * (P ^ (beta - 2 * k * u)) ^ h := by
    rw [← Real.rpow_natCast (P ^ (beta - 2 * k * u)) h, ← Real.rpow_mul hP.le,
      ← Real.rpow_add hP, ← Real.rpow_add hP]
    congr 1
    ring
  rw [mul_assoc, hpowers, mul_pow]
  ring

/-- A uniform bound on the actual next levels controls the complete finite allowance with no depth-count loss. -/
theorem allowance_le_profile {p k b eta X u H : ℕ} [NeZero p]
    {C delta beta lam : ℝ} (hC : 0 ≤ C)
    (hratio : singularCost p k u * (p : ℝ) ^ (beta - 2 * (k : ℝ) * u) ≤ 1 / 2)
    (hdeep : -((H : ℝ) / 2) ≤ (delta + (k : ℝ) * beta) * b)
    (colour : Fin k → Bool)
    (hnext : ∀ h < H, normalizedLevel p k b (k * b + h) eta X u colour lam ≤
      C * (p : ℝ) ^ (delta * b + beta * ((k * b + h : ℕ) : ℝ))) :
    conditioningAllowance p k b (k * b) eta X u H colour lam ≤
      (1 + 2 * selectionCost k u * C) * (p : ℝ) ^ ((delta + (k : ℝ) * beta) * b) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hterm (h : ℕ) (hh : h ∈ Finset.range H) :
      singularCost p k u ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h) *
        normalizedLevel p k b (k * b + h) eta X u colour lam ≤
      (C * (p : ℝ) ^ ((delta + (k : ℝ) * beta) * b)) *
        (singularCost p k u * (p : ℝ) ^ (beta - 2 * (k : ℝ) * u)) ^ h := by
    have he := profile_weight_identity hp0 (singularCost p k u) (k : ℝ) (u : ℝ) (b : ℝ) delta beta h
    have hn := hnext h (Finset.mem_range.mp hh)
    simp only [Nat.cast_add, Nat.cast_mul] at hn
    calc
      _ ≤ singularCost p k u ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h) *
          (C * (p : ℝ) ^ (delta * b + beta * ((k : ℝ) * b + h))) :=
        mul_le_mul_of_nonneg_left hn (by unfold singularCost; positivity)
      _ = C * (singularCost p k u ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h) *
          (p : ℝ) ^ (delta * b + beta * ((k : ℝ) * b + h))) := by ring
      _ = _ := by rw [he]; ring
  have hs : ∑ h ∈ Finset.range H,
      singularCost p k u ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h) *
        normalizedLevel p k b (k * b + h) eta X u colour lam ≤
      2 * C * (p : ℝ) ^ ((delta + (k : ℝ) * beta) * b) := by
    calc
      _ ≤ ∑ h ∈ Finset.range H, (C * (p : ℝ) ^ ((delta + (k : ℝ) * beta) * b)) *
          (singularCost p k u * (p : ℝ) ^ (beta - 2 * (k : ℝ) * u)) ^ h := Finset.sum_le_sum hterm
      _ = (C * (p : ℝ) ^ ((delta + (k : ℝ) * beta) * b)) *
          ∑ h ∈ Finset.range H, (singularCost p k u * (p : ℝ) ^ (beta - 2 * (k : ℝ) * u)) ^ h := by
        rw [Finset.mul_sum]
      _ ≤ (C * (p : ℝ) ^ ((delta + (k : ℝ) * beta) * b)) * 2 :=
        mul_le_mul_of_nonneg_left (finite_geometric_le_two (by unfold singularCost; positivity) hratio H)
          (mul_nonneg hC (by positivity))
      _ = _ := by ring
  unfold conditioningAllowance
  calc
    _ ≤ (p : ℝ) ^ ((delta + (k : ℝ) * beta) * b) +
        selectionCost k u * (2 * C * (p : ℝ) ^ ((delta + (k : ℝ) * beta) * b)) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hp1 hdeep)
        (mul_le_mul_of_nonneg_left hs (by unfold selectionCost; positivity))
    _ = _ := by ring

/-- The next profile slope is the exact exponent left by the full signed congruencing transfer. -/
theorem profile_exponent_identity {P u : ℝ} (hP : 0 < P) (hu : u ≠ 0)
    (a b k delta beta : ℝ) :
    P ^ (-delta * (b - a)) * (P ^ ((delta + k * beta) * b)) ^ (1 / u) =
      P ^ (delta * a + (-(1 - 1 / u) * delta + k / u * beta) * b) := by
  rw [← Real.rpow_mul hP.le, ← Real.rpow_add hP]
  congr 1
  field_simp
  ring


/-- The original prime-size budget already forces every admissible profile ratio below one half. -/
theorem profile_ratio_le_half {p k u : ℕ} [NeZero p] {C beta : ℝ}
    (hk : 2 ≤ k) (hu : k ≤ u) (hC : 1 ≤ C)
    (hbudget : (C * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (hbeta : beta ≤ (k : ℝ) * u) :
    singularCost p k u * (p : ℝ) ^ (beta - 2 * (k : ℝ) * u) ≤ 1 / 2 := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have huR : (k : ℝ) ≤ u := by exact_mod_cast hu
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hD : 2 ≤ iterationConstant k u := by
    have hpow : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * (k * u)) :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ k - 1))
    unfold iterationConstant
    nlinarith
  have hCD : iterationConstant k u ≤ C * iterationConstant k u := by nlinarith
  have h2D : 2 * iterationConstant k u ≤ (p : ℝ) := by
    have hs := (sq_le_sq₀ (by linarith : 0 ≤ iterationConstant k u)
      (by nlinarith : 0 ≤ C * iterationConstant k u)).mpr hCD
    nlinarith
  have he : ((k - 1 : ℕ) : ℝ) + (beta - 2 * (k : ℝ) * u) ≤ -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hku : (k : ℝ) ≤ (k : ℝ) * u := by nlinarith
    linarith
  calc
    _ ≤ (iterationConstant k u * (p : ℝ) ^ (k - 1)) *
        (p : ℝ) ^ (beta - 2 * (k : ℝ) * u) :=
      mul_le_mul_of_nonneg_right (singularCost_le_power p k u) (by positivity)
    _ = iterationConstant k u * (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) + (beta - 2 * (k : ℝ) * u)) := by
      rw [mul_assoc, ← Real.rpow_natCast (p : ℝ) (k - 1), ← Real.rpow_add hp0]
    _ ≤ iterationConstant k u * (p : ℝ) ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 he) (by linarith)
    _ = iterationConstant k u / (p : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
    _ ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)

/-- The full original signed recurrence improves any admissible uniform next-level profile, retaining its actual colour factor. -/
theorem conditioned_profile_step {p k a b xi eta X u H : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a < b) (hH : 1 ≤ H)
    (hgap : k * b - b ≤ 2 * H) (hX : 0 < X) {C B lam beta : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam)
    (hbudget : (C * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (hJa : meanValue ((u + 1) * k) k (X / p ^ b + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam)
    (hJdeep : meanValue ((u + 1) * k) k (X / p ^ (k * b + H) + 1) ≤
      C * ((X : ℝ) / (p : ℝ) ^ (k * b + H)) ^ lam)
    (heta : eta < p ^ b) (colourA colourB : Fin k → Bool)
    (hbeta : beta ≤ (k : ℝ) * u)
    (hdeep : -((H : ℝ) / 2) ≤
      (lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) * beta) * b)
    (hnext : ∀ h < H, normalizedLevel p k b (k * b + h) eta X u colourB lam ≤
      B * (p : ℝ) ^ ((lam - 2 * (k : ℝ) * ((u : ℝ) + 1) +
        (k : ℝ) * ((k : ℝ) + 1) / 2) * b + beta * ((k * b + h : ℕ) : ℝ))) :
    let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
    conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
      ((VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
        (1 + 2 * selectionCost k u * B) ^ (1 / (u : ℝ))) *
        (p : ℝ) ^ (delta * a + (-(1 - 1 / (u : ℝ)) * delta + (k : ℝ) / u * beta) * b) := by
  let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos (Fact.out : p.Prime)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hM := momentScale_pos hX0 hp0 (k : ℝ) (u : ℝ) (a : ℝ) (b : ℝ) lam
  have hi := normalized_iteration_of_scaled_bounds (xi := xi) hk hu hab hH hgap hX hC hlam
    hbudget hJa hJdeep heta colourA colourB
  have hallow := allowance_le_profile (delta := delta) hB
    (profile_ratio_le_half hk hu hC hbudget hbeta) hdeep colourB hnext
  have hcoeff : 0 ≤ (1 + 2 * selectionCost k u * B) := by unfold selectionCost; positivity
  have hscale := profile_exponent_identity hp0 (u := (u : ℝ))
    (by exact_mod_cast (by omega : u ≠ 0)) (a : ℝ) (b : ℝ) (k : ℝ) delta beta
  apply (div_le_iff₀ hM).mpr
  have hbound := hi.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (allowance_nonneg hX colourB lam) hallow (by positivity))
    (by unfold momentScale; positivity))
  apply hbound.trans_eq
  rw [Real.mul_rpow hcoeff (by positivity)]
  change _ = ((VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
    (1 + 2 * selectionCost k u * B) ^ (1 / (u : ℝ))) *
    (p : ℝ) ^ (delta * a + (-(1 - 1 / (u : ℝ)) * delta + (k : ℝ) / u * beta) * b) *
      momentScale X p k u a b lam
  calc
    _ = ((VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
        (1 + 2 * selectionCost k u * B) ^ (1 / (u : ℝ))) *
      ((p : ℝ) ^ (-delta * ((b : ℝ) - a)) *
        ((p : ℝ) ^ ((delta + (k : ℝ) * beta) * b)) ^ (1 / (u : ℝ))) *
      momentScale X p k u a b lam := by ring
    _ = _ := by rw [hscale]


/-- A deeper genuine quotient budget includes every coarser quotient, with the finite endpoint retained. -/
theorem quotient_budget_mono {p e f X N₀ : ℕ} (hp : 0 < p) (hef : e ≤ f)
    (hX : p ^ f ≤ X) (hN : N₀ ≤ X / p ^ f + 1) :
    p ^ e ≤ X ∧ N₀ ≤ X / p ^ e + 1 := by
  have hpow : p ^ e ≤ p ^ f := Nat.pow_le_pow_right (by omega) hef
  have hquot : X / p ^ f ≤ X / p ^ e :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos hp)).mpr
      ((Nat.mul_le_mul_left _ hpow).trans (Nat.div_mul_le_self X (p ^ f)))
  exact ⟨hpow.trans hX, by omega⟩

/-- The actual higher-moment bounds initialize a uniform signed-energy profile throughout the admissible critical range. -/
theorem initial_profile {p k a b xi eta X u : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hX : 0 < X) {C lam : ℝ} (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam)
    (hJa : meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam)
    (hJb : meanValue ((u + 1) * k) k (X / p ^ b + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam)
    (colourA colourB : Fin k → Bool) :
    let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
    conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
      C * (p : ℝ) ^ (delta * a + ((k : ℝ) * u) * b) := by
  let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have huR : (k : ℝ) ≤ u := by exact_mod_cast hu
  have hd : 0 ≤ delta := by unfold delta; linarith
  have hlow : (k : ℝ) * ((u : ℝ) + 1) ≤ lam := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by positivity) (show 0 ≤ (u : ℝ) - k by linarith)]
  have hdiv : (k : ℝ) ≤ lam / ((u : ℝ) + 1) :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < u + 1)).mpr hlow
  have hA : (u : ℝ) * (2 * (k : ℝ) - lam / ((u : ℝ) + 1)) ≤ (k : ℝ) * u := by
    nlinarith [mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg u)]
  have hgap : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hexp : (u : ℝ) * (2 * (k : ℝ) - lam / ((u : ℝ) + 1)) * ((b : ℝ) - a) ≤
      delta * a + ((k : ℝ) * u) * b := by
    have he := mul_le_mul_of_nonneg_right hA hgap
    nlinarith [mul_nonneg hd (Nat.cast_nonneg a), mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) * u by positivity) (Nat.cast_nonneg a)]
  have he := VinogradovConditionedUpper.conditioned_le_scaled_moments
    (xi := xi) (eta := eta) (by omega : 0 < u) hC hJa hJb colourA colourB
  have hid := VinogradovConditionedUpper.conditioned_scale_identity
    hX0 hp0 (k : ℝ) (u : ℝ) (a : ℝ) (b : ℝ) lam (by positivity)
  simp only [Real.rpow_natCast] at hid
  simp only [Nat.cast_add, Nat.cast_one] at he
  rw [hid] at he
  have hn : conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
      C * (p : ℝ) ^ ((u : ℝ) * (2 * (k : ℝ) - lam / ((u : ℝ) + 1)) * ((b : ℝ) - a)) :=
    (div_le_iff₀ (momentScale_pos hX0 hp0 _ _ _ _ _)).mpr (he.trans_eq (by ring))
  exact hn.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 hexp) (by linarith))

/-- A uniform estimate on actual residues and both colours includes their whole normalized level maximum. -/
theorem normalized_level_le_of_all {p k a b xi X u : ℕ} [NeZero p]
    (hX : 0 < X) (colourA : Fin k → Bool) (lam B : ℝ)
    (hbound : ∀ eta < p ^ b, ∀ colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤ B) :
    normalizedLevel p k a b xi X u colourA lam ≤ B := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hM := momentScale_pos (show (0 : ℝ) < X by exact_mod_cast hX) hp0 (k : ℝ) (u : ℝ) (a : ℝ) (b : ℝ) lam
  unfold normalizedLevel
  apply (div_le_iff₀ hM).mpr
  unfold levelConditionedMaximum
  apply Finset.sup'_le Finset.univ_nonempty
  intro eta heta
  unfold conditionedMaximum
  apply Finset.sup'_le Finset.univ_nonempty
  intro colourB hcolourB
  exact (div_le_iff₀ hM).mp (hbound eta.val eta.isLt colourB)

/-- The exact scalar exponent sequence retained by the uniform conditioned-profile iteration. -/
def affineProfile (r c B : ℝ) : ℕ → ℝ
  | 0 => B
  | n + 1 => r * affineProfile r c B n - c

/-- Every iterated exponent stays below the initial nonnegative exponent. -/
theorem affineProfile_le {r c B : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (n : ℕ) : affineProfile r c B n ≤ B := by
  induction n with
  | zero => exact le_refl _
  | succ n ih =>
    dsimp only [affineProfile]
    have he := mul_le_mul_of_nonneg_left ih hr0
    nlinarith

/-- A positive exponent defect forces an actual negative profile after finitely many steps, including the endpoint ratio one. -/
theorem exists_negative_affineProfile {r c B : ℝ} (hr1 : r ≤ 1) (hc : 0 < c) :
    ∃ n : ℕ, affineProfile r c B n < 0 := by
  by_contra! hnonneg
  have hlinear (n : ℕ) : affineProfile r c B n ≤ B - (n : ℝ) * c := by
    induction n with
    | zero => simp [affineProfile]
    | succ n ih =>
      dsimp only [affineProfile]
      have he := mul_le_mul_of_nonneg_right hr1 (hnonneg n)
      push_cast
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (B / c)
  have hnc : B < (n : ℝ) * c := (div_lt_iff₀ hc).mp hn
  have he := hlinear n
  have hpos := hnonneg n
  linarith


/-- Every finite number of profile improvements applies uniformly to actual signed conditioned moments, with all descendant cutoffs and homogeneous budgets paid. -/
theorem uniform_profile_iteration (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u)
    {C lam : ℝ} {N₀ : ℕ} (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam)
    (hbudget : ∀ p e X : ℕ, 0 < p → p ^ e ≤ X → N₀ ≤ X / p ^ e + 1 →
      meanValue ((u + 1) * k) k (X / p ^ e + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ e) ^ lam)
    (n : ℕ) :
    let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
    ∃ T : ℕ, 1 ≤ T ∧ ∃ B : ℝ, 1 ≤ B ∧ ∀ (p a b xi eta X : ℕ) [Fact p.Prime],
      a < b → p ^ (T * b) ≤ X → N₀ ≤ X / p ^ (T * b) + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
        B * (p : ℝ) ^ (delta * a +
          affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * delta) ((k : ℝ) * u) n * b) := by
  let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
  have hd : 0 ≤ delta := by unfold delta; linarith
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hr0 : (0 : ℝ) ≤ (k : ℝ) / u := by positivity
  have hr1 : (k : ℝ) / u ≤ 1 := (div_le_one hu0).mpr (by exact_mod_cast hu)
  have hc : 0 ≤ (1 - 1 / (u : ℝ)) * delta := by
    have ht : 1 / (u : ℝ) ≤ 1 := (div_le_one hu0).mpr (by exact_mod_cast (by omega : 1 ≤ u))
    exact mul_nonneg (by linarith) hd
  induction n with
  | zero =>
    refine ⟨1, by omega, C, hC, ?_⟩
    intro p a b xi eta X inst hab hX hN hp heta colourA colourB
    have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
    simp only [one_mul] at hX hN
    obtain ⟨hXa, hNa⟩ := quotient_budget_mono hp0 hab.le hX hN
    have he := initial_profile (xi := xi) (eta := eta) hk hu hab.le
      ((Nat.pow_pos hp0).trans_le hX) hC hlam
      (hbudget p a X hp0 hXa hNa) (hbudget p b X hp0 hX hN) colourA colourB
    simpa only [affineProfile] using he
  | succ n ih =>
    obtain ⟨T, hT, B, hB, hprev⟩ := ih
    let beta := affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * delta) ((k : ℝ) * u) n
    have hbeta : beta ≤ (k : ℝ) * u := affineProfile_le hr0 hr1 hc (by positivity) n
    obtain ⟨d, hdsize⟩ := exists_nat_ge (max (k : ℝ) (-2 * (delta + (k : ℝ) * beta)))
    have hdk : k ≤ d := by exact_mod_cast (le_max_left _ _).trans hdsize
    have hddepth : -(d : ℝ) / 2 ≤ delta + (k : ℝ) * beta := by
      have he := (le_max_right (k : ℝ) (-2 * (delta + (k : ℝ) * beta))).trans hdsize
      linarith
    let Bnext : ℝ := max 1 ((k.factorial : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
      (1 + 2 * selectionCost k u * B) ^ (1 / (u : ℝ)))
    refine ⟨T * (k + d), by nlinarith, Bnext, le_max_left _ _, ?_⟩
    intro p a b xi eta X inst hab hX hN hp heta colourA colourB
    have hp0 := Nat.Prime.pos (Fact.out : p.Prime)
    have hXpos : 0 < X := (Nat.pow_pos hp0).trans_le hX
    have hdeepExp : k * b + d * b ≤ (T * (k + d)) * b := by
      have he := Nat.mul_le_mul_right ((k + d) * b) hT
      nlinarith
    obtain ⟨hXd, hNd⟩ := quotient_budget_mono hp0 hdeepExp hX hN
    obtain ⟨hXb, hNb⟩ := quotient_budget_mono hp0 (by nlinarith : b ≤ k * b + d * b) hXd hNd
    have hH : 1 ≤ d * b := by
      have hd1 : 1 ≤ d := by omega
      have hb1 : 1 ≤ b := by omega
      nlinarith
    have hgap : k * b - b ≤ 2 * (d * b) := by
      have he := Nat.mul_le_mul_right b hdk
      omega
    have hdeep : -(((d * b : ℕ) : ℝ) / 2) ≤ (delta + (k : ℝ) * beta) * b := by
      have he := mul_le_mul_of_nonneg_right hddepth (Nat.cast_nonneg b)
      push_cast
      nlinarith
    have hnext : ∀ h < d * b, normalizedLevel p k b (k * b + h) eta X u colourB lam ≤
        B * (p : ℝ) ^ (delta * b + beta * ((k * b + h : ℕ) : ℝ)) := by
      intro h hh
      apply normalized_level_le_of_all hXpos colourB lam
      intro eta' heta' colourC
      have he : T * (k * b + h) ≤ (T * (k + d)) * b := by
        have hs : k * b + h ≤ (k + d) * b := by nlinarith
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left T hs
      obtain ⟨hXnext, hNnext⟩ := quotient_budget_mono hp0 he hX hN
      have hbb : b < k * b + h := by nlinarith [Nat.mul_le_mul_right b hk]
      exact hprev p b (k * b + h) eta eta' X hbb hXnext hNnext hp heta' colourB colourC
    have he := conditioned_profile_step (xi := xi) hk hu hab hH hgap hXpos hC (by linarith : 0 ≤ B)
      hlam hp (hbudget p b X hp0 hXb hNb) (hbudget p (k * b + d * b) X hp0 hXd hNd)
      heta colourA colourB hbeta hdeep hnext
    have hcoef : (VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
        (1 + 2 * selectionCost k u * B) ^ (1 / (u : ℝ)) ≤ Bnext := by
      apply le_trans _ (le_max_right _ _)
      apply mul_le_mul_of_nonneg_right _ (by unfold selectionCost; positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast VinogradovCoarseCongruence.colourFactorial_le_factorial colourA
    have he' := he.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))
    have hbeta_next : affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * delta) ((k : ℝ) * u) (n + 1) =
        -(1 - 1 / (u : ℝ)) * delta + (k : ℝ) / u * beta := by
      change (k : ℝ) / u * beta - (1 - 1 / (u : ℝ)) * delta = _
      ring
    change _ ≤ Bnext * (p : ℝ) ^ (delta * a +
      affineProfile ((k : ℝ) / u) ((1 - 1 / (u : ℝ)) * delta) ((k : ℝ) * u) (n + 1) * b)
    rw [hbeta_next]
    exact he'

end
end RiemannGaussian.VinogradovProfileIteration
