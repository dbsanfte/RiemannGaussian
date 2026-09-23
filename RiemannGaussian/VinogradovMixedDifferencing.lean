/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDifferenceEnergy
import RiemannGaussian.VinogradovMomentReduction

/-!
# Quantitative differencing of the actual congruence-restricted mixed moment

All endpoint masks are paid through complete even moments. Finite Holder
is applied before integration; no maximum is moved outside an integral.
The weighted convexity split retains the classical diagonal and
off-diagonal constants.
-/

namespace RiemannGaussian.VinogradovMixedDifferencing
noncomputable section
open scoped BigOperators
open MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovPartitionEnergy
open VinogradovMixedMoments VinogradovDifferenceEnergy

/-- The normalized Haar measure used by the mixed count. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- Circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The actual residue energy coupled to the entire original tail. -/
def residueMixedMoment {κ d : Type*} [Fintype κ] [Fintype d]
    (m s P q : ℕ) (hq : 0 < q) (v : ℕ → d → ℤ) (u : κ → d → ℤ) : ℝ :=
  ∫ theta : UnitAddTorus d,
    residueEnergy P q hq v theta ^ m * ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)

private theorem convex_split {A B t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : 0 < t) (ht1 : t < 1) (m : ℕ) :
    (A + B) ^ m ≤ t * (A / t) ^ m + (1 - t) / (1 - t) ^ m * B ^ m := by
  have hb : 0 < 1 - t := by linarith
  have h := (convexOn_pow (𝕜 := ℝ) m).2 (div_nonneg hA ht.le)
    (div_nonneg hB hb.le) ht.le hb.le (by ring : t + (1 - t) = 1)
  simp only [smul_eq_mul] at h
  have he : t * (A / t) + (1 - t) * (B / (1 - t)) = A + B := by
    field_simp
  rw [he] at h
  calc
    _ ≤ t * (A / t) ^ m + (1 - t) * (B / (1 - t)) ^ m := h
    _ = _ := by
      congr 1
      rw [div_pow]
      ring

private theorem half_bernoulli {m : ℕ} (hm : 1 ≤ m) :
    (1 / 2 : ℝ) ≤ (1 - 1 / (2 * (m : ℝ))) ^ m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ht : (1 : ℝ) / (2 * m) ≤ 1 / 2 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    (by linarith)
  have h := one_add_mul_le_pow (a := -(1 / (2 * (m : ℝ)))) (by linarith) m
  have he : (1 : ℝ) + (m : ℝ) * -(1 / (2 * (m : ℝ))) = 1 / 2 := by
    field_simp
    ring
  simpa only [he, sub_eq_add_neg] using h

/-- A convexity split with weight `1/(2m)` loses at most the factor two
in the off-diagonal alternative. This is a scalar absorption inequality. -/
theorem convex_absorption {m : ℕ} (hm : 1 ≤ m) {L D B : ℝ} (hB : 0 ≤ B)
    (h : L ≤ (1 / (2 * (m : ℝ))) * D +
      (1 - 1 / (2 * (m : ℝ))) / (1 - 1 / (2 * (m : ℝ))) ^ m * B) :
    L ≤ max D (2 * B) := by
  by_cases hLD : L ≤ D
  · exact hLD.trans (le_max_left _ _)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have ht : (1 : ℝ) / (2 * m) ≤ 1 / 2 := (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    (by linarith)
  have hb : (0 : ℝ) < 1 - 1 / (2 * (m : ℝ)) := by linarith
  have hD := mul_le_mul_of_nonneg_left (le_of_not_ge hLD)
    (show (0 : ℝ) ≤ 1 / (2 * (m : ℝ)) by positivity)
  have hc : L ≤ B / (1 - 1 / (2 * (m : ℝ))) ^ m := by
    have h' : L ≤ (1 / (2 * (m : ℝ))) * L +
        (1 - 1 / (2 * (m : ℝ))) * (B / (1 - 1 / (2 * (m : ℝ))) ^ m) :=
      (h.trans (add_le_add hD (le_refl _))).trans_eq (by ring)
    apply (mul_le_mul_iff_of_pos_left hb).mp
    nlinarith only [h']
  have hp := half_bernoulli hm
  have hn : B / (1 - 1 / (2 * (m : ℝ))) ^ m ≤ 2 * B := by
    apply (div_le_iff₀ (pow_pos hb _)).mpr
    nlinarith
  exact (hc.trans hn).trans (le_max_right _ _)

/-- The complete mixed-moment allowance for one actual displacement. -/
def differenceAllowance {κ d : Type*} [Fintype κ] [Fintype d]
    (m s P h : ℕ) (v : ℕ → d → ℤ) (u : κ → d → ℤ) : ℝ :=
  mixedMoment (m - 1) s (differenceFrequency P h v) u ^
      ((m : ℝ) / (2 * ((m : ℝ) - 1))) *
    moment s u ^ (1 - (m : ℝ) / (2 * ((m : ℝ) - 1)))

/-- The entire truncated difference sum pays its complete mixed count,
including all original tail coordinates. -/
theorem difference_power_le {κ d : Type*} [Fintype κ] [Fintype d]
    {m : ℕ} (hm : 2 ≤ m) (s P h : ℕ) (v : ℕ → d → ℤ) (u : κ → d → ℤ) :
    (∫ theta : UnitAddTorus d, ‖differenceSum P h v theta‖ ^ m *
      ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)) ≤
      differenceAllowance m s P h v u :=
  intermediate_power_le hm s _ u _ (boundaryWeight_bound P h)

/-- Finite Holder is used before integration. Each displacement keeps
its own complete mixed moment; there is no integral of a pointwise maximum. -/
theorem sum_difference_power_le {κ d : Type*} [Fintype κ] [Fintype d]
    {m : ℕ} (hm : 2 ≤ m) (s P q : ℕ) (v : ℕ → d → ℤ) (u : κ → d → ℤ) :
    (∫ theta : UnitAddTorus d,
      (2 * ∑ h : Fin (P / q), ‖differenceSum P ((h.val + 1) * q) v theta‖) ^ m *
        ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)) ≤
      2 ^ m * (P / q : ℕ) ^ (m - 1) *
        ∑ h : Fin (P / q), differenceAllowance m s P ((h.val + 1) * q) v u := by
  let w (theta : UnitAddTorus d) := ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)
  let G (theta : UnitAddTorus d) :=
    2 * ∑ h : Fin (P / q), ‖differenceSum P ((h.val + 1) * q) v theta‖
  have hw : Continuous w := (continuous_polynomial u (fun _ => 1)).norm.pow _
  have hG : Continuous G :=
    (continuous_finsetSum _ (fun h _ => (continuous_differenceSum P ((h.val + 1) * q) v).norm)).const_mul 2
  have hc (h : Fin (P / q)) : Continuous (fun theta : UnitAddTorus d =>
      ‖differenceSum P ((h.val + 1) * q) v theta‖ ^ m * w theta) :=
    ((continuous_differenceSum P ((h.val + 1) * q) v).norm.pow _).mul hw
  have hi (h : Fin (P / q)) : Integrable (fun theta : UnitAddTorus d =>
      ‖differenceSum P ((h.val + 1) * q) v theta‖ ^ m * w theta) :=
    (hc h).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hpoint (theta : UnitAddTorus d) : G theta ^ m * w theta ≤
      (2 ^ m * (P / q : ℕ) ^ (m - 1)) *
        ∑ h : Fin (P / q), ‖differenceSum P ((h.val + 1) * q) v theta‖ ^ m * w theta := by
    have h := VinogradovMomentReduction.weighted_power_bound Finset.univ
      (fun _ : Fin (P / q) => (1 : ℝ))
      (fun h => ‖differenceSum P ((h.val + 1) * q) v theta‖)
      (by simp) (fun _ _ => norm_nonneg _) (show 1 ≤ m by omega)
    simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at h
    have h' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 ^ m by positivity))
      (show 0 ≤ w theta by dsimp [w]; positivity)
    simpa only [G, mul_pow, Finset.sum_mul, mul_assoc] using h'
  calc
    _ ≤ ∫ theta : UnitAddTorus d, (2 ^ m * (P / q : ℕ) ^ (m - 1)) *
        ∑ h : Fin (P / q), ‖differenceSum P ((h.val + 1) * q) v theta‖ ^ m * w theta :=
      integral_mono ((hG.pow _).mul hw |>.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
        ((integrable_finsetSum _ (fun h _ => hi h)).const_mul _) hpoint
    _ = (2 ^ m * (P / q : ℕ) ^ (m - 1)) *
        ∑ h : Fin (P / q), ∫ theta : UnitAddTorus d,
          ‖differenceSum P ((h.val + 1) * q) v theta‖ ^ m * w theta := by
      rw [integral_const_mul, integral_finsetSum _ (fun h _ => hi h)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun h _ => difference_power_le hm s P ((h.val + 1) * q) v u))
      (by positivity)

/-- The complete classical differencing bound on the actual restricted
mixed moment. Boundary completion is proved, and every constant is explicit.
This is the `L`-to-next-`K` analytic step before polynomial-type specialization. -/
theorem residueMixedMoment_le {κ d : Type*} [Fintype κ] [Fintype d]
    {m : ℕ} (hm : 2 ≤ m) (s P q : ℕ) (hq : 0 < q)
    (v : ℕ → d → ℤ) (u : κ → d → ℤ) :
    residueMixedMoment m s P q hq v u ≤
      max ((2 * (m : ℝ) * P) ^ m * moment s u)
        (2 * (2 ^ m * (P / q : ℕ) ^ (m - 1) *
          ∑ h : Fin (P / q), differenceAllowance m s P ((h.val + 1) * q) v u)) := by
  let t : ℝ := 1 / (2 * (m : ℝ))
  let w (theta : UnitAddTorus d) := ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)
  let G (theta : UnitAddTorus d) :=
    2 * ∑ h : Fin (P / q), ‖differenceSum P ((h.val + 1) * q) v theta‖
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by
    dsimp [t]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hb : 0 < 1 - t := by linarith
  have hw : Continuous w := (continuous_polynomial u (fun _ => 1)).norm.pow _
  have hG : Continuous G :=
    (continuous_finsetSum _ (fun h _ => (continuous_differenceSum P ((h.val + 1) * q) v).norm)).const_mul 2
  have hiw : Integrable w := hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiG : Integrable (fun theta => G theta ^ m * w theta) :=
    ((hG.pow _).mul hw).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have htail : (∫ theta : UnitAddTorus d, w theta) = moment s u := by
    simp only [w, polynomial, one_mul, moment]
  have hpoint (theta : UnitAddTorus d) :
      residueEnergy P q hq v theta ^ m * w theta ≤
        (t * ((P : ℝ) / t) ^ m) * w theta +
          ((1 - t) / (1 - t) ^ m) * (G theta ^ m * w theta) := by
    have h := (pow_le_pow_left₀ (residueEnergy_nonneg P q hq v theta)
      (residueEnergy_le P q hq v theta) m).trans
      (convex_split (Nat.cast_nonneg P) (show 0 ≤ G theta by dsimp [G]; positivity) ht ht1 m)
    have h' := mul_le_mul_of_nonneg_right h (show 0 ≤ w theta by dsimp [w]; positivity)
    simpa only [add_mul, mul_assoc] using h'
  have hi : residueMixedMoment m s P q hq v u ≤
      (t * ((P : ℝ) / t) ^ m) * moment s u +
        ((1 - t) / (1 - t) ^ m) * (∫ theta : UnitAddTorus d, G theta ^ m * w theta) := by
    calc
      _ ≤ ∫ theta : UnitAddTorus d,
          (t * ((P : ℝ) / t) ^ m) * w theta +
            ((1 - t) / (1 - t) ^ m) * (G theta ^ m * w theta) :=
        integral_mono (((continuous_residueEnergy P q hq v).pow _).mul hw
          |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          ((hiw.const_mul _).add (hiG.const_mul _)) hpoint
      _ = _ := by rw [integral_add (hiw.const_mul _) (hiG.const_mul _),
        integral_const_mul, integral_const_mul, htail]
  have he : (P : ℝ) / t = 2 * (m : ℝ) * P := by
    dsimp [t]
    field_simp
  rw [he] at hi
  apply convex_absorption (show 1 ≤ m by omega)
  · apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro h hh
    exact mul_nonneg (Real.rpow_nonneg (mixedMoment_nonneg _ _ _ _) _)
      (Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _)
  · have hsum := mul_le_mul_of_nonneg_left (sum_difference_power_le hm s P q v u)
      (div_nonneg hb.le (pow_nonneg hb.le m))
    have hfinal := hi.trans (add_le_add (le_refl _) hsum)
    simpa only [t, mul_assoc] using hfinal

/-- A single *fixed* displacement attains the complete-moment bound.
It is selected after integrating the finite Holder sum. The multiplier is
exactly the classical `2*(2*floor(P/q))^m`. -/
theorem exists_difference_bound {κ d : Type*} [Fintype κ] [Fintype d]
    {m : ℕ} (hm : 2 ≤ m) (s P q : ℕ) (hq : 0 < q) (hqP : q ≤ P)
    (v : ℕ → d → ℤ) (u : κ → d → ℤ) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ P / q ∧
      residueMixedMoment m s P q hq v u ≤
        max ((2 * (m : ℝ) * P) ^ m * moment s u)
          (2 * (2 * (P / q : ℕ)) ^ m * differenceAllowance m s P (h * q) v u) := by
  classical
  have hH : 0 < P / q := Nat.div_pos hqP hq
  obtain ⟨h, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (P / q)))
    (fun h => differenceAllowance m s P ((h.val + 1) * q) v u)
    ⟨⟨0, hH⟩, Finset.mem_univ _⟩
  refine ⟨h.val + 1, by omega, by have := h.isLt; omega, ?_⟩
  have hsum : (∑ a : Fin (P / q), differenceAllowance m s P ((a.val + 1) * q) v u) ≤
      (P / q : ℕ) * differenceAllowance m s P ((h.val + 1) * q) v u := by
    simpa using Finset.sum_le_sum (fun a ha => hmax a ha)
  have he : (2 : ℝ) ^ m * (P / q : ℕ) ^ (m - 1) * (P / q : ℕ) =
      (2 * (P / q : ℕ)) ^ m := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (show 1 ≤ m by omega), mul_pow]
  apply (residueMixedMoment_le hm s P q hq v u).trans
  apply max_le_max le_rfl
  calc
    _ ≤ 2 * ((2 ^ m * (P / q : ℕ) ^ (m - 1)) *
        ((P / q : ℕ) * differenceAllowance m s P ((h.val + 1) * q) v u)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by norm_num)
    _ = _ := by rw [← he]; ring

/-- If no positive residue displacement fits, the original restricted
mixed moment is exactly diagonal. No nonempty shift family is assumed. -/
theorem residueMixedMoment_eq_diagonal {κ d : Type*} [Fintype κ] [Fintype d]
    (m s P q : ℕ) (hq : 0 < q) (hPq : P < q)
    (v : ℕ → d → ℤ) (u : κ → d → ℤ) :
    residueMixedMoment m s P q hq v u = (P : ℝ) ^ m * moment s u := by
  have : IsEmpty (Fin (P / q)) := by rw [Nat.div_eq_of_lt hPq]; infer_instance
  have he (theta : UnitAddTorus d) : residueEnergy P q hq v theta = (P : ℝ) := by
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero] using
      residueEnergy_eq_differences P q hq v theta
  unfold residueMixedMoment
  simp_rw [he]
  rw [integral_const_mul]
  simp only [polynomial, one_mul, moment]

end
end RiemannGaussian.VinogradovMixedDifferencing
