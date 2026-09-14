/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovConditioningRemainder
import RiemannGaussian.VinogradovRemainderScaling
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Actual deep conditioning remainder with a proved power saving

The original higher moments have the elementary exponent k(2u+1).
The exact finite quotients floor(X/p^j)+1 are paid by 2X/p^j only when
a complete quotient window fits. The explicit constants are
C=2^(k(2u+1))*k! and D=2u*(k-1)^(2ku).

For k>=2, u>=k, a<=b, 1<=H, b-a<=2H, p^(b+H)<=X and (C*D)^2<=p,
the actual iterated remainder is at most
(X/p^a)^k*(X/p^b)^(2ku)*p^(-H/2). The same threshold proves k<p.
The terminal finite conditioning theorem supplies this saving without a
moment-budget premise. A general transfer retains any real exponent at or above the critical value and its explicit two actual homogeneous-moment bounds; those
premises are discharged at the elementary exponent by the final theorem.

This supplies an explicit initial-exponent version of the conditioning
remainder in Wooley (2012), Lemma 5.2:
https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf
Improving the high-moment exponent, the VK growth and zero-free proof, and
the original weighted Riesz saving remain open. No new zero-free width
or historical novelty is claimed here.
-/

namespace RiemannGaussian.VinogradovConditioningPowerSaving
noncomputable section
open VinogradovMeanValue VinogradovConditioningRemainder
open VinogradovRemainderScaling VinogradovSingularConditioning

/-- The already proved all-order estimate supplies the literal elementary exponent and factorial constant. -/
theorem higher_meanValue_elementary (k u N : ℕ) :
    meanValue ((u + 1) * k) k N ≤ (N : ℝ) ^ (k * (2 * u + 1)) * k.factorial := by
  have hle : k ≤ (u + 1) * k := by
    have h := Nat.mul_le_mul_right k (by omega : 1 ≤ u + 1)
    simpa only [one_mul] using h
  have he := VinogradovPowerSumRigidity.meanValue_le_all ((u + 1) * k) k N
  rw [min_eq_right hle] at he
  have hexp : 2 * ((u + 1) * k) - k = k * (2 * u + 1) := by
    have h : 2 * ((u + 1) * k) = k * (2 * u + 1) + k := by ring
    omega
  simpa only [hexp] using he

/-- Insert the proved elementary costs at both exact quotient endpoints of the original mixed moment. -/
theorem mixed_le_elementary_quotients {p k a b xi eta X u : ℕ} [NeZero p]
    (hu : 0 < u) (colour : Fin k → Bool) :
    mixedMoment p k a b xi eta X (k * u) colour ≤
      (((X / p ^ a + 1 : ℕ) : ℝ) ^ (k * (2 * u + 1)) * k.factorial) ^ (1 / ((u + 1 : ℕ) : ℝ)) *
      (((X / p ^ b + 1 : ℕ) : ℝ) ^ (k * (2 * u + 1)) * k.factorial) ^ (1 - 1 / ((u + 1 : ℕ) : ℝ)) := by
  have he := mixed_le_higher_moments (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) hu colour
  have ht : 0 ≤ 1 - 1 / ((u + 1 : ℕ) : ℝ) := by
    have huR : (1 : ℝ) < ((u + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < u + 1)
    have h := (div_lt_one (by linarith : (0 : ℝ) < ((u + 1 : ℕ) : ℝ))).mpr huR
    linarith
  apply he.trans
  apply mul_le_mul
  · exact Real.rpow_le_rpow (by rw [meanValue_eq_count]; positivity)
      (higher_meanValue_elementary k u _) (by positivity)
  · exact Real.rpow_le_rpow (by rw [meanValue_eq_count]; positivity)
      (higher_meanValue_elementary k u _) ht
  · exact Real.rpow_nonneg (by rw [meanValue_eq_count]; positivity) _
  · positivity

/-- Pay the extra endpoint in the actual integer quotient only when a complete window fits. -/
theorem quotient_size_le_two {q X : ℕ} (hq : 0 < q) (hX : q ≤ X) :
    ((X / q + 1 : ℕ) : ℝ) ≤ 2 * ((X : ℝ) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdiv : ((X / q : ℕ) : ℝ) ≤ (X : ℝ) / q := Nat.cast_div_le
  have hone : (1 : ℝ) ≤ (X : ℝ) / q := by
    apply (le_div_iff₀ hqR).mpr
    simpa only [one_mul] using (show (q : ℝ) ≤ X by exact_mod_cast hX)
  push_cast
  linarith

/-- The exact factorial and rounding constant for the proved elementary higher moment. -/
def elementaryConstant (k u : ℕ) : ℝ :=
  (2 : ℝ) ^ (k * (2 * u + 1)) * k.factorial

/-- The explicit part of the singular iteration coefficient independent of the base. -/
def iterationConstant (k u : ℕ) : ℝ :=
  (2 * u : ℝ) * ((k - 1 : ℕ) : ℝ) ^ (2 * (k * u))

/-- The literal homogeneous moment has the stated scaled power bound with all quotient rounding paid. -/
theorem higher_meanValue_rounded {p k a X u : ℕ} [NeZero p] (hX : p ^ a ≤ X) :
    meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤
      elementaryConstant k u * ((X : ℝ) / (p : ℝ) ^ a) ^ (k * (2 * u + 1)) := by
  have hq := quotient_size_le_two (Nat.pos_of_ne_zero (NeZero.ne (p ^ a))) hX
  simp only [Nat.cast_pow] at hq
  apply (higher_meanValue_elementary k u (X / p ^ a + 1)).trans
  calc
    _ ≤ (2 * ((X : ℝ) / (p : ℝ) ^ a)) ^ (k * (2 * u + 1)) * k.factorial := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hq _
    _ = _ := by rw [mul_pow]; unfold elementaryConstant; ring

/-- The actual elementary constant is at least one, as needed for uniform absorption. -/
theorem elementaryConstant_one_le (k u : ℕ) : 1 ≤ elementaryConstant k u := by
  unfold elementaryConstant
  have hp : (1 : ℝ) ≤ 2 ^ (k * (2 * u + 1)) := one_le_pow₀ (by norm_num)
  have hf : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  nlinarith

/-- Bound the actual binomial coefficient by its base power, retaining the full remaining iteration constant. -/
theorem singularCost_le_power (p k u : ℕ) :
    singularCost p k u ≤ iterationConstant k u * (p : ℝ) ^ (k - 1) := by
  have hc := (Nat.cast_le (α := ℝ)).mpr (Nat.choose_le_pow p (k - 1))
  simp only [Nat.cast_pow] at hc
  unfold singularCost iterationConstant
  calc
    _ ≤ (2 * u : ℝ) * (p : ℝ) ^ (k - 1) * ((k - 1 : ℕ) : ℝ) ^ (2 * (k * u)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

/-- The original mixed moment receives the actual rounded elementary power costs at both scales. -/
theorem mixed_le_rounded_powers {p k a b xi eta X u : ℕ} [NeZero p]
    (hu : 0 < u) (hXa : p ^ a ≤ X) (hXb : p ^ b ≤ X) (colour : Fin k → Bool) :
    mixedMoment p k a b xi eta X (k * u) colour ≤
      elementaryConstant k u *
        (((X : ℝ) / (p : ℝ) ^ a) ^ ((k * (2 * u + 1) : ℕ) / ((u + 1 : ℕ) : ℝ)) *
          ((X : ℝ) / (p : ℝ) ^ b) ^ (((k * (2 * u + 1) : ℕ) : ℝ) * u / ((u + 1 : ℕ) : ℝ))) := by
  have huR : (1 : ℝ) < ((u + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < u + 1)
  have ht : 0 ≤ 1 - 1 / ((u + 1 : ℕ) : ℝ) := by
    have h := (div_lt_one (by linarith : (0 : ℝ) < ((u + 1 : ℕ) : ℝ))).mpr huR
    linarith
  have hC : 0 < elementaryConstant k u := lt_of_lt_of_le zero_lt_one (elementaryConstant_one_le k u)
  apply (mixed_le_higher_moments (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) hu colour).trans
  calc
    _ ≤ (elementaryConstant k u * ((X : ℝ) / (p : ℝ) ^ a) ^ (k * (2 * u + 1))) ^ (1 / ((u + 1 : ℕ) : ℝ)) *
        (elementaryConstant k u * ((X : ℝ) / (p : ℝ) ^ b) ^ (k * (2 * u + 1))) ^ (1 - 1 / ((u + 1 : ℕ) : ℝ)) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by rw [meanValue_eq_count]; positivity) (higher_meanValue_rounded hXa) (by positivity)
      · exact Real.rpow_le_rpow (by rw [meanValue_eq_count]; positivity) (higher_meanValue_rounded hXb) ht
      · exact Real.rpow_nonneg (by rw [meanValue_eq_count]; positivity) _
      · positivity
    _ = _ := by
      simp_rw [← Real.rpow_natCast]
      rw [common_power_mean hC (by positivity) (by positivity)]
      have hu0 : (((u + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have he : ((k * (2 * u + 1) : ℕ) : ℝ) * (1 - 1 / ((u + 1 : ℕ) : ℝ)) =
          ((k * (2 * u + 1) : ℕ) : ℝ) * u / ((u + 1 : ℕ) : ℝ) := by
        push_cast
        field_simp
        ring
      rw [he]
      simp only [mul_one_div]

/-- Specialize the complete scale saving to the proved elementary exponent, including every natural-power conversion. -/
theorem scaled_elementary_remainder_le {p k a b H X u : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hgap : b - a ≤ 2 * H) (hX : 0 < X) :
    (p : ℝ) ^ ((k - 1) * H) *
      ((X : ℝ) / (p : ℝ) ^ a) ^ (((k * (2 * u + 1) : ℕ) : ℝ) / ((u + 1 : ℕ) : ℝ)) *
      ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (((k * (2 * u + 1) : ℕ) : ℝ) * u / ((u + 1 : ℕ) : ℝ)) ≤
      (((X : ℝ) / (p : ℝ) ^ a) ^ k * ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))) / (p : ℝ) ^ H := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have huR : (k : ℝ) ≤ u := by exact_mod_cast hu
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hgapR : (b : ℝ) - a ≤ 2 * H := by
    have h : b ≤ a + 2 * H := by omega
    have h' : (b : ℝ) ≤ a + 2 * H := by exact_mod_cast h
    linarith
  have hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * (k + 1) / 2 ≤
      ((k * (2 * u + 1) : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have he := scaled_remainder_le (show (0 : ℝ) < X by exact_mod_cast hX) hp1 hkR huR
    habR (Nat.cast_nonneg H) hgapR hlam
  have hlam' : ((k * (2 * u + 1) : ℕ) : ℝ) - 2 * (k : ℝ) * u = k := by push_cast; ring
  rw [hlam'] at he
  convert he using 1 <;>
    simp only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
      Nat.cast_add, Nat.cast_ofNat, Real.rpow_neg (show (0 : ℝ) ≤ p by positivity), div_eq_mul_inv, mul_assoc]

/-- The scaled elementary bound covers the entire actual residue maximum. -/
theorem level_mixed_le_rounded {p k a b xi X u : ℕ} [NeZero p]
    (hu : 0 < u) (hXa : p ^ a ≤ X) (hXb : p ^ b ≤ X) (colour : Fin k → Bool) :
    levelMixedMaximum p k a b xi X u colour ≤
      elementaryConstant k u *
        (((X : ℝ) / (p : ℝ) ^ a) ^ (((k * (2 * u + 1) : ℕ) : ℝ) / ((u + 1 : ℕ) : ℝ)) *
          ((X : ℝ) / (p : ℝ) ^ b) ^ (((k * (2 * u + 1) : ℕ) : ℝ) * u / ((u + 1 : ℕ) : ℝ))) := by
  apply Finset.sup'_le Finset.univ_nonempty
  intro c hc
  exact mixed_le_rounded_powers hu hXa hXb colour

/-- The actual iterated remainder has the explicit factorial, rounding, iteration and inverse-base costs. -/
theorem deep_remainder_explicit {p k a b xi X u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hgap : b - a ≤ 2 * H)
    (hX : p ^ (b + H) ≤ X) (colour : Fin k → Bool) :
    singularCost p k u ^ H * levelMixedMaximum p k a (b + H) xi X u colour ≤
      (elementaryConstant k u * iterationConstant k u ^ H) *
        ((((X : ℝ) / (p : ℝ) ^ a) ^ k * ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))) / (p : ℝ) ^ H) := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hXa : p ^ a ≤ X := (Nat.pow_le_pow_right hp1 (by omega : a ≤ b + H)).trans hX
  have hXpos : 0 < X := (Nat.pos_of_ne_zero (NeZero.ne (p ^ (b + H)))).trans_le hX
  have hu0 : 0 < u := by omega
  have hS : singularCost p k u ^ H ≤ iterationConstant k u ^ H * (p : ℝ) ^ ((k - 1) * H) := by
    calc
      _ ≤ (iterationConstant k u * (p : ℝ) ^ (k - 1)) ^ H :=
        pow_le_pow_left₀ (by unfold singularCost; positivity) (singularCost_le_power p k u) H
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hI := level_mixed_le_rounded (xi := xi) hu0 hXa hX colour
  have hscaled := scaled_elementary_remainder_le (p := p) hk hu hab hgap hXpos
  calc
    _ ≤ singularCost p k u ^ H * (elementaryConstant k u *
        (((X : ℝ) / (p : ℝ) ^ a) ^ (((k * (2 * u + 1) : ℕ) : ℝ) / ((u + 1 : ℕ) : ℝ)) *
          ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (((k * (2 * u + 1) : ℕ) : ℝ) * u / ((u + 1 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_left hI (by unfold singularCost; positivity)
    _ ≤ (iterationConstant k u ^ H * (p : ℝ) ^ ((k - 1) * H)) * (elementaryConstant k u *
        (((X : ℝ) / (p : ℝ) ^ a) ^ (((k * (2 * u + 1) : ℕ) : ℝ) / ((u + 1 : ℕ) : ℝ)) *
          ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (((k * (2 * u + 1) : ℕ) : ℝ) * u / ((u + 1 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_right hS (by unfold elementaryConstant; positivity)
    _ = (elementaryConstant k u * iterationConstant k u ^ H) *
        ((p : ℝ) ^ ((k - 1) * H) *
          ((X : ℝ) / (p : ℝ) ^ a) ^ (((k * (2 * u + 1) : ℕ) : ℝ) / ((u + 1 : ℕ) : ℝ)) *
          ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (((k * (2 * u + 1) : ℕ) : ℝ) * u / ((u + 1 : ℕ) : ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscaled (by unfold elementaryConstant iterationConstant; positivity)

/-- Transfer two stated actual homogeneous-moment bounds to the original signed mixed moment; no sharper bounds are asserted here. -/
theorem mixed_le_of_scaled_bounds {p k a b xi eta X u : ℕ} [NeZero p]
    (hu : 0 < u) {C lam : ℝ} (hC : 1 ≤ C)
    (hA : meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam)
    (hB : meanValue ((u + 1) * k) k (X / p ^ b + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam)
    (colour : Fin k → Bool) :
    mixedMoment p k a b xi eta X (k * u) colour ≤ C *
      (((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
       ((X : ℝ) / (p : ℝ) ^ b) ^ (lam * u / ((u + 1 : ℕ) : ℝ))) := by
  have huR : (1 : ℝ) < ((u + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < u + 1)
  have ht : 0 ≤ 1 - 1 / ((u + 1 : ℕ) : ℝ) := by
    have h := (div_lt_one (by linarith : (0 : ℝ) < ((u + 1 : ℕ) : ℝ))).mpr huR
    linarith
  have hCpos : 0 < C := by linarith
  apply (mixed_le_higher_moments (p := p) (a := a) (b := b) (xi := xi) (eta := eta) (X := X) hu colour).trans
  calc
    _ ≤ (C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam) ^ (1 / ((u + 1 : ℕ) : ℝ)) *
        (C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam) ^ (1 - 1 / ((u + 1 : ℕ) : ℝ)) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by rw [meanValue_eq_count]; positivity) hA (by positivity)
      · exact Real.rpow_le_rpow (by rw [meanValue_eq_count]; positivity) hB ht
      · exact Real.rpow_nonneg (by rw [meanValue_eq_count]; positivity) _
      · positivity
    _ = _ := by
      rw [common_power_mean hCpos (by positivity) (by positivity)]
      have he : lam * (1 - 1 / ((u + 1 : ℕ) : ℝ)) = lam * u / ((u + 1 : ℕ) : ℝ) := by
        push_cast
        field_simp
        ring
      rw [he]
      simp only [mul_one_div]

/-- Transfer an admissible real exponent and two explicit actual moment bounds to the deeper remainder; the final specialization discharges these bounds. -/
theorem deep_remainder_of_scaled_bounds {p k a b xi X u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hH : 1 ≤ H) (hgap : b - a ≤ 2 * H)
    (hX : 0 < X) {C lam : ℝ} (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam)
    (hbudget : (C * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (hA : meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam)
    (hB : meanValue ((u + 1) * k) k (X / p ^ (b + H) + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ lam)
    (colour : Fin k → Bool) :
    singularCost p k u ^ H * levelMixedMaximum p k a (b + H) xi X u colour ≤
      (((X : ℝ) / (p : ℝ) ^ a) ^ (lam - 2 * (k : ℝ) * u) *
        ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))) * (p : ℝ) ^ (-((H : ℝ) / 2)) := by
  have hCpos : 0 < C := by linarith
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hp0 : (0 : ℝ) < p := by linarith
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have huR : (k : ℝ) ≤ u := by exact_mod_cast hu
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hgapR : (b : ℝ) - a ≤ 2 * H := by
    have h : b ≤ a + 2 * H := by omega
    have h' : (b : ℝ) ≤ a + 2 * H := by exact_mod_cast h
    linarith
  have hI : levelMixedMaximum p k a (b + H) xi X u colour ≤ C *
      (((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
       ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (lam * u / ((u + 1 : ℕ) : ℝ))) := by
    apply Finset.sup'_le Finset.univ_nonempty
    intro c hc
    exact mixed_le_of_scaled_bounds (by omega) hC hA hB colour
  have hS : singularCost p k u ^ H ≤ iterationConstant k u ^ H * (p : ℝ) ^ ((k - 1) * H) := by
    calc
      _ ≤ (iterationConstant k u * (p : ℝ) ^ (k - 1)) ^ H :=
        pow_le_pow_left₀ (by unfold singularCost; positivity) (singularCost_le_power p k u) H
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hs := scaled_remainder_le (show (0 : ℝ) < X by exact_mod_cast hX) hp1 hkR huR
    habR (Nat.cast_nonneg H) hgapR hlam
  have hs' : (p : ℝ) ^ ((k - 1) * H) *
      ((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
      ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (lam * u / ((u + 1 : ℕ) : ℝ)) ≤
      (((X : ℝ) / (p : ℝ) ^ a) ^ (lam - 2 * (k : ℝ) * u) *
        ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))) / (p : ℝ) ^ H := by
    convert hs using 1 <;>
      simp only [← Real.rpow_natCast, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one,
        Nat.cast_add, Nat.cast_ofNat, Real.rpow_neg hp0.le, div_eq_mul_inv, mul_assoc]
  have hb := constant_power_absorption hC
    (show 0 ≤ iterationConstant k u by unfold iterationConstant; positivity) hp0 hbudget hH
  calc
    _ ≤ singularCost p k u ^ H * (C *
        (((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
         ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (lam * u / ((u + 1 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_left hI (by unfold singularCost; positivity)
    _ ≤ (iterationConstant k u ^ H * (p : ℝ) ^ ((k - 1) * H)) * (C *
        (((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
         ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (lam * u / ((u + 1 : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_right hS (by positivity)
    _ = (C * iterationConstant k u ^ H) * ((p : ℝ) ^ ((k - 1) * H) *
        ((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
        ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (lam * u / ((u + 1 : ℕ) : ℝ))) := by ring
    _ ≤ (C * iterationConstant k u ^ H) *
        ((((X : ℝ) / (p : ℝ) ^ a) ^ (lam - 2 * (k : ℝ) * u) *
          ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))) / (p : ℝ) ^ H) :=
      mul_le_mul_of_nonneg_left hs' (by unfold iterationConstant; positivity)
    _ = (((X : ℝ) / (p : ℝ) ^ a) ^ (lam - 2 * (k : ℝ) * u) *
        ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))) *
        (C * iterationConstant k u ^ H / (p : ℝ) ^ H) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

/-- The original deeper-level remainder saves a half-depth base power using proved elementary moments and an explicit base threshold. -/
theorem deep_remainder_power_saving {p k a b xi X u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hH : 1 ≤ H) (hgap : b - a ≤ 2 * H)
    (hX : p ^ (b + H) ≤ X)
    (hp : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (colour : Fin k → Bool) :
    singularCost p k u ^ H * levelMixedMaximum p k a (b + H) xi X u colour ≤
      (((X : ℝ) / (p : ℝ) ^ a) ^ k * ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))) *
        (p : ℝ) ^ (-((H : ℝ) / 2)) := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hXa : p ^ a ≤ X := (Nat.pow_le_pow_right hp1 (by omega : a ≤ b + H)).trans hX
  have hXpos : 0 < X := (Nat.pos_of_ne_zero (NeZero.ne (p ^ (b + H)))).trans_le hX
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤
      ((k * (2 * u + 1) : ℕ) : ℝ) := by push_cast; nlinarith
  have hA : meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤ elementaryConstant k u *
      ((X : ℝ) / (p : ℝ) ^ a) ^ (((k * (2 * u + 1) : ℕ) : ℝ)) := by
    simpa only [Real.rpow_natCast] using higher_meanValue_rounded (k := k) (u := u) hXa
  have hB : meanValue ((u + 1) * k) k (X / p ^ (b + H) + 1) ≤ elementaryConstant k u *
      ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ (((k * (2 * u + 1) : ℕ) : ℝ)) := by
    simpa only [Real.rpow_natCast] using higher_meanValue_rounded (k := k) (u := u) hX
  have he := deep_remainder_of_scaled_bounds (xi := xi) hk hu hab hH hgap hXpos
    (elementaryConstant_one_le k u) hlam hp hA hB colour
  have heq : ((k * (2 * u + 1) : ℕ) : ℝ) - 2 * (k : ℝ) * u = k := by push_cast; ring
  simpa only [heq, Real.rpow_natCast] using he

/-- The same explicit constant threshold already makes the base strictly larger than the degree. -/
theorem degree_lt_of_budget {p k u : ℕ} {C : ℝ} (hk : 2 ≤ k) (hu : k ≤ u)
    (hC : 1 ≤ C) (hbudget : (C * iterationConstant k u) ^ 2 ≤ (p : ℝ)) : k < p := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have huR : (k : ℝ) ≤ u := by exact_mod_cast hu
  have hpow : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * (k * u)) :=
    one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ k - 1))
  have hD : 2 * (k : ℝ) ≤ iterationConstant k u := by
    unfold iterationConstant
    nlinarith
  have hD0 : 0 ≤ iterationConstant k u := by unfold iterationConstant; positivity
  have hCD : 2 * (k : ℝ) ≤ C * iterationConstant k u := by nlinarith
  have hsq := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 2 * k) (by positivity : 0 ≤ C * iterationConstant k u)).mpr hCD
  have hpR : (k : ℝ) < p := by nlinarith
  exact_mod_cast hpR

/-- The complete actual finite conditioning inequality has a power-saving remainder with no supplied moment-budget premise. -/
theorem finite_conditioning_power_saving {p k a b xi X u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b)
    (hH : 1 ≤ H) (hgap : b - a ≤ 2 * H) (hX : p ^ (b + H) ≤ X)
    (hp : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (colour : Fin k → Bool) :
    levelMixedMaximum p k a b xi X u colour ≤
      (((X : ℝ) / (p : ℝ) ^ a) ^ k * ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))) *
        (p : ℝ) ^ (-((H : ℝ) / 2)) +
      selectionCost k u * ∑ h ∈ Finset.range H,
        singularCost p k u ^ h * levelConditionedMaximum p k a (b + h) xi X u colour := by
  have hkp := (degree_lt_of_budget hk hu (elementaryConstant_one_le k u) hp).le
  apply (finite_conditioning_iteration hkp (by omega) (by omega) colour b H).trans
  exact add_le_add (deep_remainder_power_saving hk hu hab hH hgap hX hp colour) (le_refl _)

end
end RiemannGaussian.VinogradovConditioningPowerSaving
