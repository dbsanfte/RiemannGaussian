/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordParameters

/-!
# Ford's original moment step at every positive endpoint

The actual short-prime supply is isolated as an explicit finite arithmetic
proposition. At large endpoints the constructed scales and cutoffs apply;
below the published threshold the previous literal moment pays the extra
powers. The maximum is exactly the coefficient in Ford's Lemma 3.5.
The short-prime supply is not proved or asserted as an axiom here.
-/

namespace RiemannGaussian.VinogradovFordGlobalStep
noncomputable section
open VinogradovMeanValue VinogradovFordScales VinogradovFordSchedule
open VinogradovFordTailThreshold VinogradovFordParameters

/-- The exact short-prime input at the published real base. This is an
explicit unproved proposition, not an assumed mean-value estimate. -/
def ShortPrimeSupply (k : ℕ) (omega : ℝ) : Prop :=
  ∀ M : ℝ, publishedBase k omega ≤ M →
    ∃ π : Finset ℕ, π.card = k ^ 3 ∧
      ∀ p ∈ π, p.Prime ∧ M < (p : ℝ) ∧ (p : ℝ) ≤ (1 + omega) * M

/-- The stated short-prime input supplies all literal packets at the
constructed scales; no admissibility conditions remain as packet inputs. -/
theorem moment_bound_of_supply (k r n P s : ℕ) {C delta omega : ℝ}
    (hk : 26 ≤ k) (hs : k ≤ s) (hsMax : s ≤ k ^ 3)
    (hr1 : 1 ≤ r) (hr : r ≤ k) (hlimit : 10 * (n + 1) ≤ 9 * r)
    (hC : 0 < C) (homega : 0 < omega) (homegaHalf : omega ≤ 1 / 2)
    (hP : publishedBase k omega ^ (k + 1) ≤ P)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hdepth : (n : ℝ) * ((n : ℝ) - 1) ≤ depthReserve k r delta)
    (hroot : 1 / ((k : ℝ) + 1) ≤ stationaryScale k r delta)
    (hsupply : ShortPrimeSupply k omega)
    (hsource : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤
      C * (X : ℝ) ^ sourceExponent k s delta) :
    meanValue (s + k) k P ≤
      C * ((k : ℝ) ^ (3 * k) * (1 + omega) ^ (4 * s + k ^ 2)) *
        (P : ℝ) ^ sourceExponent k (s + k)
          (nextDefect k r delta (schedule k r n delta 0)) := by
  classical
  have hV := publishedBase_ge hk homega homegaHalf
  have hkR : (26 : ℝ) ≤ k := by exact_mod_cast hk
  have hV1 : 1 ≤ publishedBase k omega := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 26) hkR 3]
  have hpackets (d : ℕ) : ∃ π : Finset ℕ, π.card = k ^ 3 ∧
      ∀ p ∈ π, p.Prime ∧ primeScale k r n P delta d < (p : ℝ) ∧
        (p : ℝ) ≤ (1 + omega) * primeScale k r n P delta d := by
    apply hsupply
    exact base_le_scale hV1 hP
      (schedule_bounds (by omega) (by omega) hdelta hdepth hroot d).2.1
  choose π hcard hπ using hpackets
  exact moment_bound_of_packets k r n P s π hk hs hsMax hr1 hr hlimit hC homega
    homegaHalf hP hdelta hdepth hroot (fun d _ => hcard d) (fun d _ => hπ d) hsource

/-- The exact decrease splits into two nonnegative reserves when the
scale is at most the terminal scale and the depth reserve is nonnegative. -/
theorem defect_decrease_identity (k r : ℕ) (delta phi : ℝ) :
    delta - nextDefect k r delta phi =
      (k : ℝ) * (1 - r * phi) + phi * depthReserve k r delta / 2 := by
  unfold nextDefect depthReserve
  ring

/-- The original schedule never increases the defect in its admissible
range. This pays the small-endpoint exponent without an extra hypothesis. -/
theorem nextDefect_le {k r n : ℕ} (hk : 0 < k) (hr : 0 < r) {delta : ℝ}
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hdepth : (n : ℝ) * ((n : ℝ) - 1) ≤ depthReserve k r delta)
    (hroot : 1 / ((k : ℝ) + 1) ≤ stationaryScale k r delta) :
    nextDefect k r delta (schedule k r n delta 0) ≤ delta := by
  have hb := schedule_bounds hk hr hdelta hdepth hroot 0
  have hmul : (r : ℝ) * schedule k r n delta 0 ≤ 1 := by
    have hh := (le_div_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).mp hb.2.2
    simpa only [mul_comm] using hh
  have hy := (depth_nonneg n).trans hdepth
  have hh := defect_decrease_identity k r delta (schedule k r n delta 0)
  have hnonneg : 0 ≤ (k : ℝ) * (1 - r * schedule k r n delta 0) +
      schedule k r n delta 0 * depthReserve k r delta / 2 :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hmul))
      (div_nonneg (mul_nonneg hb.1.le hy) (by norm_num))
  linarith

/-- The coefficient takes the maximum of the large-endpoint packet cost
and the small-endpoint cost, as in the published repeated iteration. -/
def stepCoefficient (k s : ℕ) (omega delta delta' : ℝ) : ℝ :=
  max ((k : ℝ) ^ (3 * k) * (1 + omega) ^ (4 * s + k ^ 2))
    (publishedBase k omega ^ (((k : ℝ) + 1) * (delta - delta')))

/-- The all-endpoint coefficient is strictly positive in the published
parameter range. -/
theorem stepCoefficient_pos {k s : ℕ} (hk : 0 < k) {omega delta delta' : ℝ}
    (homega : 0 < omega) : 0 < stepCoefficient k s omega delta delta' := by
  apply lt_of_lt_of_le _ (le_max_left _ _)
  exact mul_pos (pow_pos (by exact_mod_cast hk) _) (pow_pos (by linarith) _)

/-- The literal lower-order moment controls the small endpoint with
exactly the published defect-difference exponent. -/
theorem small_endpoint_bound {k s P : ℕ} {C delta delta' V : ℝ}
    (hP : 1 ≤ P) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hsmall : (P : ℝ) ≤ V ^ (k + 1)) (hdelta : delta' ≤ delta)
    (hsource : meanValue s k P ≤ C * (P : ℝ) ^ sourceExponent k s delta) :
    meanValue (s + k) k P ≤
      C * V ^ (((k : ℝ) + 1) * (delta - delta')) *
        (P : ℝ) ^ sourceExponent k (s + k) delta' := by
  have hp : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hmoment : meanValue (s + k) k P ≤ (P : ℝ) ^ (2 * k) * meanValue s k P := by
    simpa only [meanValue, Nat.add_sub_cancel_left, Fintype.card_fin] using
      VinogradovPowerSumRigidity.moment_le_of_order_le (Nat.le_add_right s k)
        (fun n : Fin P => monomialFrequency k (n.val + 1))
  have hpow : (P : ℝ) ^ (delta - delta') ≤
      V ^ (((k : ℝ) + 1) * (delta - delta')) := by
    calc
      _ ≤ (V ^ (k + 1)) ^ (delta - delta') :=
        Real.rpow_le_rpow hp.le hsmall (sub_nonneg.mpr hdelta)
      _ = _ := by rw [← Real.rpow_natCast_mul hV]; push_cast; rfl
  calc
    _ ≤ (P : ℝ) ^ (2 * k) * (C * (P : ℝ) ^ sourceExponent k s delta) :=
      hmoment.trans (mul_le_mul_of_nonneg_left hsource (by positivity))
    _ = C * (P : ℝ) ^ (delta - delta') * (P : ℝ) ^ sourceExponent k (s + k) delta' := by
      rw [← Real.rpow_natCast]
      have he : ((2 * k : ℕ) : ℝ) + sourceExponent k s delta =
          (delta - delta') + sourceExponent k (s + k) delta' := by
        unfold sourceExponent
        push_cast
        ring
      rw [mul_left_comm, ← Real.rpow_add hp, he, Real.rpow_add hp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC)
      (Real.rpow_nonneg hp.le _)

/-- Ford's original step reaches every positive integer endpoint, with
the exact published maximum coefficient. Only the ordinary source moment,
scalar schedule restrictions and explicit short-prime supply remain. -/
theorem all_endpoint_bound (k r n s : ℕ) {C delta omega : ℝ}
    (hk : 26 ≤ k) (hs : k ≤ s) (hsMax : s ≤ k ^ 3)
    (hr1 : 1 ≤ r) (hr : r ≤ k) (hlimit : 10 * (n + 1) ≤ 9 * r)
    (hC : 0 < C) (homega : 0 < omega) (homegaHalf : omega ≤ 1 / 2)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2)
    (hdepth : (n : ℝ) * ((n : ℝ) - 1) ≤ depthReserve k r delta)
    (hroot : 1 / ((k : ℝ) + 1) ≤ stationaryScale k r delta)
    (hsupply : ShortPrimeSupply k omega)
    (hsource : ∀ X : ℕ, 1 ≤ X → meanValue s k X ≤
      C * (X : ℝ) ^ sourceExponent k s delta)
    (P : ℕ) (hP : 1 ≤ P) :
    meanValue (s + k) k P ≤
      C * stepCoefficient k s omega delta (nextDefect k r delta (schedule k r n delta 0)) *
        (P : ℝ) ^ sourceExponent k (s + k)
          (nextDefect k r delta (schedule k r n delta 0)) := by
  by_cases hlarge : publishedBase k omega ^ (k + 1) ≤ (P : ℝ)
  · apply (moment_bound_of_supply k r n P s hk hs hsMax hr1 hr hlimit hC homega
      homegaHalf hlarge hdelta hdepth hroot hsupply hsource).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hC.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · have hd := nextDefect_le (by omega : 0 < k) (by omega : 0 < r) hdelta hdepth hroot
    have hV : 0 ≤ publishedBase k omega :=
      (by positivity : (0 : ℝ) ≤ 64 * (k : ℝ) ^ 3).trans (publishedBase_ge hk homega homegaHalf)
    apply (small_endpoint_bound hP hC.le hV (le_of_not_ge hlarge) hd (hsource P hP)).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hC.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end
end RiemannGaussian.VinogradovFordGlobalStep
