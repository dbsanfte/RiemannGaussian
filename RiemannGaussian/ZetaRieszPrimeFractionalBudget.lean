/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCoreExtensions

/-!
# Fractional logarithmic costs for literal prime sets

Dyadic logarithmic shells turn the existing Chebyshev mass bound into
fractional prime moments. The bound is used to preserve the minimum-prime
information in the six-prime coefficient and pay an exponential head.
It is an upper count, not a density approximation of the signed carrier.
-/

namespace RiemannGaussian.ZetaRieszPrimeFractionalBudget
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- Explicit cost of a positive fractional logarithmic prime moment. -/
def momentConstant (a : ℝ) : ℝ := 6*Real.log 4/(1-(1/2 : ℝ)^a)

/-- Every positive exponent has a finite positive counting constant. -/
theorem momentConstant_pos {a : ℝ} (ha : 0 < a) : 0 < momentConstant a := by
  unfold momentConstant
  have h := Real.rpow_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num) ha
  positivity

private theorem shell_bound (D : Finset ℕ) {X a : ℝ} (hX : 0 < X) (ha : 0 < a)
    (hD : ∀ p ∈ D, p.Prime ∧ X/2 < Real.log p ∧ Real.log p ≤ X) :
    (∑ p ∈ D, (Real.log p)^a*Real.exp (-Real.log p)) ≤ 6*Real.log 4*X^a := by
  by_cases hne : D.Nonempty
  · obtain ⟨q,hq⟩ := hne
    have hqlog : (1/2 : ℝ) < Real.log q := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (show (2 : ℝ) ≤ q by exact_mod_cast (hD q hq).1.two_le)
      linarith [Real.log_two_gt_d9]
    have hXhalf : (1/2 : ℝ) < X := hqlog.trans_le (hD q hq).2.2
    have hmass := ZetaRieszCoreExtensions.prime_log_mass_le D hX.le
      (fun p hp => ⟨(hD p hp).1,(hD p hp).2.2⟩)
    have hs : (∑ p ∈ D, (Real.log p)^a*Real.exp (-Real.log p)) ≤
        (2*X^a/X)*(∑ p ∈ D, Real.log p*Real.exp (-Real.log p)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hl0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
      have hpw := Real.rpow_le_rpow hl0 (hD p hp).2.2 ha.le
      have hlo := (hD p hp).2.1
      have hmul : X^a ≤ (2*X^a/X)*Real.log p := by
        have h := mul_le_mul_of_nonneg_left (show X ≤ 2*Real.log p by linarith)
          (Real.rpow_nonneg hX.le a)
        calc
          _ ≤ 2*X^a*Real.log p/X := (le_div_iff₀ hX).mpr (by nlinarith only [h])
          _ = _ := by ring
      have hh := mul_le_mul_of_nonneg_right (hpw.trans hmul) (Real.exp_nonneg (-Real.log p))
      convert hh using 1
      ring
    apply hs.trans
    calc
      _ ≤ (2*X^a/X)*(Real.log 4*(1+X)) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ (2*X^a/X)*(Real.log 4*(3*X)) := by gcongr; linarith
      _ = _ := by field_simp; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

/-- Literal finite prime sets have fractional logarithmic mass of the
correct power scale. Every prime, including the small endpoints, is kept. -/
theorem prime_fractional_log_mass_le (D : Finset ℕ) {X a : ℝ}
    (hX : 0 < X) (ha : 0 < a)
    (hD : ∀ p ∈ D, p.Prime ∧ Real.log p ≤ X) :
    (∑ p ∈ D, (Real.log p)^a*Real.exp (-Real.log p)) ≤ momentConstant a*X^a := by
  have hex : ∀ p : ℕ, ∃ j : ℕ, p ∈ D →
      X*(1/2 : ℝ)^(j+1) < Real.log p ∧ Real.log p ≤ X*(1/2 : ℝ)^j := by
    intro p
    by_cases hp : p ∈ D
    · have hl : 0 < Real.log p := Real.log_pos (by exact_mod_cast (hD p hp).1.one_lt)
      obtain ⟨j,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one
        (show 0 < Real.log p/X by positivity) ((div_le_one hX).mpr (hD p hp).2)
        (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
      refine ⟨j,fun _ => ⟨?_,?_⟩⟩
      · have h := (lt_div_iff₀ hX).mp hlo
        nlinarith
      · have h := (div_le_iff₀ hX).mp hhi
        nlinarith
    · exact ⟨0,fun h => False.elim (hp h)⟩
  choose shell hshell using hex
  let J := D.image shell
  let F := fun j => D.filter (fun p => shell p = j)
  have he : ∑ p ∈ D, (Real.log p)^a*Real.exp (-Real.log p) =
      ∑ j ∈ J, ∑ p ∈ F j, (Real.log p)^a*Real.exp (-Real.log p) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to (f := fun p : ℕ => (Real.log p)^a*Real.exp (-Real.log p))
      (fun p hp => Finset.mem_image_of_mem shell hp)
  have hB (j : ℕ) : (∑ p ∈ F j, (Real.log p)^a*Real.exp (-Real.log p)) ≤
      6*Real.log 4*X^a*((1/2 : ℝ)^a)^j := by
    have hx : 0 < X*(1/2 : ℝ)^j := by positivity
    have h := shell_bound (F j) hx ha (by
      intro p hp
      obtain ⟨hp,hj⟩ := Finset.mem_filter.mp hp
      obtain ⟨hl,hu⟩ := hshell p hp
      rw [hj] at hl hu
      refine ⟨(hD p hp).1,?_,hu⟩
      simpa only [pow_succ,div_eq_mul_inv,one_div,mul_assoc,one_mul] using hl)
    have he : (X*(1/2 : ℝ)^j)^a = X^a*((1/2 : ℝ)^a)^j := by
      rw [Real.mul_rpow hX.le (by positivity),← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 1/2)]
    exact h.trans_eq (by rw [he]; ring)
  rw [he]
  have hr0 : 0 ≤ (1/2 : ℝ)^a := by positivity
  have hr1 : (1/2 : ℝ)^a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  have hsum := (summable_geometric_of_norm_lt_one (x := (1/2 : ℝ)^a)
    (by simpa only [Real.norm_eq_abs,abs_of_nonneg hr0] using hr1)).sum_le_tsum
    J (by intro j _; exact pow_nonneg hr0 j)
  have hseries : ∑' j : ℕ, ((1/2 : ℝ)^a)^j = (1-(1/2 : ℝ)^a)⁻¹ :=
    tsum_geometric_of_norm_lt_one (by simpa only [Real.norm_eq_abs,abs_of_nonneg hr0] using hr1)
  rw [hseries] at hsum
  calc
    _ ≤ ∑ j ∈ J, 6*Real.log 4*X^a*((1/2 : ℝ)^a)^j := Finset.sum_le_sum (fun j _ => hB j)
    _ = (6*Real.log 4*X^a)*∑ j ∈ J, ((1/2 : ℝ)^a)^j := by rw [Finset.mul_sum]
    _ ≤ (6*Real.log 4*X^a)*(1-(1/2 : ℝ)^a)⁻¹ :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = momentConstant a*X^a := by unfold momentConstant; ring

/-- Retain the minimum in a five-factor logarithmic cost. The marked
small factor receives half the exponent and the other four one eighth
each. No sign, phase or factorial weight is changed by this inequality. -/
theorem minimum_le_weighted_product {t r a b c d : ℝ} (ht : 0 < t)
    (hr : t ≤ r) (ha : t ≤ a) (hb : t ≤ b) (hc : t ≤ c) (hd : t ≤ d) :
    t ≤ r^(1/2 : ℝ)*a^(1/8 : ℝ)*b^(1/8 : ℝ)*c^(1/8 : ℝ)*d^(1/8 : ℝ) := by
  have hr0 := ht.le.trans hr
  have ha0 := ht.le.trans ha
  have hb0 := ht.le.trans hb
  have hc0 := ht.le.trans hc
  have hd0 := ht.le.trans hd
  calc
    _ = t^(1/2 : ℝ)*t^(1/8 : ℝ)*t^(1/8 : ℝ)*t^(1/8 : ℝ)*t^(1/8 : ℝ) := by
      rw [← Real.rpow_add ht,← Real.rpow_add ht,← Real.rpow_add ht,← Real.rpow_add ht]
      norm_num
    _ ≤ _ := by gcongr

/-- Five-prime coefficients leave four logarithmic factors after the
largest prime is counted. Retaining their minimum assigns half the cost
to the marked small prime and one sixth to each remaining prime. -/
theorem minimum_le_weighted_product_three {t r a b c : ℝ} (ht : 0 < t)
    (hr : t ≤ r) (ha : t ≤ a) (hb : t ≤ b) (hc : t ≤ c) :
    t ≤ r^(1/2 : ℝ)*a^(1/6 : ℝ)*b^(1/6 : ℝ)*c^(1/6 : ℝ) := by
  have hr0 := ht.le.trans hr
  have ha0 := ht.le.trans ha
  have hb0 := ht.le.trans hb
  have hc0 := ht.le.trans hc
  calc
    _ = t^(1/2 : ℝ)*t^(1/6 : ℝ)*t^(1/6 : ℝ)*t^(1/6 : ℝ) := by
      rw [← Real.rpow_add ht,← Real.rpow_add ht,← Real.rpow_add ht]
      norm_num
    _ ≤ _ := by gcongr

end
end RiemannGaussian.ZetaRieszPrimeFractionalBudget
