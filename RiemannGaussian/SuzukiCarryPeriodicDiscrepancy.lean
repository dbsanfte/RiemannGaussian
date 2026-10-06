/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryMellinLimit

/-!
# A main-scale obstruction to periodic carry replacement

The literal Fejer overlap and every carry endpoint are retained. Even a
zero-mean periodic carry product with bounded partial sums has a nonzero
weighted boundary discrepancy when its period is comparable to H.
-/

namespace RiemannGaussian.SuzukiCarryPeriodicDiscrepancy
noncomputable section
open Complex Filter Set
open SuzukiCarryGram SuzukiCarryCorrelation SuzukiCarryFejer SuzukiCarryMellinLimit
open scoped BigOperators Topology

/-- Real amplitude of the exact finite Fejer vector. -/
def weight (H N : ℕ) : ℝ := tent (((N+1 : ℕ) : ℝ)/(H : ℝ))

/-- The literal overlap of two coefficient rows, before any period average. -/
def overlap (H h N : ℕ) : ℝ := weight H N*weight H (N+h)

/-- The exact zero-mean remainder, with the finite period normalization. -/
def zeroMeanProduct (d h N : ℕ) : ℝ :=
  incidence N d*incidence (N+h) d-lagAutocorrelation d h

/-- The surviving weighted periodic discrepancy. -/
def discrepancy (H h d : ℕ) : ℝ :=
  ∑ N ∈ Finset.range (3*H), overlap H h N*zeroMeanProduct d h N

/-- The proposed mean/remainder split is exact for the literal row.
Neither signed piece is assumed small. -/
theorem weighted_product_eq_mean_add_discrepancy (H h d : ℕ) :
    (∑ N ∈ Finset.range (3*H), overlap H h N*incidence N d*incidence (N+h) d) =
      lagAutocorrelation d h*(∑ N ∈ Finset.range (3*H), overlap H h N)+discrepancy H h d := by
  unfold discrepancy zeroMeanProduct
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have he : (∑ N ∈ Finset.range (3*H), overlap H h N*(incidence N d*incidence (N+h) d)) =
      ∑ N ∈ Finset.range (3*H), overlap H h N*incidence N d*incidence (N+h) d := by
    apply Finset.sum_congr rfl
    intro N _
    ring
  rw [he]
  ring

theorem coefficient_eq_weight {H : ℕ} (hH : 0 < H) (N : ℕ) :
    coefficient H H N = (weight H N : ℂ) := coefficient_eq_tent hH N

theorem weight_zero_left {H N : ℕ} (hH : 0 < H) (hN : N < H) :
    weight H N = 0 := by
  apply tent_eq_zero_of_le
  rw [div_le_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)]
  exact_mod_cast (show N+1 ≤ 1*H by omega)

theorem weight_zero_right {H N : ℕ} (hH : 0 < H) (hN : 3*H ≤ N) :
    weight H N = 0 := by
  apply tent_eq_zero_of_ge
  rw [le_div_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)]
  exact_mod_cast (show 3*H ≤ N+1 by omega)

theorem weight_left {H N : ℕ} (hH : 0 < H) (hlo : H ≤ N) (hhi : N < 2*H) :
    weight H N = (((N+1 : ℕ) : ℝ)/(H : ℝ))-1 := by
  apply tent_eq_left
  · rw [le_div_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)]
    exact_mod_cast (show 1*H ≤ N+1 by omega)
  · rw [div_le_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)]
    exact_mod_cast (show N+1 ≤ 2*H by omega)

theorem weight_right {H N : ℕ} (hH : 0 < H) (hlo : 2*H ≤ N) (hhi : N < 3*H) :
    weight H N = 3-(((N+1 : ℕ) : ℝ)/(H : ℝ)) := by
  apply tent_eq_right
  · rw [le_div_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)]
    exact_mod_cast (show 2*H ≤ N+1 by omega)
  · rw [div_le_iff₀ (by exact_mod_cast hH : (0 : ℝ) < H)]
    exact_mod_cast (show N+1 ≤ 3*H by omega)

private theorem sum_supported {H h : ℕ} (hH : 0 < H) (hh : h ≤ 2*H) (g : ℕ → ℝ) :
    (∑ N ∈ Finset.range (3*H), overlap H h N*g N) =
      ∑ k ∈ Finset.range (2*H-h), overlap H h (H+k)*g (H+k) := by
  rw [show 3*H = H+2*H by omega, Finset.sum_range_add]
  have hz : (∑ N ∈ Finset.range H, overlap H h N*g N) = 0 := by
    apply Finset.sum_eq_zero
    intro N hN
    simp [overlap, weight_zero_left hH (Finset.mem_range.mp hN)]
  rw [hz, zero_add, show 2*H = (2*H-h)+h by omega, Finset.sum_range_add]
  have hz2 : (∑ k ∈ Finset.range h,
      overlap H h (H+(2*H-h+k))*g (H+(2*H-h+k))) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    simp [overlap, weight_zero_right hH (show 3*H ≤ H+(2*H-h+k)+h by omega)]
  simp only [hz2, add_zero, Nat.add_sub_cancel]

private theorem overlap_atom {H h k : ℕ} (hH : 0 < H) (hlo : H ≤ h)
    (hhi : h ≤ 2*H) (hk : k < 2*H-h) :
    overlap H h (H+k) =
      (((k+1 : ℕ) : ℝ)*((2*H-h : ℕ)-((k+1 : ℕ) : ℝ)))/(H : ℝ)^2 := by
  rw [overlap, weight_left hH (by omega) (by omega), weight_right hH (by omega) (by omega)]
  rw [Nat.cast_sub hhi]
  push_cast
  field_simp
  ring

private theorem sum_first (r : ℕ) :
    (∑ k ∈ Finset.range r, ((k+1 : ℕ) : ℝ)) = (r : ℝ)*((r : ℝ)+1)/2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem sum_overlap_polynomial (r : ℕ) :
    (∑ k ∈ Finset.range r, ((k+1 : ℕ) : ℝ)*((r : ℝ)-((k+1 : ℕ) : ℝ))) =
      (r : ℝ)*((r : ℝ)^2-1)/6 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ]
    have he : (∑ k ∈ Finset.range r, ((k+1 : ℕ) : ℝ)*
        ((r+1 : ℕ)-((k+1 : ℕ) : ℝ))) =
        (∑ k ∈ Finset.range r, ((k+1 : ℕ) : ℝ)*((r : ℝ)-((k+1 : ℕ) : ℝ)))+
          ∑ k ∈ Finset.range r, ((k+1 : ℕ) : ℝ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring
    rw [he, ih, sum_first]
    push_cast
    ring

/-- Exact overlap mass, without replacing the Fejer vector by its limit. -/
theorem sum_overlap_eq {H h : ℕ} (hH : 0 < H) (hlo : H ≤ h) (hhi : h ≤ 2*H) :
    (∑ N ∈ Finset.range (3*H), overlap H h N) =
      ((2*H-h : ℕ) : ℝ)*(((2*H-h : ℕ) : ℝ)^2-1)/(6*(H : ℝ)^2) := by
  have he := sum_supported hH hhi (fun _ => 1)
  simp only [mul_one] at he
  rw [he]
  calc
    _ = ∑ k ∈ Finset.range (2*H-h),
        (((k+1 : ℕ) : ℝ)*((2*H-h : ℕ)-((k+1 : ℕ) : ℝ)))/(H : ℝ)^2 :=
      Finset.sum_congr rfl (fun k hk => overlap_atom hH hlo hhi (Finset.mem_range.mp hk))
    _ = _ := by rw [← Finset.sum_div, sum_overlap_polynomial]; ring

/-- The literal carry product in this odd main-scale period has exactly
one negative spike, including its integer endpoint. -/
theorem carry_product_one_spike {h : ℕ} (hh : 0 < h) (N : ℕ) :
    incidence N (2*h+1)*incidence (N+h) (2*h+1) =
      -(if N%(2*h+1) = h then (1 : ℝ) else 0) := by
  have hd : 2 ≤ 2*h+1 := by omega
  have hr : N%(2*h+1) < 2*h+1 := Nat.mod_lt _ (by omega)
  rw [incidence_two_spikes hd, incidence_two_spikes hd]
  rw [show (2*h+1-1)/2 = h by omega, show 2*h+1-1 = 2*h by omega]
  by_cases hp : N%(2*h+1) = h
  · have hs : (N+h)%(2*h+1) = 2*h := by
      rw [Nat.add_mod, hp, Nat.mod_eq_of_lt (by omega : h < 2*h+1)]
      rw [show h+h = 2*h by omega, Nat.mod_eq_of_lt (by omega : 2*h < 2*h+1)]
    simp [hp, hs]
    rw [if_neg (show h ≠ 2*h by omega), if_neg (show 2*h ≠ h by omega)]
    norm_num
  · by_cases hn : N%(2*h+1) = 2*h
    · have hs : (N+h)%(2*h+1) = h-1 := by
        rw [Nat.add_mod, hn, Nat.mod_eq_of_lt (by omega : h < 2*h+1)]
        rw [show 2*h+h = (2*h+1)+(h-1) by omega, Nat.add_mod,
          Nat.mod_self, zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (by omega)
      simp [hn, hs]
      rw [if_neg (show 2*h ≠ h by omega), if_neg (show h-1 ≠ h by omega),
        if_neg (show h-1 ≠ 2*h by omega)]
      norm_num
    · simp [hp, hn]

theorem mean_one_spike {h : ℕ} (hh : 0 < h) :
    lagAutocorrelation (2*h+1) h = -1/((2*h+1 : ℕ) : ℝ) := by
  rw [lagAutocorrelation_eq (by omega)]
  rw [Nat.mod_eq_of_lt (by omega : h < 2*h+1), show (2*h+1)/2 = h by omega,
    show 2*h+1-h = h+1 by omega]
  simp [hh.ne']

theorem zeroMean_one_spike {h : ℕ} (hh : 0 < h) (N : ℕ) :
    zeroMeanProduct (2*h+1) h N = 1/((2*h+1 : ℕ) : ℝ)-
      (if N%(2*h+1) = h then 1 else 0) := by
  rw [zeroMeanProduct, carry_product_one_spike hh, mean_one_spike hh]
  ring

private theorem spike_prefix {h m : ℕ} (hh : 0 < h) (hm : m ≤ 2*h+1) :
    (∑ N ∈ Finset.range m, zeroMeanProduct (2*h+1) h N) =
      (m : ℝ)/((2*h+1 : ℕ) : ℝ)-(if h < m then 1 else 0) := by
  classical
  have he : (∑ N ∈ Finset.range m, zeroMeanProduct (2*h+1) h N) =
      ∑ N ∈ Finset.range m, (1/((2*h+1 : ℕ) : ℝ)-(if N = h then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro N hN
    rw [zeroMean_one_spike hh, Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hN; omega)]
  rw [he, Finset.sum_sub_distrib]
  have hi : (∑ N ∈ Finset.range m, if N = h then (1 : ℝ) else 0) =
      if h < m then 1 else 0 := by
    by_cases hmem : h < m
    · rw [if_pos hmem, Finset.sum_eq_single h]
      · simp
      · intro N _ hne
        simp [hne]
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr hmem))
    · rw [if_neg hmem]
      apply Finset.sum_eq_zero
      intro N hN
      have hne : N ≠ h := by have := Finset.mem_range.mp hN; omega
      simp [hne]
  rw [hi]
  simp [div_eq_mul_inv]

/-- Complete periods cancel exactly. -/
theorem sum_zeroMean_period {h : ℕ} (hh : 0 < h) :
    (∑ N ∈ Finset.range (2*h+1), zeroMeanProduct (2*h+1) h N) = 0 := by
  rw [spike_prefix hh le_rfl, if_pos (show h < 2*h+1 by omega),
    div_self (show ((2*h+1 : ℕ) : ℝ) ≠ 0 by positivity), sub_self]

/-- This counterexample satisfies the strongest proposed bounded-partial-
sum input: every prefix has magnitude at most one. -/
theorem abs_zeroMean_prefix_le_one {h : ℕ} (hh : 0 < h) (m : ℕ) :
    |∑ N ∈ Finset.range m, zeroMeanProduct (2*h+1) h N| ≤ 1 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m ≤ 2*h+1
    · rw [spike_prefix hh hm]
      have hd : (0 : ℝ) < (2*h+1 : ℕ) := by positivity
      have hratio : (m : ℝ)/((2*h+1 : ℕ) : ℝ) ≤ 1 := by
        rw [div_le_one hd]
        exact_mod_cast hm
      have hn : 0 ≤ (m : ℝ)/((2*h+1 : ℕ) : ℝ) := by positivity
      split_ifs <;> rw [abs_le] <;> constructor <;> linarith
    · have hperiod (N : ℕ) :
          zeroMeanProduct (2*h+1) h ((2*h+1)+N) = zeroMeanProduct (2*h+1) h N := by
        simp [zeroMean_one_spike hh]
      have he : (∑ N ∈ Finset.range m, zeroMeanProduct (2*h+1) h N) =
          ∑ N ∈ Finset.range (m-(2*h+1)), zeroMeanProduct (2*h+1) h N := by
        rw [show m = (2*h+1)+(m-(2*h+1)) by omega, Finset.sum_range_add,
          sum_zeroMean_period hh, zero_add]
        apply Finset.sum_congr (by congr 1; omega)
        intro N _
        exact hperiod N
      rw [he]
      exact ih (m-(2*h+1)) (by omega)

/-- Main-scale exact discrepancy: the mean is source-sized even when the
literal row lies near the end of its only period. -/
theorem discrepancy_one_spike {H h : ℕ} (hH : 0 < H) (hlo : H ≤ h)
    (hhi : 2*h < 3*H) :
    discrepancy H h (2*h+1) =
      ((2*H-h : ℕ) : ℝ)*(((2*H-h : ℕ) : ℝ)^2-1)/
        (6*(H : ℝ)^2*((2*h+1 : ℕ) : ℝ)) - overlap H h h := by
  have hh : 0 < h := by omega
  have hh2 : h ≤ 2*H := by omega
  unfold discrepancy zeroMeanProduct
  simp_rw [carry_product_one_spike hh, mean_one_spike hh, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_overlap_eq hH hlo hh2]
  have he : (∑ N ∈ Finset.range (3*H),
      overlap H h N* -(if N%(2*h+1) = h then (1 : ℝ) else 0)) = -overlap H h h := by
    rw [sum_supported hH hh2]
    rw [Finset.sum_eq_single (h-H)]
    · simp [show H+(h-H) = h by omega, Nat.mod_eq_of_lt (by omega : h < 2*h+1)]
    · intro k hk hne
      have hn : H+k < 2*h+1 := by have := Finset.mem_range.mp hk; omega
      have hk' : H+k ≠ h := by omega
      simp [Nat.mod_eq_of_lt hn, hk']
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  rw [he]
  ring

/-- Uniform noncontraction on a whole main-scale band. It includes every
prime or prime power d=2h+1 in 2H<=d<=2.02H+1. -/
theorem discrepancy_main_band_lower {H h : ℕ} (hH : 100 ≤ H)
    (hlo : H ≤ h) (hhi : 100*h ≤ 101*H) :
    (1/20 : ℝ) ≤ discrepancy H h (2*h+1) := by
  have hHp : 0 < H := by omega
  have hh2 : h ≤ 2*H := by omega
  have hstrict : 2*h < 3*H := by omega
  let X : ℝ := H
  let z : ℝ := h
  let r : ℝ := (2*H-h : ℕ)
  let D : ℝ := (2*h+1 : ℕ)
  have hX : 100 ≤ X := by change (100 : ℝ) ≤ H; exact_mod_cast hH
  have hz : 100*z ≤ 101*X := by
    change (100 : ℝ)*(h : ℝ) ≤ 101*(H : ℝ)
    exact_mod_cast hhi
  have hlo' : X ≤ z := by change (H : ℝ) ≤ h; exact_mod_cast hlo
  have hr : r = 2*X-z := by simp [r, X, z, Nat.cast_sub hh2]
  have hD : D = 2*z+1 := by simp [D, z]
  have hXp : 0 < X := by linarith
  have hrlo : (99/100 : ℝ)*X ≤ r := by linarith
  have hr0 : 0 ≤ r := by positivity
  have hDhi : D ≤ (21/10 : ℝ)*X := by linarith
  have hDp : 0 < D := by rw [hD]; linarith
  have hsq : (9/10 : ℝ)*X^2 ≤ r^2-1 := by
    have hh := (sq_le_sq₀ (by positivity : 0 ≤ (99/100 : ℝ)*X) hr0).mpr hrlo
    nlinarith [sq_nonneg (X-100)]
  have hnum : (891/1000 : ℝ)*X^3 ≤ r*(r^2-1) := by
    have hh := mul_le_mul hrlo hsq (by positivity : 0 ≤ (9/10 : ℝ)*X^2) hr0
    nlinarith
  have hmean : (7/100 : ℝ) ≤ r*(r^2-1)/(6*X^2*D) := by
    apply (le_div_iff₀ (by positivity : 0 < 6*X^2*D)).mpr
    calc
      _ ≤ (7/100 : ℝ)*(6*X^2*((21/10 : ℝ)*X)) := by
        gcongr
      _ = (441/500 : ℝ)*X^3 := by ring
      _ ≤ (891/1000 : ℝ)*X^3 := by nlinarith [show 0 ≤ X^3 by positivity]
      _ ≤ _ := hnum
  have hatom : overlap H h h ≤ (1/50 : ℝ) := by
    have hw0 : 0 ≤ weight H h := tent_nonneg _
    have hw1 : weight H (h+h) ≤ 1 := tent_le_one _
    calc
      _ ≤ weight H h*1 := mul_le_mul_of_nonneg_left hw1 hw0
      _ = weight H h := mul_one _
      _ ≤ (1/50 : ℝ) := by
        rw [weight_left hHp hlo (by omega)]
        simp only [Nat.cast_add, Nat.cast_one]
        change ((z+1)/X)-1 ≤ _
        have hh : (z+1)/X ≤ 1+(1/50 : ℝ) := (div_le_iff₀ hXp).mpr (by nlinarith)
        linarith
  rw [discrepancy_one_spike hHp hlo hstrict]
  change (1/20 : ℝ) ≤ r*(r^2-1)/(6*X^2*D)-overlap H h h
  linarith

/-- The suggested O(1/H) boundary claim already fails at h=H. -/
theorem discrepancy_diagonal_scale {H : ℕ} (hH : 0 < H) :
    discrepancy H H (2*H+1) =
      ((H : ℝ)^2-1)/(6*(H : ℝ)*(2*(H : ℝ)+1))-
        ((H : ℝ)-1)/(H : ℝ)^2 := by
  rw [discrepancy_one_spike hH le_rfl (by omega)]
  have ho := overlap_atom hH le_rfl (by omega) (k := 0) (by omega)
  simp only [Nat.add_zero] at ho
  rw [ho, show 2*H-H = H by omega]
  push_cast
  have hp : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp [hp]

/-- The boundary is nonvanishing, despite exact zero mean and uniformly
bounded partial sums. -/
theorem tendsto_discrepancy_diagonal_scale :
    Tendsto (fun H : ℕ => discrepancy H H (2*H+1)) atTop (𝓝 (1/12 : ℝ)) := by
  have hi : Tendsto (fun H : ℕ => (H : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := (((tendsto_const_nhds (x := (1 : ℝ))).sub (hi.pow 2)).div
    ((tendsto_const_nhds (x := (6 : ℝ))).mul
      ((tendsto_const_nhds (x := (2 : ℝ))).add hi)) (by norm_num)).sub
        (hi.sub (hi.pow 2))
  norm_num at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
  rw [discrepancy_diagonal_scale hH]
  have hp : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hden : 2*(H : ℝ)+1 ≠ 0 := by positivity
  field_simp [hp, hden]

/-- No fixed O(1/H) allowance follows from these periodic inputs. -/
theorem not_eventually_discrepancy_one_div_H (C : ℝ) :
    ¬(∀ᶠ H : ℕ in atTop, |discrepancy H H (2*H+1)| ≤ C/(H : ℝ)) := by
  intro hbound
  have hl : Tendsto (fun H : ℕ => C/(H : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨H, hH, hb, hs⟩ :=
    ((eventually_ge_atTop (100 : ℕ)).and (hbound.and
      (hl.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/20))))).exists
  have hh := discrepancy_main_band_lower hH le_rfl (by omega)
  have ha := le_abs_self (discrepancy H H (2*H+1))
  linarith

end
end RiemannGaussian.SuzukiCarryPeriodicDiscrepancy
