import RiemannGaussian.NatProductCollision

/-!
# Quantitative energy of positive integer rectangles

Product collisions are counted before any inverse coefficient loses its
sign. Their gcd majorant has a complete common-divisor expansion. Exact
divided-cutoff sums give a product-of-lengths times squared-harmonic
bound for the entire rectangular multiplicative energy.
-/

open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A complete gcd row sum is bounded through all its common divisors,
with a squared harmonic cost for the whole positive interval. -/
theorem sum_Icc_gcd_div_le_harmonic_sq (E : ℕ) :
    (∑ a ∈ Finset.Icc 1 E, ∑ c ∈ Finset.Icc 1 E,
      (Nat.gcd a c : ℝ) / a) ≤
      (E : ℝ) * (∑ g ∈ Finset.Icc 1 E, 1 / (g : ℝ)) ^ 2 := by
  let s := Finset.Icc 1 E
  let w : ℕ → ℕ → ℝ := fun g a ↦ if g ∣ a then 1 / (a : ℝ) else 0
  let v : ℕ → ℕ → ℝ := fun g c ↦ if g ∣ c then 1 else 0
  have hw (g a : ℕ) : 0 ≤ w g a := by dsimp [w]; split_ifs <;> positivity
  have hv (g c : ℕ) : 0 ≤ v g c := by dsimp [v]; split_ifs <;> positivity
  calc
    _ ≤ ∑ a ∈ s, ∑ c ∈ s, ∑ g ∈ s, (g : ℝ) * w g a * v g c := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro c hc
      have hap : 0 < a := (Finset.mem_Icc.mp ha).1
      have hgp : 0 < Nat.gcd a c := Nat.gcd_pos_of_pos_left c hap
      have hgm : Nat.gcd a c ∈ s := Finset.mem_Icc.mpr
        ⟨hgp, (Nat.le_of_dvd hap (Nat.gcd_dvd_left a c)).trans (Finset.mem_Icc.mp ha).2⟩
      have h := Finset.single_le_sum (f := fun g : ℕ ↦ (g : ℝ) * w g a * v g c)
        (fun g _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg g) (hw g a)) (hv g c)) hgm
      simpa only [w, v, if_pos (Nat.gcd_dvd_left a c), if_pos (Nat.gcd_dvd_right a c),
        mul_one, div_eq_mul_inv, one_mul] using h
    _ = ∑ a ∈ s, ∑ g ∈ s, ∑ c ∈ s, (g : ℝ) * w g a * v g c := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ g ∈ s, ∑ a ∈ s, ∑ c ∈ s, (g : ℝ) * w g a * v g c := Finset.sum_comm
    _ = ∑ g ∈ s, (g : ℝ) * (∑ a ∈ s, w g a) * ∑ c ∈ s, v g c := by
      apply Finset.sum_congr rfl
      intro g hg
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = ∑ g ∈ Finset.Icc 1 E, (E / g : ℕ) *
        ∑ a ∈ Finset.Icc 1 (E / g), 1 / (a : ℝ) := by
      apply Finset.sum_congr rfl
      intro g hg
      have hgp : 0 < g := (Finset.mem_Icc.mp hg).1
      have hgr : (0 : ℝ) < g := by exact_mod_cast hgp
      have hvsum : (∑ c ∈ s, v g c) = (E / g : ℕ) := by
        dsimp [s, v]
        rw [sum_Icc_dvd_eq hgp E (fun _ ↦ (1 : ℝ))]
        simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
      rw [hvsum]
      dsimp [s, w]
      rw [sum_Icc_dvd_inv_eq hgp E]
      field_simp
    _ ≤ ∑ g ∈ Finset.Icc 1 E, ((E : ℝ) / g) *
        ∑ a ∈ Finset.Icc 1 E, 1 / (a : ℝ) := by
      apply Finset.sum_le_sum
      intro g hg
      have hgr : (0 : ℝ) < g := by exact_mod_cast (Finset.mem_Icc.mp hg).1
      have hq : ((E / g : ℕ) : ℝ) ≤ (E : ℝ) / g := by
        apply (le_div_iff₀ hgr).mpr
        exact_mod_cast Nat.div_mul_le_self E g
      apply mul_le_mul hq _ (Finset.sum_nonneg (fun a _ ↦ by positivity)) (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc le_rfl (Nat.div_le_self E g)) (fun a _ _ ↦ by positivity)
    _ = _ := by
      rw [← Finset.sum_mul]
      simp only [div_eq_mul_inv, ← Finset.mul_sum]
      ring

/-- The rectangular multiplicative energy retains the exact product
collision fiber for every pair of outer factors. -/
theorem mulEnergy_Icc_eq_sum_collision (E D : ℕ) :
    Finset.mulEnergy (Finset.Icc 1 E) (Finset.Icc 1 D) =
      ∑ a ∈ Finset.Icc 1 E, ∑ c ∈ Finset.Icc 1 E,
        (((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)).filter
          (fun p : ℕ × ℕ ↦ a * p.1 = c * p.2)).card := by
  simp only [Finset.mulEnergy, Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]

/-- The complete positive integer rectangle has multiplicative energy
at most its area times the squared harmonic outer-range cost. -/
theorem mulEnergy_Icc_le_harmonic_sq (E D : ℕ) :
    (Finset.mulEnergy (Finset.Icc 1 E) (Finset.Icc 1 D) : ℝ) ≤
      (E : ℝ) * D * (∑ g ∈ Finset.Icc 1 E, 1 / (g : ℝ)) ^ 2 := by
  rw [mulEnergy_Icc_eq_sum_collision]
  push_cast
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 E, ∑ c ∈ Finset.Icc 1 E, (D : ℝ) * Nat.gcd a c / a := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro c hc
      exact card_Icc_product_collision_le_gcd (Finset.mem_Icc.mp ha).1 D
    _ = (D : ℝ) * ∑ a ∈ Finset.Icc 1 E, ∑ c ∈ Finset.Icc 1 E, (Nat.gcd a c : ℝ) / a := by
      simp only [mul_div_assoc, Finset.mul_sum]
    _ ≤ (D : ℝ) * ((E : ℝ) * (∑ g ∈ Finset.Icc 1 E, 1 / (g : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_Icc_gcd_div_le_harmonic_sq E) (Nat.cast_nonneg D)
    _ = _ := by ring

/-- The full rectangular collision count has an explicit logarithmic
bound, independent of any signs later assigned to its product fibers. -/
theorem mulEnergy_Icc_le_log_sq {E : ℕ} (hE : 1 ≤ E) (D : ℕ) :
    (Finset.mulEnergy (Finset.Icc 1 E) (Finset.Icc 1 D) : ℝ) ≤
      (E : ℝ) * D * (1 + Real.log E) ^ 2 := by
  apply (mulEnergy_Icc_le_harmonic_sq E D).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h : (∑ g ∈ Finset.Icc 1 E, 1 / (g : ℝ)) ≤ 1 + Real.log E := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
      using harmonic_le_one_add_log E
  exact (sq_le_sq₀ (Finset.sum_nonneg (fun g _ ↦ by positivity))
    (by have hER : (1 : ℝ) ≤ E := by exact_mod_cast hE
        linarith [Real.log_nonneg hER])).mpr h

end

end RiemannGaussian
