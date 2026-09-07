import RiemannGaussian.EtaDivisorGcdBound
import Mathlib.Combinatorics.Additive.Energy

/-!
# Counting actual collisions of two positive integer products

The two factors in a rectangular divisor convolution are kept distinct.
For fixed positive outer factors, every product collision forces the
second inner factor to be divisible by the corresponding reduced outer
factor. This gives a quantitative collision count before any coefficient
or Fourier estimate is applied.
-/

open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- Summing supported multiples retains the exact divided cutoff. -/
theorem sum_Icc_dvd_eq {α : Type*} [AddCommMonoid α] {g : ℕ}
    (hg : 0 < g) (D : ℕ) (f : ℕ → α) :
    (∑ d ∈ Finset.Icc 1 D, if g ∣ d then f d else 0) =
      ∑ a ∈ Finset.Icc 1 (D / g), f (g * a) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun a _ ↦ g * a)
  · intro a ha
    obtain ⟨ha1, haD⟩ := Finset.mem_Icc.mp ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨by nlinarith, (Nat.mul_le_mul_left g haD).trans (Nat.mul_div_le D g)⟩,
      dvd_mul_right g a⟩
  · intro a ha b hb heq
    exact Nat.eq_of_mul_eq_mul_left hg heq
  · intro d hd
    obtain ⟨hdD, hgd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hdD
    refine ⟨d / g, Finset.mem_Icc.mpr ?_, Nat.mul_div_cancel' hgd⟩
    exact ⟨(Nat.one_le_div_iff hg).mpr (Nat.le_of_dvd hd1 hgd),
      Nat.div_le_div_right hdD⟩
  · intro a ha
    rfl

/-- The number of positive multiples is the literal integer quotient. -/
theorem card_Icc_dvd_eq {g : ℕ} (hg : 0 < g) (D : ℕ) :
    ((Finset.Icc 1 D).filter (fun d ↦ g ∣ d)).card = D / g := by
  have h := sum_Icc_dvd_eq hg D (fun _ ↦ (1 : ℕ))
  simpa only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
    Nat.card_Icc, Nat.add_sub_cancel] using h

/-- An exact product collision forces divisibility by the reduced
outer factor, after cancellation of the genuine positive gcd. -/
theorem div_gcd_dvd_of_mul_eq_mul {a c b d : ℕ} (ha : 0 < a)
    (h : a * b = c * d) : a / Nat.gcd a c ∣ d := by
  let g := Nat.gcd a c
  have hg : 0 < g := Nat.gcd_pos_of_pos_left c ha
  have hred : (a / g) * b = (c / g) * d := by
    apply Nat.eq_of_mul_eq_mul_left hg
    calc
      g * (a / g * b) = a * b := by rw [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_left a c)]
      _ = c * d := h
      _ = g * (c / g * d) := by rw [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right a c)]
  apply (Nat.coprime_div_gcd_div_gcd hg).dvd_of_dvd_mul_left
  rw [← hred]
  exact dvd_mul_right _ _

/-- At fixed outer factors, each admissible second inner factor
determines at most one first inner factor. The gcd divisibility bound
therefore controls the entire product-collision fiber. -/
theorem card_Icc_product_collision_le_div {a c : ℕ} (ha : 0 < a) (D : ℕ) :
    (((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)).filter
      (fun p : ℕ × ℕ ↦ a * p.1 = c * p.2)).card ≤ D / (a / Nat.gcd a c) := by
  rw [← card_Icc_dvd_eq (Nat.div_gcd_pos_of_pos_left c ha) D]
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ ↦ p.2)
  · intro p hp
    obtain ⟨hpD, heq⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hpD).2,
      div_gcd_dvd_of_mul_eq_mul ha heq⟩
  · intro p hp q hq heq
    apply Prod.ext _ heq
    apply Nat.eq_of_mul_eq_mul_left ha
    calc
      a * p.1 = c * p.2 := (Finset.mem_filter.mp hp).2
      _ = c * q.2 := congrArg (fun n ↦ c * n) heq
      _ = a * q.1 := (Finset.mem_filter.mp hq).2.symm

/-- The full collision fiber has an explicit real gcd majorant,
with both original outer factors retained. -/
theorem card_Icc_product_collision_le_gcd {a c : ℕ} (ha : 0 < a) (D : ℕ) :
    ((((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)).filter
      (fun p : ℕ × ℕ ↦ a * p.1 = c * p.2)).card : ℝ) ≤
      (D : ℝ) * Nat.gcd a c / a := by
  let g := Nat.gcd a c
  have hg : 0 < g := Nat.gcd_pos_of_pos_left c ha
  have hq : 0 < a / g := Nat.div_gcd_pos_of_pos_left c ha
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hqR : (0 : ℝ) < (a / g : ℕ) := by exact_mod_cast hq
  calc
    _ ≤ ((D / (a / g) : ℕ) : ℝ) := by exact_mod_cast card_Icc_product_collision_le_div ha D
    _ ≤ (D : ℝ) / (a / g : ℕ) := by
      apply (le_div_iff₀ hqR).mpr
      exact_mod_cast Nat.div_mul_le_self D (a / g)
    _ = _ := by
      change (D : ℝ) / (a / g : ℕ) = (D : ℝ) * g / a
      rw [show (a : ℝ) = (g : ℝ) * (a / g : ℕ) by
        exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left a c)).symm]
      field_simp

end

end RiemannGaussian
