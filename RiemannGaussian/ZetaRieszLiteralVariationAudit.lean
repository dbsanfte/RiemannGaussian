/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCofactorDiscrepancy

/-!
# Cost of the literal squarefree mask in absolute Abel variation

The canonical cofactor weight is zero on every multiple of four. Its
absolute adjacent variation therefore cannot behave like the variation
of a smooth radial weight. This audits the existing error majorant; it
does not lower-bound the actual signed comparison error.
-/

noncomputable section
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszLiteralVariationAudit
open Real ZetaRieszJointPrimeEnergy

/-- One of the next four values is zero, so three adjacent differences
already dominate the value at the start. -/
theorem local_variation (w : ℕ → ℝ) (hfour : ∀ n, 4 ∣ n → w n = 0) (n : ℕ) :
    |w n| ≤ ∑ j ∈ Finset.range 3, |w (n+j)-w (n+j+1)| := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.add_zero]
  have h0 := abs_nonneg (w n-w (n+1))
  have h1 := abs_nonneg (w (n+1)-w (n+2))
  have h2 := abs_nonneg (w (n+2)-w (n+3))
  have hn : n % 4 < 4 := Nat.mod_lt _ (by decide)
  rcases (show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega) with h|h|h|h
  · rw [hfour n (Nat.dvd_iff_mod_eq_zero.mpr h), abs_zero]
    positivity
  · have he := hfour (n+3) (Nat.dvd_iff_mod_eq_zero.mpr (by omega))
    have h := (abs_sub_le (w n) (w (n+1)) (w (n+3))).trans
      (add_le_add le_rfl (abs_sub_le (w (n+1)) (w (n+2)) (w (n+3))))
    simpa only [he, sub_zero, Nat.add_assoc, add_assoc] using h
  · have he := hfour (n+2) (Nat.dvd_iff_mod_eq_zero.mpr (by omega))
    have h := abs_sub_le (w n) (w (n+1)) (w (n+2))
    rw [he, sub_zero] at h
    rw [he]
    simp only [sub_zero, zero_sub, abs_neg] at h ⊢
    simpa only [Nat.add_assoc] using (le_trans h
      (le_add_of_nonneg_right (abs_nonneg (w (n+3)))))
  · have he := hfour (n+1) (Nat.dvd_iff_mod_eq_zero.mpr (by omega))
    simp only [he, sub_zero, zero_sub, abs_neg, Nat.add_assoc] at h0 h1 h2 ⊢
    linarith

/-- The exact weighted Abel variation dominates a third of the
weighted absolute mass. The terminal jump is included. -/
theorem weighted_variation_lower (X : ℕ) (w : ℕ → ℝ)
    (hfour : ∀ n, 4 ∣ n → w n = 0) (hout : ∀ n, X < n → w n = 0) :
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ)*|w n|) ≤
      3 * ∑ n ∈ Finset.Icc 1 X, (n : ℝ)*|w n-w (n+1)| := by
  let v (n : ℕ) := (n : ℝ)*|w n-w (n+1)|
  have hv n : 0 ≤ v n := by dsimp [v]; positivity
  have hshift (j : ℕ) :
      (∑ n ∈ Finset.Icc 1 X, v (n+j)) ≤ ∑ n ∈ Finset.Icc 1 X, v n := by
    have he : (∑ n ∈ Finset.Icc 1 X, v (n+j)) =
        ∑ n ∈ (Finset.Icc 1 X).image (fun n => n+j), v n := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      dsimp at hab
      omega
    rw [he]
    have hs : (Finset.Icc 1 X).image (fun n => n+j) ⊆ Finset.Icc 1 (X+j) := by
      rintro n hn
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
      have ha := Finset.mem_Icc.mp ha
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    have hlarge : (∑ n ∈ Finset.Icc 1 (X+j), v n) = ∑ n ∈ Finset.Icc 1 X, v n := by
      symm
      apply Finset.sum_subset
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,by have := (Finset.mem_Icc.mp hn).2; omega⟩
      · intro n hn hnot
        have hnX : X < n := by have := Finset.mem_Icc.mp hn; simp only [Finset.mem_Icc, not_and] at hnot; omega
        simp [v,hout n hnX,hout (n+1) (by omega)]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => hv n)).trans_eq hlarge
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 X, ∑ j ∈ Finset.range 3, v (n+j) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        _ ≤ (n : ℝ)*(∑ j ∈ Finset.range 3, |w (n+j)-w (n+j+1)|) :=
          mul_le_mul_of_nonneg_left (local_variation w hfour n) (Nat.cast_nonneg _)
        _ ≤ _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right n j) (abs_nonneg _)
    _ = ∑ j ∈ Finset.range 3, ∑ n ∈ Finset.Icc 1 X, v (n+j) := Finset.sum_comm
    _ ≤ ∑ _j ∈ Finset.range 3, ∑ n ∈ Finset.Icc 1 X, v n :=
      Finset.sum_le_sum (fun j _ => hshift j)
    _ = _ := by simp [v]

/-- A cofactor lower threshold makes the lost factor explicit, without
any assumption on the cosine phase or the nonzero weights. -/
theorem support_variation_lower (X : ℕ) (w : ℕ → ℝ) (M : ℝ)
    (hfour : ∀ n, 4 ∣ n → w n = 0) (hout : ∀ n, X < n → w n = 0)
    (hM : ∀ n ∈ Finset.Icc 1 X, w n ≠ 0 → M ≤ n) :
    M * (∑ n ∈ Finset.Icc 1 X, |w n|) ≤
      3 * ∑ n ∈ Finset.Icc 1 X, (n : ℝ)*|w n-w (n+1)| := by
  apply le_trans _ (weighted_variation_lower X w hfour hout)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hw : w n=0
  · simp [hw]
  exact mul_le_mul_of_nonneg_right (hM n hn hw) (abs_nonneg _)

/-- The existing short-cutoff Abel allowance loses exponentially relative
to the absolute weight mass on the literal zero extension. This is a
lower bound on that MAJORANT, not on the signed comparison error. -/
theorem exponential_allowance_lower (X N : ℕ) (w : ℕ → ℝ) (b : ℝ)
    (hfour : ∀ n, 4 ∣ n → w n = 0) (hout : ∀ n, X < n → w n = 0)
    (hM : ∀ n ∈ Finset.Icc 1 X, w n ≠ 0 → exp (b*N) ≤ n) :
    (exp (15*(b*N)/16)/3) * (∑ n ∈ Finset.Icc 1 X, |w n|) ≤
      exp (-(b*N)/16) *
        ∑ n ∈ Finset.Icc 1 X, (n : ℝ)*|w n-w (n+1)| := by
  have h := mul_le_mul_of_nonneg_left
    (support_variation_lower X w (exp (b*N)) hfour hout hM)
    (show 0 ≤ exp (-(b*N)/16)/3 by positivity)
  have he : exp (-(b*N)/16)*exp (b*N)=exp (15*(b*N)/16) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    _ = (exp (-(b*N)/16)/3)*
        (exp (b*N)*(∑ n ∈ Finset.Icc 1 X, |w n|)) := by rw [← he]; ring
    _ ≤ _ := by
      calc
        _ ≤ (exp (-(b*N)/16)/3)*
          (3 * ∑ n ∈ Finset.Icc 1 X, (n : ℝ)*|w n-w (n+1)|) := h
        _ = _ := by ring

private theorem row_mem_cofactors {B : Finset ℕ} {n p : ℕ}
    (hp : p ∈ ownerRows B n) : n ∈ cofactors B := by
  obtain ⟨m,hm,_⟩ := Finset.mem_image.mp hp
  obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_image.mpr ⟨m,hm,he⟩

/-- Every multiple of four has exactly zero canonical literal weight,
regardless of its height, order, allocation, or other original masks. -/
theorem literal_weight_zero_four (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (L y scale : ℝ) (N p n : ℕ) (hfour : 4 ∣ n) :
    maskedWeight A (ownerRows B) L y scale N n p = 0 := by
  have hp : p ∉ ownerRows B n := by
    intro hp
    have hsf := (cofactors_data B hB (row_mem_cofactors hp)).1
    exact (Nat.squarefree_iff_prime_squarefree.mp hsf 2 Nat.prime_two) hfour
  simp [maskedWeight,hp]

private theorem literal_weight_outside (A B : Finset ℕ)
    (L y scale : ℝ) (N p n : ℕ) (hn : (cofactors B).sup id < n) :
    maskedWeight A (ownerRows B) L y scale N n p = 0 := by
  have hp : p ∉ ownerRows B n := by
    intro hp
    exact (not_le_of_gt hn) (Finset.le_sup (f := id) (row_mem_cofactors hp))
  simp [maskedWeight,hp]

/-- The exact original cofactor-column weights obey the variation
obstruction. No enlarged population or changed extension is substituted. -/
theorem literal_variation_lower (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (L y scale : ℝ) (N p : ℕ) :
    let X := (cofactors B).sup id
    let w := fun n => maskedWeight A (ownerRows B) L y scale N n p
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ)*|w n|) ≤
      3 * ∑ n ∈ Finset.Icc 1 X, (n : ℝ)*|w n-w (n+1)| :=
  weighted_variation_lower _ _ (literal_weight_zero_four A B hB L y scale N p)
    (literal_weight_outside A B L y scale N p)

/-- At the previously advertised cofactor threshold exp(N/2), the Abel
allowance is at least exp(15N/32)/3 times the whole absolute column mass.
This precludes interpreting its exp(-N/32) prefactor as a net saving on
the canonical masked weights. It does not preclude a joint signed proof. -/
theorem literal_short_allowance_lower (A B : Finset ℕ)
    (hB : ∀ m ∈ B, Squarefree m ∧ 3 ≤ m.primeFactors.card)
    (L y scale : ℝ) (N p : ℕ)
    (hlower : ∀ n ∈ Finset.Icc 1 ((cofactors B).sup id),
      maskedWeight A (ownerRows B) L y scale N n p ≠ 0 → exp ((N : ℝ)/2) ≤ n) :
    let X := (cofactors B).sup id
    let w := fun n => maskedWeight A (ownerRows B) L y scale N n p
    (exp (15*(N : ℝ)/32)/3) * (∑ n ∈ Finset.Icc 1 X, |w n|) ≤
      exp (-(N : ℝ)/32) *
        ∑ n ∈ Finset.Icc 1 X, (n : ℝ)*|w n-w (n+1)| := by
  have h := exponential_allowance_lower ((cofactors B).sup id) N
    (fun n => maskedWeight A (ownerRows B) L y scale N n p) (1/2)
    (literal_weight_zero_four A B hB L y scale N p)
    (literal_weight_outside A B L y scale N p)
    (by simpa only [one_div_mul_eq_div] using hlower)
  rw [show (15*((1/2 : ℝ)*N)/16)=15*N/32 by ring,
    show (-((1/2 : ℝ)*N)/16)=-(N : ℝ)/32 by ring] at h
  exact h

end RiemannGaussian.ZetaRieszLiteralVariationAudit
