/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceScoreState

/-! # Scheduled integer score after cancellation of shared rational factors
The finite-count producer is joined separately. These identities eliminate the
common offset and all score denominators from candidate comparison, preserving
equality and thus the original deterministic tie rule.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeSourceScoreCancellation

/-- Integer weight of normalized incidence/head counts at the original schedule. -/
def weight (M n lam U I H : ℕ) : ℕ := n^2*lam^2*U^2*I+4*M^2*H

/-- The scheduled score expressed through actual normalized count lanes. -/
def score (M n r lam U I H : ℕ) (offset : ℚ) : ℚ :=
  (((n:ℚ)/(2*(r:ℚ)))^2*(I:ℚ)+
    ((M:ℚ)/((r:ℚ)*(lam:ℚ)*(U:ℚ)))^2*(H:ℚ))/(U:ℚ)^2-offset

/-- Positive factor shared by every candidate in the same scheduled search. -/
def factor (r lam U : ℕ) : ℕ := 4*r^2*lam^2*U^4

/-- Exact denominator clearing; no positivity of M,n or either count is needed. -/
theorem clear_denominators (M n r lam U I H : ℕ) (offset : ℚ)
    (hr : 0 < r) (hlam : 0 < lam) (hU : 0 < U) :
    (factor r lam U:ℚ)*(score M n r lam U I H offset+offset)=(weight M n lam U I H:ℚ) := by
  have hr' : (r:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hr
  have hl' : (lam:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hlam
  have hU' : (U:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hU
  unfold factor score weight
  push_cast
  field_simp
  ring

/-- The common denominator multiplier is positive for actual scheduled data. -/
theorem factor_pos (r lam U : ℕ) (hr : 0 < r) (hlam : 0 < lam) (hU : 0 < U) :
    0 < factor r lam U := by unfold factor;positivity

/-- Integer order is exactly original score order, including equality/ties. -/
theorem weight_le_iff (M n r lam U I H I' H' : ℕ) (offset : ℚ)
    (hr : 0 < r) (hlam : 0 < lam) (hU : 0 < U) :
    weight M n lam U I H ≤ weight M n lam U I' H' ↔
      score M n r lam U I H offset ≤ score M n r lam U I' H' offset := by
  have hpos : (0:ℚ) < factor r lam U := by exact_mod_cast factor_pos r lam U hr hlam hU
  have h₁ := clear_denominators M n r lam U I H offset hr hlam hU
  have h₂ := clear_denominators M n r lam U I' H' offset hr hlam hU
  have hcast : weight M n lam U I H ≤ weight M n lam U I' H' ↔
      (weight M n lam U I H:ℚ) ≤ (weight M n lam U I' H':ℚ) := by exact_mod_cast Iff.rfl
  rw [hcast,← h₁,← h₂,mul_le_mul_iff_right₀ hpos]
  exact add_le_add_iff_right offset

/-- The universal-bank square is the support-four common averaging denominator. -/
theorem bank_square (r Q : ℕ) : (r^(2*Q))^2=(r^Q)^4 := by
  rw [← pow_mul,← pow_mul]
  congr 1
  omega

/-- Actual scheduled x agrees with the form used in the original source caller. -/
theorem scheduled_x (M r lam U : ℕ) :
    (1/((r*lam:ℕ):ℚ))*(M:ℚ)/(U:ℚ)=(M:ℚ)/((r:ℚ)*(lam:ℚ)*(U:ℚ)) := by
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
  ring

/-- Original count caps bound the actual integer weight before any bit encoding. -/
theorem weight_bound (M n lam U I H T : ℕ) (hI : I ≤ T*U^2) (hH : H ≤ T*U^2) :
    weight M n lam U I H ≤ T*U^2*(n^2*lam^2*U^2+4*M^2) := by
  unfold weight
  calc
    _ ≤ n^2*lam^2*U^2*(T*U^2)+4*M^2*(T*U^2) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hI) (Nat.mul_le_mul_left _ hH)
    _ = _ := by ring

/-- Fixed polynomial original-resource cap, without binary-magnitude substitution. -/
theorem weight_resource_bound (M n lam U I H T S : ℕ)
    (hM : M ≤ S) (hn : n ≤ S) (hl : lam ≤ S) (hU : U ≤ S) (hT : T ≤ S)
    (hI : I ≤ T*U^2) (hH : H ≤ T*U^2) :
    weight M n lam U I H ≤ S^9+4*S^5 := by
  apply (weight_bound M n lam U I H T hI hH).trans
  calc
    _ ≤ S*S^2*(S^2*S^2*S^2+4*S^2) := by gcongr
    _ = _ := by ring

end RiemannGaussian.SemiprimeSourceScoreCancellation
