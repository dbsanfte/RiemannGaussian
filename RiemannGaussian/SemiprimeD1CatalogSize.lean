/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ModeRate
import RiemannGaussian.SemiprimeD1PackingReady

/-! # Actual catalogue size and packet coefficient-recursion exponent
The full acquired catalogue has polynomial dimension after the packet/precision
scale cancellation. The literal schedule then absorbs the naive exponential
single-coefficient recursion inside the existing global degree envelope.
This is a resource inequality, not a claim of a full bit-machine controller.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1CatalogSize
open SemiprimeD1ModeRate SemiprimeD1ModeCatalog

/-- The actual catalogue length, times u, is bounded independently of tile scale. -/
theorem catalog_scaled (packets M u a i p : ℕ) (hi : i ≤ a)
    (hpackets : packets*2^a ≤ 3*M) (hu : u ≤ M)
    (hp : p*u ≤ M*2^(a-i)) (ha : (a+1)*u ≤ 2^(a-i)) :
    (catalog (packets*2^(i+1)) (modeBudget M u a i p)).length*u ≤ 246*M^2 := by
  have hslot : packets*2^(i+1) ≤ 6*M/2^(a-i) := by
    apply (Nat.le_div_iff_mul_le (show 0 < (2:ℕ)^(a-i) by positivity)).mpr
    calc
      _ = packets*(2*2^a) := by rw [Nat.mul_assoc,dyadic_tiles a i hi]
      _ ≤ 6*M := by nlinarith
  rw [catalog_length]
  have h := multiplicity_budget_scaled_le M u a i p hu hp ha
  calc
    _ ≤ (modeBudget M u a i p*(6*M/2^(a-i)))*u :=
      Nat.mul_le_mul_right u (Nat.mul_le_mul_left _ hslot)
    _ = ((6*M/2^(a-i))*modeBudget M u a i p)*u := by ring
    _ ≤ 246*M^2 := h

/-- A positive actual level gives a fixed quadratic bound for the FULL catalogue. -/
theorem catalog_quadratic (packets M u a i p : ℕ) (hi : i ≤ a)
    (hpackets : packets*2^a ≤ 3*M) (hu0 : 0 < u) (hu : u ≤ M)
    (hp : p*u ≤ M*2^(a-i)) (ha : (a+1)*u ≤ 2^(a-i)) :
    (catalog (packets*2^(i+1)) (modeBudget M u a i p)).length ≤ 246*M^2 := by
  have h := catalog_scaled packets M u a i p hi hpackets hu hp ha
  have hc := Nat.mul_le_mul_left
    (catalog (packets*2^(i+1)) (modeBudget M u a i p)).length (show 1 ≤ u by omega)
  omega

/-- One twentieth of the actual logarithm pays a complete linear logarithmic factor. -/
theorem logarithm_linear (lam : ℕ) (hlam : 1000 ≤ lam) : lam+1 ≤ 2^(lam/20) := by
  have h := SemiprimeD1PackingReady.linear_le_pow (lam/20) (by omega)
  have hm := Nat.mod_lt lam (by decide : 0 < 20)
  have he := Nat.mod_add_div lam 20
  omega

/-- A full quadratic-sized catalogue has a literal binary-logarithmic upper bound. -/
theorem quadratic_binary (s lam K : ℕ) (hs : s ≤ 2^lam) (hK : K ≤ 246*s^2) :
    K+1 ≤ 2^(2*lam+8) := by
  have hp := Nat.pow_le_pow_left hs 2
  have hsquared : s^2 ≤ 2^(2*lam) := by
    simpa only [← pow_mul, Nat.mul_comm] using hp
  have hpos : 1 ≤ (2:ℕ)^(2*lam) := Nat.one_le_pow _ _ (by decide)
  rw [pow_add]
  norm_num only [show (2:ℕ)^8=256 by norm_num]
  nlinarith

/-- The actual packet's naive coefficient recursion, even with all assignments,
fits inside the SAME global degree exponential. Its row count is at most2L;
the literal tiny packet exponent is used, so no dynamic-programming shortcut is assumed. -/
theorem packet_coefficient_envelope (lam a K rows : ℕ) (hlam : 1000 ≤ lam)
    (ha : a ≤ 4*(lam/131072)) (hK : K+1 ≤ 2^(2*lam+8)) (hrows : rows ≤ 2*2^a) :
    2^rows*(K+1)^rows ≤ 2^(2^((9*lam+9)/10)) := by
  have hlog := logarithm_linear lam hlam
  have hlinear : 2*(2*lam+9) ≤ 8*2^(lam/20) := by nlinarith
  have hexponent : a+lam/20+3 ≤ (9*lam+9)/10 := by omega
  have hsmall : (2*lam+9)*rows ≤ 2^((9*lam+9)/10) := by
    calc
      _ ≤ (2*lam+9)*(2*2^a) := Nat.mul_le_mul_left _ hrows
      _ ≤ (8*2^(lam/20))*2^a := by nlinarith
      _ = 2^(a+lam/20+3) := by
        rw [show (8:ℕ)=2^3 by norm_num]
        simp only [← pow_add]
        congr 1
        omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hexponent
  calc
    _ ≤ 2^rows*(2^(2*lam+8))^rows :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hK rows)
    _ = 2^((2*lam+9)*rows) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hsmall

end RiemannGaussian.SemiprimeD1CatalogSize
