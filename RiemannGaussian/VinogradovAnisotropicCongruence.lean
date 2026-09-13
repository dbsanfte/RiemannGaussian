/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovPrimePowerRigidity
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Different prime-power precisions in the complete moment system

Each coordinate may retain its own modulus. Counting its possible refinements
and then applying the nonsingular full-fibre bound pays their complete product
cost. The correlated-target theorem remains available upstream of this product.
-/

namespace RiemannGaussian.VinogradovAnisotropicCongruence
noncomputable section
open scoped BigOperators
open VinogradovPrimePowerRigidity

/-- The canonical representatives in a fixed residue class have at most
one entry per quotient. This includes empty target classes. -/
theorem residue_class_card_le {N d q : ℕ} [NeZero N] (hd : 0 < d)
    (hN : N = d * q) (a : ℕ) :
    (Finset.univ.filter (fun x : ZMod N => x.val % d = a)).card ≤ q := by
  classical
  let S := Finset.univ.filter (fun x : ZMod N => x.val % d = a)
  have hinj : Set.InjOn (fun x : ZMod N => x.val / d) (S : Set (ZMod N)) := by
    intro x hx y hy hxy
    apply ZMod.val_injective N
    have hrx := (Finset.mem_filter.mp hx).2
    have hry := (Finset.mem_filter.mp hy).2
    change x.val / d = y.val / d at hxy
    have hx' := Nat.mod_add_div x.val d
    have hy' := Nat.mod_add_div y.val d
    rw [hrx, hxy] at hx'
    rw [hry] at hy'
    omega
  have hsub : S.image (fun x : ZMod N => x.val / d) ⊆ Finset.range q := by
    intro b hb
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hb
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    simpa only [hN, mul_comm d q] using x.val_lt
  calc
    S.card = (S.image (fun x : ZMod N => x.val / d)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range q).card := Finset.card_le_card hsub
    _ = q := Finset.card_range q

/-- Refining one coordinate from precision e to n costs at most p^(n-e). -/
theorem prime_power_class_card_le {p n e : ℕ} [Fact p.Prime]
    (he : e ≤ n) (a : ℕ) :
    (Finset.univ.filter (fun x : ZMod (p ^ n) => x.val % p ^ e = a)).card ≤
      p ^ (n - e) := by
  have hp := (Fact.out : p.Prime).pos
  have : NeZero (p ^ n) := ⟨ne_of_gt (pow_pos hp n)⟩
  apply residue_class_card_le (pow_pos hp e)
  rw [← pow_add, Nat.add_sub_of_le he]

/-- All retained power-sum congruences can have different precisions.
The complete nonsingular solution count pays each refinement exactly once. -/
theorem nonsingular_anisotropic_card_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (e : Fin k → ℕ) (he : ∀ i, e i ≤ n) (a : Fin k → ℕ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (residuePowerSums u i).val % p ^ e i = a i)).card ≤
      p ^ (∑ i, (n - e i)) * k.factorial := by
  classical
  let T (i : Fin k) := Finset.univ.filter (fun x : ZMod (p ^ n) => x.val % p ^ e i = a i)
  have hb := nonsingular_coordinate_preimage_le hkp T
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hb
  apply hb.trans
  apply Nat.mul_le_mul_right
  calc
    (∏ i, (T i).card) ≤ ∏ i, p ^ (n - e i) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i hi
      exact prime_power_class_card_le (p := p) (he i) (a i)
    _ = p ^ (∑ i, (n - e i)) := Finset.prod_pow_eq_pow_sum _ _ _

/-- The modular vector is exactly the reduction of the literal integer
monomial sums, not an independently chosen set of frequencies. -/
theorem residuePowerSums_val {k N : ℕ} (u : Fin k → Fin N) (i : Fin k) :
    (residuePowerSums u i).val = (∑ j, (u j).val ^ (i.val + 1)) % N := by
  have he : residuePowerSums u i = ((∑ j, (u j).val ^ (i.val + 1) : ℕ) : ZMod N) := by
    simp only [residuePowerSums, Nat.cast_sum, Nat.cast_pow]
  rw [he, ZMod.val_natCast]

/-- The anisotropic estimate applies to the actual natural power sums
with each equation reduced modulo its own prime power. -/
theorem actual_anisotropic_card_le {p k n : ℕ} [Fact p.Prime]
    (hkp : k < p) (e : Fin k → ℕ) (he : ∀ i, e i ≤ n) (a : Fin k → ℕ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ n) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (∑ j, (u j).val ^ (i.val + 1)) % p ^ e i = a i)).card ≤
      p ^ (∑ i, (n - e i)) * k.factorial := by
  have hb := nonsingular_anisotropic_card_le hkp e he a
  simp only [residuePowerSums_val] at hb
  simpa only [Nat.mod_mod_of_dvd _ (pow_dvd_pow p (he _))] using hb

/-- The degree-by-degree modulus pattern pays the triangular number of
refinement digits, rather than a uniform full precision for every equation. -/
theorem degree_precision_cost (k b : ℕ) :
    (∑ i : Fin k, (k * b - (i.val + 1) * b)) = b * (k * (k - 1) / 2) := by
  simp_rw [← Nat.sub_mul]
  rw [← Finset.sum_mul]
  have he : (∑ i : Fin k, (k - (i.val + 1))) = k * (k - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => k - (i + 1)) k]
    simp_rw [Nat.add_comm _ 1, Nat.sub_add_eq]
    rw [Finset.sum_range_reflect (fun i => i) k, Finset.sum_range_id]
  rw [he, mul_comm]

/-- At moduli p^b,p^(2b),...,p^(kb), at most
k!*p^(b*k*(k-1)/2) nonsingular ordered residue tuples realize any target.
The count is uniform in p, b, k and the full target vector. -/
theorem degree_moduli_card_le {p k b : ℕ} [Fact p.Prime] (hkp : k < p)
    (a : Fin k → ℕ) :
    (Finset.univ.filter (fun u : Fin k → Fin (p ^ (k * b)) =>
      Function.Injective (fun j => ((u j).val : ZMod p)) ∧
      ∀ i, (∑ j, (u j).val ^ (i.val + 1)) % p ^ ((i.val + 1) * b) = a i)).card ≤
      p ^ (b * (k * (k - 1) / 2)) * k.factorial := by
  simpa only [degree_precision_cost] using
    actual_anisotropic_card_le hkp (fun i => (i.val + 1) * b)
      (fun i => Nat.mul_le_mul_right b (by omega : i.val + 1 ≤ k)) a

end
end RiemannGaussian.VinogradovAnisotropicCongruence
