/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeFilterPoleCancellation

/-!
# Polynomial moment filters and the full double-pole jet

The Möbius convolution of the logarithmic prime series contains `-zeta'`,
whose pole has order two. Its factorial moments involve both the value
and the first derivative of the spectral polynomial. These identities
retain that full jet before applying an analytic estimate to the regular
part of the convolution.
-/

open Complex Filter Metric Set Topology
open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- A spectral polynomial acting on a complete complex moment sequence. -/
def zetaMomentSequenceFilter (p : Polynomial ℂ) (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  p.sum (fun k c ↦ c * a (N + k))

/-- Additivity keeps the signed coefficient channels intact. -/
theorem zetaMomentSequenceFilter_add (p q : Polynomial ℂ) (a : ℕ → ℂ) (N : ℕ) :
    zetaMomentSequenceFilter (p + q) a N = zetaMomentSequenceFilter p a N + zetaMomentSequenceFilter q a N :=
  Polynomial.sum_add_index _ _ _ (by intro k; simp) (by intro k b c; ring)

/-- A monomial selects one exact sequence coordinate. -/
theorem zetaMomentSequenceFilter_monomial (k : ℕ) (c : ℂ) (a : ℕ → ℂ) (N : ℕ) :
    zetaMomentSequenceFilter (Polynomial.monomial k c) a N = c * a (N + k) :=
  Polynomial.sum_monomial_index _ _ (by simp)

/-- Multiplication by the spectral variable shifts the entire sequence. -/
theorem zetaMomentSequenceFilter_X_mul (p : Polynomial ℂ) (a : ℕ → ℂ) (N : ℕ) :
    zetaMomentSequenceFilter (Polynomial.X * p) a N = zetaMomentSequenceFilter p a (N + 1) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, zetaMomentSequenceFilter_add, hp, hq]
  | monomial k c =>
    rw [Polynomial.X_mul_monomial, zetaMomentSequenceFilter_monomial, zetaMomentSequenceFilter_monomial]
    rw [show N + (k + 1) = N + 1 + k by omega]

/-- Scalar multiplication commutes with the exact sequence filter. -/
theorem zetaMomentSequenceFilter_C_mul (p : Polynomial ℂ) (c : ℂ) (a : ℕ → ℂ) (N : ℕ) :
    zetaMomentSequenceFilter (Polynomial.C c * p) a N = c * zetaMomentSequenceFilter p a N := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [mul_add, zetaMomentSequenceFilter_add, hp, hq]
  | monomial k b =>
    rw [Polynomial.C_mul_monomial, zetaMomentSequenceFilter_monomial, zetaMomentSequenceFilter_monomial]
    ring

/-- Subtraction remains a signed operation on the complete sequence. -/
theorem zetaMomentSequenceFilter_sub (p q : Polynomial ℂ) (a : ℕ → ℂ) (N : ℕ) :
    zetaMomentSequenceFilter (p - q) a N = zetaMomentSequenceFilter p a N - zetaMomentSequenceFilter q a N := by
  have h := zetaMomentSequenceFilter_add (p - q) q a N
  rw [sub_add_cancel] at h
  exact eq_sub_iff_add_eq.mpr h.symm

/-- The simple geometric mode depends only on the polynomial's value. -/
theorem zetaMomentSequenceFilter_geometric (p : Polynomial ℂ) (b : ℂ) (N : ℕ) :
    zetaMomentSequenceFilter p (fun n ↦ b ^ (n + 1)) N = b ^ (N + 1) * p.eval b := by
  rw [zetaMomentSequenceFilter, Polynomial.eval_eq_sum, Polynomial.sum, Polynomial.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [show N + k + 1 = (N + 1) + k by omega, pow_add]
  ring

/-- A double pole sees the complete first jet, not just the value of
the spectral polynomial. The identity includes the mode `b=0`. -/
theorem zetaMomentSequenceFilter_doublePole (p : Polynomial ℂ) (b : ℂ) (N : ℕ) :
    zetaMomentSequenceFilter p (fun n ↦ ((n + 1 : ℕ) : ℂ) * b ^ (n + 2)) N =
      b ^ (N + 2) * (((N + 1 : ℕ) : ℂ) * p.eval b + b * p.derivative.eval b) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [zetaMomentSequenceFilter_add, hp, hq, Polynomial.eval_add, Polynomial.derivative_add]
    ring
  | monomial k c =>
    rw [zetaMomentSequenceFilter_monomial, Polynomial.eval_monomial, Polynomial.derivative_monomial,
      Polynomial.eval_monomial]
    rcases k with _ | k
    · simp
      ring
    · simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
      rw [show N + (k + 1) + 2 = N + 2 + (k + 1) by omega, pow_add, pow_succ]
      ring

/-- Alternating factorial normalization converts differentiation into
an exact shifted moment, including its multiplicity factor. -/
theorem signedTaylorMoment_deriv (f : ℂ → ℂ) (n : ℕ) (s : ℂ) :
    signedTaylorMoment n (deriv f) s = -((n + 1 : ℕ) : ℂ) * signedTaylorMoment (n + 1) f s := by
  rw [signedTaylorMoment, signedTaylorMoment, iteratedDeriv_succ']
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
  field_simp

/-- The actual simple pole at one gives its exact geometric moment. -/
theorem signedTaylorMoment_inv_sub_one (n : ℕ) (s : ℂ) :
    signedTaylorMoment n (fun z ↦ (z - 1)⁻¹) s = ((s - 1)⁻¹) ^ (n + 1) := by
  have ht := congrFun (iteratedDeriv_comp_const_add n (fun z : ℂ ↦ (z - 1)⁻¹) s) 0
  simp only [add_zero] at ht
  rw [signedTaylorMoment, ← ht]
  have he : (fun z : ℂ ↦ (s + z - 1)⁻¹) = (fun z ↦ (1 * z + (s - 1))⁻¹) := by
    funext z
    congr 1
    ring
  rw [he]
  simpa only [signedTaylorMoment, one_pow, one_mul] using signedTaylorMoment_inv_linear n 1 (s - 1)

/-- The double pole in `-zeta'` gives the first-jet geometric mode. -/
theorem signedTaylorMoment_inv_sub_one_sq (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    signedTaylorMoment n (fun z ↦ ((z - 1)⁻¹) ^ 2) s =
      ((n + 1 : ℕ) : ℂ) * ((s - 1)⁻¹) ^ (n + 2) := by
  have he : (fun z : ℂ ↦ ((z - 1)⁻¹) ^ 2) =ᶠ[𝓝 s]
      (fun z ↦ -deriv (fun w : ℂ ↦ (w - 1)⁻¹) z) := by
    filter_upwards [compl_singleton_mem_nhds hs] with z hz
    have hz0 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    have h := ((hasDerivAt_id z).sub_const (1 : ℂ)).fun_inv hz0
    have hd : deriv (fun w : ℂ ↦ (w - 1)⁻¹) z = -(z - 1)⁻¹ ^ 2 := by
      simpa only [id_eq, Pi.inv_apply, neg_div, one_div, inv_pow] using h.deriv
    rw [hd, neg_neg]
  rw [signedTaylorMoment_congr n he]
  have hm := signedTaylorMoment_const_mul n (-1) (deriv (fun z : ℂ ↦ (z - 1)⁻¹)) s
  simp only [neg_one_mul] at hm
  rw [hm, signedTaylorMoment_deriv, signedTaylorMoment_inv_sub_one]
  simp only [neg_mul, neg_neg]

/-- Cauchy's estimate for the exact signed factorial moments. -/
theorem norm_signedTaylorMoment_le {f : ℂ → ℂ} {s : ℂ} {R C : ℝ}
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball s R))
    (hC : ∀ z ∈ sphere s R, ‖f z‖ ≤ C) (n : ℕ) :
    ‖signedTaylorMoment n f s‖ ≤ C / R ^ n := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf hC
  have hn : (0 : ℝ) < n.factorial := by positivity
  have he : ‖signedTaylorMoment n f s‖ = ‖iteratedDeriv n f s‖ / n.factorial := by
    simp [signedTaylorMoment, norm_pow, div_eq_mul_inv, mul_comm]
  rw [he]
  apply (div_le_div_of_nonneg_right h hn.le).trans_eq
  field_simp

end

end RiemannGaussian
