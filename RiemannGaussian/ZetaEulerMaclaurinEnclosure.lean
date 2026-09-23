/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.CertifiedComplexInterval
import RiemannGaussian.ZetaEulerMaclaurinBudget

/-!
# Certified interval evaluation of the literal finite zeta approximation

The common complex endpoint power is computed once and shared by all
Bernoulli corrections. Every Dirichlet term and every correction remains
present. Successful evaluation encloses the actual finite expression in
the previously proved zeta error theorem; numerical failures propagate.
-/

namespace RiemannGaussian.ZetaEulerMaclaurinEnclosure
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaEulerMaclaurin

private theorem mem_real_rat {cfg : DyadicConfig} (hp : cfg.precision ≤ 0) (q : ℚ) :
    Mem (q : ℂ) (rational cfg.precision q 0) := by
  simpa only [Rat.cast_zero, zero_mul, add_zero] using mem_rational hp q 0

/-- Rounded rising factorial divided by the endpoint power. Scaling each
factor before multiplication prevents tiny rounded coefficients from being
amplified by an enormous unscaled rising factorial. -/
def scaledRisingBox (prec : ℤ) (N : ℕ) (A : Box) : ℕ → Box
  | 0 => rational prec 1 0
  | j + 1 => mul prec (scaledRisingBox prec N A j)
      (mul prec (add prec A (rational prec j 0)) (rational prec (1 / (N + 1)) 0))

/-- Each normalized rising-factorial enclosure retains its exact scaling. -/
theorem mem_scaledRisingBox {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s : ℂ} {A : Box} (hs : Mem s A) (N j : ℕ) :
    Mem (rising s j / (N + 1 : ℂ) ^ j) (scaledRisingBox cfg.precision N A j) := by
  induction j with
  | zero => simpa only [rising, Finset.prod_range_zero, pow_zero, div_one,
      scaledRisingBox, Rat.cast_one] using mem_real_rat hp 1
  | succ j ih =>
    have hh := mem_mul ih
      (mem_mul (mem_add hs (by simpa using mem_real_rat hp (j : ℚ)) cfg.precision)
        (mem_real_rat hp (1 / (N + 1))) cfg.precision) cfg.precision
    rw [rising_succ, pow_succ, mul_div_mul_comm]
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_mul, Rat.cast_inv, one_mul, scaledRisingBox, one_div, div_eq_mul_inv] using hh

/-- Exact rational normalized Bernoulli coefficient. -/
def coefficient (j : ℕ) : ℚ :=
  if j < 19 then ZetaEulerMaclaurinBudget.coefficientAt j
  else bernoulli (j + 2) / (j + 2).factorial

private theorem coefficient_cast (j : ℕ) :
    (coefficient j : ℂ) = (ZetaEulerMaclaurinKernel.boundary (j + 2) : ℂ) := by
  have hc : coefficient j = bernoulli (j + 2) / (j + 2).factorial := by
    unfold coefficient
    split_ifs with hj
    · exact ZetaEulerMaclaurinBudget.coefficientAt_eq j hj
    · rfl
  rw [hc]
  simp only [ZetaEulerMaclaurinKernel.boundary]
  push_cast
  rfl

/-- The finite correction polynomial, before multiplication by the common power. -/
noncomputable def correction (N : ℕ) (s : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range k, rising s (j + 1) / (N + 1 : ℂ) ^ (j + 1) * (coefficient j : ℂ)

/-- Interval arithmetic for all normalized Bernoulli corrections. -/
def correctionBox (prec : ℤ) (N : ℕ) (A : Box) : ℕ → Box
  | 0 => rational prec 0 0
  | j + 1 => add prec (correctionBox prec N A j)
      (mul prec (scaledRisingBox prec N A (j + 1)) (rational prec (coefficient j) 0))

/-- The complete finite correction is enclosed, with no signed term discarded. -/
theorem mem_correctionBox {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s : ℂ} {A : Box} (hs : Mem s A) (N k : ℕ) :
    Mem (correction N s k) (correctionBox cfg.precision N A k) := by
  induction k with
  | zero => simpa only [correction, Finset.sum_range_zero, correctionBox, Rat.cast_zero]
      using mem_real_rat hp 0
  | succ k ih =>
    rw [correction, Finset.sum_range_succ]
    exact mem_add ih (mem_mul (mem_scaledRisingBox hp hs N _) (mem_real_rat hp _) _) _

/-- Checked enclosure of every term in the literal Dirichlet prefix. -/
def prefixBox (cfg : DyadicConfig) (A : Box) : ℕ → EvalResult Box
  | 0 => .ok (rational cfg.precision 0 0)
  | n + 1 =>
    match prefixBox cfg A n with
    | .error err => .error err
    | .ok P =>
      match natPower cfg (n + 1) (neg A) with
      | .error err => .error err
      | .ok Q => .ok (add cfg.precision P Q)

/-- A successful prefix computation encloses the actual ordinary Dirichlet sum. -/
theorem mem_prefix {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s : ℂ} {A B : Box} (hs : Mem s A) (N : ℕ)
    (h : prefixBox cfg A N = .ok B) : Mem (ZetaEulerCell.partialSum N s) B := by
  induction N generalizing B with
  | zero =>
    simp only [prefixBox, Except.ok.injEq] at h
    subst B
    simpa only [ZetaEulerCell.partialSum, Finset.sum_range_zero, Rat.cast_zero] using mem_real_rat hp 0
  | succ N ih =>
    cases hP : prefixBox cfg A N with
    | error err => simp [prefixBox, hP] at h
    | ok P =>
      cases hQ : natPower cfg (N + 1) (neg A) with
      | error err => simp [prefixBox, hP, hQ] at h
      | ok Q =>
        simp only [prefixBox, hP, hQ, Except.ok.injEq] at h
        subst B
        have hq := mem_natPower hp (Nat.succ_pos N) (mem_neg hs) hQ
        simpa only [ZetaEulerCell.partialSum, Finset.sum_range_succ, Nat.cast_succ, Nat.cast_add, Nat.cast_one]
          using mem_add (ih hP) hq cfg.precision

/-- Exact common-power factorization used by the interval algorithm. -/
theorem approximation_factored (N M : ℕ) (s : ℂ) :
    approximation N s M = ZetaEulerCell.partialSum N s +
      (N + 1 : ℂ) ^ (-s) * ((N + 1 : ℂ) / (s - 1) + 1 / 2 + correction N s (M + 1)) := by
  have hA : (N + 1 : ℂ) ≠ 0 := by
    have hh : (0 : ℝ) < (N + 1 : ℝ) := by positivity
    exact_mod_cast hh.ne'
  have he : (N + 1 : ℂ) ^ (1 - s) = (N + 1 : ℂ) * (N + 1 : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hA, Complex.cpow_one]
  have hsum : (∑ j ∈ Finset.range (M + 1), rising s (j + 1) *
      (ZetaEulerMaclaurinKernel.boundary (j + 2) : ℂ) * (N + 1 : ℂ) ^ (-s - (j + 1))) =
      (N + 1 : ℂ) ^ (-s) * correction N s (M + 1) := by
    rw [correction, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [coefficient_cast, Complex.cpow_sub _ _ hA]
    rw [show (j : ℂ) + 1 = ((j + 1 : ℕ) : ℂ) by push_cast; rfl, Complex.cpow_natCast]
    ring
  rw [approximation, he, hsum]
  ring

/-- Evaluate the entire finite approximation, sharing its complex endpoint power. -/
def evaluate (cfg : DyadicConfig) (N M : ℕ) (A : Box) : EvalResult Box :=
  match prefixBox cfg A N with
  | .error err => .error err
  | .ok P =>
    match natPower cfg (N + 1) (neg A) with
    | .error err => .error err
    | .ok Q =>
      match inv cfg (add cfg.precision A (rational cfg.precision (-1) 0)) with
      | .error err => .error err
      | .ok U =>
        .ok (add cfg.precision P (mul cfg.precision Q
          (add cfg.precision
            (add cfg.precision (mul cfg.precision (rational cfg.precision (N + 1) 0) U)
              (rational cfg.precision (1 / 2) 0))
            (correctionBox cfg.precision N A (M + 1)))))

/-- Successful computation encloses exactly the finite expression in
the zeta remainder theorem, for every complex point in the input rectangle. -/
theorem mem_evaluate {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s : ℂ} {A B : Box} (hs : Mem s A) (N M : ℕ)
    (h : evaluate cfg N M A = .ok B) : Mem (approximation N s M) B := by
  cases hP : prefixBox cfg A N with
  | error err => simp [evaluate, hP] at h
  | ok P =>
    cases hQ : natPower cfg (N + 1) (neg A) with
    | error err => simp [evaluate, hP, hQ] at h
    | ok Q =>
      cases hU : inv cfg (add cfg.precision A (rational cfg.precision (-1) 0)) with
      | error err => simp [evaluate, hP, hQ, hU] at h
      | ok U =>
        simp only [evaluate, hP, hQ, hU, Except.ok.injEq] at h
        subst B
        have hu : Mem (s - 1)⁻¹ U := mem_inv hp
          (by simpa [sub_eq_add_neg] using mem_add hs (mem_real_rat hp (-1)) cfg.precision) hU
        have hq := mem_natPower hp (Nat.succ_pos N) (mem_neg hs) hQ
        have ht := mem_add (mem_prefix hp hs N hP)
          (mem_mul hq
            (mem_add
              (mem_add (mem_mul (mem_real_rat hp (N + 1)) hu cfg.precision)
                (mem_real_rat hp (1 / 2)) cfg.precision)
              (mem_correctionBox hp hs N (M + 1)) cfg.precision) cfg.precision) cfg.precision
        rw [approximation_factored]
        simpa [div_eq_mul_inv] using ht

end RiemannGaussian.ZetaEulerMaclaurinEnclosure
