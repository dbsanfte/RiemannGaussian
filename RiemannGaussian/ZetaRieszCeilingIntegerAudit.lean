/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCeilingDensityAudit
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Integer quantization is not a source-scale cancellation

The finite count construction has genuine integer labels and weights zero
or one. Its cumulative error is below two. A geometric factorial moment
error leaves the old double-source join unchanged, not below 42/25.

The last theorem EXPLICITLY assumes the moment comparison. It does not
identify the rounded count with the continuous density and does not apply
that comparison to ordinary primes. The numerical control uses integers,
not the complete prime set. No arithmetic ceiling credit is supplied.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Real
open scoped BigOperators Classical

namespace RiemannGaussian.ZetaRieszCeilingIntegerAudit
open ZetaRieszCeilingDensityAudit ZetaRieszSelbergSourceAudit
open ZetaRieszSignedSelbergPayment

/-- The atom at the literal integer label n+1. No fractional weight is
inserted after rounding the cumulative count. -/
def roundedAtom (F : ℝ → ℝ) (n : ℕ) : ℕ :=
  ⌊F ((n+1 : ℕ) : ℝ)⌋₊-⌊F (n : ℝ)⌋₊

/-- The rounded cumulative count, including integer spacing. -/
def roundedCount (F : ℝ → ℝ) (x : ℝ) : ℕ := ⌊F (⌊x⌋₊ : ℝ)⌋₊

/-- A monotone count with increments at most one gives actual binary
atoms; positivity alone is not being substituted for unit weights. -/
theorem roundedAtom_zero_or_one (F : ℝ → ℝ) (hF : Monotone F)
    (h0 : 0 ≤ F 0)
    (hstep : ∀ n : ℕ, F ((n+1 : ℕ) : ℝ) ≤ F (n : ℝ)+1) (n : ℕ) :
    roundedAtom F n = 0 ∨ roundedAtom F n = 1 := by
  have hn : 0 ≤ F (n : ℝ) := h0.trans (hF (Nat.cast_nonneg n))
  have hle := Nat.floor_mono (hstep n)
  rw [Nat.floor_add_one hn] at hle
  unfold roundedAtom
  omega

/-- All finite binary atom counts telescope exactly, including the
initial lower endpoint. -/
theorem roundedAtom_sum (F : ℝ → ℝ) (hF : Monotone F) (N : ℕ) :
    (∑ n ∈ Finset.range N, (roundedAtom F n : ℝ)) =
      (⌊F (N : ℝ)⌋₊ : ℝ)-(⌊F 0⌋₊ : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hm : ⌊F (N : ℝ)⌋₊ ≤ ⌊F ((N+1 : ℕ) : ℝ)⌋₊ :=
      Nat.floor_mono (hF (by exact_mod_cast Nat.le_succ N))
    rw [roundedAtom, Nat.cast_sub hm]
    ring

/-- The floor construction has bounded cumulative discrepancy for a
monotone one-Lipschitz count. This is NOT a prime-count error theorem. -/
theorem roundedCount_error_lt_two (F : ℝ → ℝ) (hF : Monotone F)
    (h0 : 0 ≤ F 0)
    (hLip : ∀ a b : ℝ, 0 ≤ a → a ≤ b → F b-F a ≤ b-a)
    {x : ℝ} (hx : 0 ≤ x) :
    |(roundedCount F x : ℝ)-F x| < 2 := by
  have hn : (0 : ℝ) ≤ (⌊x⌋₊ : ℝ) := Nat.cast_nonneg _
  have hnx := Nat.floor_le hx
  have hFn : 0 ≤ F (⌊x⌋₊ : ℝ) := h0.trans (hF hn)
  have hfloor := Nat.floor_le hFn
  have hFle := hF hnx
  have hgap := hLip (⌊x⌋₊ : ℝ) x hn hnx
  have hxgap := Nat.lt_floor_add_one x
  have hFgap := Nat.lt_floor_add_one (F (⌊x⌋₊ : ℝ))
  unfold roundedCount
  rw [abs_of_nonpos (by linarith only [hfloor, hFle])]
  linarith only [hgap, hxgap, hFgap]

/-- The explicit geometric price derived for a bounded cumulative
rounding error by Abel summation. Its identification with a particular
moment difference remains a separate hypothesis below. -/
def roundingPrice (u y : ℝ) (k : ℕ) : ℝ :=
  2*((k+1 : ℕ) : ℝ)*(1+‖(3/2 : ℂ)+Complex.I*y‖/(3/2))*(u/(3/2))^(k+1)

theorem roundingPrice_nonneg {u : ℝ} (hu : 0 ≤ u) (y : ℝ) (k : ℕ) :
    0 ≤ roundingPrice u y k := by
  unfold roundingPrice
  positivity

/-- The target rounding ratio is strictly below one half, not 2*u.
This says nothing about the actual ordinary-prime discrepancy. -/
theorem target_rounding_ratio {u : ℝ}
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    u/(3/2) ≤ (10001/30000 : ℝ) ∧ (10001/30000 : ℝ) < 1/2 := by
  norm_num [ZetaRieszWideOwnerAudit.radiusCeiling] at hU
  constructor <;> linarith

/-- The entire stated rounding error price tends to zero at fixed
height; no order-zero or order-one atom is removed. -/
theorem roundingPrice_tendsto {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 3/2) (y : ℝ) :
    Tendsto (roundingPrice u y) atTop (𝓝 0) := by
  have hr0 : (0 : ℝ) ≤ u/(3/2) := by positivity
  have hr1 : u/(3/2) < (1 : ℝ) := by linarith
  have ht := ((tendsto_self_mul_const_pow_of_lt_one hr0 hr1).comp
    (tendsto_add_atTop_nat 1)).const_mul
      (2*(1+‖(3/2 : ℂ)+Complex.I*y‖/(3/2)))
  convert ht using 1
  · funext k
    simp only [roundingPrice, Function.comp_def, Nat.cast_add, Nat.cast_one]
    ring
  · ring

/-- Conditional source stability, with the moment-comparison hypothesis
visible. This is neither an infinite binary witness nor an actual-prime
error payment. -/
theorem tendsto_double_of_rounding_price {y : ℝ} (hy : 1 ≤ |y|) (a : ℕ → ℂ)
    (herror : ∀ k, ‖a k-doubleMoment (10001/20000) y 40000 k‖ ≤
      roundingPrice (10001/20000) y k) :
    Tendsto a atTop (𝓝 (-2)) := by
  have he : Tendsto (fun k => a k-doubleMoment (10001/20000) y 40000 k)
      atTop (𝓝 0) := squeeze_zero_norm herror
    (roundingPrice_tendsto (by norm_num) (by norm_num) y)
  have hd := doubleMoment_tendsto (u := 10001/20000) (B := 40000)
    (by norm_num) (by norm_num) (by norm_num) hy
  simpa only [zero_add] using (he.add hd).congr (fun k => sub_add_cancel _ _)

/-- An error already tending to zero cannot remove the selected double
source. The SAME joined evaluator still eventually exceeds 42/25. The
prime-comparison premise is NOT silently inferred from integer spacing. -/
theorem rounding_error_preserves_reverse_ceiling {y : ℝ} (hy : 1 ≤ |y|)
    (a : ℕ → ℂ)
    (herror : ∀ k, ‖a k-doubleMoment (10001/20000) y 40000 k‖ ≤
      roundingPrice (10001/20000) y k) :
    ∀ᶠ N in atTop,
      (42/25 : ℝ) < (-traceError a (N-1)-
        harmonicEvaluation a (10001/20000) N).re := by
  have ht := joined_double_tendsto a (tendsto_double_of_rounding_price hy a herror)
    (u := 10001/20000) (by norm_num) (by norm_num)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp ht
  simp only [Complex.ofReal_re] at hr
  have hc := ZetaRieszEndgameSlack.retainedCost_lower
    (u := 10001/20000) (by norm_num)
    (by norm_num [ZetaRieszWideOwnerAudit.radiusCeiling])
  exact hr.eventually_const_lt (by linarith only [hc])

end RiemannGaussian.ZetaRieszCeilingIntegerAudit
