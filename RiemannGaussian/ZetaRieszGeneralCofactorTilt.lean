/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszExponentialCofactor
import RiemannGaussian.ZetaRieszCofactorTiltRate
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# General factorial tilts and arithmetic cofactor decay

A real-power prefix estimate turns every admissible positive factorial tilt
into a bound on the actual composite-cofactor contribution. A concrete
exponential cofactor schedule pays the full spatial and coefficient costs.
The exact scalar optimizer gives geometric decay away from its single
contact; the existing polynomial deletion covers contact. The complementary
original band retains every hypothetical right-half zero's source.

These are component estimates. The joint signed lower bound for surviving
semiprimes and larger composite cofactors remains open. The scalar optimizer
does not assert optimality of the cofactor growth schedule or zero exclusion.
-/

namespace RiemannGaussian.ZetaRieszGeneralCofactorTilt
noncomputable section
open scoped BigOperators Classical Topology
open Filter ZetaRieszFixedCofactor ZetaRieszGrowingCofactor ZetaRieszExponentialCofactor

/-- A discrete concavity estimate pays each real-power summand by a
successive prefix difference, with no integer-exponent restriction. -/
theorem rpow_step_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (D : ℕ) :
    ((D : ℝ) + 1) ^ (a - 1) ≤
      (((D : ℝ) + 1) ^ a - (D : ℝ) ^ a) / a := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hX : (0 : ℝ) < D + 1 := by positivity
  have hs : -1 ≤ (D : ℝ) / (D + 1) - 1 := by
    have := div_nonneg hD hX.le
    linarith
  have hb := rpow_one_add_le_one_add_mul_self hs ha.le ha1
  rw [show 1 + ((D : ℝ) / (D + 1) - 1) = D / (D + 1) by ring,
    Real.div_rpow hD hX.le, div_le_iff₀ (Real.rpow_pos_of_pos hX a)] at hb
  have hc := mul_le_mul_of_nonneg_right hb hX.le
  field_simp at hc
  rw [Real.rpow_sub_one hX.ne']
  apply (le_div_iff₀ ha).mpr
  rw [div_mul_eq_mul_div, div_le_iff₀ hX]
  nlinarith

/-- Every concave positive real power has the expected complete prefix
bound, including cutoff zero and every integer endpoint. -/
theorem sum_rpow_concave_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (a - 1)) ≤ (X : ℝ) ^ a / a := by
  induction X with
  | zero => simp [Real.zero_rpow ha.ne']
  | succ X ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hs := rpow_step_le ha ha1 X
    simp only [Nat.cast_add, Nat.cast_one]
    rw [sub_div] at hs
    linarith

/-- A complete finite power-prefix estimate for every positive real
exponent, including convex and concave regimes. -/
theorem sum_rpow_prefix_le {a : ℝ} (ha : 0 < a) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ (a - 1)) ≤
      (1 + 1 / a) * (X : ℝ) ^ a := by
  have hXa := Real.rpow_nonneg (Nat.cast_nonneg X) a
  by_cases ha1 : a ≤ 1
  · calc
      _ ≤ (X : ℝ) ^ a / a := sum_rpow_concave_le ha ha1 X
      _ ≤ (X : ℝ) ^ a + (X : ℝ) ^ a / a := le_add_of_nonneg_left hXa
      _ = _ := by ring
  · by_cases hX : X = 0
    · subst X
      simp [Real.zero_rpow ha.ne']
    · have hX0 : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
      calc
        _ ≤ ∑ _n ∈ Finset.Icc 1 X, (X : ℝ) ^ (a - 1) := by
          apply Finset.sum_le_sum
          intro n hn
          exact Real.rpow_le_rpow (Nat.cast_nonneg n)
            (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (by linarith)
        _ = (X : ℝ) * (X : ℝ) ^ (a - 1) := by simp
        _ = (X : ℝ) ^ a := by rw [Real.rpow_sub_one hX0.ne']; field_simp
        _ ≤ _ := by have := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) ha.le; nlinarith

/-- An arbitrary admissible positive tilt retains all factorial shifts
and gives the exact real-power spatial weight. -/
theorem norm_filter_le_rpow (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    {q : ℝ} (hq : 1 / 2 < q) {n : ℕ} (hn : 0 < n) :
    ‖zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      q⁻¹ ^ N * (n : ℝ) ^ ((q - 1 / 2) - 1) *
        ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k := by
  have hb := norm_zetaPrimeFilterKernel_le_tilt P N (3 / 2 + Complex.I * y)
    (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by linarith : 0 < q)
  norm_num at hb
  have he : Real.exp ((q - 3 / 2) * Real.log n) = (n : ℝ) ^ ((q - 1 / 2) - 1) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hn : (0 : ℝ) < n)]
    congr 1
    ring
  rw [he] at hb
  simpa only [inv_pow] using hb

/-- The complete original filter has a proved spatial-prefix bound for
EVERY tilt above one half, with its parameter-dependent cost retained. -/
theorem norm_sum_filter_le_rpow (P : Polynomial ℂ) (N : ℕ) (y : ℝ)
    (T : Finset ℕ) (X : ℕ) (f : ℕ → ℂ) {C q : ℝ} (hC : 0 ≤ C) (hq : 1 / 2 < q)
    (hT : ∀ n ∈ T, 0 < n ∧ n ≤ X) (hf : ∀ n ∈ T, ‖f n‖ ≤ C) :
    ‖∑ n ∈ T, f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      C * q⁻¹ ^ N * (∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        (1 + 1 / (q - 1 / 2)) * (X : ℝ) ^ (q - 1 / 2) := by
  let S : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  have hq0 : 0 < q := by linarith
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  calc
    _ ≤ ∑ n ∈ T, ‖f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ T, C * (q⁻¹ ^ N * (n : ℝ) ^ ((q - 1 / 2) - 1) * S) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul (hf n hn) (norm_filter_le_rpow P N y hq (hT n hn).1)
        (norm_nonneg _) hC
    _ = (C * q⁻¹ ^ N * S) * ∑ n ∈ T, (n : ℝ) ^ ((q - 1 / 2) - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ (C * q⁻¹ ^ N * S) * ∑ n ∈ Finset.Icc 1 X, (n : ℝ) ^ ((q - 1 / 2) - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => Finset.mem_Icc.mpr (hT n hn))
        (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ (C * q⁻¹ ^ N * S) * ((1 + 1 / (q - 1 / 2)) * (X : ℝ) ^ (q - 1 / 2)) :=
      mul_le_mul_of_nonneg_left (sum_rpow_prefix_le (by linarith) X) (by positivity)
    _ = _ := by ring

/-- The full source normalization and squared cutoff retain the exact
scalar rate of every admissible tilt, not only the unit or three-halves tilt. -/
theorem general_scale_identity {u : ℝ} (hu : 0 < u) (q : ℝ) (N : ℕ) :
    u ^ (N + 1) * q⁻¹ ^ N * (u⁻¹ ^ N) ^ (2 * (q - 1 / 2)) =
      u * ZetaRieszCofactorTiltRate.tiltRate u q ^ N := by
  have he : u * (u⁻¹ : ℝ) ^ (2 * (q - 1 / 2)) =
      Real.exp ((2 - 2 * q) * Real.log u) := by
    rw [Real.rpow_def_of_pos (inv_pos.mpr hu), Real.log_inv]
    calc
      _ = Real.exp (Real.log u) * Real.exp (-Real.log u * (2 * (q - 1 / 2))) := by
        rw [Real.exp_log hu]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ = u * (u * q⁻¹ * (u⁻¹ : ℝ) ^ (2 * (q - 1 / 2))) ^ N := by
      rw [← Real.rpow_pow_comm (inv_nonneg.mpr hu.le), mul_pow, mul_pow, pow_succ]
      ring
    _ = _ := by
      congr 2
      rw [mul_right_comm, he]
      rfl

/-- Every bounded original subband below A*(D_N+2)^2 has the exact
arbitrary-tilt geometric allowance, with its real-power spatial mass and
all parameter-dependent constants explicitly paid. -/
theorem norm_sum_filter_square_cutoff_le_tilt (P : Polynomial ℂ) (N A : ℕ) (y : ℝ)
    (T : Finset ℕ) (f : ℕ → ℂ) {C u q : ℝ} (hC : 0 ≤ C)
    (hu : 0 < u) (hu1 : u ≤ 1) (hq : 1 / 2 < q)
    (hT : ∀ n ∈ T, 0 < n ∧
      n ≤ A * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hf : ∀ n ∈ T, ‖f n‖ ≤ C) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ T,
      f n * zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      C * (∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
        (1 + 1 / (q - 1 / 2)) * (3 : ℝ) ^ (2 * (q - 1 / 2)) * u *
          (A : ℝ) ^ (q - 1 / 2) * ZetaRieszCofactorTiltRate.tiltRate u q ^ N := by
  let S : ℝ := ∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k
  have hq0 : 0 < q := by linarith
  have ha : 0 < q - 1 / 2 := by linarith
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  have hcost : 0 ≤ 1 + 1 / (q - 1 / 2) := by positivity
  have hb := norm_sum_filter_le_rpow P N y T
    (A * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) f hC hq hT hf
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] at hb
  have hp (v : ℝ) (hv : 0 ≤ v) : (v ^ 2) ^ (q - 1 / 2) = v ^ (2 * (q - 1 / 2)) := by
    rw [← Real.rpow_natCast v 2, ← Real.rpow_mul hv]
    norm_num
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * q⁻¹ ^ N * S * (1 + 1 / (q - 1 / 2)) *
        (A * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2 : ℝ) ^ 2) ^ (q - 1 / 2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ u ^ (N + 1) * (C * q⁻¹ ^ N * S * (1 + 1 / (q - 1 / 2)) *
        (A * (3 * u⁻¹ ^ N) ^ 2) ^ (q - 1 / 2)) := by
      gcongr
      exact cutoff_add_two_le hu hu1 N
    _ = (C * S * (1 + 1 / (q - 1 / 2)) * (A : ℝ) ^ (q - 1 / 2) *
        (3 : ℝ) ^ (2 * (q - 1 / 2))) *
          (u ^ (N + 1) * q⁻¹ ^ N * (u⁻¹ ^ N) ^ (2 * (q - 1 / 2))) := by
      rw [Real.mul_rpow (Nat.cast_nonneg A) (sq_nonneg _), hp _ (by positivity),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity)]
      ring
    _ = _ := by rw [general_scale_identity hu q N]; ring

/-- The full fixed-filter cost of an arbitrary admissible tilt. All
parameter costs are explicit and independent of the factorial order. -/
def tiltCost (P : Polynomial ℂ) (u q : ℝ) : ℝ :=
  (∑ k ∈ P.support, ‖P.coeff k‖ * q⁻¹ ^ k) *
    (1 + 1 / (q - 1 / 2)) * (3 : ℝ) ^ (2 * (q - 1 / 2)) * u

/-- Every cost factor is nonnegative on its actual parameter domain. -/
theorem tiltCost_nonneg (P : Polynomial ℂ) {u q : ℝ} (hu : 0 < u) (hq : 1 / 2 < q) :
    0 ≤ tiltCost P u q := by
  have hq0 : 0 < q := by linarith
  have ha : 0 < q - 1 / 2 := by linarith
  unfold tiltCost
  positivity

/-- The general-tilt bound applies to the literal Riesz coefficients
on every clipped cofactor subband, rather than just to a scalar rate. -/
theorem norm_clipped_cofactor_band_le_tilt (P : Polynomial ℂ) (N A : ℕ) (y : ℝ)
    (T : Finset ℕ) {u q : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hq : 1 / 2 < q)
    (hT : ∀ n ∈ T, ∃ a p : ℕ, 1 < a ∧ a ≤ A ∧ p.Prime ∧ ¬ p ∣ a ∧ n = p * a ∧
      n ≤ A * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ T,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      rangeCost A * tiltCost P u q * (A : ℝ) ^ (q - 1 / 2) *
        ZetaRieszCofactorTiltRate.tiltRate u q ^ N := by
  have hb := norm_sum_filter_square_cutoff_le_tilt P N A y T
    (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N))
    (rangeCost_nonneg A) hu hu1 hq (fun n hn => by
      obtain ⟨a, p, ha, _haA, hp, _hpa, rfl, hc⟩ := hT n hn
      exact ⟨Nat.mul_pos hp.pos (by omega), hc⟩)
    (fun n hn => by
      obtain ⟨a, p, ha, haA, hp, hpa, rfl, hc⟩ := hT n hn
      exact norm_coefficient_le_range u N ha haA hp hpa hc)
  convert hb using 1
  unfold tiltCost
  ring

/-- The mathematically defined optimizer now enters the actual arithmetic
bound with its exact minimum rate and every cofactor/filter cost retained. -/
theorem norm_clipped_cofactor_band_le_optimal (P : Polynomial ℂ) (N A : ℕ) (y : ℝ)
    (T : Finset ℕ) {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    (hT : ∀ n ∈ T, ∃ a p : ℕ, 1 < a ∧ a ≤ A ∧ p.Prime ∧ ¬ p ∣ a ∧ n = p * a ∧
      n ≤ A * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ T,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      rangeCost A * tiltCost P u (ZetaRieszCofactorTiltRate.optimalTilt u) *
        (A : ℝ) ^ (ZetaRieszCofactorTiltRate.optimalTilt u - 1 / 2) *
          ZetaRieszCofactorTiltRate.minimumRate u ^ N := by
  have hu0 : 0 < u := by linarith
  simpa only [ZetaRieszCofactorTiltRate.tiltRate_optimal hu0 hu1] using
    norm_clipped_cofactor_band_le_tilt P N A y T hu0 hu1.le
      (ZetaRieszCofactorTiltRate.optimalTilt_gt_half hu hu1) hT

/-- The cofactor range cost has a uniform cubic envelope before the
spatial real-power mass is multiplied in. -/
theorem rangeCost_le_cube {A : ℕ} (hA : 1 ≤ A) :
    rangeCost A ≤ 2 * (1 + 1 / Real.log 4) * (A : ℝ) ^ 3 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  apply (mul_le_mul_iff_right₀ hA0).mp
  calc
    (A : ℝ) * rangeCost A = rangeCost A * (A : ℝ) := mul_comm _ _
    _ ≤ 2 * (1 + 1 / Real.log 4) * (A : ℝ) ^ 4 := rangeCost_mul_le hA
    _ = (A : ℝ) * (2 * (1 + 1 / Real.log 4) * (A : ℝ) ^ 3) := by ring

/-- This exponent pays the complete cofactor coefficient cost together
with the exact spatial mass for an arbitrary admissible tilt. -/
theorem rangeCost_mul_rpow_le {A : ℕ} (hA : 1 ≤ A) {q : ℝ} :
    rangeCost A * (A : ℝ) ^ (q - 1 / 2) ≤
      2 * (1 + 1 / Real.log 4) * (A : ℝ) ^ (q + 5 / 2) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  calc
    _ ≤ (2 * (1 + 1 / Real.log 4) * (A : ℝ) ^ 3) * (A : ℝ) ^ (q - 1 / 2) :=
      mul_le_mul_of_nonneg_right (rangeCost_le_cube hA) (Real.rpow_nonneg hA0.le _)
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast (A : ℝ) 3, ← Real.rpow_add hA0]
      congr 2
      norm_num
      ring

/-- A fixed exponential cofactor base paying half the available
geometric saving, with the complete cofactor/spatial exponent in its denominator. -/
def growthRate (u q : ℝ) : ℝ :=
  Real.exp (-Real.log (ZetaRieszCofactorTiltRate.tiltRate u q) / (2 * (q + 5 / 2)))

/-- The scalar rate is positive for every positive tilt. -/
theorem tiltRate_pos (u : ℝ) {q : ℝ} (hq : 0 < q) :
    0 < ZetaRieszCofactorTiltRate.tiltRate u q := div_pos (Real.exp_pos _) hq

/-- A proved scalar saving leaves a cofactor growth base strictly above one. -/
theorem growthRate_gt_one (u : ℝ) {q : ℝ} (hq : 1 / 2 < q)
    (hb : ZetaRieszCofactorTiltRate.tiltRate u q < 1) : 1 < growthRate u q := by
  have hq0 : 0 < q := by linarith
  have hl := Real.log_neg (tiltRate_pos u hq0) hb
  apply Real.one_lt_exp_iff.mpr
  exact div_pos (neg_pos.mpr hl) (by linarith)

/-- The complete range exponent recovers precisely the inverse scalar
rate; all cost dependence on the chosen tilt is preserved. -/
theorem growthRate_rpow (u : ℝ) {q : ℝ} (hq : 1 / 2 < q) :
    growthRate u q ^ (2 * (q + 5 / 2)) = (ZetaRieszCofactorTiltRate.tiltRate u q)⁻¹ := by
  have hq0 : 0 < q := by linarith
  have hd : 2 * (q + 5 / 2) ≠ 0 := by linarith
  unfold growthRate
  rw [← Real.exp_mul]
  rw [div_mul_cancel₀ _ hd, Real.exp_neg, Real.exp_log (tiltRate_pos u hq0)]

/-- The concrete general-tilt cofactor range, kept inside the original
physical cutoff by a literal integer minimum. -/
def tiltedSchedule (u q : ℝ) (N : ℕ) : ℕ :=
  min ⌊growthRate u q ^ N⌋₊ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 1)

/-- The chosen range is positive at every order once the scalar saving
has been proved, including all floor effects. -/
theorem tiltedSchedule_pos (u : ℝ) {q : ℝ} (hq : 1 / 2 < q)
    (hb : ZetaRieszCofactorTiltRate.tiltRate u q < 1) (N : ℕ) :
    1 ≤ tiltedSchedule u q N := by
  have hf : 1 ≤ ⌊growthRate u q ^ N⌋₊ := Nat.le_floor (by
    simpa using one_le_pow₀ (growthRate_gt_one u hq hb).le (n := N))
  exact le_min hf (by omega)

/-- Every integer rounding preserves the complete real-power cofactor
budget, not just an asymptotic approximation to the schedule. -/
theorem tiltedSchedule_budget (u : ℝ) {q : ℝ} (hq : 1 / 2 < q) (N : ℕ) :
    (tiltedSchedule u q N : ℝ) ^ (2 * (q + 5 / 2)) ≤
      (ZetaRieszCofactorTiltRate.tiltRate u q)⁻¹ ^ N := by
  have hr : 0 < growthRate u q := Real.exp_pos _
  have hfloor : (tiltedSchedule u q N : ℝ) ≤ growthRate u q ^ N :=
    (show (tiltedSchedule u q N : ℝ) ≤ ⌊growthRate u q ^ N⌋₊ by
      exact_mod_cast min_le_left _ _).trans (Nat.floor_le (pow_pos hr N).le)
  calc
    _ ≤ (growthRate u q ^ N) ^ (2 * (q + 5 / 2)) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hfloor (by linarith)
    _ = _ := by rw [← Real.rpow_pow_comm hr.le, growthRate_rpow u hq]

/-- The general-tilt cofactor schedule grows without bound when the
scalar rate is strictly below one, with the physical-cutoff minimum retained. -/
theorem tiltedSchedule_tendsto {u q : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hq : 1 / 2 < q) (hb : ZetaRieszCofactorTiltRate.tiltRate u q < 1) :
    Tendsto (tiltedSchedule u q) atTop atTop := by
  have hr := tendsto_nat_floor_atTop.comp
    (tendsto_pow_atTop_atTop_of_one_lt (growthRate_gt_one u hq hb))
  have hd := (tendsto_add_atTop_nat 1).comp (tendsto_linearDampedCutoff hu hu1)
  apply tendsto_atTop.2
  intro b
  filter_upwards [hr.eventually_ge_atTop b, hd.eventually_ge_atTop b] with N hN hD
  exact le_min hN hD

/-- Every selected cofactor lies in the original physical logarithmic
cutoff at each order; its compact complement requires no boundary estimate. -/
theorem tiltedSchedule_log_le_length (u : ℝ) {q : ℝ} (hq : 1 / 2 < q)
    (hb : ZetaRieszCofactorTiltRate.tiltRate u q < 1) (N : ℕ) :
    Real.log (tiltedSchedule u q N) ≤ SquarefreeVaughanLogSource.length u N := by
  apply Real.log_le_log (by exact_mod_cast tiltedSchedule_pos u hq hb N :
    (0 : ℝ) < tiltedSchedule u q N)
  have hm : tiltedSchedule u q N ≤ ZetaVaughanCutoffBudget.linearDampedCutoff u N + 1 :=
    min_le_right _ _
  have hmR : (tiltedSchedule u q N : ℝ) ≤
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) + 1 := by exact_mod_cast hm
  have hD := Nat.cast_nonneg (α := ℝ) (ZetaVaughanCutoffBudget.linearDampedCutoff u N)
  change (tiltedSchedule u q N : ℝ) ≤
    ((ZetaVaughanCutoffBudget.linearDampedCutoff u N : ℝ) + 2) ^ 2
  nlinarith

/-- After paying the whole cofactor exponent the actual normalized
budget retains a square-root geometric saving, uniformly in the order. -/
theorem normalized_range_budget (u : ℝ) {q : ℝ} (hq : 1 / 2 < q) (N : ℕ) :
    (tiltedSchedule u q N : ℝ) ^ (q + 5 / 2) *
      ZetaRieszCofactorTiltRate.tiltRate u q ^ N ≤
        Real.sqrt (ZetaRieszCofactorTiltRate.tiltRate u q ^ N) := by
  have hb0 := tiltRate_pos u (show 0 < q by linarith)
  have hc : (ZetaRieszCofactorTiltRate.tiltRate u q)⁻¹ ^ N *
      ZetaRieszCofactorTiltRate.tiltRate u q ^ N = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hb0.ne', one_pow]
  have hp : ((tiltedSchedule u q N : ℝ) ^ (q + 5 / 2)) ^ 2 =
      (tiltedSchedule u q N : ℝ) ^ (2 * (q + 5 / 2)) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
    ring
  apply Real.le_sqrt_of_sq_le
  rw [mul_pow, hp]
  calc
    _ ≤ ((ZetaRieszCofactorTiltRate.tiltRate u q)⁻¹ ^ N) *
        (ZetaRieszCofactorTiltRate.tiltRate u q ^ N) ^ 2 :=
      mul_le_mul_of_nonneg_right (tiltedSchedule_budget u hq N) (sq_nonneg _)
    _ = ((ZetaRieszCofactorTiltRate.tiltRate u q)⁻¹ ^ N *
        ZetaRieszCofactorTiltRate.tiltRate u q ^ N) *
          ZetaRieszCofactorTiltRate.tiltRate u q ^ N := by ring
    _ = _ := by rw [hc, one_mul]

/-- The arithmetic class selected by the complete general-tilt budget. -/
def tiltedCompositeInsertion (u q : ℝ) (N n : ℕ) : Prop := ∃ a p : ℕ,
  1 < a ∧ a ≤ tiltedSchedule u q N ∧ Squarefree a ∧ ¬ a.Prime ∧
    p.Prime ∧ ¬ p ∣ a ∧ n = p * a

/-- The actual original band restricted to the paid composite-cofactor class. -/
def tiltedCompositeBand (u q : ℝ) (N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter (tiltedCompositeInsertion u q N)

/-- Its single compact range, used only in proving the bound. -/
def tiltedClippedBand (u q : ℝ) (N : ℕ) : Finset ℕ :=
  (tiltedCompositeBand u q N).filter fun n => n ≤ tiltedSchedule u q N *
    (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2

/-- Once the common cutoff contains the growing cofactor range, every
term outside the compact range is exactly zero by the complete two-moment
cancellation. Thus no additional boundary estimate is assumed. -/
theorem tilted_band_eq_clipped (P : Polynomial ℂ) (y u q : ℝ) (N : ℕ)
    (hL : Real.log (tiltedSchedule u q N) ≤ SquarefreeVaughanLogSource.length u N) :
    (∑ n ∈ tiltedCompositeBand u q N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
    ∑ n ∈ tiltedClippedBand u q N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  rw [tiltedClippedBand, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs with hc
  · rfl
  · obtain ⟨_hband, a, p, ha1, haA, hasf, hap, hp, hpa, rfl⟩ := Finset.mem_filter.mp hn
    have hLa : Real.log a ≤ SquarefreeVaughanLogSource.length u N :=
      (Real.log_le_log (by exact_mod_cast (show 0 < a by omega) : (0 : ℝ) < a)
        (by exact_mod_cast haA)).trans hL
    have hpa' : a * (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p * a :=
      (Nat.mul_le_mul_right _ haA).trans_lt (Nat.lt_of_not_ge hc)
    have hgt : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p := by
      nlinarith
    have hLp : SquarefreeVaughanLogSource.length u N ≤ Real.log p := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast hgt.le
    rw [coefficient_prime_mul_eq_zero_of_large hasf (by omega) hap hp hpa hLa hLp, zero_mul]


/-- The complete general-tilt composite-cofactor class obeys a geometric
bound at every order, with all prime sizes, signs and factorial shifts retained. -/
theorem norm_tilted_composite_band_le (P : Polynomial ℂ) (y : ℝ)
    {u q : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hq : 1 / 2 < q)
    (hb : ZetaRieszCofactorTiltRate.tiltRate u q < 1) (N : ℕ) :
    ‖(u : ℂ) ^ (N + 1) * ∑ n ∈ tiltedCompositeBand u q N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (2 * (1 + 1 / Real.log 4) * tiltCost P u q) *
        Real.sqrt (ZetaRieszCofactorTiltRate.tiltRate u q ^ N) := by
  have hcost := tiltCost_nonneg P hu hq
  have h4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  have hb0 := tiltRate_pos u (show 0 < q by linarith)
  rw [tilted_band_eq_clipped P y u q N (tiltedSchedule_log_le_length u hq hb N)]
  have h := norm_clipped_cofactor_band_le_tilt P N (tiltedSchedule u q N) y
    (tiltedClippedBand u q N) hu hu1 hq (fun n hn => by
      obtain ⟨hb, hc⟩ := Finset.mem_filter.mp hn
      obtain ⟨_hband, a, p, ha, haA, _hasf, _hap, hp, hpa, he⟩ := Finset.mem_filter.mp hb
      exact ⟨a, p, ha, haA, hp, hpa, he, hc⟩)
  calc
    _ ≤ rangeCost (tiltedSchedule u q N) * tiltCost P u q *
        (tiltedSchedule u q N : ℝ) ^ (q - 1 / 2) *
          ZetaRieszCofactorTiltRate.tiltRate u q ^ N := h
    _ = tiltCost P u q * (rangeCost (tiltedSchedule u q N) *
        (tiltedSchedule u q N : ℝ) ^ (q - 1 / 2)) *
          ZetaRieszCofactorTiltRate.tiltRate u q ^ N := by ring
    _ ≤ tiltCost P u q * (2 * (1 + 1 / Real.log 4) *
        (tiltedSchedule u q N : ℝ) ^ (q + 5 / 2)) *
          ZetaRieszCofactorTiltRate.tiltRate u q ^ N := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (rangeCost_mul_rpow_le (tiltedSchedule_pos u hq hb N)) hcost)
        (pow_pos hb0 N).le
    _ = (2 * (1 + 1 / Real.log 4) * tiltCost P u q) *
        ((tiltedSchedule u q N : ℝ) ^ (q + 5 / 2) *
          ZetaRieszCofactorTiltRate.tiltRate u q ^ N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalized_range_budget u hq N) (by positivity)

/-- Any admissible tilt with a proved rate below one now gives
independent decay of the whole actual arithmetic cofactor class. -/
theorem tendsto_tilted_composite_band (P : Polynomial ℂ) (y : ℝ)
    {u q : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hq : 1 / 2 < q)
    (hb : ZetaRieszCofactorTiltRate.tiltRate u q < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ n ∈ tiltedCompositeBand u q N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  have hb0 := tiltRate_pos u (show 0 < q by linarith)
  have ht := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_pow_atTop_nhds_zero_of_lt_one hb0.le hb)
  apply squeeze_zero_norm (norm_tilted_composite_band_le P y hu hu1 hq hb)
  simpa only [Real.sqrt_zero, mul_zero, Function.comp_apply] using
    ht.const_mul (2 * (1 + 1 / Real.log 4) * tiltCost P u q)


/-- The general-tilt schedule eventually exceeds every fixed polynomial
range; the minimum with the original damped cutoff is still retained. -/
theorem eventually_pow_le_tiltedSchedule {u q : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hq : 1 / 2 < q)
    (hb : ZetaRieszCofactorTiltRate.tiltRate u q < 1) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, N ^ k ≤ tiltedSchedule u q N := by
  have hr := growthRate_gt_one u hq hb
  have hr0 : 0 < growthRate u q := lt_trans zero_lt_one hr
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one k
    (inv_nonneg.mpr hr0.le) ((inv_lt_one₀ hr0).mpr hr)
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_pow_le_cutoff hu hu1 k] with N hN hD
  apply le_min _ (hD.trans (Nat.le_succ _))
  apply Nat.le_floor
  rw [Nat.cast_pow]
  have hc : (growthRate u q)⁻¹ ^ N * growthRate u q ^ N = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr0.ne', one_pow]
  have hm := mul_le_mul_of_nonneg_right hN.le (pow_pos hr0 N).le
  simpa only [mul_assoc, hc, mul_one, one_mul] using hm

/-- The exact complementary original band for any general-tilt deletion. -/
def tiltedReducedBand (u q : ℝ) (N : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter fun n => ¬ tiltedCompositeInsertion u q N n

/-- The general-tilt cut retains an exact signed partition at each
order, with unchanged physical length, frequency and polynomial filter. -/
theorem actual_band_eq_tilted_add_reduced (P : Polynomial ℂ) (N : ℕ) (y L u q : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      (∑ n ∈ tiltedCompositeBand u q N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      ∑ n ∈ tiltedReducedBand u q N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  exact (Finset.sum_filter_add_sum_filter_not (zetaPrimeLogBand N)
    (tiltedCompositeInsertion u q N) (fun n => SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)).symm

/-- Every eligible composite cofactor remaining after the general-tilt
cut exceeds its explicit threshold. Semiprimes remain outside this class. -/
theorem surviving_tilted_cofactor_gt {u q : ℝ} {N n a p : ℕ}
    (hn : n ∈ tiltedReducedBand u q N) (ha1 : 1 < a) (hasf : Squarefree a)
    (hap : ¬ a.Prime) (hp : p.Prime) (hpa : ¬ p ∣ a) (he : n = p * a) :
    tiltedSchedule u q N < a := by
  have hnot := (Finset.mem_filter.mp hn).2
  by_contra hsmall
  exact hnot ⟨a, p, ha1, by omega, hasf, hap, hp, hpa, he⟩

/-- The scalar optimizer yields an actual geometric bound for its
whole composite-cofactor class, after paying all spatial and cofactor costs. -/
theorem norm_optimal_composite_band_le (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    (hcrit : u ≠ Real.exp (-(1 / 2 : ℝ))) (N : ℕ) :
    ‖(u : ℂ) ^ (N + 1) *
      ∑ n ∈ tiltedCompositeBand u (ZetaRieszCofactorTiltRate.optimalTilt u) N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n‖ ≤
      (2 * (1 + 1 / Real.log 4) * tiltCost P u (ZetaRieszCofactorTiltRate.optimalTilt u)) *
        Real.sqrt (ZetaRieszCofactorTiltRate.minimumRate u ^ N) := by
  have hu0 : 0 < u := by linarith
  have hb := (ZetaRieszCofactorTiltRate.tiltRate_optimal hu0 hu1).trans_lt
    (ZetaRieszCofactorTiltRate.minimumRate_lt_one hu0 hcrit)
  simpa only [ZetaRieszCofactorTiltRate.tiltRate_optimal hu0 hu1] using
    norm_tilted_composite_band_le P y hu0 hu1.le
      (ZetaRieszCofactorTiltRate.optimalTilt_gt_half hu hu1) hb N

/-- Away from the one scalar contact, the exact analytic tilt pays
an unbounded composite-cofactor class with the original full filter. -/
theorem tendsto_optimal_composite_band (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    (hcrit : u ≠ Real.exp (-(1 / 2 : ℝ))) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ tiltedCompositeBand u (ZetaRieszCofactorTiltRate.optimalTilt u) N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  have hu0 : 0 < u := by linarith
  exact tendsto_tilted_composite_band P y hu0 hu1.le
    (ZetaRieszCofactorTiltRate.optimalTilt_gt_half hu hu1)
    ((ZetaRieszCofactorTiltRate.tiltRate_optimal hu0 hu1).trans_lt
      (ZetaRieszCofactorTiltRate.minimumRate_lt_one hu0 hcrit))

/-- The exact-tilt cofactor range eventually dominates every fixed
power of the order, except at the scalar envelope's single contact. -/
theorem eventually_pow_le_optimalSchedule {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1)
    (hcrit : u ≠ Real.exp (-(1 / 2 : ℝ))) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, N ^ k ≤
      tiltedSchedule u (ZetaRieszCofactorTiltRate.optimalTilt u) N := by
  have hu0 : 0 < u := by linarith
  exact eventually_pow_le_tiltedSchedule hu0 hu1
    (ZetaRieszCofactorTiltRate.optimalTilt_gt_half hu hu1)
    ((ZetaRieszCofactorTiltRate.tiltRate_optimal hu0 hu1).trans_lt
      (ZetaRieszCofactorTiltRate.minimumRate_lt_one hu0 hcrit)) k

/-- Use the analytically optimized geometric range away from its
single contact, and the independently proved polynomial range at contact. -/
def optimizedCompositeBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  if u = Real.exp (-(1 / 2 : ℝ)) then growingCompositeBand N
  else tiltedCompositeBand u (ZetaRieszCofactorTiltRate.optimalTilt u) N

/-- The corresponding exact original-band complement, including the
exceptional scalar contact rather than assuming it cannot occur. -/
def optimizedReducedBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  if u = Real.exp (-(1 / 2 : ℝ)) then growingReducedBand N
  else tiltedReducedBand u (ZetaRieszCofactorTiltRate.optimalTilt u) N

/-- The optimized arithmetic deletion decays at every actual source
scale. Its hypotheses do not assert a zero or a signed-tail bound. -/
theorem tendsto_optimized_composite_band (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) :
    Tendsto (fun N => (u : ℂ) ^ (N + 1) * ∑ n ∈ optimizedCompositeBand u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  by_cases h : u = Real.exp (-(1 / 2 : ℝ))
  · simpa only [optimizedCompositeBand, if_pos h] using
      tendsto_growing_composite_band P y (show 0 < u by linarith) hu1
  · simpa only [optimizedCompositeBand, if_neg h] using
      tendsto_optimal_composite_band P y hu hu1 h

/-- The optimized class and its complement partition the original
carrier, retaining the same signs, cutoff and factorial shifts. -/
theorem actual_band_eq_optimized_add_reduced (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      (∑ n ∈ optimizedCompositeBand u N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      ∑ n ∈ optimizedReducedBand u N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  by_cases h : u = Real.exp (-(1 / 2 : ℝ))
  · simpa only [optimizedCompositeBand, optimizedReducedBand, if_pos h] using
      actual_band_eq_growing_add_reduced P N y L
  · simpa only [optimizedCompositeBand, optimizedReducedBand, if_neg h] using
      actual_band_eq_tilted_add_reduced P N y L u (ZetaRieszCofactorTiltRate.optimalTilt u)

/-- Every hypothetical right-half zero retains its full negative
multiplicity source after the optimized deletion. The scalar contact is
covered by polynomial decay and is not asserted to be zero-free. -/
theorem tendsto_optimized_reduced_source (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N => (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
      ∑ n ∈ optimizedReducedBand (3 / 2 - rho.1.re) N,
        SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n *
          zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N
            (3 / 2 + Complex.I * rho.1.im) n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 1 / 2 < (3 / 2 - rho.1.re : ℝ) := by
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have h := (SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho).sub
    (tendsto_optimized_composite_band (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hu hu1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by
    push_cast
    rfl
  rw [hcast, actual_band_eq_optimized_add_reduced, mul_add, add_sub_cancel_left]

end
end RiemannGaussian.ZetaRieszGeneralCofactorTilt
