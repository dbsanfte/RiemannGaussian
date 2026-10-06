/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryGram
import Mathlib.MeasureTheory.Group.Integral

/-!
# Exact power-mode preflight for a carry quadratic

The continuous denominator variable is used only to feed a specified
Chebyshev power component through the literal packet kernel. At integer
denominators it agrees with the original carry. This does not assert an
actual-prime asymptotic or an independent centered quadratic estimate.
-/

namespace RiemannGaussian.SuzukiCarryGramSource
noncomputable section
open Complex MeasureTheory Set
open SuzukiIntegerCarry SuzukiCarryCorrelation SuzukiCarryGram
open scoped BigOperators

/-- Continuous-denominator carry with the same literal floor convention. -/
def realCarry (N : ℕ) (t : ℝ) : ℝ :=
  if Even (⌊2*(N : ℝ)*Real.exp (-t)⌋ : ℤ) then 0 else 1

/-- The continuous version of the exact integer-scale carry increment. -/
def realIncidence (N : ℕ) (t : ℝ) : ℝ := realCarry (N+1) t - realCarry N t

/-- The unchanged finite coefficient packet in the log-denominator variable. -/
def realPacket (S : Finset ℕ) (alpha : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ N ∈ S, alpha N * (realIncidence N t : ℂ)

/-- The exact squared packet, with every coefficient joined before a norm. -/
def realMass (S : Finset ℕ) (alpha : ℕ → ℂ) (t : ℝ) : ℝ :=
  ‖realPacket S alpha t‖^2

/-- The positive Mellin coefficient after matching the source height. -/
def sourceCoefficient (S : Finset ℕ) (alpha : ℕ → ℂ) (beta : ℝ) : ℝ :=
  ∫ t : ℝ, Real.exp (beta*t) * realMass S alpha t

/-- At each literal denominator the continuous carry is the actual integer carry. -/
theorem realCarry_log {d : ℕ} (hd : 0 < d) (N : ℕ) :
    realCarry N (Real.log d) = (carry N d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hf : (⌊2*(N : ℝ)*Real.exp (-Real.log d)⌋ : ℤ) = (((2*N)/d : ℕ) : ℤ) := by
    rw [Real.exp_neg, Real.exp_log hdR]
    rw [show 2*(N : ℝ)*(d : ℝ)⁻¹ = ((2*N : ℕ) : ℝ)/d by push_cast; ring,
      Int.floor_div_natCast, Int.floor_natCast]
    norm_cast
  rw [realCarry, hf]
  simp only [Int.even_coe_nat, Nat.even_iff, ← carry_eq_mod_two]
  rcases carry_eq_zero_or_one N d with h | h <;> simp [h]

/-- The entire continuous squared packet retains the literal integer weights. -/
theorem realMass_log {d : ℕ} (hd : 0 < d) (S : Finset ℕ) (alpha : ℕ → ℂ) :
    realMass S alpha (Real.log d) = packetMass S alpha d := by
  simp only [realMass, realPacket, realIncidence, realCarry_log hd,
    incidence, packetMass, packet, Complex.normSq_eq_norm_sq]

/-- Constant coefficients telescope in the diagnostic variable as well;
the original integer increment width is retained exactly. -/
theorem realPacket_interval_eq {A B : ℕ} (hAB : A ≤ B) (t : ℝ) :
    realPacket (Finset.Ico A B) (fun _ => 1) t =
      ((realCarry B t-realCarry A t : ℝ) : ℂ) := by
  have he : (∑ N ∈ Finset.Ico A B, realIncidence N t) = realCarry B t-realCarry A t := by
    unfold realIncidence
    rw [Finset.sum_Ico_eq_sub _ hAB,
      Finset.sum_range_sub (fun k => realCarry k t) B,
      Finset.sum_range_sub (fun k => realCarry k t) A]
    ring
  simpa only [realPacket, one_mul, ← Complex.ofReal_sum] using congrArg Complex.ofReal he

/-- Scaling a physical integer cutoff gives the exact log-variable dilation,
including every quotient endpoint. -/
theorem realCarry_mul_scale {A : ℕ} (hA : 0 < A) (B : ℕ) (t : ℝ) :
    realCarry (A*B) t = realCarry B (t-Real.log A) := by
  have he : Real.exp (-(t-Real.log A)) = Real.exp (-t)*(A : ℝ) := by
    rw [show -(t-Real.log A) = -t+Real.log A by ring, Real.exp_add,
      Real.exp_log (by exact_mod_cast hA)]
  unfold realCarry
  rw [he]
  have hh : 2*((A*B : ℕ) : ℝ)*Real.exp (-t) = 2*(B : ℝ)*(Real.exp (-t)*(A : ℝ)) := by
    push_cast
    ring
  rw [hh]

/-- A growing flat coefficient block is exactly a dilation of one fixed
quadratic profile. This prevents confusing a positive finite response
with a response that could shrink away on the moving source scale. -/
theorem realMass_flat_scale {A : ℕ} (hA : 0 < A) (t : ℝ) :
    realMass (Finset.Ico A (2*A)) (fun _ => 1) t =
      realMass {1} (fun _ => 1) (t-Real.log A) := by
  unfold realMass
  rw [realPacket_interval_eq (by omega), show 2*A = A*2 by omega,
    realCarry_mul_scale hA 2, show realCarry A t = realCarry (A*1) t by simp,
    realCarry_mul_scale hA 1]
  simp [realPacket, realIncidence]

private theorem realCarry_bounds (N : ℕ) (t : ℝ) :
    0 ≤ realCarry N t ∧ realCarry N t ≤ 1 := by
  unfold realCarry
  split_ifs <;> norm_num

private theorem measurable_realCarry (N : ℕ) : Measurable (realCarry N) :=
  (measurable_of_countable (fun k : ℤ => if Even k then (0 : ℝ) else 1)).comp
    (Int.measurable_floor.comp (measurable_const.mul
      (Real.measurable_exp.comp measurable_id.neg)))

/-- Genuine measurability of the exact squared packet. -/
theorem measurable_realMass (S : Finset ℕ) (alpha : ℕ → ℂ) :
    Measurable (realMass S alpha) := by
  apply Measurable.pow_const
  apply Measurable.norm
  apply Finset.measurable_sum
  intro N _
  exact measurable_const.mul ((Complex.measurable_ofReal).comp
    ((measurable_realCarry (N+1)).sub (measurable_realCarry N)))

private theorem realIncidence_abs_le (N : ℕ) (t : ℝ) : |realIncidence N t| ≤ 1 := by
  rw [abs_le]
  have h1 := realCarry_bounds N t
  have h2 := realCarry_bounds (N+1) t
  unfold realIncidence
  constructor <;> linarith

/-- A finite packet has a fixed total-variation envelope; used only to
justify the diagnostic integral, not as a source-scale arithmetic payment. -/
theorem realMass_le (S : Finset ℕ) (alpha : ℕ → ℂ) (t : ℝ) :
    realMass S alpha t ≤ (∑ N ∈ S, ‖alpha N‖)^2 := by
  have hn : ‖realPacket S alpha t‖ ≤ ∑ N ∈ S, ‖alpha N‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro N _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (realIncidence_abs_le N t) (norm_nonneg _)).trans_eq
      (mul_one _)
  exact sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun N _ => norm_nonneg (alpha N))) |>.mpr hn

private theorem realCarry_eq_zero {N : ℕ} {t : ℝ} (h : 2*(N : ℝ) < Real.exp t) :
    realCarry N t = 0 := by
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have hh := mul_lt_mul_of_pos_right h (Real.exp_pos (-t))
  rw [he] at hh
  have hf : (⌊2*(N : ℝ)*Real.exp (-t)⌋ : ℤ) = 0 :=
    Int.floor_eq_iff.mpr ⟨by norm_num; positivity, by simpa using hh⟩
  simp [realCarry, hf]

/-- The continuous packet has the exact same upper physical support. -/
theorem realMass_eq_zero_above {S : Finset ℕ} {alpha : ℕ → ℂ} {B : ℕ} {t : ℝ}
    (hS : ∀ N ∈ S, N ≤ B) (ht : 2*(B+1 : ℝ) < Real.exp t) :
    realMass S alpha t = 0 := by
  have hz (N : ℕ) (hN : N ∈ S) : realIncidence N t = 0 := by
    have hn : (N : ℝ) ≤ B := by exact_mod_cast hS N hN
    simp only [realIncidence, realCarry_eq_zero (by push_cast; linarith : 2*((N+1 : ℕ) : ℝ) < Real.exp t),
      realCarry_eq_zero (by linarith : 2*(N : ℝ) < Real.exp t), sub_self]
  have hp : realPacket S alpha t = 0 := by
    unfold realPacket
    apply Finset.sum_eq_zero
    intro N hN
    rw [hz N hN]
    simp
  simp [realMass, hp]

/-- The Mellin preflight is genuinely integrable for positive real source exponent. -/
theorem integrable_source {S : Finset ℕ} {alpha : ℕ → ℂ} {B : ℕ} {beta : ℝ}
    (hb : 0 < beta) (hS : ∀ N ∈ S, N ≤ B) :
    Integrable (fun t : ℝ => Real.exp (beta*t) * realMass S alpha t) := by
  let U := Real.log (2*(B+1 : ℝ))
  let C := (∑ N ∈ S, ‖alpha N‖)^2
  have hi : Integrable ((Iic U).indicator (fun t : ℝ => C*Real.exp (beta*t))) :=
    (integrable_indicator_iff measurableSet_Iic).mpr ((integrableOn_exp_mul_Iic hb U).const_mul C)
  apply hi.mono' ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
    (measurable_realMass S alpha)).aestronglyMeasurable
  filter_upwards with t
  change ‖Real.exp (beta*t)*realMass S alpha t‖ ≤
    (Iic U).indicator (fun t : ℝ => C*Real.exp (beta*t)) t
  by_cases ht : t ≤ U
  · rw [Set.indicator_of_mem (show t ∈ Iic U from ht)]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.exp_pos _).le (show 0 ≤ realMass S alpha t from sq_nonneg _))]
    simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (realMass_le S alpha t) (Real.exp_pos _).le
  · have he : 2*(B+1 : ℝ) < Real.exp t := by
      have hp : 0 < 2*(B+1 : ℝ) := by positivity
      exact (Real.log_lt_iff_lt_exp hp).mp (lt_of_not_ge ht)
    rw [realMass_eq_zero_above hS he, mul_zero, norm_zero,
      Set.indicator_of_notMem (show t ∉ Iic U from ht)]

private theorem realCarry_eq_one {N : ℕ} {t : ℝ}
    (hlo : (N : ℝ) < Real.exp t) (hhi : Real.exp t < 2*(N : ℝ)) :
    realCarry N t = 1 := by
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have h1 := mul_lt_mul_of_pos_right hhi (Real.exp_pos (-t))
  have h2 := mul_lt_mul_of_pos_right hlo (Real.exp_pos (-t))
  rw [he] at h1 h2
  have hf : (⌊2*(N : ℝ)*Real.exp (-t)⌋ : ℤ) = 1 :=
    Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
  have ho : ¬Even (1 : ℤ) := by decide
  simp only [realCarry, hf, if_neg ho]

/-- Bounds for the exact continuous denominator carry, including endpoints. -/
theorem realCarry_nonneg (N : ℕ) (t : ℝ) : 0 ≤ realCarry N t :=
  (realCarry_bounds N t).1

/-- Above the physical support the exact carry is zero. -/
theorem realCarry_zero_of_large {N : ℕ} {t : ℝ}
    (h : 2*(N : ℝ) < Real.exp t) : realCarry N t = 0 :=
  realCarry_eq_zero h

/-- The first odd quotient cell has exact unit carry. -/
theorem realCarry_one_on_cell {N : ℕ} {t : ℝ}
    (hlo : (N : ℝ) < Real.exp t) (hhi : Real.exp t < 2*(N : ℝ)) :
    realCarry N t = 1 := realCarry_eq_one hlo hhi

/-- A nonzero last coefficient cannot disappear in the joined squared kernel.
This uses an explicit open physical cell, not a continuity approximation. -/
theorem realPacket_on_last_cell {S : Finset ℕ} {alpha : ℕ → ℂ} {B : ℕ} {t : ℝ}
    (hS : ∀ N ∈ S, N ≤ B) (hB : B ∈ S)
    (ht : t ∈ Ioo (Real.log (2*(B : ℝ)+1)) (Real.log (2*(B : ℝ)+2))) :
    realPacket S alpha t = alpha B := by
  have hlo : 2*(B : ℝ)+1 < Real.exp t :=
    (Real.log_lt_iff_lt_exp (by positivity)).mp ht.1
  have hhi : Real.exp t < 2*(B : ℝ)+2 :=
    (Real.lt_log_iff_exp_lt (by positivity)).mp ht.2
  have hz (N : ℕ) (hN : N ≤ B) : realCarry N t = 0 := by
    have hnr : (N : ℝ) ≤ B := by exact_mod_cast hN
    exact realCarry_eq_zero (by linarith)
  have hb1 : realCarry (B+1) t = 1 := realCarry_eq_one (by push_cast; linarith) (by push_cast; linarith)
  unfold realPacket
  rw [Finset.sum_eq_single B]
  · simp [realIncidence, hb1, hz B le_rfl]
  · intro N hN hNB
    have hn : N+1 ≤ B := by have := hS N hN; omega
    simp [realIncidence, hz (N+1) hn, hz N (hS N hN)]
  · exact fun hnot => False.elim (hnot hB)

/-- Every nonzero finite packet has strictly positive matched source response.
It therefore cannot inherit the linear zeta-factor annihilation. -/
theorem sourceCoefficient_pos {S : Finset ℕ} {alpha : ℕ → ℂ} {B : ℕ} {beta : ℝ}
    (hb : 0 < beta) (hS : ∀ N ∈ S, N ≤ B) (hB : B ∈ S) (ha : alpha B ≠ 0) :
    0 < sourceCoefficient S alpha beta := by
  let a := Real.log (2*(B : ℝ)+1)
  let b := Real.log (2*(B : ℝ)+2)
  let c := Real.exp (beta*a)*‖alpha B‖^2
  have hab : a < b := Real.log_lt_log (by positivity) (by linarith)
  have hc : 0 < c := mul_pos (Real.exp_pos _) (sq_pos_of_pos (norm_pos_iff.mpr ha))
  have hi : Integrable ((Ioo a b).indicator (fun _ : ℝ => c)) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))
  have he : (∫ t : ℝ, (Ioo a b).indicator (fun _ : ℝ => c) t) = (b-a)*c := by
    rw [integral_indicator_const _ measurableSet_Ioo]
    simp [hab.le, smul_eq_mul]
  have hle : (∫ t : ℝ, (Ioo a b).indicator (fun _ : ℝ => c) t) ≤
      sourceCoefficient S alpha beta := by
    apply integral_mono hi (integrable_source hb hS)
    intro t
    by_cases ht : t ∈ Ioo a b
    · rw [Set.indicator_of_mem ht]
      change c ≤ Real.exp (beta*t)*‖realPacket S alpha t‖^2
      rw [realPacket_on_last_cell hS hB ht]
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.1.le hb.le)) (sq_nonneg _)
    · rw [Set.indicator_of_notMem ht]
      exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  exact (mul_pos (sub_pos.mpr hab) hc).trans_le (he ▸ hle)

/-- Zero coefficients do not alter any part of the joined packet. -/
theorem realPacket_filter_nonzero (S : Finset ℕ) (alpha : ℕ → ℂ) (t : ℝ) :
    realPacket (S.filter (fun N => alpha N ≠ 0)) alpha t = realPacket S alpha t := by
  classical
  unfold realPacket
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro N _
  by_cases h : alpha N = 0 <;> simp [h]

/-- The source response is positive for every genuinely nonzero finite
coefficient packet, with no requirement on zero coefficients at its endpoints. -/
theorem sourceCoefficient_pos_of_nonzero {S : Finset ℕ} {alpha : ℕ → ℂ} {beta : ℝ}
    (hb : 0 < beta) (ha : ∃ N ∈ S, alpha N ≠ 0) :
    0 < sourceCoefficient S alpha beta := by
  classical
  let Q := S.filter (fun N => alpha N ≠ 0)
  have hQ : Q.Nonempty := by
    obtain ⟨N, hN, hne⟩ := ha
    exact ⟨N, Finset.mem_filter.mpr ⟨hN, hne⟩⟩
  have hmax : Q.max' hQ ∈ Q := Q.max'_mem hQ
  have hle : ∀ N ∈ Q, N ≤ Q.max' hQ := fun N hN => Q.le_max' N hN
  have hp := sourceCoefficient_pos hb hle hmax (Finset.mem_filter.mp hmax).2
  have he : sourceCoefficient Q alpha beta = sourceCoefficient S alpha beta := by
    unfold sourceCoefficient realMass
    congr 1
    funext t
    rw [realPacket_filter_nonzero]
  exact he ▸ hp

/-- Exact Mellin scaling for the literal flat coefficient packet.
The positive base coefficient is independent of the growing arithmetic scale. -/
theorem sourceCoefficient_flat_scale {A : ℕ} (hA : 0 < A) (beta : ℝ) :
    sourceCoefficient (Finset.Ico A (2*A)) (fun _ => 1) beta =
      Real.exp (beta*Real.log A)*sourceCoefficient {1} (fun _ => 1) beta := by
  unfold sourceCoefficient
  simp_rw [realMass_flat_scale hA]
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => Real.exp (beta*t)*realMass {1} (fun _ => 1) (t-Real.log A)) (Real.log A)
  simp only [add_sub_cancel_right] at h
  rw [← h]
  have he (t : ℝ) : Real.exp (beta*(t+Real.log A))*realMass {1} (fun _ => 1) t =
      Real.exp (beta*Real.log A)*(Real.exp (beta*t)*realMass {1} (fun _ => 1) t) := by
    rw [mul_add, Real.exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul]

/-- Exact scale-normalized response of the Chebyshev diagnostic density
`-m * exp((beta+i*y)*t)` through the full height-twisted squared packet. -/
theorem power_mode_response (S : Finset ℕ) (alpha : ℕ → ℂ) (beta y T : ℝ) (m : ℕ) :
    (∫ t : ℝ, -(m : ℂ) * Complex.exp (((beta : ℂ)+I*y)*t) *
      Complex.exp (-(I*y)*t) * (realMass S alpha (t-T) : ℂ)) =
      (-(m : ℝ)*Real.exp (beta*T)*sourceCoefficient S alpha beta : ℝ) := by
  have hp (t : ℝ) : -(m : ℂ) * Complex.exp (((beta : ℂ)+I*y)*t) *
      Complex.exp (-(I*y)*t) = -(m : ℂ)*Complex.exp ((beta : ℂ)*t) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hp]
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun t : ℝ => -(m : ℂ)*Complex.exp ((beta : ℂ)*t)*(realMass S alpha (t-T) : ℂ)) T
  simp only [add_sub_cancel_right] at h
  rw [← h]
  have he (t : ℝ) : -(m : ℂ)*Complex.exp ((beta : ℂ)*((t+T : ℝ) : ℂ))*
      (realMass S alpha t : ℂ) =
      (-(m : ℝ)*Real.exp (beta*T)*(Real.exp (beta*t)*realMass S alpha t) : ℝ) := by
    have hx : Complex.exp ((beta : ℂ)*((t+T : ℝ) : ℂ)) =
        ((Real.exp (beta*T)*Real.exp (beta*t) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Real.exp_add]
      congr 2
      ring
    rw [hx]
    push_cast
    ring
  simp_rw [he]
  rw [integral_complex_ofReal, integral_const_mul]
  rfl

/-- A literal growing flat block has the exact matched source `-m*A^beta*C`.
The base coefficient is fixed, positive for `beta>0`, and contains no
vanishing `zeta(beta+i*y)` factor. -/
theorem flat_power_mode_response {A : ℕ} (hA : 0 < A) (beta y : ℝ) (m : ℕ) :
    (∫ t : ℝ, -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*
      Complex.exp (-(I*y)*t)*(realMass (Finset.Ico A (2*A)) (fun _ => 1) t : ℂ)) =
      (-(m : ℝ)*Real.exp (beta*Real.log A)*sourceCoefficient {1} (fun _ => 1) beta : ℝ) := by
  have h := power_mode_response (Finset.Ico A (2*A)) (fun _ => 1) beta y 0 m
  simp only [sub_zero, mul_zero, Real.exp_zero, mul_one] at h
  rw [h, sourceCoefficient_flat_scale hA]
  push_cast
  ring

/-- The diagnostic Chebyshev component has precisely the density used
in the preflight; its factor `1/rho` cancels upon logarithmic differentiation. -/
theorem hasDerivAt_diagnostic_component {rho : ℂ} (hr : rho ≠ 0) (m : ℕ) (t : ℝ) :
    HasDerivAt (fun v : ℝ => -(m : ℂ)/rho * Complex.exp (rho*v))
      (-(m : ℂ)*Complex.exp (rho*t)) t := by
  have h := ((((hasDerivAt_id t).ofReal_comp).const_mul rho).cexp).const_mul (-(m : ℂ)/rho)
  convert h using 1
  all_goals try rfl
  simp only [id_eq, Complex.ofReal_one, mul_one]
  field_simp [hr]

/-- The full diagnostic integral is genuine for positive source exponent. -/
theorem integrable_power_mode {S : Finset ℕ} {alpha : ℕ → ℂ} {B : ℕ} {beta : ℝ}
    (hb : 0 < beta) (hS : ∀ N ∈ S, N ≤ B) (y T : ℝ) (m : ℕ) :
    Integrable (fun t : ℝ => -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*
      Complex.exp (-(I*y)*t)*(realMass S alpha (t-T) : ℂ)) := by
  have h : Integrable (fun t : ℝ =>
      ((-(m : ℝ)*Real.exp (beta*T)*(Real.exp (beta*t)*realMass S alpha t) : ℝ) : ℂ)) :=
    ((integrable_source hb hS).const_mul (-(m : ℝ)*Real.exp (beta*T))).ofReal
  refine (h.comp_sub_right T).congr (Filter.Eventually.of_forall (fun t => ?_))
  have hp : -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*Complex.exp (-(I*y)*t) =
      -(m : ℂ)*Complex.exp ((beta : ℂ)*t) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  have he : Real.exp (beta*T)*Real.exp (beta*(t-T)) = Real.exp (beta*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp only
  rw [hp]
  rw [show -(m : ℝ)*Real.exp (beta*T)*(Real.exp (beta*(t-T))*realMass S alpha (t-T)) =
      -(m : ℝ)*(Real.exp (beta*T)*Real.exp (beta*(t-T)))*realMass S alpha (t-T) by ring, he]
  push_cast
  rfl

/-- A positive-multiplicity source survives with a strictly negative
matched response. No actual-zero asymptotic is assumed in this component test. -/
theorem power_mode_response_re_neg {S : Finset ℕ} {alpha : ℕ → ℂ} {B : ℕ} {beta : ℝ}
    (hb : 0 < beta) (hS : ∀ N ∈ S, N ≤ B) (hB : B ∈ S) (ha : alpha B ≠ 0)
    {m : ℕ} (hm : 0 < m) (y T : ℝ) :
    (∫ t : ℝ, -(m : ℂ)*Complex.exp (((beta : ℂ)+I*y)*t)*
      Complex.exp (-(I*y)*t)*(realMass S alpha (t-T) : ℂ)).re < 0 := by
  rw [power_mode_response, Complex.ofReal_re]
  have hp := sourceCoefficient_pos hb hS hB ha
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  nlinarith [Real.exp_pos (beta*T), mul_pos hmR (Real.exp_pos (beta*T))]

end
end RiemannGaussian.SuzukiCarryGramSource
