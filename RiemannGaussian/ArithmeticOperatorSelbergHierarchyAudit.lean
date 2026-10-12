/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorSelbergSourceAudit

/-!
# All-order positive Selberg hierarchies still allow the coherent unit Euler control

This tests an infinite hierarchy, not another optimized order-two word.
The exact ACTUAL Mobius/log-power identity and every quotient are kept.
The recursive positive hierarchy, its complete convolution algebra and
all integer Gamma UPPER bounds also hold for the coherent unit-prime
Euler control. Its full factorial source remains -2, and the centered
signed prime-minus-pair response remains nonzero.

Consequently these positivity/recurrence/upper-bound data do not imply
non-coherence. The control fails the UNALTERED actual Mobius/log-power
identity at every positive order, and is not actual Gamma-compatible.
No native mask is completed, and no signed arithmetic estimate is claimed.
-/

namespace RiemannGaussian.ArithmeticOperatorSelbergHierarchyAudit
noncomputable section
open Complex Filter Topology
open ArithmeticOperatorSelbergControlAudit ArithmeticOperatorFactorialUniqueness
open scoped BigOperators Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- Actual generalized Mangoldt coefficient, including all prime powers. -/
def lambda (k : ℕ) : ArithmeticFunction ℝ :=
  (μ : ArithmeticFunction ℝ)*ArithmeticFunction.log.ppow k

theorem lambda_zero : lambda 0=1 := by
  simp [lambda,ArithmeticFunction.ppow_zero]

theorem lambda_one : lambda 1=ArithmeticFunction.vonMangoldt := by
  simp [lambda,ArithmeticFunction.ppow_one,ArithmeticFunction.moebius_mul_log_eq_vonMangoldt]

private theorem logWeight_one :
    (1 : ArithmeticFunction ℝ).pmul ArithmeticFunction.log=0 := by
  ext n
  by_cases hn : n=1 <;> simp [ArithmeticFunction.pmul_apply,hn]

private theorem moebius_logWeight :
    (μ : ArithmeticFunction ℝ).pmul ArithmeticFunction.log=
      -((μ : ArithmeticFunction ℝ)*ArithmeticFunction.vonMangoldt) := by
  have h := arithmeticFunction_logWeight_mul (μ : ArithmeticFunction ℝ)
    (ζ : ArithmeticFunction ℝ)
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta,logWeight_one,
    ArithmeticFunction.zeta_pmul,ArithmeticFunction.moebius_mul_log_eq_vonMangoldt] at h
  have he := congrArg (fun f : ArithmeticFunction ℝ => f*μ) h
  rw [zero_mul,add_mul,mul_assoc,ArithmeticFunction.coe_zeta_mul_coe_moebius,mul_one] at he
  linear_combination -he

/-- Exact finite Selberg recurrence; this is an identity of actual
integer divisor coefficients, not a formal Euler-series calculation. -/
theorem lambda_succ (k : ℕ) :
    lambda (k+1)=(lambda k).pmul ArithmeticFunction.log+
      ArithmeticFunction.vonMangoldt*lambda k := by
  have h := arithmeticFunction_logWeight_mul (μ : ArithmeticFunction ℝ)
    (ArithmeticFunction.log.ppow k)
  rw [moebius_logWeight,neg_mul,mul_assoc,
    show (ArithmeticFunction.log.ppow k).pmul ArithmeticFunction.log=
      ArithmeticFunction.log.ppow (k+1) by
        rw [ArithmeticFunction.pmul_comm,ArithmeticFunction.ppow_succ'],
    ←lambda,←lambda] at h
  rw [mul_left_comm (μ : ArithmeticFunction ℝ) ArithmeticFunction.vonMangoldt] at h
  change (lambda k).pmul ArithmeticFunction.log=
    -(ArithmeticFunction.vonMangoldt*lambda k)+lambda (k+1) at h
  linear_combination -h

/-- Entire actual hierarchy is positive BEFORE height twisting. -/
theorem lambda_nonneg (k n : ℕ) : 0≤lambda k n := by
  induction k generalizing n with
  | zero => by_cases hn : n=1 <;> simp [lambda_zero,hn]
  | succ k ih =>
    rw [lambda_succ,ArithmeticFunction.add_apply,ArithmeticFunction.pmul_apply,
      ArithmeticFunction.mul_apply,ArithmeticFunction.log_apply]
    exact add_nonneg (mul_nonneg (ih n) (Real.log_natCast_nonneg n))
      (Finset.sum_nonneg (fun de _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (ih de.2)))

/-- Complete actual Mobius/Gamma right-hand side is extra data, not
an inequality inherited merely from a positive hierarchy. -/
theorem lambda_mul_zeta (k : ℕ) :
    lambda k*(ζ : ArithmeticFunction ℝ)=ArithmeticFunction.log.ppow k := by
  rw [lambda,mul_comm (μ : ArithmeticFunction ℝ),mul_assoc,
    ArithmeticFunction.coe_moebius_mul_coe_zeta,mul_one]

theorem lambda_le_logPower (k : ℕ) {n : ℕ} (hn : n≠0) :
    lambda k n≤(Real.log n)^k := by
  have he := congrArg (fun f : ArithmeticFunction ℝ => f n) (lambda_mul_zeta k)
  rw [ArithmeticFunction.coe_mul_zeta_apply] at he
  have hlo : lambda k n≤∑ d∈n.divisors,lambda k d :=
    Finset.single_le_sum (fun d _ => lambda_nonneg k d)
      (Nat.mem_divisors.mpr ⟨dvd_rfl,hn⟩)
  rw [he] at hlo
  cases k with
  | zero => simpa [ArithmeticFunction.ppow_zero,ArithmeticFunction.zeta_apply_ne hn] using hlo
  | succ k => simpa [ArithmeticFunction.ppow_apply (Nat.succ_pos k),ArithmeticFunction.log_apply] using hlo

/-- Every positive-order coefficient vanishes at the unit endpoint. -/
theorem lambda_one_endpoint {k : ℕ} (hk : 0<k) : lambda k 1=0 := by
  simp [lambda,ArithmeticFunction.ppow_apply hk,hk.ne']

/-- The unaltered actual hierarchy detects a missing prime at every
positive order, rather than only at the order-two Selberg word. -/
theorem lambda_prime {k p : ℕ} (hk : 0<k) (hp : p.Prime) :
    lambda k p=(Real.log p)^k := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f p) (lambda_mul_zeta k)
  rw [ArithmeticFunction.coe_mul_zeta_apply,hp.divisors] at h
  simpa [hp.ne_one,lambda_one_endpoint hk,ArithmeticFunction.ppow_apply hk,
    ArithmeticFunction.log_apply] using h

/-- The full Mangoldt convolution power is also dominated at every
order. This is the positive comparison in the classical Selberg
hierarchy, with ordinary prime powers retained. -/
theorem mangoldt_pow_le_lambda (k n : ℕ) :
    (ArithmeticFunction.vonMangoldt^k) n≤lambda k n := by
  induction k generalizing n with
  | zero => simp [lambda_zero]
  | succ k ih =>
    have hconv :
        (∑ de∈n.divisorsAntidiagonal,ArithmeticFunction.vonMangoldt de.1*
          (ArithmeticFunction.vonMangoldt^k) de.2)≤
        ∑ de∈n.divisorsAntidiagonal,ArithmeticFunction.vonMangoldt de.1*lambda k de.2 :=
      Finset.sum_le_sum (fun de _ => mul_le_mul_of_nonneg_left
        (ih de.2) ArithmeticFunction.vonMangoldt_nonneg)
    rw [pow_succ',lambda_succ,ArithmeticFunction.add_apply,ArithmeticFunction.pmul_apply,
      ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply,ArithmeticFunction.log_apply]
    exact hconv.trans (le_add_of_nonneg_left
      (mul_nonneg (lambda_nonneg k n) (Real.log_natCast_nonneg n)))

/-- Recursive hierarchy for arbitrary complex integer coefficients. -/
def hierarchy (b : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0,n => if n=1 then 1 else 0
  | k+1,n => hierarchy b k n*(Real.log n : ℂ)+convolution b (hierarchy b k) n

/-- All-order finite integer identity at the actual Mangoldt sequence. -/
theorem hierarchy_actual (k n : ℕ) : hierarchy mangoldt k n=(lambda k n : ℂ) := by
  induction k generalizing n with
  | zero => by_cases hn : n=1 <;> simp [hierarchy,lambda_zero,hn]
  | succ k ih =>
    simp only [hierarchy,lambda_succ,ArithmeticFunction.add_apply,
      ArithmeticFunction.pmul_apply,ArithmeticFunction.mul_apply,ArithmeticFunction.log_apply,
      Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_sum,convolution,mangoldt,ih]

/-- The complete hierarchy commutes with multiplicative selection at
EVERY order, with no factorization of a physical test or phase. -/
theorem hierarchy_reweight (g : ℕ →*₀ ℂ) (b : ℕ → ℂ) (k n : ℕ) :
    hierarchy (reweight g b) k n=g n*hierarchy b k n := by
  induction k generalizing n with
  | zero => by_cases hn : n=1 <;> simp [hierarchy,hn]
  | succ k ih =>
    have he : hierarchy (reweight g b) k=reweight g (hierarchy b k) := funext ih
    rw [hierarchy,hierarchy,ih,he,convolution_reweight]
    ring

/-- The entire literal masked finite sum has the same selected monoid
factor. All complex phases and cutoff masks remain inside the sum. -/
theorem masked_hierarchy_reweight (g : ℕ →*₀ ℂ) (b : ℕ → ℂ)
    (k : ℕ) (S : Finset ℕ) (w : ℕ → ℂ) :
    (∑ n∈S,w n*hierarchy (reweight g b) k n)=
      ∑ n∈S,w n*g n*hierarchy b k n := by
  simp_rw [hierarchy_reweight,mul_assoc]

/-- Actual Gamma/log-power prefix, with every integer quotient. -/
theorem factorialPrefix_actual (k N : ℕ) :
    factorialPrefix (hierarchy mangoldt k) N =
      (∑ n∈Finset.Icc 1 N,(Real.log n)^k : ℝ) := by
  have hconv (n : ℕ) : (∑ de∈n.divisorsAntidiagonal,lambda k de.1)=
      ArithmeticFunction.log.ppow k n := by
    have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (lambda_mul_zeta k)
    rw [ArithmeticFunction.mul_apply] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro de hde
    simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_zero_of_mem_divisorsAntidiagonal hde).2]
  have hsum := sum_Icc_divisorsAntidiagonal_eq_sum_divided_prefix N
    (fun d _ => (lambda k d : ℂ))
  have hprefix : (∑ n∈Finset.Icc 1 N,(ArithmeticFunction.log.ppow k n : ℂ)) =
      factorialPrefix (fun d => (lambda k d : ℂ)) N := by
    simp_rw [←hconv,Complex.ofReal_sum] at hsum ⊢
    simpa only [factorialPrefix,Finset.sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul] using hsum
  rw [funext (hierarchy_actual k),←hprefix]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n≠0 := by have h := (Finset.mem_Icc.mp hn).1; omega
  cases k with
  | zero => simp [ArithmeticFunction.ppow_zero,ArithmeticFunction.zeta_apply_ne hn0]
  | succ k => simp [ArithmeticFunction.ppow_apply (Nat.succ_pos k),ArithmeticFunction.log_apply]

/-- Genuine coherent unit-prime Euler coefficient, all powers included. -/
def control (n : ℕ) : ℂ :=
  ArithmeticOperatorBinaryEulerControl.indicatorHom (10001/20000) 54 n*mangoldt n

theorem control_hierarchy_eq (k n : ℕ) :
    hierarchy control k n=
      ArithmeticOperatorBinaryEulerControl.indicatorHom (10001/20000) 54 n*(lambda k n : ℂ) := by
  exact (hierarchy_reweight _ mangoldt k n).trans
    (congrArg (_*·) (hierarchy_actual k n))

/-- Every order has real nonnegative coefficients bounded by the ACTUAL
hierarchy. This does not assert actual equality of Gamma data. -/
theorem control_hierarchy_bounds (k n : ℕ) :
    (hierarchy control k n).im=0 ∧
      0≤(hierarchy control k n).re ∧ (hierarchy control k n).re≤lambda k n := by
  rw [control_hierarchy_eq]
  change ((if ArithmeticOperatorBinaryEulerControl.kept (10001/20000) 54 n then (1 : ℂ) else 0)*
      (lambda k n : ℂ)).im=0 ∧
    0≤((if ArithmeticOperatorBinaryEulerControl.kept (10001/20000) 54 n then (1 : ℂ) else 0)*
      (lambda k n : ℂ)).re ∧
    ((if ArithmeticOperatorBinaryEulerControl.kept (10001/20000) 54 n then (1 : ℂ) else 0)*
      (lambda k n : ℂ)).re≤lambda k n
  split_ifs <;> simp [lambda_nonneg]

/-- Even the complete positive convolution-power comparison survives
the same unit selection at every order. It is not new signed input. -/
theorem control_convolutionPower_le (k n : ℕ) :
    (ArithmeticOperatorBinaryEulerControl.indicatorHom (10001/20000) 54 n*
      ((ArithmeticFunction.vonMangoldt^k) n : ℂ)).re≤(hierarchy control k n).re := by
  rw [control_hierarchy_eq]
  change ((if ArithmeticOperatorBinaryEulerControl.kept (10001/20000) 54 n then (1 : ℂ) else 0)*
      ((ArithmeticFunction.vonMangoldt^k) n : ℂ)).re≤
    ((if ArithmeticOperatorBinaryEulerControl.kept (10001/20000) 54 n then (1 : ℂ) else 0)*
      (lambda k n : ℂ)).re
  split_ifs
  · simpa using mangoldt_pow_le_lambda k n
  · simp

/-- All integer Gamma UPPER bounds survive simultaneously at all orders. -/
theorem control_factorialPrefix_le (k N : ℕ) :
    (factorialPrefix (hierarchy control k) N).re≤
      ∑ n∈Finset.Icc 1 N,(Real.log n)^k := by
  have hactual := congrArg Complex.re (factorialPrefix_actual k N)
  simp only [factorialPrefix,Complex.re_sum,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,Complex.ofReal_re] at hactual ⊢
  rw [←hactual]
  apply Finset.sum_le_sum
  intro n _
  simpa [hierarchy_actual] using mul_le_mul_of_nonneg_left
    (control_hierarchy_bounds k n).2.2 (Nat.cast_nonneg (N/n))

/-- Simultaneous positivity, actual-hierarchy domination and every
integer Gamma upper bound. Equalities of the actual Gamma data are
deliberately stronger than this tested constraint class. -/
def PositiveUpperHierarchy (b : ℕ → ℂ) : Prop :=
  (∀ k n, (hierarchy b k n).im=0 ∧ 0≤(hierarchy b k n).re ∧
    (hierarchy b k n).re≤lambda k n) ∧
  ∀ k N, (factorialPrefix (hierarchy b k) N).re≤
    ∑ n∈Finset.Icc 1 N,(Real.log n)^k

/-- One genuine unit-prime Euler control satisfies the entire positive
hierarchy at once, not a separately chosen model for each order. -/
theorem control_positiveUpperHierarchy : PositiveUpperHierarchy control :=
  ⟨control_hierarchy_bounds,control_factorialPrefix_le⟩

/-- The same deleted genuine prime violates every positive-order
unaltered Mobius/log-power equality. This is the precise extra data
which the tested upper/positivity class omits. -/
theorem control_fails_actual_at_every_positive_order :
    ∃ p : ℕ, p.Prime ∧ ∀ k : ℕ, 0<k →
      hierarchy control k p≠(lambda k p : ℂ) := by
  obtain ⟨p,hp,hdeleted⟩ := ArithmeticOperatorBinaryEulerControl.exists_deleted_prime
  refine ⟨p,hp,?_⟩
  intro k hk
  rw [control_hierarchy_eq,ArithmeticOperatorBinaryEulerControl.indicator_prime _ _ hp]
  simp only [ArithmeticOperatorBinaryPrimeControl.retainedBase,hdeleted,sub_self,
    Complex.ofReal_zero,zero_mul]
  have hpos : 0<(Real.log p)^k := pow_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) k
  rw [lambda_prime hk hp]
  exact Ne.symm (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))

/-- Every positive order has an exact integer Gamma-prefix witness of
failure. An upper bound is not substituted for the unchanged equality. -/
theorem control_fails_actual_Gamma {k : ℕ} (hk : 0<k) :
    ∃ N : ℕ, factorialPrefix (hierarchy control k) N≠
      (∑ n∈Finset.Icc 1 N,(Real.log n)^k : ℝ) := by
  by_contra h
  push Not at h
  obtain ⟨p,hp,hfailure⟩ := control_fails_actual_at_every_positive_order
  apply hfailure k hk
  exact (finite_prefix_injective (X := p)
    (fun N _ => (h N).trans (factorialPrefix_actual k N).symm) p hp.pos le_rfl).trans
      (hierarchy_actual k p)

/-- Full Mangoldt factorial sequence of the unit-prime control. All
ordinary prime powers are retained and the height phase is unchanged. -/
def controlMoments (k : ℕ) : ℂ :=
  ((10001/20000 : ℝ) : ℂ)^(k+1)*
    ∑' n, control n*zetaPrimeLogKernel k (3/2+Complex.I*54) n

/-- Exact coherent source, inherited from the convergent unit-prime
Euler system rather than an arbitrary density or fractional measure. -/
theorem controlMoments_source :
    Tendsto controlMoments atTop (𝓝 (-2)) := by
  unfold controlMoments control mangoldt
  simpa only [mul_assoc] using
    ArithmeticOperatorBinaryEulerControl.euler_control_source

/-- Cancelling the density germ does not remove the countermodel's
signed source. The actual-word pole/source preflight is already checked
in `ArithmeticOperatorSelbergSourceAudit`. -/
theorem control_centeredTrace_not_zero :
    ¬Tendsto (ArithmeticOperatorSelbergSourceAudit.centeredTrace
      (1/2+Complex.I*54) (10001/20000) controlMoments) atTop (𝓝 0) := by
  unfold controlMoments control mangoldt
  simpa only [mul_assoc] using
    ArithmeticOperatorSelbergSourceAudit.unit_control_centered_trace_not_zero

/-- All-order positivity and Gamma upper bounds cannot imply even the
absence of a coherent negative integral factorial source. The witness
is a genuine subset of the ordinary integer primes with unit Euler
factors, but not the unaltered actual Gamma-compatible sequence. -/
theorem all_order_upper_bounds_do_not_imply_noncoherence :
    ¬ (∀ b : ℕ → ℂ, PositiveUpperHierarchy b →
      ¬Tendsto (fun k => ((10001/20000 : ℝ) : ℂ)^(k+1)*
        ∑' n, b n*zetaPrimeLogKernel k (3/2+Complex.I*54) n)
        atTop (𝓝 (-2))) := by
  intro h
  exact h control control_positiveUpperHierarchy controlMoments_source

/-- Nor do those entire positive constraints pay the pole-centered
signed prime-minus-pair statistic. No physical mask completion or
actual-Gamma compatibility is claimed for the control. -/
theorem all_order_upper_bounds_do_not_pay_centered_trace :
    ¬ (∀ b : ℕ → ℂ, PositiveUpperHierarchy b →
      Tendsto (ArithmeticOperatorSelbergSourceAudit.centeredTrace
        (1/2+Complex.I*54) (10001/20000) (fun k =>
          ((10001/20000 : ℝ) : ℂ)^(k+1)*
            ∑' n, b n*zetaPrimeLogKernel k (3/2+Complex.I*54) n))
        atTop (𝓝 0)) := by
  intro h
  exact control_centeredTrace_not_zero (h control control_positiveUpperHierarchy)

end
end RiemannGaussian.ArithmeticOperatorSelbergHierarchyAudit
