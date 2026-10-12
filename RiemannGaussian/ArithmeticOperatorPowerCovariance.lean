/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorCommutatorAudit
import RiemannGaussian.SuzukiCarryFejer
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Cross-power valuation covariance gate

Different powers of one prime may be correlated before the height phase
is estimated. With uniformly bounded, physically supported carry packets,
their extra off-diagonal covariance is restricted to bases below the
square-root cutoff. The diagonal retains every proper prime power and
its literal phase. The new interaction is therefore source-small for
every exponent above one half, leaving the old signed one-column test.

This does not cover products of different prime columns, unbounded
valuation packets, or a growing weight that invalidates the stated bound.
-/

namespace RiemannGaussian.ArithmeticOperatorPowerCovariance
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter SuzukiCarryCorrelation

/-- Full exponent rectangle; all powers up to the dyadic physical cutoff
are retained before the exact support condition is imposed. -/
def orders (J : ℕ) : Finset ℕ := Finset.Icc 1 (2*J)

/-- A same-base valuation covariance, with the phase of the first actual
prime power still inside the exponent sum. -/
def covariance (P : Finset ℕ) (J : ℕ) (f : ℕ → ℕ → ℂ)
    (phase : ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)*
    (∑ r ∈ orders J, phase (p^r)*f p r)*conj (∑ r ∈ orders J, f p r)

/-- The exact same-exponent contribution, including proper prime powers. -/
def diagonal (P : Finset ℕ) (J : ℕ) (f : ℕ → ℕ → ℂ)
    (phase : ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)*
    ∑ r ∈ orders J, phase (p^r)*(‖f p r‖^2 : ℂ)

/-- All cross-exponent terms are joined before taking any norm. -/
def cross (P : Finset ℕ) (J : ℕ) (f : ℕ → ℕ → ℂ)
    (phase : ℕ → ℂ) : ℂ :=
  ∑ p ∈ P, (Real.log p : ℂ)*∑ r ∈ orders J,
    ∑ s ∈ (orders J).erase r, phase (p^r)*f p r*conj (f p s)

/-- Exact nonlinear prime-power bookkeeping; the phase is not replaced
by a phase on the base prime. The identity itself holds for arbitrary f. -/
theorem covariance_eq_diagonal_add_cross (P : Finset ℕ) (J : ℕ)
    (f : ℕ → ℕ → ℂ) (phase : ℕ → ℂ) :
    covariance P J f phase = diagonal P J f phase+cross P J f phase := by
  classical
  unfold covariance diagonal cross
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_assoc,← mul_add]
  congr 1
  rw [map_sum,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum,← Finset.sum_erase_add _ _ hr]
  rw [← Complex.ofReal_pow,Complex.sq_norm,← Complex.mul_conj]
  ring

/-- Outside the square-root cutoff every physically supported higher
power is exactly zero, independently of any primality assumption. -/
theorem higher_order_zero {J p r : ℕ} {f : ℕ → ℕ → ℂ}
    (hp : 2^J < p) (hr : 2 ≤ r)
    (hsupport : ∀ p r, 2^(2*J) < p^r → f p r = 0) : f p r = 0 := by
  apply hsupport
  calc
    2^(2*J) = (2^J)^2 := by rw [← pow_mul]; congr 1; omega
    _ < p^2 := Nat.pow_lt_pow_left hp (by omega)
    _ ≤ p^r := pow_le_pow_right' (by have := Nat.one_le_pow J 2 (by norm_num); omega) hr

/-- Literal cross covariance cannot see large prime bases: one of the
two distinct positive exponents must be at least two. -/
theorem cross_eq_small (P : Finset ℕ) (J : ℕ) (f : ℕ → ℕ → ℂ)
    (phase : ℕ → ℂ)
    (hsupport : ∀ p r, 2^(2*J) < p^r → f p r = 0) :
    cross P J f phase = cross (P.filter (fun p => p ≤ 2^J)) J f phase := by
  classical
  unfold cross
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpnot
  have hlarge : 2^J < p := by
    by_contra h
    exact hpnot (Finset.mem_filter.mpr ⟨hp,by omega⟩)
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro r hr
  apply Finset.sum_eq_zero
  intro s hs
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp (Finset.mem_erase.mp hs).2).1
  have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
  by_cases hrr : 2 ≤ r
  · rw [higher_order_zero hlarge hrr hsupport,mul_zero,zero_mul]
  · have hss : 2 ≤ s := by omega
    rw [higher_order_zero hlarge hss hsupport,map_zero,mul_zero]

/-- Explicit source-scale budget for the extra covariance, after its
exact small-base restriction. It retains arbitrary unit-bounded phases. -/
theorem norm_cross_le {P : Finset ℕ} {J : ℕ} {f : ℕ → ℕ → ℂ}
    {phase : ℕ → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hP : P ⊆ Finset.Icc 1 (2^(2*J)))
    (hf : ∀ p ∈ P, ∀ r ∈ orders J, ‖f p r‖ ≤ B)
    (hphase : ∀ n, ‖phase n‖ ≤ 1)
    (hsupport : ∀ p r, 2^(2*J) < p^r → f p r = 0) :
    ‖cross P J f phase‖ ≤
      B^2*((2*J : ℕ) : ℝ)^3*Real.log 2*(2 : ℝ)^J := by
  classical
  rw [cross_eq_small P J f phase hsupport]
  let Q := P.filter (fun p => p ≤ 2^J)
  have hcard : (Q.card : ℝ) ≤ (2 : ℝ)^J := by
    have hsub : Q ⊆ Finset.Icc 1 (2^J) := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp,hp2⟩
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hP hp)).1,hp2⟩
    exact_mod_cast (by simpa using Finset.card_le_card hsub : Q.card ≤ 2^J)
  have hlog (p : ℕ) (hp : p ∈ Q) : ‖(Real.log p : ℂ)‖ ≤ (2*J : ℕ)*Real.log 2 := by
    rcases Finset.mem_filter.mp hp with ⟨hp,hps⟩
    have hp1 : 1 ≤ p := (Finset.mem_Icc.mp (hP hp)).1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (Real.log_nonneg (by exact_mod_cast hp1))]
    have hh := Real.log_le_log (by exact_mod_cast (by omega : 0 < p))
      (show (p : ℝ) ≤ (2 : ℝ)^(2*J) by exact_mod_cast (Finset.mem_Icc.mp (hP hp)).2)
    simpa only [Real.log_pow] using hh
  have hterm (p r s : ℕ) (hp : p ∈ Q) (hr : r ∈ orders J) (hs : s ∈ orders J) :
      ‖phase (p^r)*f p r*conj (f p s)‖ ≤ B^2 := by
    have hpP := (Finset.mem_filter.mp hp).1
    rw [norm_mul,norm_mul,Complex.norm_conj]
    calc
      _ ≤ 1*B*B := mul_le_mul
        (mul_le_mul (hphase _) (hf p hpP r hr) (norm_nonneg _)
          (by norm_num)) (hf p hpP s hs) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hcount : ((orders J).card : ℝ) = (2*J : ℕ) := by simp [orders]
  have hin (p : ℕ) (hp : p ∈ Q) :
      ‖∑ r ∈ orders J, ∑ s ∈ (orders J).erase r,
        phase (p^r)*f p r*conj (f p s)‖ ≤ ((2*J : ℕ) : ℝ)^2*B^2 := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ r ∈ orders J, ((2*J : ℕ) : ℝ)*B^2 := by
        apply Finset.sum_le_sum
        intro r hr
        apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ s ∈ orders J, B^2 :=
            (Finset.sum_le_sum (fun s hs =>
              hterm p r s hp hr (Finset.mem_erase.mp hs).2)).trans
              (Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.erase_subset _ _) (fun _ _ _ => sq_nonneg B))
          _ = _ := by simp [hcount]
      _ = _ := by simp [hcount]; ring
  unfold cross
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ p ∈ Q, ((2*J : ℕ) : ℝ)*Real.log 2*
        (((2*J : ℕ) : ℝ)^2*B^2) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul (hlog p hp) (hin p hp) (norm_nonneg _) (by positivity)
    _ = (Q.card : ℝ)*(((2*J : ℕ) : ℝ)*Real.log 2*
        (((2*J : ℕ) : ℝ)^2*B^2)) := by simp
    _ ≤ _ := by
      calc
        _ ≤ (2 : ℝ)^J*(((2*J : ℕ) : ℝ)*Real.log 2*
            (((2*J : ℕ) : ℝ)^2*B^2)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = _ := by ring

/-- Cross-power multiplication cannot change the power-source limit of
any uniformly bounded literal-cutoff packet. This is an unconditional
arithmetic-scale no-go for this extra interaction, not a prime-sum bound. -/
theorem tendsto_scaled_cross {P : ℕ → Finset ℕ}
    {f : ℕ → ℕ → ℕ → ℂ} {phase : ℕ → ℂ} {B beta : ℝ}
    (hB : 0 ≤ B) (hbeta : 1/2 < beta)
    (hP : ∀ J, P J ⊆ Finset.Icc 1 (2^(2*J)))
    (hf : ∀ J p, p ∈ P J → ∀ r ∈ orders J, ‖f J p r‖ ≤ B)
    (hphase : ∀ n, ‖phase n‖ ≤ 1)
    (hsupport : ∀ J p r, 2^(2*J) < p^r → f J p r = 0) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      cross (P J) J (f J) phase) atTop (𝓝 0) := by
  let a := Real.exp (-2*beta*Real.log 2)
  let r := a*2
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have he : r = Real.exp ((1-2*beta)*Real.log 2) := by
      dsimp [r,a]
      calc
        _ = Real.exp (-2*beta*Real.log 2)*Real.exp (Real.log 2) := by
          rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    rw [he]
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  have ht : Tendsto (fun J : ℕ =>
      (8*B^2*Real.log 2)*((J : ℝ)^3*r^J)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_lt_one 3 hr0 hr1).const_mul
      (8*B^2*Real.log 2)
  apply squeeze_zero_norm (fun J => ?_) ht
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha]
  calc
    _ ≤ a^J*(B^2*((2*J : ℕ) : ℝ)^3*Real.log 2*(2 : ℝ)^J) :=
      mul_le_mul_of_nonneg_left
        (norm_cross_le hB (hP J) (hf J) hphase (hsupport J)) (pow_nonneg ha J)
    _ = _ := by dsimp [r]; rw [mul_pow]; push_cast; ring

/-- The diagonal is the exact old signed denominator statistic; extra
same-base valuation correlations have no campaign-scale source of their
own. Every proper-power diagonal phase remains in this theorem. -/
theorem tendsto_covariance_sub_diagonal {P : ℕ → Finset ℕ}
    {f : ℕ → ℕ → ℕ → ℂ} {phase : ℕ → ℂ} {B beta : ℝ}
    (hB : 0 ≤ B) (hbeta : 1/2 < beta)
    (hP : ∀ J, P J ⊆ Finset.Icc 1 (2^(2*J)))
    (hf : ∀ J p, p ∈ P J → ∀ r ∈ orders J, ‖f J p r‖ ≤ B)
    (hphase : ∀ n, ‖phase n‖ ≤ 1)
    (hsupport : ∀ J p r, 2^(2*J) < p^r → f J p r = 0) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      (covariance (P J) J (f J) phase-diagonal (P J) J (f J) phase))
      atTop (𝓝 0) := by
  simp_rw [covariance_eq_diagonal_add_cross,add_sub_cancel_left]
  exact tendsto_scaled_cross hB hbeta hP hf hphase hsupport

/-- Any persistent source in this covariance is exactly the source in
its one-column diagonal. Adding the cross-power interaction cannot
independently cancel or detect a new source at that scale. -/
theorem tendsto_covariance_of_diagonal {P : ℕ → Finset ℕ}
    {f : ℕ → ℕ → ℕ → ℂ} {phase : ℕ → ℂ} {B beta : ℝ} {c : ℂ}
    (hB : 0 ≤ B) (hbeta : 1/2 < beta)
    (hP : ∀ J, P J ⊆ Finset.Icc 1 (2^(2*J)))
    (hf : ∀ J p, p ∈ P J → ∀ r ∈ orders J, ‖f J p r‖ ≤ B)
    (hphase : ∀ n, ‖phase n‖ ≤ 1)
    (hsupport : ∀ J p r, 2^(2*J) < p^r → f J p r = 0)
    (hsource : Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      diagonal (P J) J (f J) phase) atTop (𝓝 c)) :
    Tendsto (fun J : ℕ => (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
      covariance (P J) J (f J) phase) atTop (𝓝 c) := by
  have ht := hsource.add (tendsto_scaled_cross hB hbeta hP hf hphase hsupport)
  simpa only [covariance_eq_diagonal_add_cross,mul_add,add_zero] using ht

/-- The actual finite Fejer carry packet satisfies the uniform hypothesis;
its bound uses the exact integer quotient remainder, not prime density. -/
theorem norm_fejer_value_le_one (A H d : ℕ) :
    ‖(SuzukiCarryFejer.value A H d : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real,Real.norm_eq_abs]
  by_cases hH : H = 0
  · simp [hH,SuzukiCarryFejer.value]
  · have hHR : (0 : ℝ) < H := by exact_mod_cast (Nat.pos_of_ne_zero hH)
    apply (SuzukiCarryFejer.abs_value_le_remainder A H d).trans
    exact (div_le_one hHR).mpr (by exact_mod_cast Nat.mod_le H d)

/-- Exact physical support of the same literal Fejer packet. No prime
power endpoint is removed before applying this theorem. -/
theorem fejer_value_zero_of_large {A H d : ℕ} (hd : 2*(A+2*H) < d) :
    SuzukiCarryFejer.value A H d = 0 := by
  unfold SuzukiCarryFejer.value
  have hh : (∑ t ∈ Finset.range H,
      ((SuzukiIntegerCarry.carry (A+t+H) d : ℝ)-
        SuzukiIntegerCarry.carry (A+t) d)) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have htH := Finset.mem_range.mp ht
    rw [SuzukiIntegerCarry.carry_eq_zero_of_lt (by omega : 2*(A+t+H) < d),
      SuzukiIntegerCarry.carry_eq_zero_of_lt (by omega : 2*(A+t) < d)]
    simp
  rw [hh,zero_div]

/-- Concrete literal-prime endpoint of the covariance audit. The
complete carry/valuation covariance and its all-power diagonal have
exactly the same campaign-scale source; the extra interaction dies. -/
theorem tendsto_fejer_covariance_sub_diagonal {A H : ℕ → ℕ}
    (hphysical : ∀ J, 2*(A J+2*H J) ≤ 2^(2*J))
    (y : ℝ) {beta : ℝ} (hbeta : 1/2 < beta) :
    Tendsto (fun J : ℕ =>
      (Real.exp (-2*beta*Real.log 2)^J : ℂ)*
        (covariance ((Finset.Icc 1 (2^(2*J))).filter Nat.Prime) J
            (fun p r => (SuzukiCarryFejer.value (A J) (H J) (p^r) : ℂ)) (primePhase y)-
          diagonal ((Finset.Icc 1 (2^(2*J))).filter Nat.Prime) J
            (fun p r => (SuzukiCarryFejer.value (A J) (H J) (p^r) : ℂ)) (primePhase y)))
      atTop (𝓝 0) := by
  apply tendsto_covariance_sub_diagonal (B := 1) (by norm_num) hbeta
  · intro J
    exact Finset.filter_subset _ _
  · intro J p _ r _
    exact norm_fejer_value_le_one _ _ _
  · intro n
    exact (norm_primePhase y n).le
  · intro J p r hr
    rw [fejer_value_zero_of_large ((hphysical J).trans_lt hr)]
    norm_num

end
end RiemannGaussian.ArithmeticOperatorPowerCovariance
