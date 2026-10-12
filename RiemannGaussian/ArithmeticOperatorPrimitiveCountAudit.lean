/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFareyFourierAudit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Native primitive counts retain super-source prime endpoint jumps

Frequency zero is the literal count of ordinary primitive residues. Even
after subtracting the discrete linear density with the SAME height phase,
every sufficiently large genuine prime forces a large adjacent-cutoff jump.
Thus a global unsmoothed sublinear norm allowance is false at every height.

This early rejection does not identify a zero-source asymptotic for this
frequency, import a totient Dirichlet continuation, or reject signed,
smoothed, incomplete or genuinely ordered multi-point observables.
-/

namespace RiemannGaussian.ArithmeticOperatorPrimitiveCountAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorFareyFourierAudit SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- Full native primitive population minus a matched discrete density;
every denominator and its unchanged fixed-height phase are retained. -/
def error (c y : ℝ) (N : ℕ) : ℂ :=
  packet N 0 (primePhase y)-
    (c : ℂ)*∑ q ∈ Finset.Icc 1 N,(q : ℂ)*primePhase y q

/-- Joining the complete primitive count leaves the exact totient atom. -/
theorem error_eq (c y : ℝ) (N : ℕ) :
    error c y N=∑ q ∈ Finset.Icc 1 N,
      ((q.totient : ℂ)-(c : ℂ)*q)*primePhase y q := by
  simp only [error,packet,fourierRow_zero,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- Exact adjacent-cutoff identity; no phase or endpoint is discarded. -/
theorem error_step (c y : ℝ) (N : ℕ) :
    error c y (N+1)-error c y N=
      (((N+1).totient : ℂ)-(c : ℂ)*(N+1))*primePhase y (N+1) := by
  rw [error_eq,error_eq,Finset.sum_Icc_succ_top (by omega)]
  push_cast
  ring

/-- Actual ordinary prime cutoffs have the full rigid native jump. -/
theorem error_prime_step (c y : ℝ) {p : ℕ} (hp : p.Prime) :
    error c y p-error c y (p-1)=
      ((p : ℂ)-1-(c : ℂ)*p)*primePhase y p := by
  have he : p-1+1=p := Nat.sub_add_cancel hp.one_le
  have hs := error_step c y (p-1)
  rw [he,Nat.totient_prime hp] at hs
  simpa only [Nat.cast_sub hp.one_le,Nat.cast_one,sub_add_cancel] using hs

/-- The prime jump is linear even after exact matched-phase density
subtraction. This uses actual primes, not a freely chosen row array. -/
theorem prime_jump_lower {c : ℝ} (hc : c≤2/3) (y : ℝ) {p : ℕ}
    (hp : p.Prime) (hp12 : 12≤p) :
    (p : ℝ)/4≤‖error c y p-error c y (p-1)‖ := by
  rw [error_prime_step c y hp,norm_mul,norm_primePhase,mul_one]
  have hc' : c*(p : ℝ)≤(2/3)*(p : ℝ) :=
    mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
  have hp' : (12 : ℝ)≤p := by exact_mod_cast hp12
  have he : ((p : ℂ)-1-(c : ℂ)*p)=((p : ℝ)-1-c*p : ℝ) := by push_cast; rfl
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  exact (by linarith : (p : ℝ)/4≤(p : ℝ)-1-c*p).trans (le_abs_self _)

/-- One of the two neighboring literal prefixes must pay the prime jump. -/
theorem prime_adjacent_cost {c : ℝ} (hc : c≤2/3) (y : ℝ) {p : ℕ}
    (hp : p.Prime) (hp12 : 12≤p) :
    (p : ℝ)/4≤‖error c y p‖+‖error c y (p-1)‖ :=
  (prime_jump_lower hc y hp hp12).trans (norm_sub_le _ _)

/-- Beyond EVERY head, one native prefix has a fixed linear norm cost.
No prime-count/PNT theorem or hypothetical-zero assumption is used. -/
theorem exists_native_linear_cost {c : ℝ} (hc : c≤2/3) (y : ℝ) (B : ℕ) :
    ∃ N : ℕ,B≤N ∧ 0<N ∧ (N : ℝ)/8≤‖error c y N‖ := by
  obtain ⟨p,hpB,hp⟩ := Nat.exists_infinite_primes (max (B+1) 12)
  have hp12 : 12≤p := (le_max_right _ _).trans hpB
  have hpB' : B+1≤p := (le_max_left _ _).trans hpB
  have hp0 : (0 : ℝ)<p := by exact_mod_cast hp.pos
  have he := prime_adjacent_cost hc y hp hp12
  by_cases hlarge : (p : ℝ)/8≤‖error c y p‖
  · exact ⟨p,by omega,hp.pos,hlarge⟩
  · refine ⟨p-1,by omega,by omega,?_⟩
    have hsub : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by
      rw [Nat.cast_sub hp.one_le,Nat.cast_one]
    rw [hsub]
    have hsmall : ‖error c y p‖<(p : ℝ)/8 := lt_of_not_ge hlarge
    linarith

/-- Unsmoothed native count error cannot even be o(N), at any height. -/
theorem not_tendsto_error_over_cutoff_zero {c : ℝ} (hc : c≤2/3) (y : ℝ) :
    ¬Tendsto (fun N : ℕ => ‖error c y N‖/(N : ℝ)) atTop (𝓝 0) := by
  intro ht
  have he : ∀ᶠ N : ℕ in atTop,‖error c y N‖/(N : ℝ)<1/8 :=
    (tendsto_order.mp ht).2 (1/8) (by norm_num)
  obtain ⟨B,hB⟩ := eventually_atTop.mp he
  obtain ⟨N,hBN,hN0,hcost⟩ := exists_native_linear_cost hc y B
  have hN : (0 : ℝ)<N := by exact_mod_cast hN0
  have hsmall := (div_lt_iff₀ hN).mp (hB N hBN)
  linarith

/-- No fixed sublinear power envelope can pay this full native prefix. -/
theorem not_eventually_subsource_bound {c : ℝ} (hc : c≤2/3) (y : ℝ)
    {beta : ℝ} (hb : beta<1) (C : ℝ) :
    ¬∀ᶠ N : ℕ in atTop,‖error c y N‖≤C*(N : ℝ)^beta := by
  intro he
  have ht : Tendsto (fun N : ℕ => C*(N : ℝ)^(beta-1)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (by linarith : 0<1-beta)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [neg_sub,Function.comp_apply,mul_zero] using hh.const_mul C
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖error c y N‖/(N : ℝ)≤C*(N : ℝ)^(beta-1) := by
    filter_upwards [he,eventually_ge_atTop 1] with N hN hN1
    have hpos : (0 : ℝ)<N := by exact_mod_cast (by omega : 0<N)
    calc
      _ ≤ C*(N : ℝ)^beta/(N : ℝ) := div_le_div_of_nonneg_right hN hpos.le
      _ = _ := by rw [Real.rpow_sub hpos,Real.rpow_one]; ring
  exact not_tendsto_error_over_cutoff_zero hc y
    (squeeze_zero' (Eventually.of_forall (fun N => by positivity)) hbound ht)

/-- The usual discrete primitive-count density lies within the rejected
range. Only the explicit constant is certified here, not a density asymptotic. -/
theorem standard_density_le : 6/Real.pi^2≤(2/3 : ℝ) := by
  have hp : (0 : ℝ)<Real.pi^2 := by positivity
  apply (div_le_iff₀ hp).mpr
  nlinarith [Real.pi_gt_three]

/-- The early rejection includes the usual centered primitive count at
every fixed phase height and every campaign power beta<1. -/
theorem standard_density_not_eventually_subsource (y : ℝ) {beta : ℝ}
    (hb : beta<1) (C : ℝ) :
    ¬∀ᶠ N : ℕ in atTop,‖error (6/Real.pi^2) y N‖≤C*(N : ℝ)^beta :=
  not_eventually_subsource_bound standard_density_le y hb C

end
end RiemannGaussian.ArithmeticOperatorPrimitiveCountAudit
