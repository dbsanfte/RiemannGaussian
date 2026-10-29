/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimePublicReportPolynomial

/-! # Actual scheduled scalar dimensions have a fixed polynomial envelope
The executable fast guard supplies all auxiliary dimension bounds. Balanced
heads and scopes are coarsened here only inside scalar preprocessing resources,
never in their exponential traversal terms.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeScheduledScalarBudget
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters
open SemiprimeScheduledFactorExecution SemiprimePublicBudgetDimensions
open SemiprimePublicCounterBudget

/-- The actual finite sample, group and degree dimensions are at most n. -/
theorem schedule_dimensions_le (N : ℕ) (hg : fastGuard N) :
    groups N ≤ wireCount N ∧ points N ≤ wireCount N ∧ degree N ≤ wireCount N := by
  rcases hg with ⟨_,_,hr,hQ,_,hRQ,_,_,_,hh,_,_⟩
  have hrr : groups N ≤ (groups N)^2 := Nat.le_self_pow (by decide) _
  have hrr16 : (groups N)^2 ≤ 16*points N*(groups N)^2 := by
    simpa only [one_mul] using Nat.mul_le_mul_right ((groups N)^2)
      (show 1 ≤ 16*points N by omega)
  have hq : points N ≤ points N*(groups N)^2 := by
    simpa only [mul_one] using Nat.mul_le_mul_left (points N)
      (Nat.one_le_pow 2 (groups N) (by omega))
  have hq16 : points N*(groups N)^2 ≤ 16*points N*(groups N)^2 :=
    Nat.mul_le_mul_right ((groups N)^2) (by omega)
  exact ⟨hrr.trans (hrr16.trans hh),hq.trans (hq16.trans hh),by omega⟩

/-- Positive rational tolerance excludes a zero source denominator. -/
theorem denominator_pos (N : ℕ) (hg : fastGuard N) : 0<groups N*lambda N := by
  have he := hg.2.2.2.2.2.2.1
  by_contra hn
  have hz : groups N*lambda N=0 := Nat.eq_zero_of_not_pos hn
  simp only [epsilon,hz,Nat.cast_zero,div_zero] at he
  exact (lt_irrefl (0 : ℚ)) he

/-- The actual incidence-load guard bounds both paid finite alphabets. -/
theorem alphabets_le (N : ℕ) (hg : fastGuard N) :
    (groups N)^(2*points N) ≤ 2*wireCount N ∧
      (groups N)^(points N) ≤ 2*wireCount N := by
  have hd := denominator_pos N hg
  rcases hg with ⟨_,_,hr,_,_,_,_,_,hl,_,_,_⟩
  have hs : 1 ≤ (groups N*lambda N)^2 := Nat.one_le_pow 2 _ hd
  have hc : 1 ≤ 4*(2+scopeBound (bitLength N))*(groups N*lambda N)^2 := by
    simpa only [one_mul] using Nat.mul_le_mul
      (show 1 ≤ 4*(2+scopeBound (bitLength N)) by omega) hs
  have hload : 4*(2+scopeBound (bitLength N))*((groups N)^(2*points N))^2*
      (groups N*lambda N)^2 ≤ 2*wireCount N := by
    simpa only [SemiprimeCounterRate.scheduledDimension,groups,points,lambda] using hl
  have hp : ((groups N)^(2*points N))^2 ≤ 
      (4*(2+scopeBound (bitLength N))*(groups N*lambda N)^2)*
        ((groups N)^(2*points N))^2 := by
    simpa only [one_mul] using Nat.mul_le_mul_right
      (((groups N)^(2*points N))^2) hc
  have hsq : ((groups N)^(2*points N))^2 ≤ 2*wireCount N := by
    nlinarith only [hp,hload]
  have hD : (groups N)^(2*points N) ≤ 2*wireCount N :=
    (Nat.le_self_pow (by decide) _).trans hsq
  have hA : (groups N)^(points N) ≤ (groups N)^(2*points N) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact ⟨hD,hA.trans hD⟩

/-- A coarse head ceiling bound is safe only for scalar preprocessing. -/
theorem head_scalar_le (N : ℕ) (hg : fastGuard N) : headBound N ≤ 2*wireCount N := by
  have hr : 2 ≤ groups N := hg.2.2.1
  have hrq : (0 : ℚ)<2*(groups N : ℚ) := by exact_mod_cast (show 0<2*groups N by omega)
  unfold headBound
  apply Nat.ceil_le.mpr
  rw [div_le_iff₀ hrq]
  push_cast
  have hr' : (2 : ℚ) ≤ groups N := by exact_mod_cast hr
  have hn : (0 : ℚ) ≤ wireCount N := by positivity
  have hm := mul_nonneg hn (sub_nonneg.mpr hr')
  nlinarith only [hn,hm]

/-- Literal inclusive support precision is bounded with no new cutoff advice. -/
theorem precision_scalar_le (N : ℕ) (hg : fastGuard N) :
    precision N ≤ 2*(wireCount N)^2+1 := by
  have hR := (schedule_dimensions_le N hg).2.2
  have hd := Nat.div_le_self (2*wireCount N*degree N) (points N)
  have hm := Nat.mul_le_mul_left (2*wireCount N) hR
  unfold precision
  nlinarith only [hd,hm]

/-- One fixed scalar resource polynomial, leaving entry and decoder envelopes
as their already explicit fixed-polynomial definitions. -/
def scalarEnvelope (n : ℕ) : ℕ :=
  20*n+2*n^2+5+entryEnvelope n+scopeEnvelope n+decoderEnvelope n

/-- The ACTUAL scheduled scalar resource sum fits the stated polynomial.
No new finite-menu, factor-dimension or head-size advice is supplied. -/
theorem scalarResources_le (N : ℕ) (hN : 0<N) (hg : fastGuard N) :
    SemiprimePublicReportPolynomial.scalarResources N ≤ scalarEnvelope (wireCount N) := by
  have hF := factorCount_le N hN
  have hd := schedule_dimensions_le N hg
  have ha := alphabets_le N hg
  have hh := head_scalar_le N hg
  have hp := precision_scalar_le N hg
  have hw := scope_le N hN
  unfold SemiprimePublicReportPolynomial.scalarResources scalarEnvelope
  omega

end RiemannGaussian.SemiprimeScheduledScalarBudget
