/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorCrtBoundaryAudit
import RiemannGaussian.ArithmeticOperatorTwistSourceAudit
import Mathlib.Data.ZMod.Basic

/-!
# Complete flat additive-lag averaging keeps the first cutoff, loses the second column

This audit completes the *lag* period, not the original row period. The
literal first-row endpoints and every second-row translate are retained.
For every first-row integer the second divisor hits exactly once. Thus the
entire signed joined statistic is a first-column quotient remainder; after
centering by the literal first-column count its extra channel is zero.

This freezes only complete flat lag averaging. Nonconstant lag codes,
incomplete lag periods, correlated lag masks and the actual cofactor phase
on the second row are not being averaged away or norm-paid.
-/

namespace RiemannGaussian.ArithmeticOperatorCrtLagAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorCrtBoundaryAudit ArithmeticOperatorGammaTwistAudit
open ArithmeticOperatorTwistSourceAudit SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- Divisibility is a single point of the literal translated residue period. -/
theorem lag_dvd_iff {e : ℕ} [NeZero e] (n : ℕ) (h : ZMod e) :
    e ∣ n+h.val ↔ h = -(n : ZMod e) := by
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add, ZMod.natCast_zmod_val]
  constructor
  · intro hh
    exact eq_neg_of_add_eq_zero_right hh
  · intro hh
    rw [hh, add_neg_cancel]

/-- No original row cutoff is completed here. Every row hits once,
including the zero lag and the last translate in the period. -/
theorem sum_lag_indicator {e : ℕ} [NeZero e] (n : ℕ) :
    (∑ h : ZMod e, if e ∣ n+h.val then (1 : ℂ) else 0) = 1 := by
  classical
  simp_rw [lag_dvd_iff]
  simp

/-- This identity also keeps an arbitrary signed/complex row kernel intact. -/
theorem flat_lag_row_join {e : ℕ} [NeZero e] (X : ℕ) (row : ℕ → ℂ) :
    (∑ h : ZMod e, ∑ n ∈ Finset.Icc 1 X,
      row n*(if e ∣ n+h.val then (1 : ℂ) else 0)) =
      ∑ n ∈ Finset.Icc 1 X, row n := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.mul_sum, sum_lag_indicator, mul_one]

private theorem incidenceCount_eq_sum (X h d e : ℕ) :
    (incidenceCount X h d e : ℂ) =
      ∑ n ∈ Finset.Icc 1 X, if d ∣ n ∧ e ∣ n+h then (1 : ℂ) else 0 := by
  classical
  rw [← Finset.sum_filter]
  simp [incidenceCount]

/-- Exact native two-column join on the full lag period. The first
column still has its literal floor, and every proper prime power is allowed. -/
theorem sum_lag_incidenceCount {e : ℕ} [NeZero e] (X d : ℕ) :
    (∑ h : ZMod e, (incidenceCount X h.val d e : ℂ)) = ((X/d : ℕ) : ℂ) := by
  classical
  simp_rw [incidenceCount_eq_sum]
  rw [Finset.sum_comm]
  have hc (n : ℕ) :
      (∑ h : ZMod e, if d ∣ n ∧ e ∣ n+h.val then (1 : ℂ) else 0) =
        if d ∣ n then 1 else 0 := by
    by_cases hd : d ∣ n
    · simp only [hd, true_and]
      exact sum_lag_indicator n
    · simp [hd]
  simp_rw [hc]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  convert Nat.Ioc_filter_dvd_card_eq_div X d using 1
  congr 2

/-- Flat lag average, still a literal integer cutoff. -/
def lagAverage {e : ℕ} [NeZero e] (X d : ℕ) : ℂ :=
  (∑ h : ZMod e, (incidenceCount X h.val d e : ℂ))/(e : ℂ)

theorem lagAverage_eq {e : ℕ} [NeZero e] (X d : ℕ) :
    lagAverage (e := e) X d = ((X/d : ℕ) : ℂ)/(e : ℂ) := by
  rw [lagAverage, sum_lag_incidenceCount]

/-- The joined boundary, centered only after summing the signed lag
period. This is NOT the sum of absolute CRT discrepancies. -/
def lagBoundary {e : ℕ} [NeZero e] (X d : ℕ) : ℂ :=
  lagAverage (e := e) X d-(X : ℂ)/((d : ℂ)*e)

theorem lagBoundary_eq {d e : ℕ} [NeZero e] (hd : d ≠ 0) (X : ℕ) :
    lagBoundary (e := e) X d =
      (((X/d : ℕ) : ℂ)-(X : ℂ)/(d : ℂ))/(e : ℂ) := by
  rw [lagBoundary, lagAverage_eq]
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have he0 : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne e)
  field_simp

/-- Centering by the *literal* first-column count annihilates the
entire extra two-column response, with no source or density distinction. -/
theorem sum_lag_literal_center_eq_zero {e : ℕ} [NeZero e] (X d : ℕ) :
    (∑ h : ZMod e, ((incidenceCount X h.val d e : ℂ)-
      ((X/d : ℕ) : ℂ)/(e : ℂ))) = 0 := by
  classical
  rw [Finset.sum_sub_distrib, sum_lag_incidenceCount]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have he0 : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne e)
  field_simp
  ring

private theorem finEquiv_natCast {e : ℕ} [NeZero e] (h : Fin e) :
    ZMod.finEquiv e h = (h.val : ZMod e) := by
  apply ZMod.val_injective e
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h.is_lt]
  cases e with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ e => rfl

/-- All compatible lags are counted, including shared-base prime powers
and the diagonal. The coprime-only successor mean must not be reused here. -/
theorem sum_compatible_lags {e : ℕ} [NeZero e] {g : ℕ} (hg : g ∣ e) :
    (∑ h : ZMod e, if g ∣ h.val then (1 : ℂ) else 0) = ((e/g : ℕ) : ℂ) := by
  classical
  have hs :
      (∑ h ∈ Finset.range e, if g ∣ h then (1 : ℂ) else 0) =
        ∑ h ∈ Finset.range e, if g ∣ h+1 then (1 : ℂ) else 0 := by
    have ha := Finset.sum_range_succ (fun h : ℕ => if g ∣ h then (1 : ℂ) else 0) e
    have hb := Finset.sum_range_succ' (fun h : ℕ => if g ∣ h then (1 : ℂ) else 0) e
    simp only [ite_eq_left hg, dvd_zero, ite_true] at ha hb
    exact add_right_cancel (ha.symm.trans hb)
  calc
    _ = ∑ h : Fin e, if g ∣ h.val then (1 : ℂ) else 0 := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv e).toEquiv
      intro h
      change (if g ∣ h.val then (1 : ℂ) else 0) =
        if g ∣ (ZMod.finEquiv e h).val then 1 else 0
      rw [finEquiv_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt h.is_lt]
    _ = ∑ h ∈ Finset.range e, if g ∣ h then (1 : ℂ) else 0 := by
      exact Fin.sum_univ_eq_sum_range (fun h : ℕ => if g ∣ h then (1 : ℂ) else 0) e
    _ = ∑ h ∈ Finset.range e, if g ∣ h+1 then (1 : ℂ) else 0 := hs
    _ = ((e/g : ℕ) : ℂ) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_multiples]

/-- The actual compatible CRT density at a general lag, not the
coprime-only mean for successor rows. -/
def compatibleMean (X h d e : ℕ) : ℂ :=
  if Nat.gcd d e ∣ h then (X : ℂ)/(Nat.lcm d e : ℂ) else 0

/-- The flat sum of the exact compatibility means has precisely the
one-column continuous density. No positivity or norm has been inserted. -/
theorem sum_lag_compatibleMean {d e : ℕ} [NeZero e] (hd : d ≠ 0) (X : ℕ) :
    (∑ h : ZMod e, compatibleMean X h.val d e) = (X : ℂ)/(d : ℂ) := by
  classical
  have hg := Nat.gcd_dvd_right d e
  have hg0 : Nat.gcd d e ≠ 0 := (Nat.gcd_pos_of_pos_left e (Nat.pos_of_ne_zero hd)).ne'
  have hl0 : Nat.lcm d e ≠ 0 := Nat.lcm_ne_zero hd (NeZero.ne e)
  have hprod : (Nat.gcd d e : ℂ)*(Nat.lcm d e : ℂ) = (d : ℂ)*e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have hdiv : ((e/Nat.gcd d e : ℕ) : ℂ)*(Nat.gcd d e : ℂ) = (e : ℂ) := by
    exact_mod_cast Nat.div_mul_cancel hg
  unfold compatibleMean
  have heq (h : ZMod e) :
      (if Nat.gcd d e ∣ h.val then (X : ℂ)/(Nat.lcm d e : ℂ) else 0) =
        (if Nat.gcd d e ∣ h.val then (1 : ℂ) else 0)*
          ((X : ℂ)/(Nat.lcm d e : ℂ)) := by split_ifs <;> simp
  simp_rw [heq]
  rw [← Finset.sum_mul, sum_compatible_lags hg]
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  have hgC : (Nat.gcd d e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg0
  have hlC : (Nat.lcm d e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl0
  have ha : ((e/Nat.gcd d e : ℕ) : ℂ)*(d : ℂ) = (Nat.lcm d e : ℂ) := by
    apply mul_left_cancel₀ hgC
    calc
      _ = (d : ℂ)*(((e/Nat.gcd d e : ℕ) : ℂ)*(Nat.gcd d e : ℂ)) := by ring
      _ = (d : ℂ)*e := by rw [hdiv]
      _ = (Nat.gcd d e : ℂ)*(Nat.lcm d e : ℂ) := hprod.symm
  field_simp
  linear_combination (X : ℂ)*ha

/-- Complete signed literal CRT boundary, still at the original cutoff.
Flat averaging leaves exactly the first quotient remainder, not a new
small pair-correlation error. -/
theorem sum_lag_crt_boundary {d e : ℕ} [NeZero e] (hd : d ≠ 0) (X : ℕ) :
    (∑ h : ZMod e, ((incidenceCount X h.val d e : ℂ)-
      compatibleMean X h.val d e)) =
        ((X/d : ℕ) : ℂ)-(X : ℂ)/(d : ℂ) := by
  rw [Finset.sum_sub_distrib, sum_lag_incidenceCount, sum_lag_compatibleMean hd]

/-- The surviving first-column kernel is deliberately unpaid. -/
def firstRemainder (X d : ℕ) : ℂ := ((X/d : ℕ) : ℂ)-(X : ℂ)/(d : ℂ)

/-- Joined boundary for arbitrary (even nonseparable) pair code. -/
def joinedBoundary (D E : Finset ℕ) (X : ℕ) (w v : ℕ → ℂ) (code : ℕ → ℕ → ℂ) : ℂ :=
  ∑ d ∈ D, ∑ e ∈ E, w d*v e*code d e*firstRemainder X d/(e : ℂ)

/-- The complete flat-lag join supplies one signed scalar profile even
for arbitrary nonseparable codes. No absolute value separates its terms. -/
theorem joinedBoundary_eq_scalar (D E : Finset ℕ) (X : ℕ)
    (w v : ℕ → ℂ) (code : ℕ → ℕ → ℂ) :
    joinedBoundary D E X w v code =
      ∑ d ∈ D, w d*(firstRemainder X d*
        ∑ e ∈ E, v e*code d e/(e : ℂ)) := by
  unfold joinedBoundary
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- A flat separable second-column code conserves the entire old
first-column packet, multiplying it by one scalar. -/
theorem joinedBoundary_separable (D E : Finset ℕ) (X : ℕ) (w v : ℕ → ℂ) :
    joinedBoundary D E X w v (fun _ _ => 1) =
      (∑ d ∈ D, w d*firstRemainder X d)*(∑ e ∈ E, v e/(e : ℂ)) := by
  rw [joinedBoundary_eq_scalar]
  simp only [mul_one]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Free bookkeeping cannot give an all-weight signed estimate unless
its complete joined scalar kernel vanishes. Actual Gamma constraints
have not been claimed for these arbitrary control arrays. -/
theorem joinedBoundary_bound_forall_weights_iff (D E : Finset ℕ) (X : ℕ)
    (v : ℕ → ℂ) (code : ℕ → ℕ → ℂ) (B : ℝ) :
    (∀ w : ℕ → ℂ, ‖joinedBoundary D E X w v code‖ ≤ B) ↔
      0 ≤ B ∧ ∀ d ∈ D, firstRemainder X d*
        (∑ e ∈ E, v e*code d e/(e : ℂ)) = 0 := by
  simp_rw [joinedBoundary_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

/-- The phased second column has its literal Mangoldt weight. This is
a prime-leg phase, not a silently substituted cofactor phase. -/
def partner (e : ℕ) (y : ℝ) : ℂ :=
  (ArithmeticFunction.vonMangoldt e : ℂ)*primePhase y e/(e : ℂ)

/-- Native flat-lag join against any complex row, with the second
prime-power phase retained exactly. -/
def phasedRowJoin {e : ℕ} [NeZero e] (X : ℕ) (y : ℝ) (row : ℕ → ℂ) : ℂ :=
  (ArithmeticFunction.vonMangoldt e : ℂ)*primePhase y e*
    (∑ h : ZMod e, ∑ n ∈ Finset.Icc 1 X,
      row n*(if e ∣ n+h.val then (1 : ℂ) else 0))/(e : ℂ)

theorem phasedRowJoin_eq {e : ℕ} [NeZero e] (X : ℕ) (y : ℝ) (row : ℕ → ℂ) :
    phasedRowJoin (e := e) X y row = partner e y*(∑ n ∈ Finset.Icc 1 X, row n) := by
  rw [phasedRowJoin, flat_lag_row_join]
  unfold partner
  ring

/-- The actual linear commutator remains the *same* unpaid packet
after adding the flat-lag column; this is not a new nonlinear source estimate. -/
theorem phased_commutator_cutoff {e : ℕ} [NeZero e] (X : ℕ) (y : ℝ) :
    phasedRowJoin (e := e) X y (twistCommutator (primePhase y)) =
      partner e y*cutoffDefect (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) y X := by
  rw [phasedRowJoin_eq]
  unfold cutoffDefect
  simp only [defect_eq_commutator]

theorem partner_ne_zero {e : ℕ} (he : e.Prime) (y : ℝ) : partner e y ≠ 0 := by
  unfold partner
  apply div_ne_zero
  · apply mul_ne_zero
    · rw [ArithmeticFunction.vonMangoldt_apply_prime he]
      exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast he.one_lt)).ne'
    · exact norm_ne_zero_iff.mp (by rw [norm_primePhase]; norm_num)
  · exact Nat.cast_ne_zero.mpr he.ne_zero

/-- The genuine old Euler source is conserved, not independently
controlled, at every actual multiplicity. No native pair boundary source
is inferred from a linear Chebyshev diagnostic here. -/
theorem phased_commutator_actual_source (rho : NontrivialZetaZero) (e : ℕ) :
    Tendsto (fun z : ℂ => (z-rho.1)*(partner e rho.1.im*response rho.1.im z))
      (𝓝[≠] rho.1) (𝓝 (partner e rho.1.im*
        (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ)))) := by
  have hh := (tendsto_commutator_source rho).const_mul (partner e rho.1.im)
  convert hh using 1
  ext z
  ring

theorem phased_commutator_actual_source_ne_zero (rho : NontrivialZetaZero)
    {e : ℕ} (he : e.Prime) :
    partner e rho.1.im*
      (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ)) ≠ 0 :=
  mul_ne_zero (partner_ne_zero he _) (commutator_source_ne_zero rho)

/-- Density centering retains the old source as well; it creates no
new flat-lag arithmetic restriction. The power-response identity is only
a source/pole diagnostic, not a literal cutoff asymptotic. -/
theorem phased_commutator_code_source_ne_zero (rho : NontrivialZetaZero)
    {e : ℕ} (he : e.Prime) {H : ℝ} (hH : 0 < H) :
    partner e rho.1.im*
      ((-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ))*
        (∑ i ∈ Finset.range 4, poleCode (1-I*rho.1.im) 1 i*
          ArithmeticOperatorDilationAudit.powerResponse (rho.1.re : ℂ) ((2 : ℝ)^i*H))) ≠ 0 :=
  mul_ne_zero (partner_ne_zero he _) (matched_commutator_code_nonzero rho hH)

/-- The centered extra row channel is identically zero even when the
row retains all actual Gamma/Mangoldt data and cofactor correlations.
It therefore annihilates every source, not just density. -/
theorem flat_lag_extra_row_eq_zero {e : ℕ} [NeZero e] (X : ℕ) (row : ℕ → ℂ) :
    (∑ h : ZMod e, ∑ n ∈ Finset.Icc 1 X,
      row n*((if e ∣ n+h.val then (1 : ℂ) else 0)-1/(e : ℂ))) = 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro n _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_lag_indicator]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have he0 : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne e)
  field_simp
  ring

/-- Exact guard against extending the flat audit to nonconstant codes:
the second row evaluates the code at the *selected* lag, not its mean.
An actual second-cofactor phase can depend on this selected lag. -/
theorem coded_lag_indicator {e : ℕ} [NeZero e] (n : ℕ) (code : ZMod e → ℂ) :
    (∑ h : ZMod e, code h*(if e ∣ n+h.val then (1 : ℂ) else 0)) =
      code (-(n : ZMod e)) := by
  classical
  simp_rw [lag_dvd_iff, mul_ite, mul_one, mul_zero]
  simp

/-- Row-dependent correlated codes and every translate remain explicit;
the flat cancellation is unavailable unless this selected value is constant. -/
theorem coded_lag_row_join {e : ℕ} [NeZero e] (X : ℕ)
    (row : ℕ → ℂ) (code : ℕ → ZMod e → ℂ) :
    (∑ h : ZMod e, ∑ n ∈ Finset.Icc 1 X,
      row n*code n h*(if e ∣ n+h.val then (1 : ℂ) else 0)) =
      ∑ n ∈ Finset.Icc 1 X, row n*code n (-(n : ZMod e)) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, coded_lag_indicator]

end
end RiemannGaussian.ArithmeticOperatorCrtLagAudit
