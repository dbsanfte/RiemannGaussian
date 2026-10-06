/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryGramSource

/-!
# Exact Fejer localization of literal carry packets

Triangular coefficients average complete flat packets. Periodicity and an
exact exchange of the two window lengths bound their small-denominator
kernel, without a generic norm of the whole gcd matrix. This localization
does not bound the centered signed mass at the surviving arithmetic scale.
-/

namespace RiemannGaussian.SuzukiCarryFejer
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set SuzukiIntegerCarry SuzukiCarryCorrelation SuzukiCarryGram SuzukiCarryGramSource
open Filter
open scoped Topology

/-- The triangular coefficient packet, expressed as an average of flat intervals. -/
def coefficient (A H N : ℕ) : ℂ :=
  (H : ℂ)⁻¹ * ∑ t ∈ Finset.range H,
    if A+t ≤ N ∧ N < A+t+H then 1 else 0

/-- The identical packet after telescoping its inner factorial increments. -/
def value (A H d : ℕ) : ℝ :=
  (∑ t ∈ Finset.range H, ((carry (A+t+H) d : ℝ)-(carry (A+t) d : ℝ))) / H

private theorem packet_mul_coeff (S : Finset ℕ) (alpha : ℕ → ℂ) (c : ℂ) (d : ℕ) :
    packet S (fun N => c*alpha N) d = c*packet S alpha d := by
  unfold packet
  simp_rw [mul_assoc]
  rw [Finset.mul_sum]

private theorem packet_sum_coeff (S T : Finset ℕ) (b : ℕ → ℕ → ℂ) (d : ℕ) :
    packet S (fun N => ∑ t ∈ T, b t N) d = ∑ t ∈ T, packet S (b t) d := by
  unfold packet
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Exact identification with the finite-support Gram packet; all repeated
incidences are collected in the same coefficient rather than discarded. -/
theorem packet_eq_value (A H d : ℕ) :
    packet (Finset.range (A+2*H)) (coefficient A H) d = (value A H d : ℂ) := by
  classical
  have hrow (t : ℕ) (ht : t ∈ Finset.range H) :
      packet (Finset.range (A+2*H))
        (fun N => if A+t ≤ N ∧ N < A+t+H then 1 else 0) d =
      packet (Finset.Ico (A+t) (A+t+H)) (fun _ => 1) d := by
    have hfilter : (Finset.range (A+2*H)).filter (fun N => A+t ≤ N ∧ N < A+t+H) =
        Finset.Ico (A+t) (A+t+H) := by
      ext N
      have := Finset.mem_range.mp ht
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    unfold packet
    rw [← hfilter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro N _
    by_cases hn : A+t ≤ N ∧ N < A+t+H
    · simp only [if_pos hn, one_mul]
    · simp only [if_neg hn, zero_mul]
  change packet (Finset.range (A+2*H))
    (fun N => (H : ℂ)⁻¹ * ∑ t ∈ Finset.range H,
      if A+t ≤ N ∧ N < A+t+H then 1 else 0) d = _
  rw [packet_mul_coeff, packet_sum_coeff]
  have hsum : (∑ t ∈ Finset.range H,
      packet (Finset.range (A+2*H))
        (fun N => if A+t ≤ N ∧ N < A+t+H then 1 else 0) d) =
      (((∑ t ∈ Finset.range H, ((carry (A+t+H) d : ℝ)-(carry (A+t) d : ℝ))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [hrow t ht, packet_interval_eq (by omega)]
  rw [hsum]
  unfold value
  push_cast
  ring

private theorem window_exchange (f : ℕ → ℝ) (H r : ℕ) :
    (∑ t ∈ Finset.range H, (f (t+r)-f t)) =
      ∑ t ∈ Finset.range r, (f (t+H)-f t) := by
  have h1 := Finset.sum_range_add f r H
  have h2 := Finset.sum_range_add f H r
  have hh1 : (∑ t ∈ Finset.range H, f (t+r)) = ∑ t ∈ Finset.range H, f (r+t) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.add_comm]
  have hh2 : (∑ t ∈ Finset.range r, f (t+H)) = ∑ t ∈ Finset.range r, f (H+t) := by
    apply Finset.sum_congr rfl
    intro t _
    rw [Nat.add_comm]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [Nat.add_comm r H] at h1
  linarith

/-- The small-denominator Fejer amplitude is suppressed by the exact
remainder `H mod d`. Complete denominator periods cost zero. -/
theorem abs_value_le_remainder (A H d : ℕ) :
    |value A H d| ≤ (H%d : ℕ)/(H : ℝ) := by
  have hp (t : ℕ) : carry (A+t+H) d = carry (A+t+H%d) d := by
    rw [show A+t+H = A+t+H%d+d*(H/d) by
      have h := Nat.mod_add_div H d
      omega, carry_add_multiple_period]
  have hnum : (∑ t ∈ Finset.range H, ((carry (A+t+H) d : ℝ)-(carry (A+t) d : ℝ))) =
      ∑ t ∈ Finset.range (H%d), ((carry (A+t+H) d : ℝ)-(carry (A+t) d : ℝ)) := by
    calc
      _ = ∑ t ∈ Finset.range H, ((carry (A+t+H%d) d : ℝ)-(carry (A+t) d : ℝ)) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [hp]
      _ = _ := by
        simpa only [Nat.add_assoc] using
          window_exchange (fun t => (carry (A+t) d : ℝ)) H (H%d)
  have hbound : |∑ t ∈ Finset.range (H%d),
      ((carry (A+t+H) d : ℝ)-(carry (A+t) d : ℝ))| ≤ (H%d : ℕ) := by
    have hnorm : |∑ t ∈ Finset.range (H%d), ((carry (A+t+H) d : ℝ)-(carry (A+t) d : ℝ))| ≤
        ∑ t ∈ Finset.range (H%d), |(carry (A+t+H) d : ℝ)-(carry (A+t) d : ℝ)| := by
      simpa only [Real.norm_eq_abs] using
        norm_sum_le (Finset.range (H%d)) (fun t => (carry (A+t+H) d : ℝ)-(carry (A+t) d : ℝ))
    apply hnorm.trans
    calc
      _ ≤ ∑ _t ∈ Finset.range (H%d), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        rcases carry_eq_zero_or_one (A+t+H) d with h1 | h1 <;>
          rcases carry_eq_zero_or_one (A+t) d with h2 | h2 <;> norm_num [h1, h2]
      _ = _ := by simp
  unfold value
  rw [hnum, abs_div, abs_of_nonneg (show 0 ≤ (H : ℝ) from Nat.cast_nonneg H)]
  exact div_le_div_of_nonneg_right hbound (Nat.cast_nonneg H)

/-- The actual Gram weight has an independently proved squared localization
bound. No prime height or absolute matrix budget has been used. -/
theorem packetMass_le_remainder (A H d : ℕ) :
    packetMass (Finset.range (A+2*H)) (coefficient A H) d ≤
      ((H%d : ℕ)/(H : ℝ))^2 := by
  rw [packetMass, packet_eq_value]
  have h := abs_value_le_remainder A H d
  rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h

/-- Every divisor of the packet length is removed exactly, not just in a
continuum limit or after averaging a prime-density model. -/
theorem packet_eq_zero_of_dvd {A H d : ℕ} (hd : d ∣ H) :
    packet (Finset.range (A+2*H)) (coefficient A H) d = 0 := by
  have h := abs_value_le_remainder A H d
  rw [Nat.mod_eq_zero_of_dvd hd, Nat.cast_zero, zero_div] at h
  have hz : value A H d = 0 := by have := abs_le.mp h; linarith
  rw [packet_eq_value, hz, Complex.ofReal_zero]

/-- The first triangular coefficient is nonzero whenever the packet length is positive. -/
theorem coefficient_first {H : ℕ} (hH : 0 < H) (A : ℕ) :
    coefficient A H A = (H : ℂ)⁻¹ := by
  unfold coefficient
  rw [Finset.sum_eq_single 0]
  · simp [hH]
  · intro t _ ht
    have hh : ¬(A+t ≤ A ∧ A < A+t+H) := by omega
    rw [if_neg hh]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hH))

/-- Localization does not destroy matched power-source sensitivity:
the same literal triangular coefficients have strictly positive response. -/
theorem matched_sourceCoefficient_pos {H : ℕ} (hH : 0 < H) (A : ℕ)
    {beta : ℝ} (hb : 0 < beta) :
    0 < sourceCoefficient (Finset.range (A+2*H)) (coefficient A H) beta := by
  apply sourceCoefficient_pos_of_nonzero hb
  refine ⟨A, Finset.mem_range.mpr (by omega), ?_⟩
  rw [coefficient_first hH A]
  exact inv_ne_zero (by exact_mod_cast hH.ne')

/-- The same finite triangular coefficients telescope in the continuous
denominator variable used for the power-mode preflight. -/
theorem realPacket_eq_average (A H : ℕ) (v : ℝ) :
    realPacket (Finset.range (A+2*H)) (coefficient A H) v =
      (((∑ t ∈ Finset.range H, (realCarry (A+t+H) v-realCarry (A+t) v))/H : ℝ) : ℂ) := by
  classical
  have hrow (t : ℕ) (ht : t ∈ Finset.range H) :
      (∑ N ∈ Finset.range (A+2*H),
        (if A+t ≤ N ∧ N < A+t+H then (1 : ℂ) else 0)*(realIncidence N v : ℂ)) =
      ((realCarry (A+t+H) v-realCarry (A+t) v : ℝ) : ℂ) := by
    have hfilter : (Finset.range (A+2*H)).filter (fun N => A+t ≤ N ∧ N < A+t+H) =
        Finset.Ico (A+t) (A+t+H) := by
      ext N
      have := Finset.mem_range.mp ht
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    have he := realPacket_interval_eq (A := A+t) (B := A+t+H) (by omega) v
    rw [realPacket, ← hfilter, Finset.sum_filter] at he
    convert he using 1
    apply Finset.sum_congr rfl
    intro N _
    by_cases hn : A+t ≤ N ∧ N < A+t+H <;> simp [hn]
  unfold realPacket coefficient
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have he : (∑ t ∈ Finset.range H, ∑ N ∈ Finset.range (A+2*H),
      (if A+t ≤ N ∧ N < A+t+H then (1 : ℂ) else 0)*(realIncidence N v : ℂ)) =
      (((∑ t ∈ Finset.range H, (realCarry (A+t+H) v-realCarry (A+t) v)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl hrow
  rw [he]
  push_cast
  ring

/-- A fixed macroscopic cell detects the triangular packet uniformly in
its growing length; this is stronger than finite-packet positivity. -/
theorem realMass_on_macroscopic_cell {H : ℕ} (hH : 2 ≤ H) {v : ℝ}
    (hv : v ∈ Ioo (Real.log (4*(H : ℝ))) (Real.log ((9/2 : ℝ)*H))) :
    (1/9 : ℝ) ≤ realMass (Finset.range (H+2*H)) (coefficient H H) v := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hlo : 4*(H : ℝ) < Real.exp v := (Real.log_lt_iff_lt_exp (by positivity)).mp hv.1
  have hhi : Real.exp v < (9/2 : ℝ)*H := (Real.lt_log_iff_exp_lt (by positivity)).mp hv.2
  have hz (t : ℕ) (ht : t ∈ Finset.range H) : realCarry (H+t) v = 0 := by
    have htR : (t : ℝ) < H := by exact_mod_cast Finset.mem_range.mp ht
    exact realCarry_zero_of_large (by push_cast; linarith)
  have ho (t : ℕ) (ht : t ∈ Finset.Ico ((H+1)/2) H) :
      realCarry (H+t+H) v = 1 := by
    have hb := Finset.mem_Ico.mp ht
    have htlo : H ≤ 2*t := by omega
    have hr1 : (t : ℝ) < H := by exact_mod_cast hb.2
    have hr2 : (H : ℝ) ≤ 2*t := by exact_mod_cast htlo
    exact realCarry_one_on_cell (by push_cast; linarith) (by push_cast; linarith)
  have hsum : ((H-(H+1)/2 : ℕ) : ℝ) ≤
      ∑ t ∈ Finset.range H, (realCarry (H+t+H) v-realCarry (H+t) v) := by
    calc
      _ = ∑ _t ∈ Finset.Ico ((H+1)/2) H, (1 : ℝ) := by simp
      _ = ∑ t ∈ Finset.Ico ((H+1)/2) H, (realCarry (H+t+H) v-realCarry (H+t) v) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [ho t ht, hz t (Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2), sub_zero]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (by intro t ht; exact Finset.mem_range.mpr (Finset.mem_Ico.mp ht).2)
        (by intro t ht _; rw [hz t ht, sub_zero]; exact realCarry_nonneg _ _)
  have hcount : (H : ℝ)/3 ≤ ((H-(H+1)/2 : ℕ) : ℝ) := by
    have hn : H ≤ 3*(H-(H+1)/2) := by omega
    have hr : (H : ℝ) ≤ 3*((H-(H+1)/2 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hav : (1/3 : ℝ) ≤
      (∑ t ∈ Finset.range H, (realCarry (H+t+H) v-realCarry (H+t) v))/(H : ℝ) := by
    exact (le_div_iff₀ hHR).mpr (by linarith)
  rw [realMass, realPacket_eq_average, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith

/-- The matched Fejer power coefficient is uniformly source-sized:
it is at least `log(9/8)/9 * H^beta` on every growing literal packet.
No actual-zero asymptotic is inferred from this diagnostic inequality. -/
theorem sourceCoefficient_uniform_lower {H : ℕ} (hH : 2 ≤ H) {beta : ℝ} (hb : 0 < beta) :
    Real.log (9/8 : ℝ)/9 * Real.exp (beta*Real.log H) ≤
      sourceCoefficient (Finset.range (H+2*H)) (coefficient H H) beta := by
  let a := Real.log (4*(H : ℝ))
  let b := Real.log ((9/2 : ℝ)*H)
  let c := Real.exp (beta*Real.log H)/9
  have hHR : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hab : a < b := Real.log_lt_log (by positivity) (by linarith)
  have hi : Integrable ((Ioo a b).indicator (fun _ : ℝ => c)) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (integrableOn_const (by simp))
  have he : (∫ v : ℝ, (Ioo a b).indicator (fun _ : ℝ => c) v) = (b-a)*c := by
    rw [integral_indicator_const _ measurableSet_Ioo]
    simp [hab.le, smul_eq_mul]
  have hdiff : b-a = Real.log (9/8 : ℝ) := by
    dsimp [a, b]
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
    norm_num
  have hle : (∫ v : ℝ, (Ioo a b).indicator (fun _ : ℝ => c) v) ≤
      sourceCoefficient (Finset.range (H+2*H)) (coefficient H H) beta := by
    apply integral_mono hi (integrable_source hb (fun N hN => (Finset.mem_range.mp hN).le))
    intro v
    by_cases hv : v ∈ Ioo a b
    · rw [Set.indicator_of_mem hv]
      have hvH : Real.log H ≤ v :=
        (Real.log_le_log hHR (by linarith : (H : ℝ) ≤ 4*H)).trans hv.1.le
      have hs := realMass_on_macroscopic_cell hH hv
      change c ≤ Real.exp (beta*v)*realMass _ _ v
      calc
        c = Real.exp (beta*Real.log H)*(1/9 : ℝ) := by dsimp [c]; ring
        _ ≤ Real.exp (beta*v)*realMass _ _ v := mul_le_mul
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvH hb.le)) hs (by norm_num)
          (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem hv]
      exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  rw [he, hdiff] at hle
  simpa only [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hle

/-- The literal small-denominator part of the already joined quadratic.
The height phase is retained through the finite packet join. -/
def lowPacket (A H D : ℕ) (y : ℝ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D, (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
    (packetMass (Finset.range (A+2*H)) (coefficient A H) d : ℂ)

/-- The exact unpaid complement on the full physical support; it keeps
the same coefficient packet and phase, not a surrogate prime density. -/
def highPacket (A H D : ℕ) (y : ℝ) : ℂ :=
  ∑ d ∈ (Finset.Icc 1 (2*(A+2*H))).filter (fun d => D < d),
    (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
      (packetMass (Finset.range (A+2*H)) (coefficient A H) d : ℂ)

/-- The complete quadratic splits exactly into the paid low-denominator
sector and the explicit, still-signed high-denominator sector. -/
theorem fullQuadratic_eq_low_high {A H D : ℕ} (hD : D ≤ 2*(A+2*H)) (y : ℝ) :
    fullQuadratic (Finset.range (A+2*H)) (coefficient A H) (primePhase y) =
      lowPacket A H D y+highPacket A H D y := by
  classical
  rw [fullQuadratic_eq_quadratic (X := 2*(A+2*H)) _ _ _ (fun N hN => by
    have := Finset.mem_range.mp hN
    omega), primePhase_quadratic_eq_joined]
  have hfilter : (Finset.Icc 1 (2*(A+2*H))).filter (fun d => d ≤ D) = Finset.Icc 1 D := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (2*(A+2*H))) (fun d => d ≤ D)
    (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
      (packetMass (Finset.range (A+2*H)) (coefficient A H) d : ℂ))
  simpa only [hfilter, not_le, lowPacket, highPacket] using he.symm

/-- An independent arithmetic estimate for the small-denominator sector,
using the exact Fejer remainder and the literal Chebyshev mass bound.
This is not a budget for the whole central quadratic. -/
theorem norm_lowPacket_le {H : ℕ} (hH : 0 < H) (A D : ℕ) (y : ℝ) :
    ‖lowPacket A H D y‖ ≤ (Real.log 4+4)*(D : ℝ)*((D : ℝ)/H)^2 := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hmass (d : ℕ) (hd : d ∈ Finset.Icc 1 D) :
      packetMass (Finset.range (A+2*H)) (coefficient A H) d ≤ ((D : ℝ)/H)^2 := by
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hm : H%d ≤ D := (Nat.mod_lt H hdpos).le.trans (Finset.mem_Icc.mp hd).2
    apply (packetMass_le_remainder A H d).trans
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm) hHR.le
  have hpsi : (∑ d ∈ Finset.Icc 1 D, ArithmeticFunction.vonMangoldt d) ≤
      (Real.log 4+4)*(D : ℝ) := by
    have h := Chebyshev.psi_le_const_mul_self (x := (D : ℝ)) (Nat.cast_nonneg D)
    simpa only [Chebyshev.psi, Nat.floor_natCast,
      ← Finset.Icc_add_one_left_eq_Ioc, zero_add] using h
  unfold lowPacket
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D, ArithmeticFunction.vonMangoldt d*((D : ℝ)/H)^2 := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, norm_mul, norm_primePhase, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (packetMass_nonneg _ _ _)]
      exact mul_le_mul_of_nonneg_left (hmass d hd) ArithmeticFunction.vonMangoldt_nonneg
    _ = (∑ d ∈ Finset.Icc 1 D, ArithmeticFunction.vonMangoldt d)*((D : ℝ)/H)^2 := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpsi (sq_nonneg _)

/-- Square-scale packets pay every prime power at most `N` with an actual
`1/N` saving, uniformly in the location and the fixed height. -/
theorem norm_squareScale_lowPacket_le {N : ℕ} (hN : 0 < N) (A : ℕ) (y : ℝ) :
    ‖lowPacket A (N^2) N y‖ ≤ (Real.log 4+4)/(N : ℝ) := by
  apply (norm_lowPacket_le (pow_pos hN 2) A N y).trans_eq
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

/-- The paid small-denominator sector tends to zero absolutely, with no
zero hypothesis and no discarded prime-power or height phase. -/
theorem tendsto_squareScale_lowPacket (A : ℕ → ℕ) (y : ℝ) :
    Tendsto (fun N => lowPacket (A N) (N^2) N y) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hbound : ∀ᶠ N : ℕ in atTop, ‖lowPacket (A N) (N^2) N y‖ ≤
      (Real.log 4+4)/(N : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact norm_squareScale_lowPacket_le hN (A N) y
  have hlim : Tendsto (fun N : ℕ => (Real.log 4+4)/(N : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, ← div_eq_mul_inv, one_div] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log 4+4)
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hbound hlim

/-- Exact source normalization at the campaign boundary on a cofinal
integer scale. This contains no hypothetical-zero or prime-distribution input. -/
theorem cofinal_campaign_source (N : ℕ) :
    (((N^20000 : ℕ) : ℝ) ^ (19999/20000 : ℝ)) = (N : ℝ)^19999 := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  norm_num

/-- The same actual-prime sector has a fixed source-scale power saving:
`H=N^20000`, `D=N^19998` corresponds to `D=H^(9999/10000)`.
The rest of the quadratic is explicitly excluded from this estimate. -/
theorem norm_cofinal_campaign_lowPacket_le {N : ℕ} (hN : 0 < N) (A : ℕ) (y : ℝ) :
    ‖lowPacket A (N^20000) (N^19998) y‖/(N : ℝ)^19999 ≤
      (Real.log 4+4)/(N : ℝ)^5 := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ ≤ ((Real.log 4+4)*((N^19998 : ℕ) : ℝ)*
        ((((N^19998 : ℕ) : ℝ)/((N^20000 : ℕ) : ℝ))^2))/(N : ℝ)^19999 :=
      div_le_div_of_nonneg_right (norm_lowPacket_le (pow_pos hN 20000) A (N^19998) y)
        (pow_nonneg (Nat.cast_nonneg N) 19999)
    _ = _ := by push_cast; field_simp

/-- The small-denominator power saving holds throughout the campaign
strip, on the same literal packet and with its full fixed-height phase. -/
theorem norm_cofinal_strip_lowPacket_le {N : ℕ} (hN : 0 < N) (A : ℕ) (y : ℝ)
    {beta : ℝ} (hb : (19999/20000 : ℝ) ≤ beta) :
    ‖lowPacket A (N^20000) (N^19998) y‖/(((N^20000 : ℕ) : ℝ)^beta) ≤
      (Real.log 4+4)/(N : ℝ)^5 := by
  have hbase : (1 : ℝ) ≤ (N^20000 : ℕ) := by
    have hp : 1 ≤ N^20000 := one_le_pow₀ (by omega : 1 ≤ N)
    simpa only [Nat.cast_one] using (Nat.cast_le (α := ℝ)).mpr hp
  have hp := Real.rpow_le_rpow_of_exponent_le hbase hb
  have hl : (0 : ℝ) < (((N^20000 : ℕ) : ℝ)^(19999/20000 : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  apply (div_le_div_of_nonneg_left (norm_nonneg _) hl hp).trans
  rw [cofinal_campaign_source]
  exact norm_cofinal_campaign_lowPacket_le hN A y

end
end RiemannGaussian.SuzukiCarryFejer
