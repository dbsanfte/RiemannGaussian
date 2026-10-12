/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorSuccessorGammaAudit
import RiemannGaussian.ZetaPrimeWindow
import Mathlib.Data.Nat.ModEq

/-!
# Literal successor CRT boundary: a cofinal absolute-completion obstruction

Different divisor columns meet consecutive ordinary integer rows. The
finite pair join is valid for arbitrary complex arrays, and its CRT
compatibility is kept exactly. Replacing counts by their periodic means
and norm-paying every boundary is a separate, unsuccessful operation:
the actual large-prime subpopulation alone has a linear completion debit.
This is NOT a bound on the joined signed prime correlation.
-/

namespace RiemannGaussian.ArithmeticOperatorCrtBoundaryAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorKummerCutoff ArithmeticOperatorGammaTwistAudit
open SuzukiCarryCorrelation PrimeWindow
open scoped BigOperators Topology ComplexConjugate

/-- Literal count, including both endpoints and the full translated row. -/
def incidenceCount (X h d e : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => d ∣ n ∧ e ∣ n+h)).card

/-- Complete two-row convolution, all arithmetic columns retained. -/
def shiftedRows (X h : ℕ) (f g : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X, divisorObservation f n*divisorObservation g (n+h)

private theorem observation_eq_finite {X n : ℕ} (hn : 0 < n) (hnX : n ≤ X)
    (f : ℕ → ℂ) :
    divisorObservation f n = ∑ d ∈ Finset.Icc 1 X, if d ∣ n then f d else 0 := by
  classical
  have he : (Finset.Icc 1 X).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨_, hd⟩
      exact ⟨hd, hn.ne'⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, (Nat.le_of_dvd hn hd).trans hnX⟩, hd⟩
  rw [← Finset.sum_filter, he]
  rfl

/-- Exact finite CRT/incidence joining does not assume prime structure
or pay an order boundary. -/
theorem shiftedRows_eq_pairs (X h : ℕ) (f g : ℕ → ℂ) :
    shiftedRows X h f g =
      ∑ d ∈ Finset.Icc 1 (X+h), ∑ e ∈ Finset.Icc 1 (X+h),
        f d*g e*(incidenceCount X h d e : ℂ) := by
  classical
  have hc (d e : ℕ) :
      (incidenceCount X h d e : ℂ) =
        ∑ n ∈ Finset.Icc 1 X, if d ∣ n ∧ e ∣ n+h then (1 : ℂ) else 0 := by
    rw [← Finset.sum_filter]
    simp [incidenceCount]
  symm
  unfold shiftedRows
  simp_rw [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans (Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn0, hnX⟩ := Finset.mem_Icc.mp hn
  rw [observation_eq_finite hn0 (by omega : n ≤ X+h),
    observation_eq_finite (by omega : 0 < n+h) (by omega : n+h ≤ X+h)]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hd : e ∣ n <;> by_cases he : d ∣ n+h <;> simp_all

/-- Full CRT compatibility, not merely a same-column restriction. -/
theorem gcd_dvd_lag {n h d e : ℕ} (hd : d ∣ n) (he : e ∣ n+h) :
    Nat.gcd d e ∣ h := by
  have ha := (Nat.gcd_dvd_left d e).trans hd
  have hb := (Nat.gcd_dvd_right d e).trans he
  simpa using Nat.dvd_sub hb ha

/-- Incompatible columns have exactly zero literal incidence. -/
theorem incidenceCount_zero_of_incompatible {X h d e : ℕ}
    (hbad : ¬ Nat.gcd d e ∣ h) : incidenceCount X h d e = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro n _ hn
  exact hbad (gcd_dvd_lag hn.1 hn.2)

/-- Both large prime columns cannot meet successor rows at an even
cutoff. Their periodic CRT mean nevertheless is positive. -/
theorem incidenceCount_large_odd_primes {H p q : ℕ} (hH : 1 ≤ H)
    (hp : p.Prime) (hq : q.Prime) (hpL : 2*H < p) (hqL : 2*H < q)
    (hpU : p ≤ 4*H) : incidenceCount (4*H) 1 p q = 0 := by
  classical
  unfold incidenceCount
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  intro n hn hde
  obtain ⟨hn0, hnX⟩ := Finset.mem_Icc.mp hn
  have hnp : n = p := by
    obtain ⟨k, hk⟩ := hde.1
    have hk0 : 0 < k := by nlinarith
    have hk1 : k < 2 := by nlinarith
    have : k = 1 := by omega
    simpa [this] using hk
  have hpmod : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hqmod : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by omega)
  have hpstrict : p < 4*H := by
    by_contra hh
    have : p = 4*H := by omega
    omega
  rw [hnp] at hde
  obtain ⟨k, hk⟩ := hde.2
  have hk0 : 0 < k := by nlinarith
  have hk1 : k < 2 := by nlinarith
  have : k = 1 := by omega
  have heq : p+1 = q := by simpa [this] using hk
  omega

/-- Ordinary-prime band, used only as a subpopulation of the full
prime-power completion debit. -/
def primeBand (H a b : ℕ) : Finset ℕ :=
  (Finset.Ioc (a*H) (b*H)).filter Nat.Prime

/-- Logarithmic mass of the literal finite prime band. -/
def logMass (H a b : ℕ) : ℝ := ∑ p ∈ primeBand H a b, Real.log p

theorem logMass_eq_theta {H a b : ℕ} (hab : a ≤ b) :
    logMass H a b = Chebyshev.theta (b*H : ℕ)-Chebyshev.theta (a*H : ℕ) := by
  have hs : Finset.Icc 0 (a*H) ⊆ Finset.Icc 0 (b*H) :=
    Finset.Icc_subset_Icc le_rfl (Nat.mul_le_mul_right H hab)
  have hd : Finset.Icc 0 (b*H) \ Finset.Icc 0 (a*H) = Finset.Ioc (a*H) (b*H) := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff (f := fun n : ℕ => if n.Prime then Real.log n else 0) hs
  rw [hd] at h
  simpa only [logMass, primeBand, Chebyshev.theta_eq_sum_Icc,
    Nat.floor_natCast, Finset.sum_filter] using (eq_sub_iff_add_eq.mpr h)

private theorem theta_dyadic_scaled {a : ℕ} (ha : 0 < a) :
    Tendsto (fun J : ℕ => Chebyshev.theta (a*2^J : ℕ)/(2^J : ℕ)) atTop (𝓝 (a : ℝ)) := by
  have hpow : Tendsto (fun J : ℕ => ((2^J : ℕ) : ℝ)) atTop atTop := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have ht := (theta_div_tendsto_one.comp
    (hpow.const_mul_atTop (by exact_mod_cast ha : 0 < (a : ℝ)))).mul_const (a : ℝ)
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [] with J
  have hJ : (2^J : ℝ) ≠ 0 := by positivity
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  dsimp
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- Existing unconditional PNT supplies only the positive mass used to
refute absolute boundary payment; no signed prime estimate is inferred. -/
theorem tendsto_logMass_dyadic {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun J : ℕ => logMass (2^J) a b/(2^J : ℕ)) atTop
      (𝓝 ((b : ℝ)-a)) := by
  have ht := (theta_dyadic_scaled (ha.trans_le hab)).sub (theta_dyadic_scaled ha)
  simpa only [logMass_eq_theta hab, sub_div] using ht

/-- Mean of the full CRT period. Incompatible successor columns have
mean zero rather than an invented independent density. -/
def crtMean (X d e : ℕ) : ℝ :=
  if d.Coprime e then (X : ℝ)/((d : ℝ)*e) else 0

/-- The completion boundary with its actual prime-power phases retained. -/
def boundaryTerm (X : ℕ) (y : ℝ) (d e : ℕ) : ℝ :=
  ‖((ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d)*
    conj ((ArithmeticFunction.vonMangoldt e : ℂ)*primePhase y e)*
      (((incidenceCount X 1 d e : ℝ)-crtMean X d e : ℝ) : ℂ)‖

/-- Full termwise absolute-completion debit. Every prime power through
the two literal row cutoffs is included, not just the selected subband. -/
def fullBoundaryDebit (X : ℕ) (y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (X+1), ∑ e ∈ Finset.Icc 1 (X+1), boundaryTerm X y d e

/-- This equality diagnoses the norm-payment class, not cancellation in
the signed aggregate: unit prime phases do not diminish its debit. -/
theorem boundaryTerm_eq (X : ℕ) (y : ℝ) (d e : ℕ) :
    boundaryTerm X y d e = ArithmeticFunction.vonMangoldt d*
      ArithmeticFunction.vonMangoldt e*|(incidenceCount X 1 d e : ℝ)-crtMean X d e| := by
  simp only [boundaryTerm, norm_mul, Complex.norm_conj, norm_primePhase, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := d)),
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := e))]

private theorem band_boundary_lower {H p q : ℕ} (hH : 1 ≤ H)
    (hp : p ∈ primeBand H 2 3) (hq : q ∈ primeBand H 3 4) (y : ℝ) :
    Real.log p*Real.log q/(4*H : ℕ) ≤ boundaryTerm (4*H) y p q := by
  obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqI, hqP⟩ := Finset.mem_filter.mp hq
  obtain ⟨hpL, hpU⟩ := Finset.mem_Ioc.mp hpI
  obtain ⟨hqL, hqU⟩ := Finset.mem_Ioc.mp hqI
  have hpX : p ≤ 4*H := by omega
  have hq2 : 2*H < q := by omega
  have hco : p.Coprime q := (Nat.coprime_primes hpP hqP).mpr (by omega)
  rw [boundaryTerm_eq, incidenceCount_large_odd_primes hH hpP hqP hpL hq2 hpX,
    ArithmeticFunction.vonMangoldt_apply_prime hpP,
    ArithmeticFunction.vonMangoldt_apply_prime hqP]
  rw [crtMean, ite_eq_left hco]
  simp only [Nat.cast_zero, zero_sub, abs_neg]
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hpP.pos
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hqP.pos
  have hX0 : 0 < ((4*H : ℕ) : ℝ) := by positivity
  rw [abs_of_pos (div_pos hX0 (mul_pos hp0 hq0)), div_eq_mul_inv]
  have hb : (((4*H : ℕ) : ℝ))⁻¹ ≤ ((4*H : ℕ) : ℝ)/((p : ℝ)*q) := by
    apply (le_div_iff₀ (mul_pos hp0 hq0)).mpr
    apply (inv_mul_le_iff₀ hX0).mpr
    have hpR : (p : ℝ) ≤ ((4*H : ℕ) : ℝ) := by exact_mod_cast hpX
    have hqR : (q : ℝ) ≤ ((4*H : ℕ) : ℝ) := by exact_mod_cast hqU
    exact mul_le_mul hpR hqR hq0.le hX0.le
  exact mul_le_mul_of_nonneg_left hb
    (mul_nonneg (Real.log_nonneg (by exact_mod_cast hpP.one_le))
      (Real.log_nonneg (by exact_mod_cast hqP.one_le)))

/-- The two distinct large-prime bands alone force this lower debit.
Their CRT counts are zero, so there is no diagonal or single-column loss. -/
theorem logMass_product_le_debit {H : ℕ} (hH : 1 ≤ H) (y : ℝ) :
    logMass H 2 3*logMass H 3 4/(4*H : ℕ) ≤ fullBoundaryDebit (4*H) y := by
  classical
  have hsub {a b : ℕ} (hb : b ≤ 4) :
      primeBand H a b ⊆ Finset.Icc 1 (4*H+1) := by
    intro p hp
    obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_Icc.mpr ⟨hpP.one_le, ?_⟩
    exact (Finset.mem_Ioc.mp hpI).2.trans
      ((Nat.mul_le_mul_right H hb).trans (by omega))
  calc
    _ = ∑ p ∈ primeBand H 2 3, ∑ q ∈ primeBand H 3 4,
        Real.log p*Real.log q/(4*H : ℕ) := by
      unfold logMass
      simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
      rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ primeBand H 2 3, ∑ q ∈ primeBand H 3 4,
        boundaryTerm (4*H) y p q :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq =>
        band_boundary_lower hH hp hq y))
    _ ≤ fullBoundaryDebit (4*H) y := by
      unfold fullBoundaryDebit
      apply (Finset.sum_le_sum (fun p _ =>
        Finset.sum_le_sum_of_subset_of_nonneg (hsub (a := 3) (by omega))
          (fun q _ _ => norm_nonneg _))).trans
      exact Finset.sum_le_sum_of_subset_of_nonneg (hsub (a := 2) (by omega))
        (fun p _ _ => Finset.sum_nonneg (fun q _ => norm_nonneg _))

/-- Cofinal linear absolute CRT boundary at actual primes, every height.
It is larger than any campaign source `X^beta`, `beta<1`. This rules out
termwise CRT completion payment, not a joined signed estimate. -/
theorem eventually_fullBoundaryDebit_lower (y : ℝ) :
    ∀ᶠ J : ℕ in atTop,
      ((4*2^J : ℕ) : ℝ)/64 ≤ fullBoundaryDebit (4*2^J) y := by
  have hp := (tendsto_logMass_dyadic (a := 2) (b := 3) (by omega) (by omega)).eventually
    (eventually_gt_nhds (show (1/2 : ℝ) < (3 : ℝ)-2 by norm_num))
  have hq := (tendsto_logMass_dyadic (a := 3) (b := 4) (by omega) (by omega)).eventually
    (eventually_gt_nhds (show (1/2 : ℝ) < (4 : ℝ)-3 by norm_num))
  filter_upwards [hp, hq] with J hp hq
  have hH : 1 ≤ 2^J := Nat.one_le_pow J 2 (by omega)
  have hpos : (0 : ℝ) < ((2^J : ℕ) : ℝ) := by positivity
  have hpL := (lt_div_iff₀ hpos).mp hp
  have hqL := (lt_div_iff₀ hpos).mp hq
  have hb := logMass_product_le_debit hH y
  apply le_trans ?_ hb
  have hm : ((2^J : ℕ) : ℝ)^2/4 ≤ logMass (2^J) 2 3*logMass (2^J) 3 4 := by
    have hp0 : 0 ≤ logMass (2^J) 2 3 := by linarith
    have hq0 : 0 ≤ logMass (2^J) 3 4 := by linarith
    nlinarith
  have hX : 0 < ((4*2^J : ℕ) : ℝ) := by positivity
  apply (le_div_iff₀ hX).mpr
  push_cast at *
  nlinarith

/-- Its source-normalized debit actually diverges for every `beta<1`.
No all-height prime or zero hypothesis occurs in this no-go theorem. -/
theorem tendsto_scaled_fullBoundaryDebit_atTop {beta : ℝ} (hb : beta < 1) (y : ℝ) :
    Tendsto (fun J : ℕ => (Real.exp (-beta*Real.log 2))^J*
      fullBoundaryDebit (4*2^J) y) atTop atTop := by
  have hr : 1 < 2*Real.exp (-beta*Real.log 2) := by
    have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have he : 2*Real.exp (-beta*Real.log 2) = Real.exp ((1-beta)*Real.log 2) := by
      rw [show (1-beta)*Real.log 2 = Real.log 2+(-beta*Real.log 2) by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [he]
    exact Real.one_lt_exp_iff.mpr (mul_pos (by linarith) hl)
  have ht := (tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop
    (show (0 : ℝ) < 1/16 by norm_num)
  apply tendsto_atTop_mono' atTop ?_ ht
  filter_upwards [eventually_fullBoundaryDebit_lower y] with J hJ
  have hh := mul_le_mul_of_nonneg_left hJ
    (pow_nonneg (Real.exp_pos (-beta*Real.log 2)).le J)
  convert hh using 1
  push_cast
  rw [mul_pow]
  ring

end
end RiemannGaussian.ArithmeticOperatorCrtBoundaryAudit
