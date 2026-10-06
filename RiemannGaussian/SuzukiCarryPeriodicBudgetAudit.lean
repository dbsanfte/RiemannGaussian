/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarryPeriodicDiscrepancy
import RiemannGaussian.SuzukiCarryMellinRate
import RiemannGaussian.ZetaPrimeWindow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Audit of the periodic remainder's source-scale cost

All three modulations and both lag orientations are joined first. This is
an obstruction to a periodic-remainder norm/SBP budget, not a lower bound
on the signed prime sum or a proof that arbitrary prime cancellation is
impossible.
-/

namespace RiemannGaussian.SuzukiCarryPeriodicBudgetAudit
noncomputable section
open Complex Set Filter
open SuzukiCarryGramSource SuzukiCarryPhaseCode SuzukiCarryMellinRate SuzukiCarryFejer
open SuzukiCarryPeriodicDiscrepancy
open SuzukiCarryCorrelation
open scoped BigOperators Topology ComplexConjugate

/-- Joined cosine symbol of both off-diagonal lag orientations. The factor
two is retained separately in the literal budget below. -/
def symbol (c : Fin 3 → ℂ) (tau x : ℝ) : ℂ :=
  c 0+c 1*(Real.cos (tau*x) : ℂ)+c 2*(Real.cos (2*tau*x) : ℂ)

private theorem analytic_symbol (c : Fin 3 → ℂ) (tau : ℝ) :
    AnalyticOnNhd ℝ (symbol c tau) univ := by
  intro x _
  have ha (v : ℝ) : AnalyticAt ℝ (fun x : ℝ => (Real.cos (v*x) : ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp
      (Real.analyticAt_cos.comp (analyticAt_const.mul analyticAt_id))
  exact (analyticAt_const.add (analyticAt_const.mul (ha tau))).add
    (analyticAt_const.mul (ha (2*tau)))

/-- No nonzero phase code can remove the whole main-scale open interval.
This applies to every fixed positive tau, not just a universal small code. -/
theorem exists_symbol_ne_zero_on_interval {c : Fin 3 → ℂ} (hc : c ≠ 0)
    {tau a b : ℝ} (ht : 0 < tau) (hab : a < b) :
    ∃ x : ℝ, x ∈ Ioo a b ∧ symbol c tau x ≠ 0 := by
  by_contra hno
  push Not at hno
  have heq : symbol c tau = (0 : ℝ → ℂ) :=
    (analytic_symbol c tau).eq_of_eventuallyEq analyticOnNhd_const (by
      filter_upwards [Ioo_mem_nhds (by linarith : a < (a+b)/2)
        (by linarith : (a+b)/2 < b)] with x hx
      exact hno x hx)
  have h0 := congrFun heq 0
  have h1 := congrFun heq (Real.pi/tau)
  have h2 := congrFun heq (Real.pi/(2*tau))
  have he1 : tau*(Real.pi/tau) = Real.pi := by field_simp
  have he2 : 2*tau*(Real.pi/tau) = 2*Real.pi := by field_simp
  have he3 : tau*(Real.pi/(2*tau)) = Real.pi/2 := by field_simp
  have he4 : 2*tau*(Real.pi/(2*tau)) = Real.pi := by field_simp
  simp [symbol] at h0
  simp [symbol, he1, he2] at h1
  simp [symbol, he3, he4] at h2
  apply hc
  funext j
  fin_cases j
  · change c 0 = 0
    linear_combination (1/4 : ℂ)*h0+(1/4 : ℂ)*h1+(1/2 : ℂ)*h2
  · change c 1 = 0
    linear_combination (1/2 : ℂ)*h0-(1/2 : ℂ)*h1
  · change c 2 = 0
    linear_combination (1/4 : ℂ)*h0+(1/4 : ℂ)*h1-(1/2 : ℂ)*h2

/-- A nonzero code has a fixed open prime band with positive symbol norm. -/
theorem exists_symbol_band {c : Fin 3 → ℂ} (hc : c ≠ 0) {tau : ℝ} (ht : 0 < tau) :
    ∃ a b kappa : ℝ, 1 < a ∧ a < b ∧ b < 101/100 ∧ 0 < kappa ∧
      ∀ x ∈ Icc a b, kappa ≤ ‖symbol c tau x‖ := by
  obtain ⟨x, hx, hn⟩ := exists_symbol_ne_zero_on_interval hc ht
    (by norm_num : (1 : ℝ) < 101/100)
  let kappa := ‖symbol c tau x‖/2
  have hkp : 0 < kappa := half_pos (norm_pos_iff.mpr hn)
  have hopen : IsOpen {v : ℝ | kappa < ‖symbol c tau v‖} := by
    apply isOpen_lt continuous_const
    unfold symbol
    fun_prop
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp hopen x
    (by dsimp [kappa]; exact half_lt_self (norm_pos_iff.mpr hn))
  let delta := min epsilon (min (x-1) ((101/100 : ℝ)-x))/2
  have hdp : 0 < delta := by
    apply half_pos
    exact lt_min hepsilon (lt_min (by linarith [hx.1]) (by linarith [hx.2]))
  have hdE : delta < epsilon := by
    have hh := min_le_left epsilon (min (x-1) ((101/100 : ℝ)-x))
    dsimp [delta]
    linarith
  have hdL : 2*delta ≤ x-1 := by
    have hh := (min_le_right epsilon (min (x-1) ((101/100 : ℝ)-x))).trans (min_le_left _ _)
    dsimp [delta]
    linarith
  have hdR : 2*delta ≤ (101/100 : ℝ)-x := by
    have hh := (min_le_right epsilon (min (x-1) ((101/100 : ℝ)-x))).trans (min_le_right _ _)
    dsimp [delta]
    linarith
  refine ⟨x-delta, x+delta, kappa, by linarith, by linarith, by linarith, hkp, ?_⟩
  intro v hv
  have hd : dist v x < epsilon := by
    rw [Real.dist_eq]
    have habs : |v-x| ≤ delta := abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2]⟩
    exact habs.trans_lt hdE
  exact (hball (Metric.mem_ball.mpr hd)).le

/-- Exact normalized canonical coefficients, with finite Mellin sampling
retained. -/
def normalizedCode (H : ℕ) (p : ℂ) (tau : ℝ) : Fin 3 → ℂ :=
  canonical (fun j => scaledResponse H p ((j : ℕ)*tau))

/-- The actual continuum limit of that same code. -/
def limitCode (p : ℂ) (tau : ℝ) : Fin 3 → ℂ :=
  canonical (fun j => continuumResponse p ((j : ℕ)*tau))

theorem tendsto_normalizedCode {p : ℂ} (hp : 0 < p.re) (tau : ℝ) (j : Fin 3) :
    Tendsto (fun H : ℕ => normalizedCode H p tau j) atTop (𝓝 (limitCode p tau j)) := by
  fin_cases j <;> dsimp [normalizedCode, limitCode, canonical]
  all_goals exact (tendsto_scaledResponse hp _).sub (tendsto_scaledResponse hp _)

/-- Source-sensitive codes have nonzero limiting coefficients. -/
theorem limitCode_ne_zero_of_source {p s : ℂ} {tau : ℝ}
    (hd : continuumDet p s tau ≠ 0) : limitCode p tau ≠ 0 := by
  intro hz
  have he := canonical_response (fun j : Fin 3 => continuumResponse p ((j : ℕ)*tau))
    (fun j : Fin 3 => continuumResponse s ((j : ℕ)*tau))
  change (∑ j : Fin 3, limitCode p tau j*continuumResponse s ((j : ℕ)*tau)) =
    -continuumDet p s tau at he
  simp only [hz, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at he
  exact hd (neg_eq_zero.mp he.symm)

private theorem symbol_error (c e : Fin 3 → ℂ) (tau x : ℝ) :
    ‖symbol c tau x-symbol e tau x‖ ≤
      ‖c 0-e 0‖+‖c 1-e 1‖+‖c 2-e 2‖ := by
  have he : symbol c tau x-symbol e tau x =
      (c 0-e 0)+(c 1-e 1)*(Real.cos (tau*x) : ℂ)+
        (c 2-e 2)*(Real.cos (2*tau*x) : ℂ) := by unfold symbol; ring
  rw [he]
  have h1 : ‖(Real.cos (tau*x) : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (tau*x)
  have h2 : ‖(Real.cos (2*tau*x) : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one (2*tau*x)
  calc
    _ ≤ ‖(c 0-e 0)+(c 1-e 1)*(Real.cos (tau*x) : ℂ)‖+
        ‖(c 2-e 2)*(Real.cos (2*tau*x) : ℂ)‖ := norm_add_le _ _
    _ ≤ ‖c 0-e 0‖+‖(c 1-e 1)*(Real.cos (tau*x) : ℂ)‖+
        ‖(c 2-e 2)*(Real.cos (2*tau*x) : ℂ)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ _ := by
      simp only [norm_mul]
      have hh1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (c 1-e 1))
      have hh2 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (c 2-e 2))
      simp only [mul_one] at hh1 hh2
      linarith

private theorem eventually_symbol_close {p : ℂ} (hp : 0 < p.re) (tau : ℝ)
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∀ᶠ H : ℕ in atTop, ∀ x : ℝ,
      ‖symbol (normalizedCode H p tau) tau x-symbol (limitCode p tau) tau x‖ < epsilon := by
  have ht (j : Fin 3) :
      Tendsto (fun H : ℕ => ‖normalizedCode H p tau j-limitCode p tau j‖) atTop (𝓝 0) := by
    simpa using ((tendsto_normalizedCode hp tau j).sub
      (tendsto_const_nhds (x := limitCode p tau j))).norm
  have hh := ((ht 0).add (ht 1)).add (ht 2)
  simp only [add_zero] at hh
  filter_upwards [hh.eventually (gt_mem_nhds he)] with H hH
  intro x
  exact (symbol_error _ _ tau x).trans_lt hH

/-- Audit cost AFTER all modulations and both lag orientations are joined.
The full Lambda support and fixed-height phase remain literal. -/
def periodicBudget (H : ℕ) (c : Fin 3 → ℂ) (tau y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (3*H), ∑ h ∈ Finset.Icc 1 (2*H),
    ‖(ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
      (2*symbol c tau ((h : ℝ)/(H : ℝ)))*(discrepancy H h d : ℂ)‖

theorem periodicBudget_nonneg (H : ℕ) (c : Fin 3 → ℂ) (tau y : ℝ) :
    0 ≤ periodicBudget H c tau y :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))

/-- A literal ordinary-prime subband of the surviving correlated sector. -/
def primeBand (H : ℕ) (a b : ℝ) : Finset ℕ :=
  PrimeWindow.primesInWindow (2*a*(H : ℝ)) (b/a)

private theorem primeBand_bounds {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {H p : ℕ} (hp : p ∈ primeBand H a b) :
    2*a*(H : ℝ) < p ∧ (p : ℝ) ≤ 2*b*(H : ℝ) ∧ p.Prime := by
  have hb : 0 < b := ha.trans hab
  have hh := PrimeWindow.mem_primesInWindow_bounds
    (by positivity : 0 ≤ 2*a*(H : ℝ)) (by positivity : 0 ≤ b/a) hp
  have he : (b/a)*(2*a*(H : ℝ)) = 2*b*(H : ℝ) := by field_simp
  rw [he] at hh
  exact hh

/-- The actual prime mass in any fixed multiplicative band is linear.
This is the classical unconditional PNT already proved in the repository. -/
theorem tendsto_primeBand_mass {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun H : ℕ => (∑ p ∈ primeBand H a b, Real.log p)/(H : ℝ))
      atTop (𝓝 (2*(b-a))) := by
  have hb : 0 < b := ha.trans hab
  have hA : 1 ≤ b/a := (le_div_iff₀ ha).mpr (by linarith)
  have hscale : Tendsto (fun H : ℕ => 2*a*(H : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have ht := ((PrimeWindow.theta_interval_div_tendsto
    (by positivity : 0 < b/a)).comp hscale).mul_const (2*a)
  have he : (b/a-1)*(2*a) = 2*(b-a) := by field_simp
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
  rw [primeBand, PrimeWindow.sum_log_primesInWindow (by positivity) hA]
  dsimp only [Function.comp_apply]
  have hHp : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  field_simp [hHp, ha.ne']

private theorem primeBand_geometry {a b : ℝ} (ha : 1 < a) (hab : a < b)
    (hb : b < 101/100) {H p : ℕ} (hH : 100 ≤ H) (hp : p ∈ primeBand H a b) :
    p = 2*((p-1)/2)+1 ∧ H ≤ (p-1)/2 ∧ 100*((p-1)/2) ≤ 101*H := by
  obtain ⟨hl, hu, hprime⟩ := primeBand_bounds (by linarith) hab hp
  have hHr : (100 : ℝ) ≤ H := by exact_mod_cast hH
  have hlo : (2*H : ℕ) < p := by
    have hh : (2 : ℝ)*(H : ℝ) < p := by nlinarith
    exact_mod_cast hh
  have hp2 : p ≠ 2 := by omega
  have hodd := hprime.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  have he : p = 2*((p-1)/2)+1 := by omega
  have hcast : (p : ℝ) = 2*((p-1)/2 : ℕ)+1 := by exact_mod_cast he
  have hi : (100 : ℝ)*((p-1)/2 : ℕ) ≤ 101*(H : ℝ) := by nlinarith
  exact ⟨he, by omega, by exact_mod_cast hi⟩

/-- The obstructive prime family is outside every already-paid low cutoff
D<=2H, and inside the literal upper cutoff. -/
theorem primeBand_in_high_sector {a b : ℝ} (ha : 1 < a) (hab : a < b)
    (hb : b < 101/100) {H D p : ℕ} (hH : 100 ≤ H) (hD : D ≤ 2*H)
    (hp : p ∈ primeBand H a b) : D < p ∧ p ≤ 3*H := by
  obtain ⟨he, hl, hu⟩ := primeBand_geometry ha hab hb hH hp
  constructor <;> omega

/-- A source-scale budget lower bound on the literal prime subband. The
phase is retained in the cost; prime powers outside this subband remain
in the full budget. -/
theorem periodicBudget_primeBand_lower {a b kappa : ℝ} (ha : 1 < a) (hab : a < b)
    (hb : b < 101/100) {H : ℕ} (hH : 100 ≤ H)
    (c : Fin 3 → ℂ) (tau y : ℝ)
    (hcode : ∀ p ∈ primeBand H a b,
      kappa ≤ ‖symbol c tau (((p-1)/2 : ℕ)/(H : ℝ))‖) :
    (kappa/10)*(∑ p ∈ primeBand H a b, Real.log p) ≤ periodicBudget H c tau y := by
  classical
  let term := fun d h : ℕ => ‖(ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
      (2*symbol c tau ((h : ℝ)/(H : ℝ)))*(discrepancy H h d : ℂ)‖
  have hsubset : primeBand H a b ⊆ Finset.Icc 1 (3*H) := by
    intro p hp
    obtain ⟨he, hl, hu⟩ := primeBand_geometry ha hab hb hH hp
    apply Finset.mem_Icc.mpr
    constructor <;> omega
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ primeBand H a b, ∑ h ∈ Finset.Icc 1 (2*H), term p h := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨he, hl, hu⟩ := primeBand_geometry ha hab hb hH hp
      have hprime := (primeBand_bounds (by linarith) hab hp).2.2
      have hE := discrepancy_main_band_lower hH hl hu
      rw [← he] at hE
      have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
      have hnorm : term p ((p-1)/2) = Real.log p*2*
          ‖symbol c tau (((p-1)/2 : ℕ)/(H : ℝ))‖*discrepancy H ((p-1)/2) p := by
        dsimp [term]
        simp only [norm_mul, norm_primePhase, mul_one, norm_ofNat,
          ArithmeticFunction.vonMangoldt_apply_prime hprime, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hlog, abs_of_nonneg (by linarith : 0 ≤ discrepancy H ((p-1)/2) p)]
        ring
      have hterm : (kappa/10)*Real.log p ≤ term p ((p-1)/2) := by
        rw [hnorm]
        have hh := mul_le_mul (hcode p hp) hE (by norm_num : (0 : ℝ) ≤ 1/20)
          (norm_nonneg _)
        have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ Real.log p*2 by positivity)
        nlinarith
      have hsingle : term p ((p-1)/2) ≤
          ∑ h ∈ Finset.Icc 1 (2*H), term p h :=
        Finset.single_le_sum (fun h _ => show 0 ≤ term p h from norm_nonneg _)
          (show (p-1)/2 ∈ Finset.Icc 1 (2*H) from Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      exact hterm.trans hsingle
    _ ≤ ∑ p ∈ Finset.Icc 1 (3*H), ∑ h ∈ Finset.Icc 1 (2*H), term p h :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun _ _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    _ = _ := rfl

/-- Once the determinant gate is passed, the joined periodic error budget
has a genuinely linear lower bound. No conjectural prime estimate is used. -/
theorem eventually_periodicBudget_linear_of_source {p s : ℂ}
    (hp : 0 < p.re) {tau : ℝ} (ht : 0 < tau)
    (hd : continuumDet p s tau ≠ 0) (y : ℝ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ H : ℕ in atTop,
      epsilon*(H : ℝ) ≤ periodicBudget H (normalizedCode H p tau) tau y := by
  obtain ⟨a, b, kappa, ha, hab, hb, hk, hband⟩ :=
    exists_symbol_band (limitCode_ne_zero_of_source hd) ht
  let A := (2*a+b)/3
  let B := (a+2*b)/3
  have hA : 1 < A := by dsimp [A]; linarith
  have hAB : A < B := by dsimp [A, B]; linarith
  have hB : B < 101/100 := by dsimp [B]; linarith
  have hgap : 0 < A-a := by dsimp [A]; linarith
  have hBbelow : B < b := by dsimp [B]; linarith
  have hclose := eventually_symbol_close hp tau (half_pos hk)
  have hsize : ∀ᶠ H : ℕ in atTop, 1/(2*(A-a)) ≤ (H : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hmass := (tendsto_primeBand_mass (by linarith : 0 < A) hAB).eventually
    (lt_mem_nhds (by linarith : B-A < 2*(B-A)))
  refine ⟨(kappa/20)*(B-A), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (100 : ℕ), hclose, hsize, hmass]
    with H hH hcloseH hsizeH hmassH
  have hHr : (100 : ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0 : ℝ) < H := by linarith
  have hcode : ∀ q ∈ primeBand H A B,
      kappa/2 ≤ ‖symbol (normalizedCode H p tau) tau (((q-1)/2 : ℕ)/(H : ℝ))‖ := by
    intro q hq
    obtain ⟨hql, hqu, _⟩ := primeBand_bounds (by linarith : 0 < A) hAB hq
    obtain ⟨he, _, _⟩ := primeBand_geometry hA hAB hB hH hq
    have heR : (q : ℝ) = 2*((q-1)/2 : ℕ)+1 := by exact_mod_cast he
    have hmul : (1/2 : ℝ) ≤ (A-a)*(H : ℝ) := by
      have hh := (div_le_iff₀ (by positivity : 0 < 2*(A-a))).mp hsizeH
      nlinarith
    have hx : (((q-1)/2 : ℕ)/(H : ℝ)) ∈ Icc a b := by
      constructor
      · apply (le_div_iff₀ hHp).mpr
        nlinarith
      · apply (div_le_iff₀ hHp).mpr
        nlinarith
    have hl := hband _ hx
    have herr := hcloseH (((q-1)/2 : ℕ)/(H : ℝ))
    have hn := norm_sub_norm_le (symbol (limitCode p tau) tau (((q-1)/2 : ℕ)/(H : ℝ)))
      (symbol (normalizedCode H p tau) tau (((q-1)/2 : ℕ)/(H : ℝ)))
    rw [norm_sub_rev] at hn
    linarith
  have hl := periodicBudget_primeBand_lower hA hAB hB hH
    (normalizedCode H p tau) tau y hcode
  have hmassLower : (B-A)*(H : ℝ) ≤ ∑ q ∈ primeBand H A B, Real.log q :=
    ((lt_div_iff₀ hHp).mp hmassH).le
  calc
    _ = (kappa/20)*((B-A)*(H : ℝ)) := by ring
    _ ≤ (kappa/20)*(∑ q ∈ primeBand H A B, Real.log q) := by gcongr
    _ = (kappa/2/10)*(∑ q ∈ primeBand H A B, Real.log q) := by ring
    _ ≤ _ := hl

/-- The error budget grows strictly faster than every matched H^beta
source with beta<1, even after joining all codes and both orientations. -/
theorem periodicBudget_source_diverges {p s : ℂ} (hp : 0 < p.re)
    {tau beta : ℝ} (ht : 0 < tau) (hb : beta < 1)
    (hd : continuumDet p s tau ≠ 0) (y : ℝ) :
    Tendsto (fun H : ℕ => periodicBudget H (normalizedCode H p tau) tau y/
      (H : ℝ)^beta) atTop atTop := by
  obtain ⟨epsilon, he, hbound⟩ := eventually_periodicBudget_linear_of_source hp ht hd y
  have hr := (tendsto_rpow_atTop (by linarith : 0 < 1-beta)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hg := hr.const_mul_atTop he
  apply tendsto_atTop_mono' atTop _ hg
  filter_upwards [eventually_gt_atTop (0 : ℕ), hbound] with H hH hbudget
  have hHp : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    epsilon*(H : ℝ)^(1-beta) = epsilon*(H : ℝ)/(H : ℝ)^beta := by
      rw [Real.rpow_sub hHp, Real.rpow_one]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hbudget (Real.rpow_nonneg hHp.le beta)

/-- The unchanged slow phase family used by the native code. -/
def phases (H : ℕ) (tau : ℝ) (j : Fin 3) : ℝ := ((j : ℕ)*tau)/(H : ℝ)

/-- Both signed lag orientations of the literal canonical code. -/
def nativeLagPair (H : ℕ) (tau y : ℝ) (h : ℕ) : ℂ :=
  lagFactor Finset.univ (code H (phases H tau) y) (phases H tau) (h : ℤ)+
    lagFactor Finset.univ (code H (phases H tau) y) (phases H tau) (-(h : ℤ))

private theorem normalizedCode_eq_native (H : ℕ) (tau y : ℝ) (j : Fin 3) :
    normalizedCode H (SuzukiCarryPoleCenter.poleExponent y) tau j =
      Complex.exp (-SuzukiCarryPoleCenter.poleExponent y*(Real.log H : ℂ))*
        code H (phases H tau) y j := by
  fin_cases j <;> dsimp [normalizedCode, phases, code, canonical, scaledResponse]
  all_goals ring

private theorem exp_pair (x : ℝ) :
    Complex.exp (I*x)+Complex.exp (I*(-x : ℝ)) = 2*(Real.cos x : ℂ) := by
  rw [show I*(x : ℂ) = (x : ℂ)*I by ring,
    show I*((-x : ℝ) : ℂ) = -(x : ℂ)*I by push_cast; ring,
    ← Complex.two_cos, ← Complex.ofReal_cos]

/-- Exact native-to-normalized bridge, before a norm is taken. -/
theorem normalized_nativeLagPair (H h : ℕ) (tau y : ℝ) :
    Complex.exp (-SuzukiCarryPoleCenter.poleExponent y*(Real.log H : ℂ))*
      nativeLagPair H tau y h =
        2*symbol (normalizedCode H (SuzukiCarryPoleCenter.poleExponent y) tau)
          tau ((h : ℝ)/(H : ℝ)) := by
  unfold nativeLagPair lagFactor
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have he (j : Fin 3) :
      Complex.exp (I*(phases H tau j)*(h : ℤ))+
        Complex.exp (I*(phases H tau j)*(-(h : ℤ))) =
      2*(Real.cos ((j : ℕ)*tau*((h : ℝ)/(H : ℝ))) : ℂ) := by
    have h1 : I*(phases H tau j)*(h : ℤ) =
        I*(((j : ℕ)*tau*((h : ℝ)/(H : ℝ)) : ℝ) : ℂ) := by
      unfold phases
      push_cast
      ring
    have h2 : I*(phases H tau j)*(-(h : ℤ)) =
        I*(-((j : ℕ)*tau*((h : ℝ)/(H : ℝ))) : ℝ) := by
      unfold phases
      push_cast
      ring
    rw [h1, h2, exp_pair]
  have hs : (∑ j : Fin 3,
      Complex.exp (-SuzukiCarryPoleCenter.poleExponent y*(Real.log H : ℂ))*
        (code H (phases H tau) y j*Complex.exp (I*(phases H tau j)*(h : ℤ))))+
      (∑ j : Fin 3,
        Complex.exp (-SuzukiCarryPoleCenter.poleExponent y*(Real.log H : ℂ))*
          (code H (phases H tau) y j*Complex.exp (I*(phases H tau j)*(-(h : ℤ))))) =
      ∑ j : Fin 3, normalizedCode H (SuzukiCarryPoleCenter.poleExponent y) tau j*
        (2*(Real.cos ((j : ℕ)*tau*((h : ℝ)/(H : ℝ))) : ℂ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [normalizedCode_eq_native]
    calc
      _ = Complex.exp (-SuzukiCarryPoleCenter.poleExponent y*(Real.log H : ℂ))*
          code H (phases H tau) y j*(Complex.exp (I*(phases H tau j)*(h : ℤ))+
            Complex.exp (I*(phases H tau j)*(-(h : ℤ)))) := by ring
      _ = _ := by rw [he]
  simp only [Int.cast_neg]
  rw [hs]
  simp [Fin.sum_univ_three, symbol]
  ring

/-- Native budget of the actual phase-coded periodic replacement. -/
def nativePeriodicBudget (H : ℕ) (tau y : ℝ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 (3*H), ∑ h ∈ Finset.Icc 1 (2*H),
    ‖(ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
      nativeLagPair H tau y h*(discrepancy H h d : ℂ)‖

/-- Exact identification with the two oriented rows of the ORIGINAL
modulated Fejer vector. Every coefficient, endpoint and subset sign is
kept before taking a norm in the audit cost. -/
theorem native_row_discrepancy {H : ℕ} (hH : 0 < H) (h d : ℕ) (tau y : ℝ) :
    (∑ j : Fin 3, code H (phases H tau) y j*
      ∑ N ∈ Finset.range (3*H),
        (modulate (coefficient H H) (phases H tau j) N*
            conj (modulate (coefficient H H) (phases H tau j) (N+h))+
          modulate (coefficient H H) (phases H tau j) (N+h)*
            conj (modulate (coefficient H H) (phases H tau j) N))*
        (zeroMeanProduct d h N : ℂ)) =
      nativeLagPair H tau y h*(discrepancy H h d : ℂ) := by
  have hrow (j : Fin 3) (N : ℕ) :
      modulate (coefficient H H) (phases H tau j) N*
          conj (modulate (coefficient H H) (phases H tau j) (N+h))+
        modulate (coefficient H H) (phases H tau j) (N+h)*
          conj (modulate (coefficient H H) (phases H tau j) N) =
      (SuzukiCarryPeriodicDiscrepancy.overlap H h N : ℂ)*
        (Complex.exp (I*(phases H tau j)*(h : ℤ))+
          Complex.exp (I*(phases H tau j)*(-(h : ℤ)))) := by
    rw [modulate_mul_conj, modulate_mul_conj, coefficient_eq_weight hH,
      coefficient_eq_weight hH, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [show (N : ℤ)-(N+h : ℕ) = -(h : ℤ) by omega,
      show ((N+h : ℕ) : ℤ)-N = (h : ℤ) by omega]
    unfold SuzukiCarryPeriodicDiscrepancy.overlap
    push_cast
    ring
  simp_rw [hrow]
  have hsum (j : Fin 3) :
      (∑ N ∈ Finset.range (3*H), (SuzukiCarryPeriodicDiscrepancy.overlap H h N : ℂ)*
        (Complex.exp (I*(phases H tau j)*(h : ℤ))+
          Complex.exp (I*(phases H tau j)*(-(h : ℤ))))*(zeroMeanProduct d h N : ℂ)) =
      (Complex.exp (I*(phases H tau j)*(h : ℤ))+
        Complex.exp (I*(phases H tau j)*(-(h : ℤ))))*(discrepancy H h d : ℂ) := by
    rw [discrepancy, Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N _
    push_cast
    ring
  simp_rw [hsum]
  unfold nativeLagPair lagFactor
  rw [add_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Int.cast_neg]
  ring

/-- The division by H is exactly the campaign's native normalization. -/
theorem nativePeriodicBudget_div_H {H : ℕ} (hH : 0 < H) (tau y : ℝ) :
    nativePeriodicBudget H tau y/(H : ℝ) =
      periodicBudget H (normalizedCode H (SuzukiCarryPoleCenter.poleExponent y) tau) tau y := by
  have hf : ‖Complex.exp (-SuzukiCarryPoleCenter.poleExponent y*(Real.log H : ℂ))‖ =
      (H : ℝ)⁻¹ := by
    rw [Complex.norm_exp]
    have he : (-SuzukiCarryPoleCenter.poleExponent y*(Real.log H : ℂ)).re = -Real.log H := by
      simp only [Complex.mul_re, Complex.neg_re, SuzukiCarryPoleCenter.poleExponent_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul, one_mul]
    rw [he, Real.exp_neg, Real.exp_log (by exact_mod_cast hH : (0 : ℝ) < H)]
  unfold nativePeriodicBudget periodicBudget
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  have he := congrArg norm (show
      Complex.exp (-SuzukiCarryPoleCenter.poleExponent y*(Real.log H : ℂ))*
        ((ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
          nativeLagPair H tau y h*(discrepancy H h d : ℂ)) =
      (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
        (2*symbol (normalizedCode H (SuzukiCarryPoleCenter.poleExponent y) tau)
          tau ((h : ℝ)/(H : ℝ)))*(discrepancy H h d : ℂ) by
    rw [show Complex.exp (-SuzukiCarryPoleCenter.poleExponent y*(Real.log H : ℂ))*
        ((ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
          nativeLagPair H tau y h*(discrepancy H h d : ℂ)) =
      (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
        (Complex.exp (-SuzukiCarryPoleCenter.poleExponent y*(Real.log H : ℂ))*
          nativeLagPair H tau y h)*(discrepancy H h d : ℂ) by ring,
      normalized_nativeLagPair])
  rw [norm_mul, hf] at he
  simpa only [div_eq_mul_inv, mul_comm] using he

/-- Decisive obstruction for the proposed periodic-remainder payment:
any fixed code retaining a nonzero matched source has a native budget
strictly larger than that source scale. -/
theorem nativePeriodicBudget_source_diverges {tau beta : ℝ} (ht : 0 < tau)
    (hb : beta < 1) (y : ℝ)
    (hd : continuumDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau ≠ 0) :
    Tendsto (fun H : ℕ => nativePeriodicBudget H tau y/(H : ℝ)^(1+beta)) atTop atTop := by
  have hp : 0 < (SuzukiCarryPoleCenter.poleExponent y).re := by
    rw [SuzukiCarryPoleCenter.poleExponent_re]
    norm_num
  have he := periodicBudget_source_diverges hp ht hb hd y
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with H hH
  rw [← nativePeriodicBudget_div_H hH, Real.rpow_add (by exact_mod_cast hH : (0 : ℝ) < H),
    Real.rpow_one]
  ring

/-- Retaining the source and paying the periodic norm remainder at that
source scale are incompatible, for the actual native code. -/
theorem not_source_and_periodic_budget_decay {tau beta : ℝ} (ht : 0 < tau)
    (hb : beta < 1) (y : ℝ) :
    ¬(continuumDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau ≠ 0 ∧
      Tendsto (fun H : ℕ => nativePeriodicBudget H tau y/(H : ℝ)^(1+beta))
        atTop (𝓝 0)) := by
  rintro ⟨hd, hdecay⟩
  have hhigh := (nativePeriodicBudget_source_diverges ht hb y hd).eventually
    (eventually_gt_atTop (1 : ℝ))
  have hsmall := hdecay.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨H, hH, hS⟩ := (hhigh.and hsmall).exists
  linarith

/-- Every allowance obtained by estimating the joined rows separately
inherits the same source-divergent lower bound. This includes a partial-
sum/total-variation allowance from discrete summation by parts. -/
theorem componentwise_allowance_source_diverges {tau beta : ℝ} (ht : 0 < tau)
    (hb : beta < 1) (y : ℝ)
    (hd : continuumDet (SuzukiCarryPoleCenter.poleExponent y) (beta : ℂ) tau ≠ 0)
    (allowance : ℕ → ℕ → ℕ → ℝ)
    (hallowance : ∀ᶠ H : ℕ in atTop, ∀ d ∈ Finset.Icc 1 (3*H),
      ∀ h ∈ Finset.Icc 1 (2*H),
      ‖(ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
        nativeLagPair H tau y h*(discrepancy H h d : ℂ)‖ ≤ allowance H d h) :
    Tendsto (fun H : ℕ =>
      (∑ d ∈ Finset.Icc 1 (3*H), ∑ h ∈ Finset.Icc 1 (2*H), allowance H d h)/
        (H : ℝ)^(1+beta)) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (nativePeriodicBudget_source_diverges ht hb y hd)
  filter_upwards [hallowance] with H hH
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg H) _)
  exact Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun h hh => hH d hd h hh))

end
end RiemannGaussian.SuzukiCarryPeriodicBudgetAudit
