/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorFixedLagSourceAudit
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Growing additive lags still need an actual nonlinear source theorem

Concentrating the diagnostic source on perfect r-th powers preserves its
EXACT Mellin residue and removes the density pole. In the bulk n>=H^r,
no two supported labels differ by a positive lag <=H^(r-1), for r>=2.
Thus one fixed integer row kills even growing lag families and every
correlated mask in this range, at every scale. This is a source-inference
no-go, not an estimate for actual primes or a generalized-prime model.
All exact actual Gamma constraints are explicitly outside this control.
-/

namespace RiemannGaussian.ArithmeticOperatorGrowingLagSourceAudit
noncomputable section
open Complex Filter ArithmeticOperatorNonlinearSourceAudit
open ArithmeticOperatorSuccessorSourceAudit ArithmeticOperatorIncidenceFreedom
open ArithmeticOperatorKummerCutoff
open scoped BigOperators Topology ComplexConjugate

/-- A single scale-independent row on literal integer r-th powers. -/
def powerRow (r : ℕ) (v : ℂ) (beta : ℝ) : ℕ → ℂ :=
  Function.extend (fun n : ℕ => n^r)
    (fun n => (r : ℂ)*matchedRow v ((r : ℝ)*beta) n) (fun _ => 0)

/-- Genuine meromorphic response after the exact integer reindexing. -/
def response (r : ℕ) (v : ℂ) (beta : ℝ) (s : ℂ) : ℂ :=
  (r : ℂ)*smoothResponse v ((r : ℝ)*beta) ((r : ℂ)*s)

theorem powerRow_on_power {r : ℕ} (hr : 0<r) (v : ℂ) (beta : ℝ) (n : ℕ) :
    powerRow r v beta (n^r) = (r : ℂ)*matchedRow v ((r : ℝ)*beta) n :=
  (Nat.pow_left_injective hr.ne').extend_apply _ _ n

/-- Exact support at every integer endpoint, including zero. -/
theorem powerRow_ne_zero_implies_power (r : ℕ) (v : ℂ) (beta : ℝ) {n : ℕ}
    (hn : powerRow r v beta n≠0) : ∃ m : ℕ, m^r=n := by
  by_contra hh
  exact hn (Function.extend_apply' _ _ n hh)

private theorem power_term {r : ℕ} (hr : 0<r) (v : ℂ) (beta : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (powerRow r v beta) s (n^r) =
      (r : ℂ)*LSeries.term (matchedRow v ((r : ℝ)*beta)) ((r : ℂ)*s) n := by
  by_cases hn : n=0
  · simp [hn,hr.ne']
  · rw [LSeries.term_of_ne_zero (pow_ne_zero _ hn),LSeries.term_of_ne_zero hn,
      powerRow_on_power hr]
    simp only [Nat.cast_pow]
    rw [←Complex.natCast_cpow_natCast_mul n r s]
    ring

/-- The model has an absolutely convergent coefficient series on its
stated half-plane; continuation is never confused with that series. -/
theorem power_hasSum {r : ℕ} (hr : 0<r) (v : ℂ) (beta : ℝ)
    {s : ℂ} (hs : beta<s.re) :
    LSeriesHasSum (powerRow r v beta) s (response r v beta s) := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have ht : (r : ℝ)*beta<((r : ℂ)*s).re := by
    simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]
    exact mul_lt_mul_of_pos_left hs hrR
  have hf0 : HasSum (fun n : ℕ =>
      LSeries.term (matchedRow v ((r : ℝ)*beta)) ((r : ℂ)*s) n)
      (smoothResponse v ((r : ℝ)*beta) ((r : ℂ)*s)) := by
    rw [←smooth_euler_response v ((r : ℝ)*beta) ht]
    exact (matched_summable v ((r : ℝ)*beta) ht).hasSum
  have hf := hf0.mul_left (r : ℂ)
  have hcomp : HasSum (fun n : ℕ => LSeries.term (powerRow r v beta) s (n^r))
      (response r v beta s) := by
    exact hf.congr_fun (fun n => power_term hr v beta s n)
  have hz : ∀ n : ℕ, n ∉ Set.range (fun m : ℕ => m^r) →
      LSeries.term (powerRow r v beta) s n=0 := by
    intro n hn
    by_cases h0 : n=0
    · simp [h0]
    · rw [LSeries.term_of_ne_zero h0]
      have hz : powerRow r v beta n=0 := Function.extend_apply' _ _ n hn
      simp [hz]
  exact ((Nat.pow_left_injective hr.ne').hasSum_iff
    (f := fun n => LSeries.term (powerRow r v beta) s n) hz).mp hcomp

/-- Multiplication by r cancels the scale derivative in the residue.
The matched source amplitude is EXACTLY v for every r>0. -/
theorem tendsto_power_source {r : ℕ} (hr : 0<r) (v : ℂ) (beta : ℝ) :
    Tendsto (fun s : ℂ => (s-(beta : ℂ))*response r v beta s)
      (𝓝[≠] (beta : ℂ)) (𝓝 v) := by
  have hr0 : (r : ℂ)≠0 := Nat.cast_ne_zero.mpr hr.ne'
  have ht : Tendsto (fun s : ℂ => (r : ℂ)*s)
      (𝓝[≠] (beta : ℂ)) (𝓝[≠] (((r : ℝ)*beta : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun s : ℂ => (r : ℂ)*s) := continuous_const.mul continuous_id
      simpa only [Complex.ofReal_mul,Complex.ofReal_natCast] using
        hc.continuousAt.tendsto.mono_left
          (show 𝓝[≠] (beta : ℂ)≤𝓝 (beta : ℂ) from nhdsWithin_le_nhds)
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff,Set.mem_singleton_iff] at hs ⊢
      intro he
      simp only [Complex.ofReal_mul,Complex.ofReal_natCast] at he
      exact hs (mul_left_cancel₀ hr0 he)
  have hh := (tendsto_smooth_source v ((r : ℝ)*beta)).comp ht
  convert hh using 1
  funext s
  dsimp only [response,Function.comp_def]
  push_cast
  ring

/-- No hidden ordinary-density pole is restored by concentrating the
matched component on the growing-gap integer support. -/
theorem analyticAt_density {r : ℕ} (hr : 0<r) (v : ℂ) {beta : ℝ} (hb : beta<1) :
    AnalyticAt ℂ (response r v beta) 1 := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hne : (r : ℂ)*1-(((r : ℝ)*beta-1 : ℝ) : ℂ)≠1 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [mul_one,Complex.sub_re,Complex.natCast_re,
      Complex.one_re,Complex.ofReal_re] at hh
    nlinarith only [hrR,hb,hh]
  let f : ℂ → ℂ := fun s => (r : ℂ)*s-(((r : ℝ)*beta-1 : ℝ) : ℂ)
  have hf : AnalyticAt ℂ f 1 := by dsimp [f]; fun_prop
  have hz : AnalyticAt ℂ riemannZeta (f 1) := analyticOn_riemannZeta _ hne
  have ha : AnalyticAt ℂ (fun s => riemannZeta (f s)) 1 := hz.comp hf
  exact analyticAt_const.mul (analyticAt_const.mul ha)

theorem hasDensityFreeSource {r : ℕ} (hr : 0<r) {v : ℂ} (hv : v≠0)
    {beta : ℝ} (hb : beta<1) : HasDensityFreeSource (powerRow r v beta) beta v :=
  ⟨hv,response r v beta,
    (fun _ hs => (power_hasSum hr v beta hs).LSeriesSummable),
    (fun _ hs => (power_hasSum hr v beta hs).LSeries_eq),
    analyticAt_density hr v hb,tendsto_power_source hr v beta⟩

/-- The growing support gap uses ordinary integer addition and powers,
not a pointwise norm or a continuous spacing approximation. -/
theorem power_pair_zero {r H n h : ℕ} (hr : 2≤r) (hH : 0<H)
    (hn : H^r≤n) (hh : 0<h) (hsize : h≤H^(r-1)) (v : ℂ) (beta : ℝ) :
    powerRow r v beta n*conj (powerRow r v beta (n+h))=0 := by
  by_cases hleft : powerRow r v beta n=0
  · rw [hleft,zero_mul]
  by_cases hright : powerRow r v beta (n+h)=0
  · rw [hright,map_zero,mul_zero]
  obtain ⟨a,ha⟩ := powerRow_ne_zero_implies_power r v beta hleft
  obtain ⟨b,hb⟩ := powerRow_ne_zero_implies_power r v beta hright
  have hr0 : r≠0 := by omega
  have hHa : H≤a := (Nat.pow_le_pow_iff_left hr0).mp (by rwa [ha])
  have hab : a<b := by
    by_contra h
    have hp := Nat.pow_le_pow_left (by omega : b≤a) r
    rw [ha,hb] at hp
    omega
  have hs := Nat.pow_le_pow_left (show a+1≤b by omega) r
  have hg := pow_add_mul_le_add_pow (a := a) (b := (1 : ℕ)) (by omega) (by omega) r
  simp only [mul_one] at hg
  have hp := Nat.pow_le_pow_left hHa (r-1)
  have hp0 : 0<H^(r-1) := by positivity
  rw [hb] at hs
  rw [ha] at hg
  nlinarith only [hr,hs,hg,hp,hp0,hsize]

/-- Join every growing lag and every correlated physical mask before
estimating: this entire detector is exactly zero in the model. -/
def bulkLagPacket (r H : ℕ) (S : Finset ℕ) (W : ℕ → ℕ → ℂ) (g : ℕ → ℂ) : ℂ :=
  ∑ h ∈ S, ∑ n ∈ Finset.Icc (H^r) (4*H^r), W n h*g n*conj (g (n+h))

theorem bulkLagPacket_zero {r H : ℕ} (hr : 2≤r) (hH : 0<H) (S : Finset ℕ)
    (hS : ∀ h ∈ S, 0<h ∧ h≤H^(r-1)) (W : ℕ → ℕ → ℂ) (v : ℂ) (beta : ℝ) :
    bulkLagPacket r H S W (powerRow r v beta)=0 := by
  unfold bulkLagPacket
  apply Finset.sum_eq_zero
  intro h hmem
  apply Finset.sum_eq_zero
  intro n hn
  rw [mul_assoc,power_pair_zero hr hH (Finset.mem_Icc.mp hn).1
    (hS h hmem).1 (hS h hmem).2,mul_zero]

/-- One fixed row, not a scale-dependent countermodel, simultaneously
defeats every growing lag code within this power-spacing range. -/
theorem exists_invisible_growing_lag_model {r : ℕ} (hr : 2≤r) {v : ℂ} (hv : v≠0)
    {beta : ℝ} (hb : beta<1) :
    ∃ g : ℕ → ℂ, HasDensityFreeSource g beta v ∧
      (∀ H : ℕ, 0<H → ∀ S : Finset ℕ, (∀ h ∈ S, 0<h ∧ h≤H^(r-1)) →
        ∀ W : ℕ → ℕ → ℂ, bulkLagPacket r H S W g=0) ∧
      ∀ n>0, divisorObservation (inverseRows g) n=g n := by
  refine ⟨powerRow r v beta,hasDensityFreeSource (by omega) hv hb,?_,?_⟩
  · intro H hH S hS W
    exact bulkLagPacket_zero hr hH S hS W v beta
  · intro n hn
    exact observation_inverseRows _ hn

/-- Every rational polynomial sublinear lag range is covered by one
FIXED model. At physical cutoff 4*2^(2*A*J), all lags through
2^(2*B*J) are invisible, for B/A<1. No floating exponent audit is used. -/
theorem exists_invisible_sublinear_lag_model {A B : ℕ} (hBA : B<A)
    {v : ℂ} (hv : v≠0) {beta : ℝ} (hb : beta<1) :
    ∃ g : ℕ → ℂ, HasDensityFreeSource g beta v ∧
      (∀ J : ℕ, ∀ W : ℕ → ℕ → ℂ,
        bulkLagPacket (2*A) (2^J) (Finset.Icc 1 (2^(2*B*J))) W g=0) ∧
      ∀ n>0, divisorObservation (inverseRows g) n=g n := by
  obtain ⟨g,hg,hzero,hdiv⟩ := exists_invisible_growing_lag_model
    (r := 2*A) (by omega) hv hb
  refine ⟨g,hg,?_,hdiv⟩
  intro J W
  apply hzero (2^J) (by positivity)
  intro h hh
  obtain ⟨hh0,hh1⟩ := Finset.mem_Icc.mp hh
  refine ⟨hh0,hh1.trans ?_⟩
  rw [←pow_mul]
  apply Nat.pow_le_pow_right (by omega : 0<(2 : ℕ))
  have hB : 2*B≤2*A-1 := by omega
  nlinarith only [hB]

/-- A linear source never guarantees this growing nonlinear response,
even when its phase and every literal integer mask are retained jointly. -/
theorem source_alone_does_not_force_sublinear_lag_response {A B : ℕ} (hBA : B<A)
    {v : ℂ} (hv : v≠0) {beta : ℝ} (hb : beta<1) :
    ¬ (∀ g : ℕ → ℂ, HasDensityFreeSource g beta v →
      ∃ J : ℕ, ∃ W : ℕ → ℕ → ℂ,
        bulkLagPacket (2*A) (2^J) (Finset.Icc 1 (2^(2*B*J))) W g≠0) := by
  obtain ⟨g,hg,hzero,_⟩ := exists_invisible_sublinear_lag_model hBA hv hb
  intro hh
  obtain ⟨J,W,hne⟩ := hh g hg
  exact hne (hzero J W)

/-- The source amplitude may be the exact actual multiplicity-weighted
commutator residue. The countermodel is still NOT the actual prime row. -/
theorem matched_zero_does_not_force_sublinear_lag_response {A B : ℕ} (hBA : B<A)
    (rho : NontrivialZetaZero) :
    ¬ (∀ g : ℕ → ℂ,
      HasDensityFreeSource g rho.1.re
        (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ)) →
      ∃ J : ℕ, ∃ W : ℕ → ℕ → ℂ,
        bulkLagPacket (2*A) (2^J) (Finset.Icc 1 (2^(2*B*J))) W g≠0) :=
  source_alone_does_not_force_sublinear_lag_response hBA
    (ArithmeticOperatorTwistSourceAudit.commutator_source_ne_zero rho)
    (NontrivialZetaZero.re_lt_one rho)

/-- Not just pairs: every finite additive hyperedge inside the growing
spacing bound vanishes, including arbitrary zero-preserving leg functions. -/
theorem power_pattern_zero {r H n : ℕ} (hr : 2≤r) (hH : 0<H) (hn : H^r≤n)
    (P : Finset ℕ) (hP : ∀ i ∈ P, i≤H^(r-1)) (hcard : 1<P.card)
    (leg : ℕ → ℂ → ℂ) (hleg : ∀ i ∈ P, leg i 0=0) (v : ℂ) (beta : ℝ) :
    (∏ i ∈ P, leg i (powerRow r v beta (n+i)))=0 := by
  classical
  obtain ⟨a,ha,b,hb,hne⟩ := Finset.one_lt_card.mp hcard
  have horder : ∃ a ∈ P, ∃ b ∈ P, a<b := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨a,ha,b,hb,h⟩
    · exact ⟨b,hb,a,ha,h⟩
  obtain ⟨a,ha,b,hb,hab⟩ := horder
  by_contra hprod
  have hnonzero (i : ℕ) (hi : i ∈ P) : powerRow r v beta (n+i)≠0 := by
    intro hz
    exact ((Finset.prod_ne_zero_iff.mp hprod) i hi) (by rw [hz,hleg i hi])
  have hp := power_pair_zero hr hH (show H^r≤n+a by omega)
    (Nat.sub_pos_of_lt hab) (show b-a≤H^(r-1) by have := hP b hb; omega) v beta
  have he : n+a+(b-a)=n+b := by omega
  rw [he] at hp
  exact (mul_ne_zero (hnonzero a ha) (by
    intro hh
    exact hnonzero b hb (by simpa using hh))) hp

end
end RiemannGaussian.ArithmeticOperatorGrowingLagSourceAudit
