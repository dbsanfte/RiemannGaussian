/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeMomentCoherence
import RiemannGaussian.ZetaRieszPrimeCompletionPhase
import RiemannGaussian.ArithmeticOperatorGramAudit
import RiemannGaussian.ArithmeticOperatorGammaTwistAudit
import RiemannGaussian.ZetaSignedPoleControl
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Complete minimum/GCD of a binomial row: exact source-conservation audit

The literal row INCLUDING its unit endpoints has GCD one at every n.
The normalized interior GCD has logarithm EXACTLY the actual Mangoldt
coefficient, with every proper power and both small heads retained.
Its full complex factorial source is consequently the old actual
prime-moment source, after an independently paid proper-power error.

These are source and collapse audits, not a new RH criterion credited
as arithmetic progress. Controls are not granted actual binomial/Gamma
data. Constrained incomplete split families and distinct-prime geometry
are outside this complete-row prototype.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorKummerMinimumAudit
open Complex Filter ZetaPrimeMomentCoherence

/-- Complete literal binomial row; the two unit endpoints are included. -/
def completeGcd (n : ℕ) : ℕ := (Finset.range (n+1)).gcd n.choose

/-- All NONTRIVIAL splits of one row, with empty GCD normalized to one.
The endpoint exclusion is explicit and is never called a small error. -/
def interiorGcd (n : ℕ) : ℕ := max 1 ((Finset.Icc 1 (n-1)).gcd n.choose)

/-- One literal unit endpoint already kills every complete-row source. -/
theorem completeGcd_eq_one (n : ℕ) : completeGcd n=1 := by
  have hd : completeGcd n∣1 := by
    simpa only [completeGcd,Nat.choose_zero_right] using
      Finset.gcd_dvd (f := n.choose)
        (show 0∈Finset.range (n+1) by simp)
  exact Nat.dvd_one.mp hd

/-- The classic prime-power classification is applied to ALL interior
splits at the actual cutoff, not to a selected valuation maximizer. -/
theorem interiorGcd_eq (n : ℕ) :
    interiorGcd n=if IsPrimePow n then n.minFac else 1 := by
  by_cases hp : IsPrimePow n
  · rw [ite_eq_left hp,interiorGcd,Choose.gcd_choose_eq_minFac_of_isPrimePow hp]
    exact max_eq_right (by have := Nat.minFac_pos n; omega)
  · rw [ite_eq_right hp,interiorGcd]
    by_cases hn : 1<n
    · rw [Choose.gcd_choose_eq_one_of_not_isPrimePow hn hp,max_self]
    · have hs : n=0 ∨ n=1 := by omega
      rcases hs with rfl | rfl <;> norm_num

theorem interiorGcd_one_le (n : ℕ) : 1 ≤ interiorGcd n := le_max_left _ _

theorem interiorGcd_prime_power {p r : ℕ} (hp : p.Prime) (hr : 0<r) :
    interiorGcd (p^r)=p := by
  rw [interiorGcd_eq,ite_eq_left (hp.prime.isPrimePow.pow hr.ne'),hp.pow_minFac hr.ne']

/-- Every valuation order survives in the source coefficient: a tower
has GCD p, not p^r and not zero. -/
theorem log_interiorGcd_eq_mangoldt (n : ℕ) :
    Real.log (interiorGcd n)=ArithmeticFunction.vonMangoldt n := by
  rw [interiorGcd_eq,ArithmeticFunction.vonMangoldt_apply]
  split_ifs <;> simp

theorem log_interiorGcd_nonneg (n : ℕ) : 0≤Real.log (interiorGcd n) := by
  rw [log_interiorGcd_eq_mangoldt]
  exact ArithmeticFunction.vonMangoldt_nonneg

theorem interiorGcd_gt_one_iff (n : ℕ) : 1 < interiorGcd n ↔ IsPrimePow n := by
  rw [interiorGcd_eq]
  by_cases hp : IsPrimePow n
  · rw [ite_eq_left hp]
    exact iff_of_true (Nat.minFac_prime hp.ne_one).one_lt hp
  · simp [hp]

/-- The entire joined packet, with moving masks and phases permitted
in w. No divisor, prime-power or physical endpoint is omitted. -/
def packet (X : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ n∈Finset.Icc 1 X,(Real.log (interiorGcd n) : ℂ)*w n

theorem packet_eq_original (X : ℕ) (w : ℕ → ℂ) :
    packet X w=∑ n∈Finset.Icc 1 X,(ArithmeticFunction.vonMangoldt n : ℂ)*w n := by
  simp only [packet,log_interiorGcd_eq_mangoldt]

/-- Any full two-row correlated mask also sees exactly the SAME actual
Mangoldt pair, not a new cross-prime constraint or a nonlinear source. -/
theorem joined_pair_eq_original (X Y : ℕ) (W : ℕ → ℕ → ℂ) :
    (∑ n∈Finset.Icc 1 X,∑ m∈Finset.Icc 1 Y,
      (Real.log (interiorGcd n) : ℂ)*(Real.log (interiorGcd m) : ℂ)*W n m)=
    ∑ n∈Finset.Icc 1 X,∑ m∈Finset.Icc 1 Y,
      (ArithmeticFunction.vonMangoldt n : ℂ)*(ArithmeticFunction.vonMangoldt m : ℂ)*W n m := by
  simp only [log_interiorGcd_eq_mangoldt]

/-- Arbitrary-weight payment of the complete observation would already
pay the old scalar Mangoldt test; it fails as soon as prime two is kept. -/
theorem no_free_weight_payment {X : ℕ} (hX : 2≤X) (B : ℝ) :
    ¬∀ w : ℕ → ℂ,‖packet X w‖≤B := by
  intro h
  have hh : ∀ w : ℕ → ℂ,
      ‖∑ n∈Finset.Icc 1 X,w n*(ArithmeticFunction.vonMangoldt n : ℂ)‖≤B := by
    intro w
    simpa only [packet_eq_original,mul_comm] using h w
  have hz := (ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff
    (Finset.Icc 1 X) (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) B).mp hh |>.2
  have h2 := hz 2 (Finset.mem_Icc.mpr ⟨by norm_num,hX⟩)
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    Complex.ofReal_eq_zero] at h2
  exact (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne' h2

/-- The exact continued scalar response; the series below is only used
in the Euler half-plane. -/
def response (s : ℂ) : ℂ := -logDeriv riemannZeta s

theorem phased_euler_response (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => (Real.log (interiorGcd n) : ℂ)*SuzukiCarryCorrelation.primePhase y n) s=
      response (s+I*y) := by
  simp only [log_interiorGcd_eq_mangoldt]
  rw [ArithmeticOperatorGammaTwistAudit.LSeries_primePhase,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs)]
  rw [response,logDeriv_apply,neg_div]

/-- Exact density subtraction, made BEFORE any source estimate. -/
def centeredResponse (s : ℂ) : ℂ := response s-1/(s-1)

/-- The density subtraction has a genuine analytic germ at one. -/
theorem centered_density_analytic :
    ∃ E : ℂ → ℂ,AnalyticAt ℂ E 1 ∧ centeredResponse=ᶠ[𝓝[≠] (1 : ℂ)] E := by
  have hA := differentiable_riemannZeta₁.analyticAt (1 : ℂ)
  have hn : riemannZeta₁ (1 : ℂ)≠0 := by simp
  refine ⟨fun s => -logDeriv riemannZeta₁ s,(hA.deriv.div hA hn).neg,?_⟩
  filter_upwards [hA.continuousAt.eventually_ne hn |>.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs (hs1 : s≠1)
  have hz : riemannZeta s≠0 := by
    rw [riemannZeta_eq_inv_sub_mul hs1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hs1)) hs
  rw [centeredResponse,response,neg_logDeriv_riemannZeta_eq_pole_sub hs1 hz]
  ring

/-- Every genuine nontrivial zero has the original negative analytic
multiplicity source, without exposure or a diagnostic-source inference. -/
theorem actual_zero_source (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*response s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_riemannZeta_nontrivialZero rho)
    (analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)).neg
  simpa only [response,analyticZetaZeroMultiplicity,mul_neg] using h

theorem centered_actual_zero_source (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*centeredResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hc : ContinuousAt (fun s : ℂ => (s-rho.1)*(1/(s-1))) rho.1 := by
    fun_prop (disch := exact sub_ne_zero.mpr rho.2.2.2)
  have hz : Tendsto (fun s : ℂ => (s-rho.1)*(1/(s-1))) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have h := (actual_zero_source rho).sub hz
  simpa only [mul_sub,centeredResponse,sub_zero] using h

theorem source_ne_zero (rho : NontrivialZetaZero) :
    -(analyticZetaZeroMultiplicity rho : ℂ)≠0 :=
  neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (analyticZetaZeroMultiplicity_positive rho)))

/-- Every literal factorial order retains all integers and the full
height phase. This definition is an audit observation, not a new carrier. -/
def minimumMoment (k : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ,(Real.log (interiorGcd n) : ℂ)*zetaPrimeLogKernel k s n

theorem hasSum_minimumMoment {s : ℂ} (hs : 1<s.re) (k : ℕ) :
    HasSum (fun n : ℕ => (Real.log (interiorGcd n) : ℂ)*zetaPrimeLogKernel k s n)
      (zetaPrimeLogMoment k s) := by
  simpa only [log_interiorGcd_eq_mangoldt,zetaPrimeLogKernel,mul_assoc] using
    hasSum_zetaPrimeLogMoment hs k

theorem minimumMoment_eq {s : ℂ} (hs : 1<s.re) (k : ℕ) :
    minimumMoment k s=zetaPrimeLogMoment k s := (hasSum_minimumMoment hs k).tsum_eq

/-- Full source-scaled interior minimum, including ALL proper powers. -/
def minimumSource (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*minimumMoment k (center y)

theorem minimumSource_eq (u y : ℝ) (k : ℕ) :
    minimumSource u y k=moments u y k+
      (u : ℂ)^(k+1)*zetaProperPrimePowerMoment k (center y) := by
  rw [minimumSource,minimumMoment_eq (by norm_num [ZetaPrimeMomentCoherence.center]),
    zetaPrimeLogMoment_eq_prime_add_proper k (by norm_num [ZetaPrimeMomentCoherence.center]),moments]
  ring

/-- The only limit transfer error is the existing independently paid
proper-power term; no binomial endpoint or mask error is hidden here. -/
theorem proper_scale_tendsto {u : ℝ} (hu : 0≤u) (hu1 : u<1) (y : ℝ) :
    Tendsto (fun k : ℕ => (u : ℂ)^(k+1)*zetaProperPrimePowerMoment k (center y))
      atTop (𝓝 0) := by
  have h := tendsto_zetaProperPrimePowerFilter_mul_pow (1 : Polynomial ℂ) y
    (a := (u : ℂ)) (by simpa only [Complex.norm_real,Real.norm_of_nonneg hu] using hu1)
  have hs : (1 : Polynomial ℂ).support={0} := by
    ext k
    by_cases hk : k=0 <;> simp [Polynomial.mem_support_iff,Polynomial.coeff_one,hk]
  simpa only [zetaProperPrimePowerFilter,hs,Finset.sum_singleton,
    Polynomial.coeff_one_zero,one_mul,Nat.add_zero,ZetaPrimeMomentCoherence.center] using h

/-- Complete minimum coherence is EXACTLY old prime-moment coherence.
This equality is a collapse/no-new-input theorem, not RH progress. -/
theorem minimumSource_tendsto_iff {u y : ℝ} (hu : 0≤u) (hu1 : u<1) (l : ℂ) :
    Tendsto (minimumSource u y) atTop (𝓝 l) ↔ Tendsto (moments u y) atTop (𝓝 l) := by
  have hp := proper_scale_tendsto hu hu1 y
  constructor
  · intro h
    simpa only [sub_zero] using (h.sub hp).congr (fun k => by rw [minimumSource_eq]; ring)
  · intro h
    simpa only [add_zero] using (h.add hp).congr (fun k => (minimumSource_eq u y k).symm)

/-- The actual exposed zero, with arbitrary multiplicity, survives the
interior minimum. No source is inferred for new incomplete split masks. -/
theorem minimum_actual_exposed_source (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖) :
    Tendsto (minimumSource (3/2-rho.1.re) rho.1.im) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  apply (minimumSource_tendsto_iff
    (by linarith [NontrivialZetaZero.re_lt_one rho]) (by linarith) _).mpr
  exact ZetaRieszPrimeCompletionPhase.tendsto_ordinary_prime_source rho hrho hexposed

/-- The reverse identifies the exact ACTUAL zero and its multiplicity,
without exposure, from the same old coherent moment source. -/
theorem minimum_source_identifies_actual_zero {u y : ℝ} (hu : 0<u) (hu1 : u<1)
    {m : ℕ} (hm : 0<m)
    (h : Tendsto (minimumSource u y) atTop (𝓝 (-(m : ℂ)))) :
    ∃ rho : NontrivialZetaZero,rho.1=candidate u y ∧ analyticZetaZeroMultiplicity rho=m :=
  exists_zero_multiplicity_of_tendsto hu hu1 hm ((minimumSource_tendsto_iff hu.le hu1 _).mp h)

/-- Complete endpoints have an identically zero source at every order. -/
def completeSource (u y : ℝ) (k : ℕ) : ℂ :=
  (u : ℂ)^(k+1)*∑' n : ℕ,(Real.log (completeGcd n) : ℂ)*zetaPrimeLogKernel k (center y) n

theorem completeSource_eq_zero (u y : ℝ) (k : ℕ) : completeSource u y k=0 := by
  simp only [completeSource,completeGcd_eq_one,Nat.cast_one,Real.log_one,
    Complex.ofReal_zero,zero_mul,tsum_zero,mul_zero]

/-- Excluding the unit splits restores the FULL original zero source.
It cannot be called a source-small endpoint payment. -/
theorem endpoint_deletion_not_paid (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero,tau≠rho →
      3/2-rho.1.re<‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖) :
    ¬Tendsto (fun k => minimumSource (3/2-rho.1.re) rho.1.im k-
      completeSource (3/2-rho.1.re) rho.1.im k) atTop (𝓝 0) := by
  intro h
  simp only [completeSource_eq_zero,sub_zero] at h
  exact source_ne_zero rho
    (tendsto_nhds_unique (minimum_actual_exposed_source rho hrho hexposed) h)

end RiemannGaussian.ArithmeticOperatorKummerMinimumAudit

#lint+ in RiemannGaussian.ArithmeticOperatorKummerMinimumAudit

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut reports : Array Json := #[]
  for (n,ci) in env.constants.toList do
    if env.isImportedConst n then continue
    declarations := declarations+1
    if ci.isAxiom then throwError "Project-defined axiom: {n}"
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in {n}: {ax}"
    if ci.isTheorem then theorems := theorems+1
    reports := reports.push (Json.mkObj [("declaration",toJson n.toString),
      ("isTheorem",toJson ci.isTheorem),("axioms",toJson (axs.map Name.toString))])
  unless declarations>0 do throwError "Empty complete Kummer-minimum audit."
  logInfo m!"Kummer-minimum audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-kummer-minimum"
  IO.FS.writeFile ".lake/arithmetic-operator-kummer-minimum/axioms.json"
    (Json.mkObj [("scope",toJson "literal complete/interior binomial row GCD, every proper power, actual zero source and exact coherence collapse"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
