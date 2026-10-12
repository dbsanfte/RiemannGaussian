/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorGammaPatternAudit
import RiemannGaussian.ArithmeticOperatorGammaHierarchyAudit

/-!
# Fixed complete Gamma rows at different dilation scales are source-blind

Every divisor and actual prime power in each row is retained, including
its indispensable cofactor height phase. Different positive integer scale
factors are allowed, without a nearby-endpoint restriction. Joining the
finite product gives one phased polynomial in log(n). Its genuine Euler
series is a finite combination of derivatives of zeta, analytic at every
point with real part different from one. Thus this nonlinear COMPLETE
Gamma prototype has no matched off-line zero residue.

This is a source-gate rejection, not an estimate of an incomplete divisor
row, a prime-leg-only twist, a moving degree/scale family or its commutator.
-/

namespace RiemannGaussian.ArithmeticOperatorGammaDilationAudit
noncomputable section
open Complex Filter ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Topology Classical

/-- Literal product of complete, differently dilated integer divisor rows. -/
def packet (S : Finset ℕ) (scale : ℕ → ℕ) (y : ℕ → ℝ) (n : ℕ) : ℂ :=
  ∏ i ∈ S, coupledDivisor (primePhase (y i)) (scale i*n)

/-- The full fixed scale phase, kept without norm payment. -/
def scalePhase (S : Finset ℕ) (scale : ℕ → ℕ) (y : ℕ → ℝ) : ℂ :=
  ∏ i ∈ S, primePhase (y i) (scale i)

/-- Coefficient of a particular subset of logarithmic slots. -/
def subsetCoefficient (S U : Finset ℕ) (scale : ℕ → ℕ) : ℂ :=
  ∏ i ∈ S\U, (Real.log (scale i) : ℂ)

/-- Joined continuation; only the Euler half-plane is asserted to be a sum. -/
def response (S : Finset ℕ) (scale : ℕ → ℕ) (y : ℕ → ℝ) (s : ℂ) : ℂ :=
  scalePhase S scale y * ∑ U ∈ S.powerset,
    subsetCoefficient S U scale * (-1 : ℂ)^U.card *
      iteratedDeriv U.card riemannZeta (s+I*(∑ i ∈ S, y i))

private theorem phase_product (S : Finset ℕ) (y : ℕ → ℝ) (n : ℕ) :
    (∏ i ∈ S, primePhase (y i) n)=primePhase (∑ i ∈ S, y i) n := by
  unfold primePhase
  rw [←Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.sum_mul,Finset.mul_sum,neg_mul,Finset.sum_neg_distrib]

/-- Exact finite integer join, before source analysis or any inequality. -/
theorem packet_eq_log_polynomial (S : Finset ℕ) (scale : ℕ → ℕ) (y : ℕ → ℝ)
    (hscale : ∀ i ∈ S, 0<scale i) {n : ℕ} (hn : 0<n) :
    packet S scale y n = scalePhase S scale y *
      primePhase (∑ i ∈ S, y i) n *
      ∑ U ∈ S.powerset, subsetCoefficient S U scale*(Real.log n : ℂ)^U.card := by
  have he (i : ℕ) (hi : i∈S) :
      coupledDivisor (primePhase (y i)) (scale i*n)=
        (primePhase (y i) (scale i)*primePhase (y i) n)*
          ((Real.log (scale i) : ℂ)+(Real.log n : ℂ)) := by
    rw [coupledDivisor_primePhase _ (Nat.mul_pos (hscale i hi) hn),
      primePhase_mul _ (hscale i hi) hn]
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (hscale i hi).ne')
      (by exact_mod_cast hn.ne'),Complex.ofReal_add]
  unfold packet
  rw [Finset.prod_congr rfl he,Finset.prod_mul_distrib,Finset.prod_mul_distrib,
    phase_product]
  congr 1
  rw [show (∏ i ∈ S, ((Real.log (scale i) : ℂ)+(Real.log n : ℂ)))=
      ∏ i ∈ S, ((Real.log n : ℂ)+(Real.log (scale i) : ℂ)) by
        apply Finset.prod_congr rfl;intro i _;ring,
    Finset.prod_add]
  simp only [Finset.prod_const,subsetCoefficient,mul_comm]

/-- Prefix identity retains the physical endpoint and all product rows. -/
theorem cutoff_packet_eq (S : Finset ℕ) (scale : ℕ → ℕ) (y : ℕ → ℝ)
    (hscale : ∀ i ∈ S, 0<scale i) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, packet S scale y n)=
      scalePhase S scale y * ∑ n ∈ Finset.Icc 1 X,
        primePhase (∑ i ∈ S, y i) n *
          ∑ U ∈ S.powerset, subsetCoefficient S U scale*(Real.log n : ℂ)^U.card := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun n hn =>
    (packet_eq_log_polynomial S scale y hscale (Finset.mem_Icc.mp hn).1).trans
      (by ring))

private theorem iterated_log_one (k n : ℕ) :
    (LSeries.logMul^[k] (1 : ℕ → ℂ)) n=(Real.log n : ℂ)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',LSeries.logMul,ih,←Complex.natCast_log]
    ring

private theorem logPower_summable (k : ℕ) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (fun n : ℕ => (Real.log n : ℂ)^k) s := by
  have hb : LSeries.abscissaOfAbsConv (LSeries.logMul^[k] (1 : ℕ → ℂ))<s.re := by
    rw [LSeries.absicssaOfAbsConv_logPowMul,LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hs
  have hh := LSeriesSummable_of_abscissaOfAbsConv_lt_re hb
  simpa only [funext (iterated_log_one k)] using hh

private theorem logPower_series (k : ℕ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n : ℕ => (Real.log n : ℂ)^k) s=
      (-1 : ℂ)^k*iteratedDeriv k riemannZeta s := by
  have he : LSeries (1 : ℕ → ℂ)=ᶠ[𝓝 s] riemannZeta := by
    filter_upwards [isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hs]
      with z hz
    exact LSeries_one_eq_riemannZeta hz
  have hb : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ)<s.re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hs
  have hh := LSeries_iteratedDeriv (f := (1 : ℕ → ℂ)) k hb
  rw [he.iteratedDeriv_eq k] at hh
  simp only [funext (iterated_log_one k)] at hh
  rw [hh]
  have hsign : (-1 : ℂ)^k*(-1 : ℂ)^k=1 := by
    rw [←mul_pow]
    norm_num
  simp only [←mul_assoc,hsign,one_mul]

/-- Genuine absolute convergence of the joined log-slot series, separately
from its continuation. This does not drop any proper-power incidence. -/
theorem packet_summable (S : Finset ℕ) (scale : ℕ → ℕ) (y : ℕ → ℝ)
    (hscale : ∀ i ∈ S, 0<scale i) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable (packet S scale y) s := by
  have hshift : 1<(s+I*(∑ i ∈ S, y i)).re := by simpa using hs
  have hu (U : Finset ℕ) :
      LSeriesSummable (fun n : ℕ =>
        subsetCoefficient S U scale*(Real.log n : ℂ)^U.card) (s+I*(∑ i ∈ S,y i)) := by
    simpa only [Pi.smul_def,smul_eq_mul] using
      (logPower_summable U.card hshift).smul (subsetCoefficient S U scale)
  have hh := LSeriesSummable.sum (S := S.powerset) (fun U _ => hu U)
  have hf := (LSeriesSummable_primePhase_iff _ (∑ i ∈ S,y i) s).mpr hh
  have hg := hf.smul (scalePhase S scale y)
  apply (LSeriesSummable_congr s ?_).mp hg
  intro n hn
  simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  rw [packet_eq_log_polynomial S scale y hscale (Nat.pos_of_ne_zero hn)]
  ring

/-- Exact Euler response of ALL joined factorial/Gamma slots. Genuine
absolute convergence is proved above, not assumed from the formula. -/
theorem packet_euler_response (S : Finset ℕ) (scale : ℕ → ℕ) (y : ℕ → ℝ)
    (hscale : ∀ i ∈ S, 0<scale i) {s : ℂ} (hs : 1<s.re) :
    LSeries (packet S scale y) s=response S scale y s := by
  have hshift : 1<(s+I*(∑ i ∈ S, y i)).re := by simpa using hs
  have hu (U : Finset ℕ) : LSeriesSummable
      (subsetCoefficient S U scale • (fun n : ℕ => (Real.log n : ℂ)^U.card))
        (s+I*(∑ i ∈ S,y i)) :=
    (logPower_summable U.card hshift).smul _
  let f : ℕ → ℂ := ∑ U ∈ S.powerset,
    subsetCoefficient S U scale • (fun n : ℕ => (Real.log n : ℂ)^U.card)
  have he : ∀ {n : ℕ}, n≠0 → packet S scale y n=
      (scalePhase S scale y • (fun n => f n*primePhase (∑ i ∈ S,y i) n)) n := by
    intro n hn
    simp only [Pi.smul_apply,smul_eq_mul,f,Finset.sum_apply]
    rw [packet_eq_log_polynomial S scale y hscale (Nat.pos_of_ne_zero hn)]
    ring
  rw [LSeries_congr he s,LSeries_smul,LSeries_primePhase]
  change scalePhase S scale y * LSeries
    (∑ U ∈ S.powerset, subsetCoefficient S U scale •
      (fun n : ℕ => (Real.log n : ℂ)^U.card)) (s+I*(∑ i ∈ S,y i))=_
  rw [LSeries_sum (fun U _ => hu U)]
  unfold response
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  rw [LSeries_smul,logPower_series U.card hshift]
  ring

/-- Complete dilation products have no off-line singular source.
No actual-zero exposure, simplicity or multiplicity assumption is needed. -/
theorem response_analyticAt (S : Finset ℕ) (scale : ℕ → ℕ) (y : ℕ → ℝ)
    {s : ℂ} (hs : s.re≠1) : AnalyticAt ℂ (response S scale y) s := by
  have hz : s+I*(∑ i ∈ S,y i)≠1 := by
    intro hh
    apply hs
    have he := congrArg Complex.re hh
    simpa using he
  have ha := analyticOn_riemannZeta _ hz
  have hc : AnalyticAt ℂ (fun z : ℂ => z+I*(∑ i ∈ S,y i)) s :=
    analyticAt_id.add analyticAt_const
  unfold response
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro U _
  exact analyticAt_const.mul
    (AnalyticAt.comp (g := iteratedDeriv U.card riemannZeta)
      (f := fun z : ℂ => z+I*(∑ i ∈ S,y i)) (x := s)
      (by simpa only [iteratedDeriv_eq_iterate] using ha.iterated_deriv U.card) hc)

/-- All actual nontrivial-zero residues are zero in this entire prototype,
including nonlinear products at non-nearby positive integer dilations. -/
theorem tendsto_response_zero_source (S : Finset ℕ) (scale : ℕ → ℕ)
    (y : ℕ → ℝ) (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*response S scale y s)
      (𝓝[≠] rho.1) (𝓝 0) := by
  have hz : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1)
      (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  have ha := response_analyticAt S scale y (ne_of_lt (NontrivialZetaZero.re_lt_one rho))
  simpa only [zero_mul] using hz.mul
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- A finite analytic transform-level code of whole dilation products is
also source-blind. A singular code would be additional analytic input. -/
theorem tendsto_finite_analytic_code_zero_source {ι : Type*} (A : Finset ι)
    (S : ι → Finset ℕ) (scale : ι → ℕ → ℕ) (y : ι → ℕ → ℝ)
    (code : ι → ℂ → ℂ) (rho : NontrivialZetaZero)
    (hcode : ∀ i ∈ A, AnalyticAt ℂ (code i) rho.1) :
    Tendsto (fun s : ℂ => (s-rho.1)*∑ i ∈ A,
      code i s*response (S i) (scale i) (y i) s) (𝓝[≠] rho.1) (𝓝 0) := by
  have he : (fun s : ℂ => (s-rho.1)*∑ i ∈ A,
      code i s*response (S i) (scale i) (y i) s)=
      fun s => ∑ i ∈ A, code i s*((s-rho.1)*response (S i) (scale i) (y i) s) := by
    funext s
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [he]
  simpa only [mul_zero,Finset.sum_const_zero] using
    tendsto_finsetSum A (fun i hi =>
      ((hcode i hi).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).mul
        (tendsto_response_zero_source (S i) (scale i) (y i) rho))

/-- Explicit no-go endpoint: a nonzero matched residue cannot arise
from the exact completed row product, regardless of actual multiplicity. -/
theorem no_nonzero_response_source (S : Finset ℕ) (scale : ℕ → ℕ)
    (y : ℕ → ℝ) (rho : NontrivialZetaZero) {v : ℂ} (hv : v≠0) :
    ¬Tendsto (fun s : ℂ => (s-rho.1)*response S scale y s)
      (𝓝[≠] rho.1) (𝓝 v) := by
  intro hh
  exact hv (tendsto_nhds_unique hh (tendsto_response_zero_source S scale y rho))

end
end RiemannGaussian.ArithmeticOperatorGammaDilationAudit
