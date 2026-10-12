/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import scripts.ArithmeticOperatorPFreeTwoAudit
import scripts.ArithmeticOperatorCrossUnitAudit
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Actual Euler source of the unmarked cofactor-two p-free trace

The native resonant trace is exactly a fixed principal/mod-four character
selector. Its ordinary-prime Euler continuation has a nonzero actual zeta
source, even after exact density-pole removal. This is a scoped collapse
audit, not an independent signed estimate or a native cutoff-source theorem.
Every proper prime power is retained in an explicit analytic correction.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators Classical Topology
namespace RiemannGaussian.ArithmeticOperatorPFreeTwoSourceAudit
open Complex Filter ArithmeticOperatorPFreeUnitAudit ArithmeticOperatorPFreeTwoAudit
open ArithmeticOperatorCrossUnitAudit

/-- The old parity selector, extended by the actual level-eight characters. -/
def selector (n : ℕ) : ℂ := ((1 : DirichletCharacter ℂ 8) n+charFour n)/2

theorem charFour_nat (n : ℕ) : charFour n=(ZMod.χ₄ n : ℂ) := by
  change (ZMod.χ₄ (((n : ZMod 8).val : ℕ) : ZMod 4) : ℂ)=_
  rw [ZMod.val_natCast]
  have hc : ((n%8 : ℕ) : ZMod 4)=(n : ZMod 4) := by
    rw [ZMod.natCast_eq_natCast_iff']
    omega
  rw [hc]

theorem principal_odd {n : ℕ} (hn : Odd n) : (1 : DirichletCharacter ℂ 8) n=1 := by
  apply MulChar.one_apply
  rw [ZMod.isUnit_iff_coprime]
  simpa only [show (2 : ℕ)^3=8 by norm_num] using
    (Nat.coprime_two_right.mpr hn).pow_right 3

theorem quadCode_neg_one {q : ℕ} [Fact q.Prime] (hq2 : q≠2) :
    quadCode q (-1)=(ZMod.χ₄ q : ℂ) := by
  rw [show (-1 : ZMod q)=((-1 : ℤ) : ZMod q) by norm_cast,
    quadCode_int,legendreSym.at_neg_one hq2]

/-- Literal ordinary-prime resonant row; prime two is a separate excluded head. -/
def twoQuadTrace (q : ℕ) : ℂ :=
  if h : q.Prime ∧ q≠2 then
    letI : Fact q.Prime := ⟨h.1⟩
    codedUnitTrace (1 : DirichletCharacter ℂ 2) (quadCode q) (2*q)
      (resonance (1 : DirichletCharacter ℂ 2) (quadCode q))
  else 0

theorem twoQuadTrace_prime {q : ℕ} (hq : q.Prime) (hq2 : q≠2) :
    twoQuadTrace q=selector q := by
  let : Fact q.Prime := ⟨hq⟩
  have hodd : Odd q := hq.odd_of_ne_two hq2
  rw [twoQuadTrace,dite_eq_left ⟨hq,hq2⟩,codedUnitTrace_two_resonant hq hodd,
    quadCode_neg_one hq2,selector,principal_odd hodd,charFour_nat]

theorem twoQuadTrace_two : twoQuadTrace 2=0 := by
  simp [twoQuadTrace]

theorem selector_two : selector 2=0 := by
  have hp : (1 : DirichletCharacter ℂ 8) (2 : ℕ)=0 := by
    apply MulChar.map_nonunit
    change ¬IsUnit ((2 : ℕ) : ZMod 8)
    rw [ZMod.isUnit_iff_coprime]
    decide
  change ((1 : DirichletCharacter ℂ 8) (2 : ℕ)+charFour (2 : ℕ))/2=0
  rw [hp,charFour_nat]
  norm_num [ZMod.χ₄_nat_eq_if_mod_four]

theorem norm_selector_le (n : ℕ) : ‖selector n‖≤1 := by
  unfold selector
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  have hp := (1 : DirichletCharacter ℂ 8).norm_le_one (n : ZMod 8)
  have h4 := charFour.norm_le_one (n : ZMod 8)
  have ht := norm_add_le ((1 : DirichletCharacter ℂ 8) n) (charFour n)
  linarith

/-- Completed character coefficient with all actual prime powers. -/
def bulkCoefficient (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)*selector n

/-- Proper prime powers with exactly the same parity selector. -/
def properCoefficient (n : ℕ) : ℂ := (zetaProperPrimePowerCoefficient n : ℂ)*selector n

/-- The genuine ordinary-prime p-free row coefficient. -/
def rowCoefficient (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)*twoQuadTrace n

theorem rowCoefficient_eq (n : ℕ) :
    rowCoefficient n=bulkCoefficient n-properCoefficient n := by
  by_cases hn2 : n=2
  · subst n
    simp [rowCoefficient,twoQuadTrace_two,bulkCoefficient,properCoefficient,selector_two]
  · by_cases hp : n.Prime
    · rw [rowCoefficient,twoQuadTrace_prime hp hn2]
      simp [bulkCoefficient,properCoefficient,zetaProperPrimePowerCoefficient,hp]
    · simp [rowCoefficient,twoQuadTrace,hp,bulkCoefficient,properCoefficient,
        zetaProperPrimePowerCoefficient]

/-- Exactly the two actual logarithmic derivatives of the joined selector. -/
def completeResponse (s : ℂ) : ℂ :=
  -(logDeriv (1 : DirichletCharacter ℂ 8).LFunction s+logDeriv charFour.LFunction s)/2

theorem bulkCoefficient_summable {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable bulkCoefficient s := by
  apply Summable.of_norm
  apply (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm.of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  unfold bulkCoefficient
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_selector_le n)

theorem bulk_euler {s : ℂ} (hs : 1<s.re) : LSeries bulkCoefficient s=completeResponse s := by
  let f (χ : DirichletCharacter ℂ 8) : ℕ → ℂ :=
    fun n => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)
  have hf (χ : DirichletCharacter ℂ 8) : LSeriesSummable (f χ) s :=
    χ.LSeriesSummable_twist_vonMangoldt hs
  have he (χ : DirichletCharacter ℂ 8) : LSeries (f χ) s=-logDeriv χ.LFunction s := by
    change LSeries ((fun n : ℕ => χ n)*(fun n => (ArithmeticFunction.vonMangoldt n : ℂ))) s=_
    rw [χ.LSeries_twist_vonMangoldt_eq hs,
      ←χ.deriv_LFunction_eq_deriv_LSeries hs,←χ.LFunction_eq_LSeries hs]
    simp only [logDeriv_apply,neg_div]
  have hj : bulkCoefficient=(1/2 : ℂ) • (f 1+f charFour) := by
    funext n
    simp only [bulkCoefficient,selector,Pi.add_apply,Pi.smul_apply,smul_eq_mul,f]
    ring
  rw [hj,LSeries_smul,LSeries_add (hf 1) (hf charFour),he 1,he charFour]
  unfold completeResponse
  ring

theorem phased_bulk_euler (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => bulkCoefficient n*SuzukiCarryCorrelation.primePhase y n) s=
      completeResponse (s+I*y) := by
  rw [ArithmeticOperatorGammaTwistAudit.LSeries_primePhase,bulk_euler (by simpa using hs)]

theorem proper_summable {s : ℂ} (hs : 1/2<s.re) : LSeriesSummable properCoefficient s := by
  apply Summable.of_norm
  apply (LSeriesSummable_zetaProperPrimePower hs).norm.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  unfold properCoefficient
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_selector_le n)

theorem analyticAt_proper {s : ℂ} (hs : 1/2<s.re) : AnalyticAt ℂ (LSeries properCoefficient) s := by
  have ha : LSeries.abscissaOfAbsConv properCoefficient≤(1/2 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun y hy =>
      proper_summable (by simpa using hy))
  exact LSeries_analyticOnNhd _ _ (lt_of_le_of_lt ha (by exact_mod_cast hs))

/-- Euler continuation of the ordinary-prime row, with the explicit proper-power correction. -/
def rowResponse (s : ℂ) : ℂ := completeResponse s-LSeries properCoefficient s

theorem row_euler {s : ℂ} (hs : 1<s.re) : LSeries rowCoefficient s=rowResponse s := by
  have hj : rowCoefficient=bulkCoefficient-properCoefficient := funext rowCoefficient_eq
  rw [hj,LSeries_sub (bulkCoefficient_summable hs) (proper_summable (by linarith)),
    bulk_euler hs,rowResponse]

theorem phased_row_euler (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (fun n => rowCoefficient n*SuzukiCarryCorrelation.primePhase y n) s=
      rowResponse (s+I*y) := by
  rw [ArithmeticOperatorGammaTwistAudit.LSeries_primePhase,row_euler (by simpa using hs)]

/-- Both genuine divisor orders enter with the same sign; simultaneous L-zeros cannot erase it. -/
def sourceMass (rho : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity rho : ℝ)/2+
    (analyticOrderNatAt charFour.LFunction rho.1 : ℝ)/2

theorem tendsto_completeResponse_residue (rho : NontrivialZetaZero) :
    Tendsto (fun s : ℂ => (s-rho.1)*completeResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(sourceMass rho : ℂ))) := by
  have hp := AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (analyticAt_principal rho.2.2.2)
    (by rw [principal_order rho]; exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho)
  have hm : analyticOrderNatAt (1 : DirichletCharacter ℂ 8).LFunction rho.1=
      analyticZetaZeroMultiplicity rho := by
    unfold analyticOrderNatAt analyticZetaZeroMultiplicity
    rw [principal_order rho]
    rfl
  rw [hm] at hp
  have h4 := AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    ((DirichletCharacter.differentiable_LFunction charFour_ne_one).analyticAt rho.1)
    (nonprincipal_order_ne_top charFour charFour_ne_one rho.1)
  convert (hp.add h4).neg.div_const 2 using 1
  · funext s
    unfold completeResponse
    ring
  · simp only [sourceMass,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_natCast,
      Complex.ofReal_ofNat]
    ring

theorem sourceMass_lower (rho : NontrivialZetaZero) :
    (analyticZetaZeroMultiplicity rho : ℝ)/2≤sourceMass rho := by
  unfold sourceMass
  have h4 : (0 : ℝ)≤analyticOrderNatAt charFour.LFunction rho.1 := Nat.cast_nonneg _
  linarith

theorem sourceMass_pos (rho : NontrivialZetaZero) : 0<sourceMass rho := by
  have hp : (0 : ℝ)<analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith [sourceMass_lower rho]

theorem sourceMass_ne_zero (rho : NontrivialZetaZero) : (sourceMass rho : ℂ)≠0 := by
  exact_mod_cast (sourceMass_pos rho).ne'

theorem tendsto_rowResponse_residue (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    Tendsto (fun s : ℂ => (s-rho.1)*rowResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(sourceMass rho : ℂ))) := by
  have ht : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hp := ht.mul ((analyticAt_proper hrho).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [rowResponse,mul_sub,zero_mul,sub_zero] using
    (tendsto_completeResponse_residue rho).sub hp

/-- Exact half-pole removal, leaving the arithmetic selector unchanged. -/
def centeredResponse (s : ℂ) : ℂ := completeResponse s-1/(2*(s-1))

theorem centeredResponse_density_germ :
    centeredResponse=ᶠ[𝓝[≠] (1 : ℂ)]
      (fun s => -(logDeriv filledPrincipal s+logDeriv charFour.LFunction s)/2) := by
  have hlog : logDeriv (1 : DirichletCharacter ℂ 8).LFunction=ᶠ[𝓝[≠] (1 : ℂ)]
      logDeriv (fun s : ℂ => filledPrincipal s/(s-1)) :=
    logDeriv_congr_nhdsNE (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact principal_filled_eq hs)
  have hn : ∀ᶠ s in 𝓝 (1 : ℂ),filledPrincipal s≠0 :=
    (analyticAt_filledPrincipal 1).continuousAt.eventually_ne filledPrincipal_one_ne_zero
  filter_upwards [hlog,hn.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with s hl hns hs
  unfold centeredResponse completeResponse
  rw [hl,logDeriv_fun_div (g := fun w : ℂ => w-1) s hns (sub_ne_zero.mpr hs)
    (analyticAt_filledPrincipal s).differentiableAt (by fun_prop)]
  simp only [logDeriv_apply,deriv_sub_const,deriv_id'',one_div]
  field_simp [sub_ne_zero.mpr hs]
  ring

theorem analyticAt_density_fill :
    AnalyticAt ℂ (fun s => -(logDeriv filledPrincipal s+logDeriv charFour.LFunction s)/2) 1 := by
  have h4 := (DirichletCharacter.differentiable_LFunction charFour_ne_one).analyticAt (1 : ℂ)
  have hp := (analyticAt_filledPrincipal 1).deriv.div (analyticAt_filledPrincipal 1)
    filledPrincipal_one_ne_zero
  exact (hp.add (h4.deriv.div h4 (charFour.LFunction_apply_one_ne_zero charFour_ne_one))).neg.div_const

theorem tendsto_centered_density_residue :
    Tendsto (fun s : ℂ => (s-1)*centeredResponse s) (𝓝[≠] 1) (𝓝 0) := by
  have ht : Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 ((1 : ℂ)-1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have h := ht.mul (analyticAt_density_fill.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at h
  exact h.congr' (centeredResponse_density_germ.symm.mono (fun s he =>
    congrArg (fun v : ℂ => (s-1)*v) he))

/-- The actual completed density pole has coefficient one half. -/
theorem tendsto_complete_density_residue :
    Tendsto (fun s : ℂ => (s-1)*completeResponse s) (𝓝[≠] 1) (𝓝 (1/2)) := by
  have hp : Tendsto (fun s : ℂ => (s-1)*(1/(2*(s-1)))) (𝓝[≠] 1) (𝓝 (1/2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    field_simp [sub_ne_zero.mpr hs]
  convert tendsto_centered_density_residue.add hp using 1
  · funext s
    unfold centeredResponse
    ring
  · norm_num

/-- The pole-centered ordinary-prime row retains all proper powers as a regular correction. -/
def centeredRowResponse (s : ℂ) : ℂ := centeredResponse s-LSeries properCoefficient s

theorem centeredRowResponse_eq (s : ℂ) :
    centeredRowResponse s=rowResponse s-1/(2*(s-1)) := by
  unfold centeredRowResponse rowResponse centeredResponse
  ring

theorem tendsto_centeredRowResponse_residue (rho : NontrivialZetaZero) (hrho : 1/2<rho.1.re) :
    Tendsto (fun s : ℂ => (s-rho.1)*centeredRowResponse s) (𝓝[≠] rho.1)
      (𝓝 (-(sourceMass rho : ℂ))) := by
  have ht : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hc : ContinuousAt (fun s : ℂ => 1/(2*(s-1))) rho.1 :=
    continuousAt_const.div (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
      (mul_ne_zero (by norm_num) (sub_ne_zero.mpr rho.2.2.2))
  have h := (tendsto_rowResponse_residue rho hrho).sub
    (ht.mul (hc.tendsto.mono_left nhdsWithin_le_nhds))
  simpa only [centeredRowResponse_eq,mul_sub,zero_mul,sub_zero] using h

theorem tendsto_centeredRow_density_residue :
    Tendsto (fun s : ℂ => (s-1)*centeredRowResponse s) (𝓝[≠] 1) (𝓝 0) := by
  have ht : Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-1) (𝓝[≠] 1) (𝓝 ((1 : ℂ)-1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hp := ht.mul ((analyticAt_proper (by norm_num : 1/2<(1 : ℂ).re)).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds)
  simpa only [centeredRowResponse,mul_sub,zero_mul,sub_zero] using
    tendsto_centered_density_residue.sub hp

/-- Neither the analytic proper-power correction nor exact pole removal kills
the genuine zero source of this fixed-selector collapse. -/
theorem not_analyticAt_centeredRowResponse (rho : NontrivialZetaZero)
    (hrho : 1/2<rho.1.re) : ¬AnalyticAt ℂ centeredRowResponse rho.1 := by
  intro ha
  have ht : Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun s : ℂ => s-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hz := ht.mul (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at hz
  exact neg_ne_zero.mpr (sourceMass_ne_zero rho)
    (tendsto_nhds_unique (tendsto_centeredRowResponse_residue rho hrho) hz)

end RiemannGaussian.ArithmeticOperatorPFreeTwoSourceAudit

#lint+ in RiemannGaussian.ArithmeticOperatorPFreeTwoSourceAudit

open Lean Elab Command in
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
  unless declarations>0 do throwError "Empty p-free cofactor-two source audit."
  logInfo m!"P-free two source audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-pfree-two-source"
  IO.FS.writeFile ".lake/arithmetic-operator-pfree-two-source/axioms.json"
    (Json.mkObj [("scope",toJson "unmarked ordinary-q cofactor-two trace is a principal/mod-four character selector; its Euler continuation retains every actual right-half-zero residue after analytic proper-power and exact density-pole removal; no native cofinal estimate inferred"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
