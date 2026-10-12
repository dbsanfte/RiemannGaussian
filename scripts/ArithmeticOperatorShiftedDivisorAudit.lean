/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorTwistSourceAudit
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.Linter
import Lean.Util.CollectAxioms

/-!
# Finite shifted-divisor parameter jets do not recover the prime leg

Ordinary divisor parameter derivatives insert polynomials in `log(d)`
against ALL divisors. The actual row inserts von Mangoldt instead. Exact
finite-prefix inversion forces equality already on the individual divisor
weights. Every multiple of six is then a distinct polynomial root, while
the value at two is nonzero: an exact transfer up to X needs degree at
least floor(X/6). This freezes ONLY the fixed finite-log-jet shortcut.

The logarithmic proxy has a convergent Euler response but is analytic at
every matched actual zero. The exact prime leg has a nonzero residue.
Möbius inversion restores that singular source; it supplies no independent
estimate of its literal masked sum. No published estimate is imported.
-/

namespace RiemannGaussian.ArithmeticOperatorShiftedDivisorAudit
noncomputable section
open Complex Filter ArithmeticOperatorGammaTwistAudit
open ArithmeticOperatorTwistSourceAudit SuzukiCarryCorrelation
open scoped BigOperators Topology

/-- A finite shift-parameter jet of ordinary divisor coefficients. -/
def logJetRow (P : Polynomial ℂ) (y : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, P.eval (Real.log d : ℂ)*primePhase y d

/-- The all-divisor logarithmic proxy, before Möbius deconvolution. -/
def logProxy (y : ℝ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, (Real.log d : ℂ)*primePhase y d

/-- Finite-prefix divisor observations are injective, including every
proper power and the unit endpoint. No arbitrary phase is replaced. -/
theorem prefix_divisor_injective {X : ℕ} {f g : ℕ → ℂ}
    (h : ∀ n, 0<n → n≤X → (∑ d ∈ n.divisors, f d) = ∑ d ∈ n.divisors, g d)
    {n : ℕ} (hn : 0<n) (hX : n≤X) : f n = g n := by
  have hs : ∀ m n : ℕ, m∣n → n∈Set.Icc 1 X → m∈Set.Icc 1 X := by
    intro m n hmn hnX
    exact ⟨Nat.pos_of_dvd_of_pos hmn hnX.1, (Nat.le_of_dvd hnX.1 hmn).trans hnX.2⟩
  have hi := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
    (f := fun d => f d-g d) (g := fun _ => (0 : ℂ)) (Set.Icc 1 X) hs
  have hz := hi.mp (by
    intro k hk hkX
    rw [Finset.sum_sub_distrib, h k hk hkX.2, sub_self]) n hn ⟨hn,hX⟩
  apply sub_eq_zero.mp
  exact (by simpa only [mul_zero,Finset.sum_const_zero] using hz.symm)

theorem primePhase_ne_zero (y : ℝ) (n : ℕ) : primePhase y n≠0 := by
  intro h
  have hh := norm_primePhase y n
  rw [h,norm_zero] at hh
  norm_num at hh

/-- Exact native row equality forces the individual jet coefficient to
be von Mangoldt. Positive prefix endpoints and the full twist survive. -/
theorem coefficient_eq_of_rows_eq {X : ℕ} {P : Polynomial ℂ} {y : ℝ}
    (h : ∀ n, 0<n → n≤X → logJetRow P y n=primeLegDivisor (primePhase y) n)
    {n : ℕ} (hn : 0<n) (hX : n≤X) :
    P.eval (Real.log n : ℂ)=(ArithmeticFunction.vonMangoldt n : ℂ) := by
  have hh := prefix_divisor_injective (f := fun d => P.eval (Real.log d : ℂ)*primePhase y d)
    (g := fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) h hn hX
  exact mul_right_cancel₀ (primePhase_ne_zero y n) hh

/-- Ordinary addition supplies linearly many distinct zero-weight
labels: a multiple of six is never a prime power. -/
theorem mangoldt_six_mul (j : ℕ) : ArithmeticFunction.vonMangoldt (6*(j+1))=0 := by
  have h6 : ¬IsPrimePow (6 : ℕ) := by decide
  have hn : ¬IsPrimePow (6*(j+1)) := fun h =>
    h6 (h.dvd (dvd_mul_right 6 (j+1)) (by norm_num))
  rw [ArithmeticFunction.vonMangoldt_apply,ite_eq_right hn]

theorem logarithm_six_mul_injective :
    Function.Injective (fun j : ℕ => (Real.log (6*(j+1) : ℕ) : ℂ)) := by
  intro i j h
  have hh := congrArg Real.exp (Complex.ofReal_injective h)
  rw [Real.exp_log (by positivity),Real.exp_log (by positivity)] at hh
  norm_cast at hh
  omega

/-- A finite-degree exact import is quantitatively impossible: even
on a literal prefix, its degree must grow linearly with the cutoff. -/
theorem cutoff_div_six_le_jet_degree {X : ℕ} (hX : 2≤X) {P : Polynomial ℂ} {y : ℝ}
    (h : ∀ n, 0<n → n≤X → logJetRow P y n=primeLegDivisor (primePhase y) n) :
    X/6≤P.natDegree := by
  have htwo := coefficient_eq_of_rows_eq h (by norm_num : 0<(2 : ℕ)) hX
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at htwo
  have hP : P≠0 := by
    intro he
    rw [he,Polynomial.eval_zero] at htwo
    have hh := congrArg Complex.re htwo
    simp only [Complex.zero_re,Complex.ofReal_re] at hh
    exact (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne' hh.symm
  let Z : Finset ℂ := (Finset.range (X/6)).image (fun j => (Real.log (6*(j+1) : ℕ) : ℂ))
  have hc : Z.card=X/6 := by
    rw [Finset.card_image_of_injective _ logarithm_six_mul_injective,Finset.card_range]
  have hr : Z.val⊆P.roots := by
    intro z hz
    change z∈Z at hz
    rcases Finset.mem_image.mp hz with ⟨j,hj,rfl⟩
    have hjX : 6*(j+1)≤X := by
      calc
        _ ≤ 6*(X/6) := Nat.mul_le_mul_left 6 (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
        _ ≤ X := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self X 6
    apply (Polynomial.mem_roots hP).mpr
    change P.eval (Real.log (6*(j+1) : ℕ) : ℂ)=0
    rw [coefficient_eq_of_rows_eq h (by omega) hjX,mangoldt_six_mul,Complex.ofReal_zero]
  simpa only [hc] using Polynomial.card_le_degree_of_subset_roots hr

/-- No fixed finite polynomial in log can give all actual twisted
prime-divisor rows. This is NOT an obstruction to a new inverse estimate. -/
theorem no_fixed_log_jet (P : Polynomial ℂ) (y : ℝ) :
    ¬(∀ n, 0<n → logJetRow P y n=primeLegDivisor (primePhase y) n) := by
  intro h
  have hh := cutoff_div_six_le_jet_degree
    (X := 6*(P.natDegree+1)) (by omega) (fun n hn _ => h n hn)
  have hdiv : 6*(P.natDegree+1)/6=P.natDegree+1 := by omega
  rw [hdiv] at hh
  omega

theorem logProxy_eq_convolution (y : ℝ) :
    logProxy y=LSeries.convolution
      (fun d => (Real.log d : ℂ)*primePhase y d) (1 : ℕ → ℂ) := by
  funext n
  rw [LSeries.convolution_def]
  simp only [logProxy,Pi.one_apply,mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun d _ => (Real.log d : ℂ)*primePhase y d)]

private theorem convolution_assoc (f g h : ℕ → ℂ) :
    LSeries.convolution (LSeries.convolution f g) h=
      LSeries.convolution f (LSeries.convolution g h) := by
  simp only [LSeries.convolution,ArithmeticFunction.toArithmeticFunction_eq_self,mul_assoc]

/-- The phase stays on BOTH multiplicative fibers in an exact inverse.
This identity grants no actual Gamma data to an arbitrary input array. -/
theorem convolution_twisted (f g : ℕ → ℂ) (y : ℝ) (n : ℕ) :
    LSeries.convolution (fun d => f d*primePhase y d) (fun d => g d*primePhase y d) n=
      LSeries.convolution f g n*primePhase y n := by
  rw [LSeries.convolution_def,LSeries.convolution_def,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro da hda
  have hm := (Nat.mem_divisorsAntidiagonal.mp hda).1
  have hd : 0<da.1 := (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hda).bot_lt
  have ha : 0<da.2 := (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hda).bot_lt
  have hp : primePhase y da.1*primePhase y da.2=primePhase y n := by
    rw [←primePhase_mul y hd ha,hm]
  calc
    _ = f da.1*g da.2*(primePhase y da.1*primePhase y da.2) := by ring
    _ = _ := by rw [hp]

private theorem moebius_logPhase (y : ℝ) :
    LSeries.convolution (fun d => (ArithmeticFunction.moebius d : ℂ)*primePhase y d)
      (fun d : ℕ => (Real.log d : ℂ)*primePhase y d)=
      fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d := by
  funext n
  by_cases hn : n=0
  · simp [hn]
  rw [convolution_twisted _ _ y n]
  have hh := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => (ArithmeticFunction.vonMangoldt d : ℂ))
    (g := fun d => (Real.log d : ℂ))).mp (fun d _ => by
      rw [←Complex.ofReal_sum,ArithmeticFunction.vonMangoldt_sum]) n (Nat.pos_of_ne_zero hn)
  rw [LSeries.convolution_def]
  dsimp only
  rw [hh]

private theorem primeLeg_eq_convolution (y : ℝ) :
    primeLegDivisor (primePhase y)=LSeries.convolution
      (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d) (1 : ℕ → ℂ) := by
  funext n
  rw [LSeries.convolution_def]
  simp only [primeLegDivisor,Pi.one_apply,mul_one]
  rw [Nat.sum_divisorsAntidiagonal (fun d _ =>
    (ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d)]

/-- Exact native Möbius deconvolution of the all-divisor logarithmic
proxy. All unit/proper-power endpoints, inverse signs and phases remain. -/
theorem moebius_logProxy_eq_primeLeg (y : ℝ) :
    LSeries.convolution (fun d => (ArithmeticFunction.moebius d : ℂ)*primePhase y d)
      (logProxy y)=primeLegDivisor (primePhase y) := by
  rw [logProxy_eq_convolution,←convolution_assoc,moebius_logPhase,primeLeg_eq_convolution]

/-- An arbitrary literal correlated mask must follow the inverse
product fiber. A divisor theorem for the proxy cannot silently drop it. -/
theorem masked_inverse_identity (S : Finset ℕ) (w : ℕ → ℂ) (y : ℝ) :
    (∑ n ∈ S, w n*primeLegDivisor (primePhase y) n)=
      ∑ n ∈ S, w n*(∑ da ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius da.1 : ℂ)*primePhase y da.1*logProxy y da.2) := by
  rw [←moebius_logProxy_eq_primeLeg,LSeries.convolution_def]

private theorem logPhase_eq_coupled (y : ℝ) :
    (fun d : ℕ => (Real.log d : ℂ)*primePhase y d)=coupledDivisor (primePhase y) := by
  funext n
  by_cases hn : n=0
  · simp [hn,coupledDivisor]
  · rw [coupledDivisor_primePhase y (Nat.pos_of_ne_zero hn),mul_comm]

/-- Genuine absolute convergence of the logarithmic proxy, with no
claim about an Euler series inside its convergence boundary. -/
theorem logProxy_euler_response (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (logProxy y) s=riemannZeta s*(-deriv riemannZeta (s+I*y)) := by
  have ht : 1<(s+I*y).re := by simpa using hs
  have hl : LSeriesSummable (fun d => (Real.log d : ℂ)*primePhase y d) s := by
    rw [LSeriesSummable_primePhase_iff]
    have hab : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ)<(s+I*y).re := by
      simpa only [LSeries.abscissaOfAbsConv_one] using
        (show (1 : EReal)<((s+I*y).re : EReal) from by exact_mod_cast ht)
    have he : (fun d : ℕ => (Real.log d : ℂ))=LSeries.logMul (1 : ℕ → ℂ) := by
      funext d
      simp only [LSeries.logMul,Pi.one_apply,mul_one,Complex.natCast_log]
    rw [he]
    exact LSeriesSummable_logMul_of_lt_re hab
  rw [logProxy_eq_convolution,LSeries_convolution' hl (LSeriesSummable_one_iff.mpr hs),
    logPhase_eq_coupled,coupled_series_eq_shifted_derivative hs y,
    LSeries_one_eq_riemannZeta hs,mul_comm]

/-- Prime-leg continuation in the original zeta coordinate. -/
def primeResponse (y : ℝ) (z : ℂ) : ℂ :=
  riemannZeta (z-I*y)*(-logDeriv riemannZeta z)

/-- The fixed all-divisor logarithmic proxy has no reciprocal zeta. -/
def proxyResponse (y : ℝ) (z : ℂ) : ℂ :=
  riemannZeta (z-I*y)*(-deriv riemannZeta z)

theorem primeResponse_euler (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (primeLegDivisor (primePhase y)) s=primeResponse y (s+I*y) := by
  simpa only [primeResponse,add_sub_cancel_right] using primeLeg_euler_response y hs

theorem proxyResponse_euler (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (logProxy y) s=proxyResponse y (s+I*y) := by
  simpa only [proxyResponse,add_sub_cancel_right] using logProxy_euler_response y hs

/-- On the Euler half-plane the EXACT inverse restores the source
denominator. No estimate is transferred across this division. -/
theorem primeResponse_eq_proxy_div_zeta (y : ℝ) {z : ℂ} (hz : 1<z.re) :
    primeResponse y z=proxyResponse y z/riemannZeta z := by
  unfold primeResponse proxyResponse
  rw [logDeriv_apply]
  field_simp [riemannZeta_ne_zero_of_one_lt_re hz]

private theorem analyticAt_outer_zeta (rho : NontrivialZetaZero) :
    AnalyticAt ℂ (fun z => riemannZeta (z-I*rho.1.im)) rho.1 := by
  have he : rho.1-I*rho.1.im=(rho.1.re : ℂ) := by apply Complex.ext <;> simp
  have hne : (rho.1.re : ℂ)≠1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.ofReal_re,Complex.one_re] at hh
    exact (NontrivialZetaZero.re_lt_one rho).ne hh
  exact (analyticOn_riemannZeta _ (by rwa [he])).comp
    ((analyticAt_id (𝕜 := ℂ) (z := rho.1)).sub analyticAt_const)

/-- The proxy is regular at EVERY actual matched zero, including
multiple zeros; no exposure, simplicity or RH premise enters. -/
theorem analyticAt_proxyResponse (rho : NontrivialZetaZero) :
    AnalyticAt ℂ (proxyResponse rho.1.im) rho.1 :=
  (analyticAt_outer_zeta rho).mul ((analyticAt_riemannZeta_nontrivialZero rho).deriv.neg)

theorem proxy_zero_source (rho : NontrivialZetaZero) :
    Tendsto (fun z : ℂ => (z-rho.1)*proxyResponse rho.1.im z)
      (𝓝[≠] rho.1) (𝓝 0) := by
  have hz : Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self] using (show Tendsto (fun z : ℂ => z-rho.1)
      (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simpa only [zero_mul] using hz.mul
    ((analyticAt_proxyResponse rho).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)

/-- By contrast the actual prime leg retains the exact nonzero
multiplicity-weighted source already checked in the commutator audit. -/
theorem prime_zero_source (rho : NontrivialZetaZero) :
    Tendsto (fun z : ℂ => (z-rho.1)*primeResponse rho.1.im z)
      (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ))) := by
  have hz : Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa only [sub_self] using (show Tendsto (fun z : ℂ => z-rho.1)
      (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hd : Tendsto (deriv riemannZeta) (𝓝[≠] rho.1) (𝓝 (deriv riemannZeta rho.1)) :=
    (analyticAt_riemannZeta_nontrivialZero rho).deriv.continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds
  have ht := (tendsto_commutator_source rho).sub (hz.mul hd)
  simp only [zero_mul,sub_zero] at ht
  convert ht using 1
  funext z
  unfold ArithmeticOperatorTwistSourceAudit.response primeResponse
  ring

/-- An actual inverse-source transfer cannot be source-o(1). The
ordinary divisor proxy loses exactly the residue the target must retain. -/
theorem prime_sub_proxy_source (rho : NontrivialZetaZero) :
    Tendsto (fun z : ℂ => (z-rho.1)*(primeResponse rho.1.im z-proxyResponse rho.1.im z))
      (𝓝[≠] rho.1)
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*riemannZeta (rho.1.re : ℂ))) := by
  simpa only [sub_zero,mul_sub] using (prime_zero_source rho).sub (proxy_zero_source rho)

theorem prime_sub_proxy_not_source_small (rho : NontrivialZetaZero) :
    ¬Tendsto (fun z : ℂ => (z-rho.1)*(primeResponse rho.1.im z-proxyResponse rho.1.im z))
      (𝓝[≠] rho.1) (𝓝 0) := by
  intro h
  exact commutator_source_ne_zero rho (tendsto_nhds_unique (prime_sub_proxy_source rho) h)

end
end RiemannGaussian.ArithmeticOperatorShiftedDivisorAudit

#lint+ in RiemannGaussian.ArithmeticOperatorShiftedDivisorAudit

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
  unless declarations>0 do throwError "Empty shifted-divisor audit."
  logInfo m!"Shifted-divisor audit: {declarations} declarations, {theorems} theorems; only standard axioms."
  IO.FS.createDirAll ".lake/arithmetic-operator-shifted-divisor"
  IO.FS.writeFile ".lake/arithmetic-operator-shifted-divisor/axioms.json"
    (Json.mkObj [("scope",toJson "exact finite-log-jet replacement needs degree >= floor(X/6); logarithmic proxy source lost and restored by unpaid exact Mobius inverse"),
      ("onlyStandardAxioms",toJson true),("namespaceLinters",toJson (15:Nat)),
      ("allLocalDeclarationsByModuleProvenance",toJson true),
      ("declarations",toJson declarations),("theoremsIncludingGeneratedHelpers",toJson theorems),
      ("declarationAxioms",Json.arr reports)]).pretty
