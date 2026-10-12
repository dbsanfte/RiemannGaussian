/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ArithmeticOperatorCharacterSourceAudit
import RiemannGaussian.ArithmeticOperatorPeriodicGammaAudit
import RiemannGaussian.ArithmeticOperatorTwistSourceAudit

/-!
# Fixed coprime CRT masks with both character legs retained

The exact arithmetic-progression projection of the actual prime-only
Gamma discrepancy codes BOTH its divisor and its cofactor. Its Euler
response is L(s)*(-logDeriv L(s+iy)) + L'(s+iy), not a bare coded
Mangoldt series. Removing the principal character leaves a matched
zeta-zero residue only if a retained nonprincipal L-function has a
common zero there. No common-zero conjecture is assumed.

This audits fixed coprime residue masks only. Nonunit residues, growing
moduli, genuinely correlated two-column masks and signed native CRT
boundaries remain open. No native row period is completed or norm-paid.
-/

namespace RiemannGaussian.ArithmeticOperatorCharacterCofactorAudit
noncomputable section
open Complex Filter
open ArithmeticOperatorGammaTwistAudit SuzukiCarryCorrelation
open scoped BigOperators Topology Classical

/-- Actual character-coded discrepancy of the prime and cofactor phases. -/
def row {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) (n : ℕ) : ℂ :=
  χ n * twistCommutator (primePhase y) n

private theorem character_divisor_product {q : ℕ} (χ : DirichletCharacter ℂ q)
    {n d : ℕ} (hd : d ∈ n.divisors) : χ n=χ d*χ (n/d) := by
  calc
    χ n = χ (d*(n/d) : ℕ) := congrArg (fun a : ℕ => χ a)
      (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)).symm
    _ = χ d*χ (n/d) := by simp only [Nat.cast_mul,map_mul]

/-- No character is dropped from the cofactor, even at a proper power. -/
theorem row_eq_divisor_cofactor {q : ℕ} (χ : DirichletCharacter ℂ q)
    (y : ℝ) (n : ℕ) :
    row χ y n = ∑ d ∈ n.divisors,
      (ArithmeticFunction.vonMangoldt d : ℂ)*χ d*primePhase y d*
        χ (n/d)*(1-primePhase y (n/d)) := by
  rw [row,twistCommutator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [character_divisor_product χ hd]
  ring

/-- Literal residue projection; this retains the row boundary exactly. -/
def apRow {q : ℕ} (a : ZMod q) (y : ℝ) (n : ℕ) : ℂ :=
  if (n : ZMod q)=a then twistCommutator (primePhase y) n else 0

/-- Exact character expansion is used only on a COPRIME residue. -/
theorem apRow_eq_characters {q : ℕ} [NeZero q] (a : ZMod q)
    (ha : IsUnit a) (y : ℝ) (n : ℕ) :
    apRow a y n = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹*row χ y n := by
  rw [eq_inv_mul_iff_mul_eq₀ <| by
    exact_mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp only [row,← mul_assoc,← Finset.sum_mul]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
  by_cases h : (n : ZMod q)=a
  · simp [apRow,h]
  · simp [apRow,h,Ne.symm h]

/-- A fixed additive CRT lag is the residue -h, without completing N. -/
theorem lag_mask_eq_apRow {q : ℕ} (h : ZMod q) (y : ℝ) (n : ℕ) :
    (if (n : ZMod q)+h=0 then twistCommutator (primePhase y) n else 0) =
      apRow (-h) y n := by
  simp only [apRow,add_eq_zero_iff_eq_neg]

/-- Arbitrary native cutoff and outer mask, with every character joined. -/
theorem finite_ap_join {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (y : ℝ) (X : ℕ) (test : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X,test n*apRow a y n) =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ a⁻¹*(∑ n ∈ Finset.Icc 1 X,test n*row χ y n) := by
  simp_rw [apRow_eq_characters a ha,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Ordinary character continuation in the ORIGINAL zero coordinate. -/
def response {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (y : ℝ) (z : ℂ) : ℂ :=
  χ.LFunction (z-I*y)*(-logDeriv χ.LFunction z)+deriv χ.LFunction z

private theorem prime_convolution {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) :
    (fun n : ℕ => χ n*primeLegDivisor (primePhase y) n) =
      LSeries.convolution
        (fun d => χ d*(ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d)
        (fun a => χ a) := by
  funext n
  rw [LSeries.convolution_def]
  dsimp only
  rw [Nat.sum_divisorsAntidiagonal
    (fun d a => χ d*(ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*χ a)]
  simp only [primeLegDivisor,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [character_divisor_product χ hd]
  ring

private theorem whole_convolution {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ) :
    (fun n : ℕ => χ n*coupledDivisor (primePhase y) n) =
      LSeries.convolution
        (fun d => χ d*(ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d)
        (fun a => χ a*primePhase y a) := by
  funext n
  rw [LSeries.convolution_def]
  dsimp only
  rw [Nat.sum_divisorsAntidiagonal
    (fun d a => χ d*(ArithmeticFunction.vonMangoldt d : ℂ)*primePhase y d*
      (χ a*primePhase y a))]
  simp only [coupledDivisor,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [character_divisor_product χ hd]
  ring

/-- Actual prime AND cofactor character appear in the convergent series.
No Dirichlet series is asserted to converge outside Re(s)>1. -/
theorem euler_response {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (row χ y) s=response χ y (s+I*y) := by
  have ht : 1<(s+I*y).re := by simpa using hs
  have hf := (LSeriesSummable_primePhase_iff
    (fun d => χ d*(ArithmeticFunction.vonMangoldt d : ℂ)) y s).mpr
      (χ.LSeriesSummable_twist_vonMangoldt ht)
  have hc := χ.LSeriesSummable_of_one_lt_re hs
  have hd := (LSeriesSummable_primePhase_iff (fun d => χ d) y s).mpr
    (χ.LSeriesSummable_of_one_lt_re ht)
  have he : row χ y = (fun n : ℕ => χ n*primeLegDivisor (primePhase y) n)-
      (fun n : ℕ => χ n*coupledDivisor (primePhase y) n) := by
    funext n
    simp only [row,Pi.sub_apply]
    rw [← primeLegDivisor_sub_coupled]
    ring
  have hp : LSeriesSummable (fun n => χ n*primeLegDivisor (primePhase y) n) s := by
    rw [prime_convolution]
    exact hf.convolution hc
  have hw : LSeriesSummable (fun n => χ n*coupledDivisor (primePhase y) n) s := by
    rw [whole_convolution]
    exact hf.convolution hd
  have hΛ : LSeries (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ))
      (s+I*y) = -deriv (LSeries (fun n : ℕ => χ n)) (s+I*y)/
        LSeries (fun n : ℕ => χ n) (s+I*y) := by
    have heq : (fun n : ℕ => χ n*(ArithmeticFunction.vonMangoldt n : ℂ)) =
        (fun n : ℕ => χ n)*(fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) := by
      funext n
      rfl
    rw [heq]
    exact χ.LSeries_twist_vonMangoldt_eq ht
  rw [he,LSeries_sub hp hw,prime_convolution,whole_convolution,
    LSeries_convolution' hf hc,LSeries_convolution' hf hd,
    LSeries_primePhase,LSeries_primePhase,hΛ,
    ← χ.deriv_LFunction_eq_deriv_LSeries ht,← χ.LFunction_eq_LSeries ht,
    ← χ.LFunction_eq_LSeries hs]
  have hn : χ.LFunction (s+I*y)≠0 := by
    rw [χ.LFunction_eq_LSeries ht]
    exact χ.LSeries_ne_zero_of_one_lt_re ht
  unfold response
  simp only [add_sub_cancel_right,logDeriv_apply]
  field_simp [hn]
  ring

theorem row_summable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (y : ℝ) {s : ℂ} (hs : 1<s.re) : LSeriesSummable (row χ y) s := by
  have ht : 1<(s+I*y).re := by simpa using hs
  have hf := (LSeriesSummable_primePhase_iff
    (fun d => χ d*(ArithmeticFunction.vonMangoldt d : ℂ)) y s).mpr
      (χ.LSeriesSummable_twist_vonMangoldt ht)
  have hc := χ.LSeriesSummable_of_one_lt_re hs
  have hd := (LSeriesSummable_primePhase_iff (fun d : ℕ => χ d) y s).mpr
    (χ.LSeriesSummable_of_one_lt_re ht)
  have he : row χ y = (fun n : ℕ => χ n*primeLegDivisor (primePhase y) n)-
      (fun n : ℕ => χ n*coupledDivisor (primePhase y) n) := by
    funext n
    simp only [row,Pi.sub_apply]
    rw [← primeLegDivisor_sub_coupled]
    ring
  rw [he,prime_convolution,whole_convolution]
  exact (hf.convolution hc).sub (hf.convolution hd)

/-- The nonprincipal response is analytic when its actual L divisor
does not meet the chosen point. This is NOT a common-zero theorem. -/
theorem analyticAt_response_of_no_common_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (y : ℝ) (z : ℂ)
    (hz : χ.LFunction z≠0) : AnalyticAt ℂ (response χ y) z := by
  have ha (w : ℂ) := (DirichletCharacter.differentiable_LFunction hχ).analyticAt w
  have hc : AnalyticAt ℂ (fun w => χ.LFunction (w-I*y)) z :=
    AnalyticAt.comp (ha (z-I*y)) (analyticAt_id.sub analyticAt_const)
  exact hc.mul ((ha z).deriv.div (ha z) hz).neg |>.add (ha z).deriv

/-- No nonprincipal L-function is locally identically zero: its entire
continuation and its nonzero value at two give a genuine finite order. -/
theorem analyticOrderAt_LFunction_ne_top {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (z : ℂ) :
    analyticOrderAt χ.LFunction z≠⊤ := by
  intro htop
  have ha : AnalyticOnNhd ℂ χ.LFunction Set.univ := fun w _ =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt w
  have he : χ.LFunction=(0 : ℂ → ℂ) := ha.eq_of_eventuallyEq
    analyticOnNhd_const (analyticOrderAt_eq_top.mp htop)
  have hn : χ.LFunction (2 : ℂ)≠0 := by
    rw [χ.LFunction_eq_LSeries (by norm_num)]
    exact χ.LSeries_ne_zero_of_one_lt_re (by norm_num)
  exact hn (by rw [he]; rfl)

/-- Exact nonprincipal source, with its own ACTUAL analytic multiplicity.
The cofactor L-value may annihilate it and is not assumed nonzero. -/
theorem tendsto_response_residue {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (y : ℝ) (z : ℂ) :
    Tendsto (fun w : ℂ => (w-z)*response χ y w) (𝓝[≠] z)
      (𝓝 (-(analyticOrderNatAt χ.LFunction z : ℂ)*χ.LFunction (z-I*y))) := by
  have ha (w : ℂ) := (DirichletCharacter.differentiable_LFunction hχ).analyticAt w
  have ht : Tendsto (fun w : ℂ => w-z) (𝓝[≠] z) (𝓝 0) := by
    simpa using (show Tendsto (fun w : ℂ => w-z) (𝓝[≠] z) (𝓝 (z-z)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hl := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt (ha z)
    (analyticOrderAt_LFunction_ne_top χ hχ z)).neg
  have hc : Tendsto (fun w : ℂ => χ.LFunction (w-I*y)) (𝓝[≠] z)
      (𝓝 (χ.LFunction (z-I*y))) :=
    (ContinuousAt.comp' (g := χ.LFunction) (f := fun w : ℂ => w-I*y)
      (ha (z-I*y)).continuousAt
      (show ContinuousAt (fun w : ℂ => w-I*y) z from
        (continuous_id.sub continuous_const).continuousAt)).tendsto.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (deriv χ.LFunction) (𝓝[≠] z) (𝓝 (deriv χ.LFunction z)) :=
    (ha z).deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := (hl.mul hc).add (ht.mul hd)
  simp only [zero_mul,add_zero] at h
  convert h using 1
  funext w
  unfold response
  ring

/-- The entire nonprincipal response is also analytic at the density
point after the cofactor character is retained. -/
theorem analyticAt_nonprincipal_density {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ≠1) (y : ℝ) :
    AnalyticAt ℂ (response χ y) 1 :=
  analyticAt_response_of_no_common_zero χ hχ y 1 (χ.LFunction_apply_one_ne_zero hχ)

/-- One signed finite character code, before any individual allowance. -/
def codeResponse {q : ℕ} [NeZero q] (S : Finset (DirichletCharacter ℂ q))
    (coeff : DirichletCharacter ℂ q → ℂ) (y : ℝ) (z : ℂ) : ℂ :=
  ∑ χ ∈ S,coeff χ*response χ y z

/-- Actual multiplicities and the exact cofactor values remain in one
signed scalar residue. They are not separately norm-paid. -/
theorem tendsto_code_residue {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (coeff : DirichletCharacter ℂ q → ℂ)
    (hS : ∀ χ ∈ S,χ≠1) (y : ℝ) (z : ℂ) :
    Tendsto (fun w : ℂ => (w-z)*codeResponse S coeff y w) (𝓝[≠] z)
      (𝓝 (∑ χ ∈ S,coeff χ*
        (-(analyticOrderNatAt χ.LFunction z : ℂ)*χ.LFunction (z-I*y)))) := by
  have h := tendsto_finsetSum S (fun χ hχ =>
    (tendsto_response_residue χ (hS χ hχ) y z).const_mul (coeff χ))
  convert h using 1
  funext w
  unfold codeResponse
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- A code residue at a zeta zero needs both an additional actual
nonprincipal L-zero AND a nonzero cofactor value. This is the source
preflight obstruction, with every multiplicity retained. -/
theorem source_forces_common_L_zero_and_cofactor {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (coeff : DirichletCharacter ℂ q → ℂ)
    (hS : ∀ χ ∈ S,χ≠1) (y : ℝ) (rho : NontrivialZetaZero)
    {v : ℂ} (hv : v≠0)
    (hsource : Tendsto (fun w : ℂ => (w-rho.1)*codeResponse S coeff y w)
      (𝓝[≠] rho.1) (𝓝 v)) :
    ∃ χ ∈ S,χ≠1 ∧ coeff χ≠0 ∧ χ.LFunction rho.1=0 ∧
      χ.LFunction (rho.1-I*y)≠0 := by
  by_contra h
  have he : (∑ χ ∈ S,coeff χ*
      (-(analyticOrderNatAt χ.LFunction rho.1 : ℂ)*χ.LFunction (rho.1-I*y)))=0 := by
    apply Finset.sum_eq_zero
    intro χ hχ
    by_cases hc : coeff χ=0
    · simp [hc]
    by_cases hf : χ.LFunction (rho.1-I*y)=0
    · simp [hf]
    have hz : χ.LFunction rho.1≠0 := by
      intro hz
      exact h ⟨χ,hχ,hS χ hχ,hc,hz,hf⟩
    have ho : analyticOrderNatAt χ.LFunction rho.1=0 := by
      simp only [analyticOrderNatAt,analyticOrderAt_eq_zero.mpr (Or.inr hz),ENat.toNat_zero]
    simp [ho]
  exact hv (tendsto_nhds_unique hsource
    (by simpa only [he] using tendsto_code_residue S coeff hS y rho.1))

/-- If the extra common-zero input is absent, the entire code is
regular at the selected zeta coordinate, not merely residue-free. -/
theorem analyticAt_code_of_no_common_zero {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (coeff : DirichletCharacter ℂ q → ℂ)
    (hS : ∀ χ ∈ S,χ≠1) (y : ℝ) (z : ℂ)
    (hz : ∀ χ ∈ S,χ.LFunction z≠0) :
    AnalyticAt ℂ (codeResponse S coeff y) z := by
  have h := Finset.analyticAt_sum S (fun χ hχ =>
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => coeff χ) z).mul
        (analyticAt_response_of_no_common_zero χ (hS χ hχ) y z (hz χ hχ)))
  exact h.congr (Filter.Eventually.of_forall (fun w => by
    simp only [Finset.sum_apply,Pi.mul_apply,codeResponse]))

/-- Principal deletion removes density as an analytic germ, not just
as an ordinary residue. It supplies no new common-zero information. -/
theorem analyticAt_code_density {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (coeff : DirichletCharacter ℂ q → ℂ)
    (hS : ∀ χ ∈ S,χ≠1) (y : ℝ) :
    AnalyticAt ℂ (codeResponse S coeff y) 1 :=
  analyticAt_code_of_no_common_zero S coeff hS y 1
    (fun χ hχ => χ.LFunction_apply_one_ne_zero (hS χ hχ))

/-- Both original density coordinates are regular after principal
deletion. The prime phase and cofactor phase are not interchanged. -/
theorem analyticAt_code_shifted_density {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) (coeff : DirichletCharacter ℂ q → ℂ)
    (hS : ∀ χ ∈ S,χ≠1) (y : ℝ) :
    AnalyticAt ℂ (codeResponse S coeff y) (1+I*y) :=
  analyticAt_code_of_no_common_zero S coeff hS y (1+I*y)
    (fun χ hχ => χ.LFunction_ne_zero_of_one_le_re (Or.inl (hS χ hχ)) (by simp))

/-- Only finitely many local Euler factors distinguish the principal
character from zeta; these are not completion errors. -/
def principalFactor (q : ℕ) (z : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors,(1-(p : ℂ)^(-z))

theorem analyticAt_principalFactor (q : ℕ) (z : ℂ) :
    AnalyticAt ℂ (principalFactor q) z := by
  have hp (p : ℕ) (hp : p∈q.primeFactors) :
      AnalyticAt ℂ (fun w : ℂ => 1-(p : ℂ)^(-w)) z := by
    have hp0 : (p : ℂ)≠0 := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    let : NeZero (p : ℂ) := ⟨hp0⟩
    have ha := (differentiable_const_cpow_of_neZero (p : ℂ)).analyticAt (-z)
    exact analyticAt_const.sub (AnalyticAt.comp ha analyticAt_id.neg)
  exact (Finset.analyticAt_prod q.primeFactors hp).congr
    (Filter.Eventually.of_forall (fun w => by simp only [principalFactor,Finset.prod_apply]))

/-- No finite excluded-prime factor vanishes in the positive half-plane. -/
theorem principalFactor_ne_zero (q : ℕ) {z : ℂ} (hz : 0<z.re) :
    principalFactor q z≠0 := by
  unfold principalFactor
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hnorm : ‖(p : ℂ)^(-z)‖<1 := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.prime_of_mem_primeFactors hp).pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt) (by simpa using hz)
  intro hzero
  have he := congrArg norm (sub_eq_zero.mp hzero)
  simp only [norm_one] at he
  linarith

private theorem principal_germ {q : ℕ} [NeZero q] {z : ℂ} (hz : z≠1) :
    (1 : DirichletCharacter ℂ q).LFunction =ᶠ[𝓝 z]
      principalFactor q*riemannZeta := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
  exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hw

/-- The principal character retains exactly every genuine zeta-zero
multiplicity. Principal coding is not new independent source information. -/
theorem principal_order {q : ℕ} [NeZero q] (rho : NontrivialZetaZero) :
    analyticOrderAt (1 : DirichletCharacter ℂ q).LFunction rho.1 =
      analyticOrderAt riemannZeta rho.1 := by
  rw [analyticOrderAt_congr (principal_germ (q := q) rho.2.2.2),
    analyticOrderAt_mul (analyticAt_principalFactor q rho.1)
      (analyticAt_riemannZeta_nontrivialZero rho),
    analyticOrderAt_eq_zero.mpr (Or.inr (principalFactor_ne_zero q
      (NontrivialZetaZero.zero_lt_re rho))),zero_add]

/-- The principal cofactor value at the matched real coordinate is
nonzero, by the existing real-strip eta theorem and finite Euler factors. -/
theorem principal_matched_cofactor_ne_zero {q : ℕ} [NeZero q]
    (rho : NontrivialZetaZero) :
    (1 : DirichletCharacter ℂ q).LFunction (rho.1.re : ℂ)≠0 := by
  have hr : (rho.1.re : ℂ)≠1 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [ofReal_re,one_re] at hh
    linarith [NontrivialZetaZero.re_lt_one rho]
  change DirichletCharacter.LFunctionTrivChar q (rho.1.re : ℂ)≠0
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hr]
  exact mul_ne_zero (principalFactor_ne_zero q (NontrivialZetaZero.zero_lt_re rho))
    (ArithmeticOperatorTwistSourceAudit.real_strip_zeta_ne_zero
      (NontrivialZetaZero.zero_lt_re rho) (NontrivialZetaZero.re_lt_one rho))

/-- Exact principal-character commutator source, retaining every actual
analytic multiplicity and the literal cofactor response. -/
theorem tendsto_principal_source {q : ℕ} [NeZero q] (rho : NontrivialZetaZero) :
    Tendsto (fun z : ℂ => (z-rho.1)*response (1 : DirichletCharacter ℂ q) rho.1.im z)
      (𝓝[≠] rho.1) (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)*
        (1 : DirichletCharacter ℂ q).LFunction (rho.1.re : ℂ))) := by
  let χ : DirichletCharacter ℂ q := 1
  have ha (z : ℂ) (hz : z≠1) : AnalyticAt ℂ χ.LFunction z := by
    have hd : DifferentiableOn ℂ χ.LFunction ({(1 : ℂ)}ᶜ) := fun w hw =>
      (χ.differentiableAt_LFunction w (Or.inl hw)).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hz)
  have he : rho.1-I*rho.1.im=(rho.1.re : ℂ) := by apply Complex.ext <;> simp
  have hr : rho.1-I*rho.1.im≠1 := by
    rw [he]
    intro h
    have hh := congrArg Complex.re h
    simp only [ofReal_re,one_re] at hh
    linarith [NontrivialZetaZero.re_lt_one rho]
  have hfinite : analyticOrderAt χ.LFunction rho.1≠⊤ := by
    rw [principal_order rho]
    exact analyticOrderAt_riemannZeta_nontrivialZero_ne_top rho
  have hm : analyticOrderNatAt χ.LFunction rho.1=analyticZetaZeroMultiplicity rho := by
    unfold analyticZetaZeroMultiplicity analyticOrderNatAt
    rw [principal_order rho]
  have hl := (AnalyticAt.tendsto_sub_mul_logDeriv_analyticOrderNatAt
    (ha rho.1 rho.2.2.2) hfinite).neg
  rw [hm] at hl
  have hc : Tendsto (fun w : ℂ => χ.LFunction (w-I*rho.1.im)) (𝓝[≠] rho.1)
      (𝓝 (χ.LFunction (rho.1.re : ℂ))) := by
    rw [← he]
    exact (ContinuousAt.comp' (g := χ.LFunction) (f := fun w : ℂ => w-I*rho.1.im)
      (ha (rho.1-I*rho.1.im) hr).continuousAt
      (show ContinuousAt (fun w : ℂ => w-I*rho.1.im) rho.1 from
        (continuous_id.sub continuous_const).continuousAt)).tendsto.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun w : ℂ => w-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun w : ℂ => w-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hd : Tendsto (deriv χ.LFunction) (𝓝[≠] rho.1) (𝓝 (deriv χ.LFunction rho.1)) :=
    (ha rho.1 rho.2.2.2).deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := (hl.mul hc).add (ht.mul hd)
  simp only [zero_mul,add_zero] at h
  convert h using 1
  funext w
  unfold response
  ring

theorem principal_source_ne_zero {q : ℕ} [NeZero q] (rho : NontrivialZetaZero) :
    -(analyticZetaZeroMultiplicity rho : ℂ)*
      (1 : DirichletCharacter ℂ q).LFunction (rho.1.re : ℂ)≠0 :=
  mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr
    (analyticZetaZeroMultiplicity_positive rho).ne')) (principal_matched_cofactor_ne_zero rho)

/-- Continuation of the fixed coprime residue projection. -/
def apResponse {q : ℕ} [NeZero q] (a : ZMod q) (y : ℝ) (z : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹*codeResponse Finset.univ (fun χ => χ a⁻¹) y z

/-- The projected continuation agrees with the actual native residue
coefficients on the Euler half-plane. Every prime-power fiber remains. -/
theorem ap_euler_response {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (y : ℝ) {s : ℂ} (hs : 1<s.re) :
    LSeries (apRow a y) s=apResponse a y (s+I*y) := by
  have he : apRow a y = (q.totient : ℂ)⁻¹ •
      ∑ χ : DirichletCharacter ℂ q,χ a⁻¹ • row χ y := by
    funext n
    simp only [Pi.smul_apply,Finset.sum_apply,smul_eq_mul,apRow_eq_characters a ha]
  rw [he,LSeries_smul,LSeries_sum (fun χ _ => (row_summable χ y hs).smul (χ a⁻¹))]
  unfold apResponse codeResponse
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  rw [LSeries_smul,euler_response χ y hs]

/-- Exact principal/nonprincipal split, with its cofactor factors intact. -/
theorem apResponse_eq_principal_complement {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) (y : ℝ) (z : ℂ) :
    apResponse a y z = (q.totient : ℂ)⁻¹*
      (response (1 : DirichletCharacter ℂ q) y z+
        codeResponse (Finset.univ.erase 1) (fun χ => χ a⁻¹) y z) := by
  have ha' : IsUnit a⁻¹ := isUnit_of_dvd_one ⟨a,(ZMod.inv_mul_of_unit a ha).symm⟩
  unfold apResponse codeResponse
  rw [← Finset.add_sum_erase Finset.univ (fun χ : DirichletCharacter ℂ q =>
    χ a⁻¹*response χ y z) (Finset.mem_univ 1),MulChar.one_apply ha',one_mul]

/-- Absence of ADDITIONAL common L-zeros leaves the old actual zeta
residue in every fixed coprime progression. No such absence is assumed
unconditionally, and no native cutoff asymptotic is inferred here. -/
theorem tendsto_ap_source_of_no_common_zero {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) (rho : NontrivialZetaZero)
    (hL : ∀ χ : DirichletCharacter ℂ q,χ≠1 → χ.LFunction rho.1≠0) :
    Tendsto (fun z : ℂ => (z-rho.1)*apResponse a rho.1.im z) (𝓝[≠] rho.1)
      (𝓝 ((q.totient : ℂ)⁻¹*(-(analyticZetaZeroMultiplicity rho : ℂ)*
        (1 : DirichletCharacter ℂ q).LFunction (rho.1.re : ℂ)))) := by
  have hS : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,χ≠1 :=
    fun _ hχ => (Finset.mem_erase.mp hχ).1
  have hA := analyticAt_code_of_no_common_zero (Finset.univ.erase 1)
    (fun χ => χ a⁻¹) hS rho.1.im rho.1 (fun χ hχ => hL χ (hS χ hχ))
  have ht : Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1) (𝓝 0) := by
    simpa using (show Tendsto (fun z : ℂ => z-rho.1) (𝓝[≠] rho.1) (𝓝 (rho.1-rho.1)) from
      (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hzero := ht.mul (hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at hzero
  have h := ((tendsto_principal_source (q := q) rho).add hzero).const_mul (q.totient : ℂ)⁻¹
  simp only [add_zero] at h
  convert h using 1
  funext z
  rw [apResponse_eq_principal_complement a ha]
  ring

theorem ap_source_ne_zero {q : ℕ} [NeZero q] (rho : NontrivialZetaZero) :
    (q.totient : ℂ)⁻¹*(-(analyticZetaZeroMultiplicity rho : ℂ)*
      (1 : DirichletCharacter ℂ q).LFunction (rho.1.re : ℂ))≠0 :=
  mul_ne_zero (inv_ne_zero (by exact_mod_cast
    (Nat.totient_pos.mpr q.pos_of_neZero).ne')) (principal_source_ne_zero rho)

/-- Literal native row with arbitrary first-column data, not asserted
to satisfy the actual Gamma or Mobius identities. -/
def freePacket {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ)
    (X : ℕ) (test w : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,test n*χ n*
    ArithmeticOperatorTwistSourceAudit.defect w y n

/-- Exact joined scalar includes every literal cutoff and cofactor. -/
def joinedKernel {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ)
    (X : ℕ) (test : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,if d∣n then
    test n*χ d*χ (n/d)*primePhase y d*(1-primePhase y (n/d)) else 0

private theorem defect_finite (w : ℕ → ℂ) (y : ℝ) {n X : ℕ}
    (hn : 0<n) (hnX : n≤X) :
    ArithmeticOperatorTwistSourceAudit.defect w y n =
      ∑ d ∈ Finset.Icc 1 X,if d∣n then
        w d*primePhase y d*(1-primePhase y (n/d)) else 0 := by
  have he : (Finset.Icc 1 X).filter (fun d => d∣n)=n.divisors := by
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
    constructor
    · rintro ⟨_,hd⟩
      exact ⟨hd,hn.ne'⟩
    · rintro ⟨hd,_⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,(Nat.le_of_dvd hn hd).trans hnX⟩,hd⟩
  unfold ArithmeticOperatorTwistSourceAudit.defect
    ArithmeticOperatorCommutatorAudit.divisorConvolution
  rw [Nat.sum_divisorsAntidiagonal
    (fun d a => w d*primePhase y d*(1-primePhase y a)),← he,Finset.sum_filter]

/-- All finite bookkeeping remains true for arbitrary weights and
outer masks. No actual-prime bound is obtained by this join. -/
theorem freePacket_eq_scalar {q : ℕ} (χ : DirichletCharacter ℂ q) (y : ℝ)
    (X : ℕ) (test w : ℕ → ℂ) :
    freePacket χ y X test w =
      ∑ d ∈ Finset.Icc 1 X,w d*joinedKernel χ y X test d := by
  unfold freePacket
  simp_rw [joinedKernel,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [defect_finite w y (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs with hd
  · have he : χ n=χ d*χ (n/d) := by
      calc
        χ n=χ (d*(n/d) : ℕ) := congrArg (fun a : ℕ => χ a) (Nat.mul_div_cancel' hd).symm
        _=χ d*χ (n/d) := by simp only [Nat.cast_mul,map_mul]
    rw [he]
    ring
  · simp

/-- Specialization restores the unaltered actual Mangoldt row. -/
theorem freePacket_actual {q : ℕ} (χ : DirichletCharacter ℂ q)
    (y : ℝ) (X : ℕ) (test : ℕ → ℂ) :
    freePacket χ y X test (fun d => (ArithmeticFunction.vonMangoldt d : ℂ)) =
      ∑ n ∈ Finset.Icc 1 X,test n*row χ y n := by
  simp only [freePacket,ArithmeticOperatorTwistSourceAudit.defect_eq_commutator,row,mul_assoc]

/-- A universal free-column allowance is possible only for a zero
joined kernel. Free controls are NOT actual Gamma-compatible data. -/
theorem bound_forall_free_columns_iff {q : ℕ} (χ : DirichletCharacter ℂ q)
    (y : ℝ) (X : ℕ) (test : ℕ → ℂ) (B : ℝ) :
    (∀ w,‖freePacket χ y X test w‖≤B) ↔
      0≤B ∧ ∀ d ∈ Finset.Icc 1 X,joinedKernel χ y X test d=0 := by
  simp_rw [freePacket_eq_scalar]
  exact ArithmeticOperatorGramAudit.scalar_bound_forall_weights_iff _ _ _

end
end RiemannGaussian.ArithmeticOperatorCharacterCofactorAudit
